{-# OPTIONS_GHC -funbox-strict-fields #-}
module Database.Zippy.Types
    ( ZippyStorage(..), ZippyDataType(..)

    , ZippyD(..)

    , SZippyD(..), InMemoryD(..), InMemoryAtomD(..)
    , eraseInMemoryD

    , ZippyTyName(..), ZippyDataConName(..), ZippyTyRef(..)
    , GenericZippyTyCon(..), ZippyTyCon(..), GenericZippyTyCon(..)
    , GenericZippyField(..), ZippyField(..), zippyFieldType
    , ZippyDataArgName(..), ZippyTyVarName(..)
    , GenericZippyDataCon(..), ZippyDataCon(..), ZippyFieldType(..)
    , ZippySimpleT(..), ZippyAlgebraicT(..), GenericZippyAlgebraicT(..)
    , ZippyT(..), ZippySchema(..)
    , zippySchemaRootType, mapZippyAlgebraicT

    , Zipper(..), ZipperCursorInfo(..), ModificationState(..)
    , Context(..), Movement(..)

    , TransactionLog(..), TransactionEntry(..)

    , MoveResult(..), CurResult(..)
    , TxF(..), Tx(..), TxnStepsChan(..), TxCommitStatus(..)
    , txnStepTxnId

    , move, moveOOB, cur, cut, childRef, curTy, parentArgHole, commit, abort
    , logAction

    , TxnId(..), RunTxnStepFn(..), TxnStep(..)
    , TxLogAction(..), simpleTxActionLogger, txResultActionLogger
    , TxState(..), ZippyState(..), zippyRootType

    , ZippyDiskState(..), ZippyDiskCache(..), emptyDiskCache

    , spineStrictMap
    ) where

import Control.Monad.Free.Church
import Control.Concurrent.MVar
import Control.Concurrent.Chan
import Control.Concurrent.MVar
import Control.DeepSeq
import Control.Applicative

import Data.ByteString (ByteString)
import Data.Coerce
import Data.HashMap.Strict (HashMap)
import Data.Hashable (Hashable(..), hashWithSalt)
import Data.IORef
import Data.Int
import Data.Monoid
import Data.Sequence (Seq)
import Data.String
import Data.Text (Text)
import Data.Vector (Vector)
import Data.Word
import Data.Time.Clock.POSIX
import Data.HashPSQ (HashPSQ)

import qualified Data.HashPSQ as PSQ
import qualified Data.ByteString as BS
import qualified Data.Text as T
import qualified Data.Vector as V

import System.IO

-- * User Defined Kinds

-- | A user-defined Kind that we use to signify whether a ZippyD is stored
--   in-memory or on-disk.
--
--   The use of this kind lets us specify the type of functions that only
--   operate on data that have been brought into memory. This means that
--   we can easily restrict which parts of the codebase get disk ZippyD access.
data ZippyStorage = OnDisk
                  | InMemory

data ZippyDataType = Composite
                   | Atom

-- * Zippy Data

-- | Data structure capable of storing all Zippy types.
--
--   Although it may look like it, this data structure contains no typing information.
--   In order to correctly interpret the data, you must also know the type of data
--   being stored.
--
--   We do however use phantom types to enforce invariants on the location of particular
--   data, to keep track of whether the data is on disk or in memory at the type level
data ZippyD    :: ZippyStorage -> ZippyDataType -> * -> * where
    IntegerD   :: !Int64                       -> ZippyD InMemory Atom Int64
    TextD      :: !Text                        -> ZippyD InMemory Atom Text
    FloatingD  :: !Double                      -> ZippyD InMemory Atom Double
    BinaryD    :: !ByteString                  -> ZippyD InMemory Atom ByteString
    CompositeD :: !Word16 -> !(Vector SZippyD) -> ZippyD InMemory Composite a

    OnDiskD    :: !Word64                      -> ZippyD OnDisk dt a

-- ** Existentials restricting the types of zippy data

-- | A GADT that can be used to erase all type-level information about the type of ZippyD
data SZippyD where
    SZippyD :: !(ZippyD s dt a) -> SZippyD

instance NFData SZippyD where
    rnf a = a `seq` () -- Since SZippyD is strict and ZippyD is strict in all its field, this evaluates it "enough"

-- | A simple ZippyD wrapper that can only hold in-memory atoms (so no CompositeD or OnDiskD)
data InMemoryAtomD where
    InMemoryAtomD :: !(ZippyD InMemory Atom a) -> InMemoryAtomD

-- | A simple ZippyD wrapper that can only hold in-memory ZippyDs (so no OnDiskD)
data InMemoryD where
    InMemoryD :: !(ZippyD InMemory dt a) -> InMemoryD

deriving instance Show (ZippyD s dt a)
instance Show SZippyD where
    show (SZippyD z) = show z
instance Show InMemoryAtomD where
    show (InMemoryAtomD z) = show z
instance Show InMemoryD where
    show (InMemoryD z) = show z

instance Eq (ZippyD s dt a) where
    x == y = SZippyD x == SZippyD y
instance Ord (ZippyD s dt a) where
    compare x y = compare (SZippyD x) (SZippyD y)

instance Eq SZippyD where
    SZippyD (IntegerD x) == SZippyD (IntegerD y) = x == y
    SZippyD (TextD x) == SZippyD (TextD y) = x == y
    SZippyD (FloatingD x) == SZippyD (FloatingD y) = x == y
    SZippyD (BinaryD x) == SZippyD (BinaryD y) = x == y
    SZippyD (CompositeD xTag xArgs) == SZippyD (CompositeD yTag yArgs) = xTag == yTag && xArgs == yArgs
    SZippyD (OnDiskD x) == SZippyD (OnDiskD y) = x == y
    SZippyD _ == SZippyD _ = False
instance Ord SZippyD where
    compare (SZippyD (IntegerD x)) (SZippyD (IntegerD y)) = compare x y
    compare (SZippyD (TextD x)) (SZippyD (TextD y)) = compare x y
    compare (SZippyD (FloatingD x)) (SZippyD (FloatingD y)) = compare x y
    compare (SZippyD (BinaryD x)) (SZippyD (BinaryD y)) = compare x y
    compare (SZippyD (CompositeD xTag xArgs)) (SZippyD (CompositeD yTag yArgs)) = compare (xTag, xArgs) (yTag, yArgs)
    compare (SZippyD (IntegerD _)) _ = LT
    compare _ (SZippyD (IntegerD _)) = GT
    compare (SZippyD (TextD _)) _ = LT
    compare _ (SZippyD (TextD _)) = GT
    compare (SZippyD (FloatingD _)) _ = LT
    compare _ (SZippyD (FloatingD _)) = GT
    compare (SZippyD (BinaryD _)) _ = LT
    compare _ (SZippyD (BinaryD _)) = GT
    compare (SZippyD (CompositeD _ _)) _ = LT
    compare _ (SZippyD (CompositeD _ _)) = GT
    compare (SZippyD (OnDiskD _)) _ = LT

-- | Forget the type-level fact that we have this ZippyD in memory
eraseInMemoryD :: InMemoryD -> SZippyD
eraseInMemoryD (InMemoryD a) = SZippyD a

-- * Zippy types
--
--   We make extensive use of vectors here because (1) the number of types and constructors is relatively small and
--   (2) vectors are O(1) with little overhead

data ZippyTyName = ZippyTyName
                 { tyModule :: !Text
                 , tyName   :: !Text }
                   deriving (Show, Eq, Ord)
data GenericZippyTyCon tyRef = ZippyTyCon !ZippyTyName !(Vector tyRef)
                               deriving (Show, Eq, Ord, Functor)
newtype ZippyTyVarName = ZippyTyVarName Text
    deriving (Show, Eq, Ord, IsString, Hashable)
newtype ZippyDataConName = ZippyDataConName Text
    deriving (Show, Eq, Ord, IsString)

newtype ZippyTyRef = ZippyTyRef Int
    deriving (Show, Eq, Ord, Hashable)
newtype ZippyDataArgName = ZippyDataArgName Text
    deriving (Show, Eq, Ord, IsString)

data ZippyFieldType tyRef = SimpleFieldT !ZippySimpleT
                          | RefFieldT    !tyRef
                            deriving (Show, Eq, Ord, Functor)

data ZippyScopedTyRef = LocalTyRef !ZippyTyRef
                      | GlobalTyRef !ZippyTyRef
                        deriving (Show, Eq, Ord)

data GenericZippyField tyRef =
    ZippyNamedField !ZippyDataArgName !tyRef
  | ZippyUnnamedField !tyRef
    deriving (Show, Eq, Ord, Functor)

type ZippyField = GenericZippyField (ZippyFieldType ZippyTyRef)

zippyFieldType :: GenericZippyField tyRef -> tyRef
zippyFieldType (ZippyNamedField _ x) = x
zippyFieldType (ZippyUnnamedField x) = x

data GenericZippyDataCon tyRef =
    ZippyDataCon !ZippyDataConName !(Vector (GenericZippyField tyRef))
    deriving (Show, Eq, Ord, Functor)

type ZippyDataCon = GenericZippyDataCon (ZippyFieldType ZippyTyRef)

data ZippySimpleT = IntegerT
                  | TextT
                  | FloatingT
                  | BinaryT
                    deriving (Show, Eq, Ord)

type ZippyTyCon = GenericZippyTyCon ZippyTyVarName
data GenericZippyAlgebraicT tyVar tyRef =
    ZippyAlgebraicT !(GenericZippyTyCon tyVar) !(Vector (GenericZippyDataCon tyRef))
    deriving (Show, Eq, Ord, Functor)

type ZippyAlgebraicT = GenericZippyAlgebraicT (ZippyFieldType ZippyTyRef) (ZippyFieldType ZippyTyRef)

data ZippyT = SimpleT !ZippySimpleT
            | AlgebraicT !ZippyAlgebraicT
              deriving (Show, Eq, Ord)

data ZippySchema = ZippySchema
                 { zippySchemaRoot :: !ZippyTyRef
                 , zippyTypes      :: !(Vector ZippyT) }
                   deriving (Show, Eq, Ord)

zippySchemaRootType :: ZippySchema -> ZippyT
zippySchemaRootType (ZippySchema { zippySchemaRoot = ZippyTyRef rootTyRef, zippyTypes = allTypes }) =
    allTypes V.! fromIntegral rootTyRef

mapZippyAlgebraicT :: (a -> a') -> (b -> b') -> GenericZippyAlgebraicT a b -> GenericZippyAlgebraicT a' b'
mapZippyAlgebraicT fa fb (ZippyAlgebraicT tyCon args) = ZippyAlgebraicT (fmap fa tyCon) (fmap (fmap fb) args)

instance Hashable ZippyTyName where
    hashWithSalt salt (ZippyTyName mod name) = hash mod `hashWithSalt` hash name `hashWithSalt` salt

-- * The Zipper type

-- | As we enter deeper into the data structure, we want to keep track of whether or not we make any
--   changes. If we make no changes, then we should just link back to the old version of things.
data ModificationState = StillOnDisk !Word64
                       | OnlyInMemory
                         deriving Show

-- | The Zipper type keeps track of all the 'context' surrounding our position
--   in the database.
data Zipper = Zipper !ModificationState !ZippyT !InMemoryD ![Context]
              deriving Show

data ZipperCursorInfo = ZipperCursorInfo
                      { zipperCurType :: !ZippyT
                      , zipperParentArgHole :: !(Maybe Int) }
                        deriving Show

-- | A datastructure describing an unzipped CompositeD.
--
--   `Within modified argHole tag args` represents a CompositeD with a hole in the argHole'th argument.
--   When the context is rezipped, the resulting CompositeD will have tag `tag` and arguments
--   `args`, but with the argHole'th argument replaced by the rezipped value
data Context = Within !ModificationState !ZippyT !Int !Word16 !(Vector SZippyD)
               deriving Show

-- | All possible movements within a structure
data Movement = Replace !InMemoryD
              | Down !Int
              | Up
                deriving Show

-- * Transactions

-- | Transaction logs log all the directions we've moved through the data structure,
--   and what we found there.
newtype TransactionLog = TransactionLog (Seq TransactionEntry)
    deriving (Show, Monoid)

data TransactionEntry where
    TxnDown :: !Int -> TransactionEntry
    TxnUp :: TransactionEntry
    TxnCheckTag :: !Word16 -> TransactionEntry
    TxnCheckAtom :: !(ZippyD InMemory Atom a) -> TransactionEntry
    TxnCheckChildDiskRef :: !Int -> !Word64 -> TransactionEntry
    TxnReplace :: !(ZippyD InMemory dt a) -> TransactionEntry
deriving instance Show TransactionEntry

-- ** The Tx monad

data MoveResult = AtRoot
                | CannotDescendIntoAtom
                | NoSuchChild !Int
                | Moved !ZippyT
                  deriving Show

data CurResult = CurHasTag !Word16
               | CurIsAtom !InMemoryAtomD
                 deriving Show

data RebaseFailureMode = AbortOnFailedRebase -- ^ If a sync fails, abort the transaction
                       | RestartFromLastSavePoint -- ^ If a sync fails, restart the current part of the transaction from the last save point, or abort if there is none.
                         deriving Show

data TxF next = MoveTx !Movement (MoveResult -> next)
              | CurTx (CurResult -> next)
              | ChildRefTx !Int (Maybe SZippyD -> next)

              -- Path querying information...
              | ParentArgHoleTx (Maybe Int -> next)
              | CurTyTx ((ZippyT, ZippySchema) -> next)

              -- Zipper cutting
              | CutTx (Zipper -> next)
              | MoveOOBTx !Zipper !Movement ((Zipper, MoveResult) -> next)

              | RebaseTx !RebaseFailureMode next
              | CommitTx (TxCommitStatus -> next)
              | AbortTx

              | LogActionTx !TxLogAction next
                deriving Functor
type Tx = F TxF

type TxnStepsChan = Chan TxnStep

move :: Movement -> Tx MoveResult
move movement = liftF (MoveTx movement id)

moveOOB :: Zipper -> Movement -> Tx (Zipper, MoveResult)
moveOOB z movement = liftF (MoveOOBTx z movement id)

cur :: Tx CurResult
cur = liftF (CurTx id)

cut :: Tx Zipper
cut = liftF (CutTx id)

curTy :: Tx (ZippyT, ZippySchema)
curTy = liftF (CurTyTx id)

childRef :: Int -> Tx (Maybe SZippyD)
childRef which = liftF (ChildRefTx which id)

parentArgHole :: Tx (Maybe Int)
parentArgHole = liftF (ParentArgHoleTx id)

-- | Attempts to commit the current transaction.
--
--   This function terminates the Tx monad. Handling the result
--   of a commit should be handled by the interpreter.
commit :: Tx TxCommitStatus
commit = liftF (CommitTx id)

-- | Causes the transaction to ensure that it could be operating on the
--   most recently commited version of the database.
--
--   The sync method determines what to do on failure. We can choose to
--   abort or restart from the last save point.
--
--   The sync method has the nice bonus of totally erasing the log, so it
--   can be used to optimize transactions after a complex operation, to ensure
--   that the complex operation never has to be re-run because of a failure later
--   on in the transaction.
rebase :: RebaseFailureMode -> Tx ()
rebase failMode = liftF (RebaseTx failMode ())

abort :: Tx a
abort = liftF AbortTx

logAction :: TxLogAction -> Tx ()
logAction act = liftF (LogActionTx act ())

-- ** Multiple concurrent transactions

newtype TxnId = TxnId Word32
    deriving (Show, Eq, Ord, Hashable)

data TxCommitStatus = TxCommitted
                    | TxCannotMerge
                      deriving Show

type RunTxnStepFn a = Tx a -> IO ()
data TxnStep where
--    TxnStep :: !TxnId -> !(TxF (Tx a)) -> RunTxnStepFn a -> TxnStep
    TxnStepCommit :: !TxnId -> MVar TxCommitStatus -> TxnStep
    TxnStepMove :: !TxnId -> !Movement -> MVar (ZipperCursorInfo, MoveResult) -> TxnStep
    TxnStepCur :: !TxnId -> MVar (ZipperCursorInfo, CurResult) -> TxnStep
    TxnStepChildRef :: !TxnId -> !Int -> MVar (Maybe SZippyD) -> TxnStep

    -- Asynchronous transactions...
    TxnStepDesynchronize :: !TxnId -> MVar (Zipper, ZippyDiskCache, TransactionLog) -> TxnStep
    TxnStepCommitLog :: !TxnId -> !TransactionLog -> MVar TxCommitStatus -> TxnStep
    TxnStepDesyncedRead :: !TxnId -> !ZippyT -> !Word64 -> MVar (ZippyDiskCache, InMemoryD) -> TxnStep
    TxnStepSynchronize :: !TxnId -> !Zipper -> !TransactionLog -> MVar () -> TxnStep

txnStepTxnId :: TxnStep -> TxnId
txnStepTxnId (TxnStepCommit id _) = id
txnStepTxnId (TxnStepMove id _ _) = id
txnStepTxnId (TxnStepCur id _) = id
txnStepTxnId (TxnStepChildRef id _ _) = id
txnStepTxnId (TxnStepCommitLog id _ _) = id
txnStepTxnId (TxnStepDesynchronize id _) = id
txnStepTxnId (TxnStepSynchronize id _ _ _) = id
txnStepTxnId (TxnStepDesyncedRead id _ _ _) = id

data TxLogAction = TxLogResult !Zipper
                 | TxLogMessage !String
                   deriving Show

simpleTxActionLogger :: TxLogAction -> IO ()
simpleTxActionLogger (TxLogMessage s) = putStrLn ("Zephyr: " ++ s)
simpleTxActionLogger _ = putStrLn "Cannot log result in this transaction"

txResultActionLogger :: Applicative m => Chan (m Zipper) -> TxLogAction -> IO ()
txResultActionLogger _ (TxLogMessage s) = putStrLn ("Zephyr: " ++ s)
txResultActionLogger zChan (TxLogResult z) = writeChan zChan (pure z)

-- | Transaction state
--
--   A transaction is represented by the lazily-executing transaction, as well as
--   the strict zipper. Concurrency is achieved by the transaction runner evaluating
--   txAction in a separate IO thread. The IO threads return their results to the
--   coordinator through a Chan, and then quit.
data TxState = TxState
             { txZipper :: !Zipper
             , txLog    :: !TransactionLog

             , txRootAtStart :: !Word64 }
             | TxDesynced
             { txRootAtStart :: !Word64 }

data ZippyState = ZippyState
                { zippyTxns      :: IORef (HashMap TxnId TxState)
                , zippyRootPtr   :: IORef Word64

                , zippyDiskState :: IORef ZippyDiskState

                , zippySchema    :: !ZippySchema }

-- | Inspect the database schema to determine the root data type for the database
zippyRootType :: ZippyState -> ZippyT
zippyRootType (ZippyState { zippySchema = sch }) = zippySchemaRootType sch

-- * Disk operations

data ZippyDiskCache = ZippyDiskCache
                    { diskCacheSize    :: !Word64
                    , diskCacheMaxSize :: !Word64

                    , diskCache        :: !(HashPSQ Word64 POSIXTime InMemoryD) }

emptyDiskCache :: Word64 -> ZippyDiskCache
emptyDiskCache maxSize = ZippyDiskCache 0 maxSize PSQ.empty

data ZippyDiskState = ZippyDiskState
                    { zippyRootHandle :: Handle
                    , zippyDataHandle :: Handle

                    , zippyDataCache  :: !ZippyDiskCache }

spineStrictMap :: (a -> b) -> [a] -> [b]
spineStrictMap f [] = []
spineStrictMap f (x:xs) = let !x' = f x
                              !xs' = spineStrictMap f xs
                              !r = x':xs'
                          in r
