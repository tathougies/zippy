{-# OPTIONS_GHC -fwarn-incomplete-patterns -funbox-strict-fields #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Database.Zippy.Transaction
    ( txnServe

    , interpretTxSync

    , interpretTxAsync, ShouldResync(..)

    , canonicalBuilderForZipper, emptyAsyncDiskState) where

import Prelude hiding (foldlM)

import Database.Zippy.Types
import Database.Zippy.Data
import Database.Zippy.Disk

import Control.Applicative
import Control.Monad
import Control.Monad.Free
import Control.Monad.Free.Church (fromF)
import Control.Concurrent
import Control.Concurrent.Chan

import Data.IORef
import Data.Monoid
import Data.Sequence (viewr, viewl, ViewL(..), ViewR(..), (|>), (<|))
import Data.Word
import Data.ByteString.Builder
import Data.Foldable (foldlM)
import Data.String
import qualified Data.Text.Encoding as TE
import qualified Data.Sequence as Seq
import qualified Data.HashMap.Strict as HM
import qualified Data.Vector as V

import System.IO hiding (char8)
import System.Log.Logger

data TxLogVerificationResult = TxLogVerified !InMemoryD
                             | TxLogVerificationFails
                               deriving Show

txnOpenRoot :: ZippyDiskState -> ZippyT -> Word64 -> IO (Zipper, ZippyDiskState)
txnOpenRoot diskState dataType curRoot =
    do (root, diskState') <- coordinateReadZippyD diskState dataType curRoot
       return (Zipper (StillOnDisk curRoot) dataType root [], diskState')

recordMove :: Movement -> TransactionLog -> TransactionLog
recordMove (Replace (InMemoryD newVal)) (TransactionLog log)
    | (logPrev :> (TxnReplace _)) <- viewr log = TransactionLog (logPrev |> TxnReplace newVal)
    | otherwise = TransactionLog (log |> TxnReplace newVal)
recordMove Up (TransactionLog log)
    | (logPrev :> (TxnDown _)) <- viewr log = TransactionLog logPrev
    | otherwise = TransactionLog (log |> TxnUp)
recordMove (Down i) (TransactionLog log) = TransactionLog (log |> TxnDown i)

recordTagCheck :: Word16 -> TransactionLog -> TransactionLog
recordTagCheck !tag txnLog@(TransactionLog log)
    | (logPrev :> (TxnCheckTag !oldTag)) <- viewr log
       = if oldTag == tag then txnLog else TransactionLog (logPrev |> TxnCheckTag tag)
    | otherwise = TransactionLog (log |> TxnCheckTag tag)

recordAtomCheck :: ZippyD InMemory Atom a -> TransactionLog -> TransactionLog
recordAtomCheck !atom txnLog@(TransactionLog log) =
    -- | (logPrev :> (TxnCheckAtom !oldAtom)) <- viewr log
    --   = if SZippyD oldAtom == SZippyD atom then txnLog else TransactionLog (logPrev |> TxnCheckAtom atom)
    -- | otherwise = 
        TransactionLog (log |> TxnCheckAtom atom)

recordDiskRefCheck :: Int -> Word64 -> TransactionLog -> TransactionLog
recordDiskRefCheck !child !offs txnLog@(TransactionLog log)
    | (logPrev :> (TxnCheckChildDiskRef logChild logOffs)) <- viewr log,
      logChild == child = if logOffs == offs then txnLog else TransactionLog (logPrev |> TxnCheckChildDiskRef child offs)
    | otherwise = TransactionLog (log |> TxnCheckChildDiskRef child offs)


conForTag :: Word16 -> ZippyAlgebraicT -> ZippyDataCon
conForTag tag (ZippyAlgebraicT _ cons) = cons V.! fromIntegral tag

typeForConArg :: ZippySchema -> ZippyDataCon -> Int -> ZippyT
typeForConArg schema (ZippyDataCon _ argTypes) forArg =
    case zippyFieldType (argTypes V.! forArg) of
      RefFieldT (ZippyTyRef tyRef) -> zippyTypes schema V.! tyRef
      SimpleFieldT simple -> SimpleT simple

class ZippyDiskStateLike diskState where
    readFromDiskState :: diskState -> ZippyT -> Word64 -> IO (InMemoryD, diskState)

instance ZippyDiskStateLike ZippyDiskState where
    readFromDiskState = coordinateReadZippyD

instance ZippyDiskStateLike TxAsyncDiskState where
    readFromDiskState st@(TxAsyncDiskState cache txnsChan txnId diskResultMVar) ty diskOffs =
        case peekCache diskOffs cache of
             Just dt -> return (dt, st)
             Nothing -> do writeChan txnsChan (TxnStepDesyncedRead txnId ty diskOffs diskResultMVar)
                           (cache', ret) <- takeMVar diskResultMVar
                           return (ret, TxAsyncDiskState cache' txnsChan txnId diskResultMVar)

{-# SPECIALIZE moveZipper :: TxAsyncDiskState -> ZippySchema -> Movement -> Zipper -> IO (Zipper, MoveResult, TxAsyncDiskState) #-}
moveZipper :: ZippyDiskStateLike diskState => diskState -> ZippySchema -> Movement -> Zipper -> IO (Zipper, MoveResult, diskState)
moveZipper diskSt _ Up z@(Zipper _ _ _ []) = return (z, AtRoot, diskSt)
moveZipper diskSt _ Up (Zipper OnlyInMemory _ (InMemoryD newChild) (Within _ parentT argHole tag args:ctxts)) =
    -- We're moving up to our parent. The zipper will now move to our parent, who will be assigned a combined modification state.
    return (Zipper OnlyInMemory parentT (InMemoryD (CompositeD tag (args `V.unsafeUpd` [(argHole, SZippyD newChild)]))) ctxts, Moved parentT, diskSt)
moveZipper diskSt _ Up (Zipper (StillOnDisk childDskOffs) _ _ (Within parentModState parentT argHole tag args:ctxts)) =
    -- Even though we've read the child into memory, it hasn't been modified, so we can just refer to it in the future...
    return (Zipper parentModState parentT (InMemoryD (CompositeD tag (args `V.unsafeUpd` [(argHole, SZippyD (OnDiskD childDskOffs))]))) ctxts, Moved parentT, diskSt)
moveZipper diskSt _ (Replace inMemChild) (Zipper _ curT _ ctxts) =
    return (Zipper OnlyInMemory curT inMemChild ctxts, Moved curT, diskSt)
moveZipper (diskSt :: diskState) schema (Down toChild) z@(Zipper modified parentT@(~(AlgebraicT parentConstructors)) (InMemoryD (CompositeD tag args)) ctxts)
    | Nothing <- args V.!? toChild = return (z, NoSuchChild toChild, diskSt)
    | otherwise = case args V.! toChild of
                    SZippyD (OnDiskD dskOffset) ->
                        do (child, diskSt') <- readFromDiskState diskSt childT dskOffset
                           return (Zipper (StillOnDisk dskOffset) childT child (Within modified parentT toChild tag args:ctxts), Moved childT, diskSt')
                    SZippyD (child@(IntegerD _)) -> provedInMemory child
                    SZippyD (child@(TextD _)) -> provedInMemory child
                    SZippyD (child@(FloatingD _)) -> provedInMemory child
                    SZippyD (child@(BinaryD _)) -> provedInMemory child
                    SZippyD (child@(CompositeD _ _)) -> provedInMemory child
      where provedInMemory :: ZippyD InMemory dt a -> IO (Zipper, MoveResult, diskState)
            provedInMemory child = return (Zipper OnlyInMemory childT (InMemoryD child) (Within modified parentT toChild tag args:ctxts), Moved childT, diskSt)

            childT = let con = conForTag tag parentConstructors
                     in typeForConArg schema con toChild
moveZipper diskSt _ (Down _) z = return (z, CannotDescendIntoAtom, diskSt)

txnServe :: TxnStepsChan -> ZippyState -> IO ()
txnServe txnStepsChan st =
    forever $
    do nextStep <- readChan txnStepsChan
       let txnId = txnStepTxnId nextStep
       txns <- readIORef (zippyTxns st)
       txn <- case HM.lookup txnId txns of
                Just txn -> return txn
                Nothing -> do curRoot <- readIORef (zippyRootPtr st)
                              disk <- readIORef (zippyDiskState st)
                              (rootZ, disk') <- txnOpenRoot disk (zippyRootType st) curRoot
                              let txState = TxState rootZ mempty curRoot
                              modifyIORef (zippyTxns st) (HM.insert txnId txState)
                              writeIORef (zippyDiskState st) disk'
                              return txState
       case txn of
         TxState {} -> serveSynced st txn nextStep
         TxDesynced {} -> serveDesynced st txn nextStep

serveDesynced :: ZippyState -> TxState -> TxnStep -> IO ()
serveDesynced st txn nextStep =
    case nextStep of
      TxnStepSynchronize txnId z' log' retV ->
          do modifyIORef (zippyTxns st) (HM.insert txnId (TxState z' log' (txRootAtStart txn)))
             putMVar retV ()
      TxnStepCommitLog txnId log' retV -> doCommit st txnId log' retV
      TxnStepDesyncedRead txnId ty diskOffs retV -> doDesyncedRead st ty diskOffs retV
      _ -> fail "Sync command in desynced transaction"

serveSynced :: ZippyState -> TxState -> TxnStep -> IO ()
serveSynced st txn nextStep =
    case nextStep of
      TxnStepMove txnId movement retV ->
          do disk <- readIORef (zippyDiskState st)
             (zipper', res, disk') <- {-# SCC moveZipper #-} moveZipper disk (zippySchema st) movement (txZipper txn)
             writeIORef (zippyDiskState st) disk'
             case res of
               Moved _ -> do let txn' = txn { txZipper = zipper'
                                            , txLog = recordMove movement (txLog txn) }
                             modifyIORef (zippyTxns st) (HM.insert txnId txn')
                             putMVar retV (zipperCursorInfo zipper', res)
               _ -> putMVar retV (zipperCursorInfo (txZipper txn), res)
      TxnStepCur txnId retV ->
          case txZipper txn of
            Zipper _ _ (InMemoryD (CompositeD tag _)) _ ->
                do let txn' = txn { txLog = recordTagCheck tag (txLog txn) }
                   modifyIORef (zippyTxns st) (HM.insert txnId txn')
                   putMVar retV (zipperCursorInfo (txZipper txn), CurHasTag tag)
            Zipper _ _ (InMemoryD atom) _ ->
                do let continue :: ZippyD InMemory Atom x -> IO ()
                       continue atom = do let txn' = txn { txLog = recordAtomCheck atom (txLog txn) }
                                          modifyIORef (zippyTxns st) (HM.insert txnId txn')
                                          putMVar retV (zipperCursorInfo (txZipper txn), CurIsAtom (InMemoryAtomD atom))
                   case atom of -- Prove to the compiler that atom is atomic (turn on warn incomplete patterns and we know that we couldn't get anything else here)
                     atom@(IntegerD _) -> continue atom
                     atom@(TextD _) -> continue atom
                     atom@(FloatingD _) -> continue atom
                     atom@(BinaryD _) -> continue atom
      TxnStepChildRef txnId which retV ->
          case txZipper txn of
            Zipper _ _ (InMemoryD (CompositeD _ args)) _ ->
                case args V.!? which of
                  Nothing -> putMVar retV Nothing
                  Just arg@(SZippyD (OnDiskD offs)) -> do let txn' = txn { txLog = recordDiskRefCheck which offs (txLog txn) }
                                                          modifyIORef (zippyTxns st) (HM.insert txnId txn')
                                                          putMVar retV (Just arg)

                  -- Enumerate cases for proof
                  Just arg -> putMVar retV (Just arg)
            _ -> putMVar retV Nothing
      TxnStepCommit txnId retV -> doCommit st txnId (txLog txn) retV
      TxnStepDesyncedRead txnId ty diskOffs retV -> doDesyncedRead st ty diskOffs retV
      TxnStepDesynchronize txnId retV ->
          do diskState <- readIORef (zippyDiskState st)
             modifyIORef (zippyTxns st) (HM.insert txnId (TxDesynced (txRootAtStart txn)))
             putMVar retV (txZipper txn, zippyDataCache diskState, txLog txn)
      _ -> fail "Received async request from sync transaction"

doDesyncedRead st ty diskOffs retV =
    do diskState <- readIORef (zippyDiskState st)
       res <- lookupCache (zippyDataCache diskState) diskOffs
       case res of
         Just (ret, cache') ->
             do writeIORef (zippyDiskState st) (diskState { zippyDataCache = cache' })
                putMVar retV (cache', ret)
         Nothing -> do (ret, diskState') <- coordinateReadZippyD diskState ty diskOffs
                       writeIORef (zippyDiskState st) diskState'
                       putMVar retV (zippyDataCache diskState', ret)

doCommit st txnId txLog retV =
    do let finishWriteOutDb disk db =
               do -- This log has been verified, so we are now going to save the transaction root to disk.
                  -- Then we will update the roots file, and modify our own root ptr
                  infoM "serveZippy" ("Writing " ++ showZippyD (zippySchema st) (eraseInMemoryD db) ++ " to disk")
                  (newRoot, disk') <- {-# SCC "wr" #-} coordinateWriteZippyD disk db
                  infoM "serveZippy" ("New root is at " ++ show newRoot)
                  disk''<- coordinateCommitRoot disk' newRoot
                  writeIORef (zippyRootPtr st) newRoot
                  writeIORef (zippyDiskState st) disk''
                  return TxCommitted

       curRoot <- readIORef (zippyRootPtr st)
       disk <- readIORef (zippyDiskState st)

       (rootZ, disk') <- txnOpenRoot disk (zippyRootType st) curRoot
       (res, disk'') <- verifyLog disk' (zippySchema st) txLog rootZ
       infoM "serveZippy" ("Committing log " ++ show txLog)
       status <- case res of
                   TxLogVerified newDb -> finishWriteOutDb disk'' newDb
                   TxLogVerificationFails -> do writeIORef (zippyDiskState st) disk''
                                                return TxCannotMerge
       -- Regardless of the commit status, this transaction is now dead...
       modifyIORef (zippyTxns st) (HM.delete txnId)
       sz <- HM.size <$> readIORef (zippyTxns st)
       infoM "serveZippy" ("# txns: " ++ show sz)
       putMVar retV status

rezip :: ZippyDiskState -> ZippySchema -> Zipper -> IO (InMemoryD, ZippyDiskState)
rezip disk sch z = do res <- {-# SCC moveZipper #-} moveZipper disk sch Up z
                      case res of
                        (Zipper _ _ root [], AtRoot, disk') -> return (root, disk')
                        (_, AtRoot, _) -> fail "zipper at root, but there are still contexts left..."
                        (z', _, disk') -> rezip disk' sch z'

verifyLog :: ZippyDiskState -> ZippySchema -> TransactionLog -> Zipper -> IO (TxLogVerificationResult, ZippyDiskState)
verifyLog disk sch (TransactionLog log) z = go
    where go = case logView of
                 EmptyL -> do (db, disk') <- rezip disk sch z
                              return (TxLogVerified db, disk')
                 (TxnDown i :< log') -> checkedMove disk (Down i) log'
                 (TxnUp :< log') -> checkedMove disk Up log'
                 (TxnReplace x :< log') -> checkedMove disk (Replace (InMemoryD x)) log'
                 (TxnCheckChildDiskRef i offs :< log') -> checkChildDiskRef disk i offs log'
                 (TxnCheckTag tag :< log') -> checkTag disk tag log'
                 (TxnCheckAtom expAtom :< log') ->
                     case z of
                       Zipper _ _ (InMemoryD actAtom) _
                           | SZippyD actAtom == SZippyD expAtom -> verifyLog disk sch (TransactionLog log') z
                       _ -> return (TxLogVerificationFails, disk)

          logView = viewl log

          checkedMove disk move log' =
              do res <- {-# SCC moveZipper #-} moveZipper disk sch move z
                 case res of
                   (z', Moved _, disk') -> verifyLog disk' sch (TransactionLog log') z'
                   (_, _, disk') -> return (TxLogVerificationFails, disk')

          checkTag disk expTag log' =
              case z of
                Zipper _ _ (InMemoryD (CompositeD actTag args)) _
                    | actTag == expTag -> verifyLog disk sch (TransactionLog log') z
                _ -> return (TxLogVerificationFails, disk)

          checkChildDiskRef disk i offs log' =
              case z of
                Zipper _ _ (InMemoryD (CompositeD _ args)) _ ->
                    case args V.! i of
                      SZippyD (OnDiskD actOffs)
                          | actOffs == offs -> verifyLog disk sch (TransactionLog log') z
                      _ -> return (TxLogVerificationFails, disk)
                _ -> return (TxLogVerificationFails, disk)

zipperCursorInfo :: Zipper -> ZipperCursorInfo
zipperCursorInfo (Zipper _ curTy _ ctxts) =
    ZipperCursorInfo curTy $
    case ctxts of
      [] -> Nothing
      Within _ _ argHole _ _:_ -> Just argHole

-- * Tx monad interpretation

data TxInterpretState =
    TxInterpretState
    { commitStatusMVar :: !(MVar TxCommitStatus)
    , moveResultMVar   :: !(MVar (ZipperCursorInfo, MoveResult))
    , curResultMVar    :: !(MVar (ZipperCursorInfo, CurResult))
    , childRefMVar     :: !(MVar (Maybe SZippyD))

    , curZipperCursor  :: !ZipperCursorInfo
    , curSchema        :: !ZippySchema

    , txnsChan         :: !TxnStepsChan
    , txnId            :: !TxnId }

interpretTxSync' :: TxInterpretState -> Free TxF a -> IO a
interpretTxSync' !_ (Pure x) = return x
interpretTxSync' !st (Free (MoveTx movement next)) =
    do writeChan (txnsChan st) (TxnStepMove (txnId st) movement (moveResultMVar st))
       (z', res) <- takeMVar (moveResultMVar st)
       interpretTxSync' (st { curZipperCursor = z' }) (next res)
interpretTxSync' !st (Free (CurTx next)) =
    do writeChan (txnsChan st) (TxnStepCur (txnId st) (curResultMVar st))
       interpretTxSync' st =<< (next . snd <$> takeMVar (curResultMVar st))
interpretTxSync' !st (Free (CommitTx next)) =
    do writeChan (txnsChan st) (TxnStepCommit (txnId st) (commitStatusMVar st))
       interpretTxSync' st =<< (next <$> takeMVar (commitStatusMVar st))
interpretTxSync' !st (Free (ChildRefTx i next)) =
    do writeChan (txnsChan st) (TxnStepChildRef (txnId st) i (childRefMVar st))
       interpretTxSync' st =<< (next <$> takeMVar (childRefMVar st))
interpretTxSync' !st (Free (ParentArgHoleTx next)) =
    interpretTxSync' st (next (zipperParentArgHole (curZipperCursor st)))
interpretTxSync' !st (Free (CurTyTx next)) =
    interpretTxSync' st (next (zipperCurType (curZipperCursor st), curSchema st))

-- | Interprets a Tx monad by sending all requests to the transaction coordinator.
--   This means that the transaction coordinator is always up-to-date and can enforce
--   things like priorities among transactions. Use this method for long-running, priority
--   batch updates where raw read or write speed do not matter as much
interpretTxSync :: ZippySchema -> TxnStepsChan -> TxnId -> Tx a -> IO a
interpretTxSync sch txnsChan txnId tx =
    do curResult <- newEmptyMVar
       moveResult <- newEmptyMVar
       childRefResult <- newEmptyMVar
       commitStatusResult <- newEmptyMVar

       writeChan txnsChan (TxnStepCur txnId curResult)
       (z, _) <- takeMVar curResult

       let st = TxInterpretState
                { commitStatusMVar = commitStatusResult
                , moveResultMVar = moveResult
                , curResultMVar = curResult
                , childRefMVar = childRefResult

                , curZipperCursor = z
                , curSchema = sch

                , txnsChan = txnsChan
                , txnId = txnId }

       interpretTxSync' st (fromF tx)

data TxAsyncInterpretSettings =
    TxAsyncInterpretSettings
    { asyncCommitStatusMVar :: !(MVar TxCommitStatus)
    , asyncDiskResultMVar   :: !(MVar (ZippyDiskCache, InMemoryD))

    , asyncCurSchema        :: !ZippySchema

    , asyncTxnsChan         :: !TxnStepsChan
    , asyncTxnId            :: !TxnId

    , asyncLogAction        :: TxLogAction -> IO () }

data TxAsyncInterpretState =
    TxAsyncInterpretState
    { asyncDiskCache        :: !ZippyDiskCache
    , asyncCurZipper        :: !Zipper
    , asyncInterpreterLog   :: !TransactionLog }

data TxAsyncDiskState = TxAsyncDiskState !ZippyDiskCache !TxnStepsChan !TxnId !(MVar (ZippyDiskCache, InMemoryD))

data ShouldResync = ResyncAfterTx | DontResyncAfterTx
                    deriving Show

asyncDiskState :: TxAsyncInterpretSettings -> TxAsyncInterpretState -> TxAsyncDiskState
asyncDiskState !settings !st = TxAsyncDiskState (asyncDiskCache st) (asyncTxnsChan settings) (asyncTxnId settings) (asyncDiskResultMVar settings)

interpretTxAsync' :: TxAsyncInterpretSettings -> TxAsyncInterpretState -> Free TxF a -> IO (TxAsyncInterpretState, a)
interpretTxAsync' !_ !st (Pure x) = {-# SCC pure #-} return (st, x)
interpretTxAsync' !settings !st (Free (MoveTx movement next)) =
    {-# SCC moveTx #-}
    do (z, res, TxAsyncDiskState cache' _ _ _) <- moveZipper (asyncDiskState settings st) (asyncCurSchema settings) movement (asyncCurZipper st)
       interpretTxAsync' settings (st { asyncDiskCache = cache'
                                      , asyncCurZipper = z
                                      , asyncInterpreterLog = case res of
                                                                Moved _ -> recordMove movement (asyncInterpreterLog st)
                                                                _ -> asyncInterpreterLog st })
                                  (next res)
interpretTxAsync' !settings !st (Free (CurTx next) :: Free TxF a) =
    {-# SCC curTx #-}
    case asyncCurZipper st of
      Zipper _ _ (InMemoryD (CompositeD tag _)) _ ->
          interpretTxAsync' settings (st { asyncInterpreterLog = recordTagCheck tag (asyncInterpreterLog st) }) (next (CurHasTag tag))
      Zipper _ _ (InMemoryD atom) _ ->
          let continue :: ZippyD InMemory Atom x -> IO (TxAsyncInterpretState, a)
              continue atom = interpretTxAsync' settings (st { asyncInterpreterLog = recordAtomCheck atom (asyncInterpreterLog st)}) (next (CurIsAtom (InMemoryAtomD atom)))
          in case atom of
               atom@(IntegerD _) -> continue atom
               atom@(TextD _) -> continue atom
               atom@(FloatingD _) -> continue atom
               atom@(BinaryD _) -> continue atom
interpretTxAsync' !settings !st (Free (CommitTx next)) =
    {-# SCC commitTx #-}
    do writeChan (asyncTxnsChan settings) (TxnStepCommitLog (asyncTxnId settings) (asyncInterpreterLog st) (asyncCommitStatusMVar settings))
       interpretTxAsync' settings st =<< (next <$> takeMVar (asyncCommitStatusMVar settings))
interpretTxAsync' !settings !st (Free (ChildRefTx which next)) =
    {-# SCC childRefTx #-}
    case asyncCurZipper st of
      Zipper _ _ (InMemoryD (CompositeD _ args)) _ ->
          case args V.!? which of
            Nothing -> interpretTxAsync' settings st (next Nothing)
            Just arg@(SZippyD (OnDiskD offs)) ->
                interpretTxAsync' settings (st { asyncInterpreterLog = recordDiskRefCheck which offs (asyncInterpreterLog st) }) (next (Just arg))
            Just arg -> interpretTxAsync' settings st (next (Just arg))
      _ -> interpretTxAsync' settings st (next Nothing)
interpretTxAsync' !settings !st (Free (ParentArgHoleTx next)) =
    {-# SCC parentArgHoleTx #-}
    case asyncCurZipper st of
      Zipper _ _ _ [] -> interpretTxAsync' settings st (next Nothing)
      Zipper _ _ _ (Within _ _ argHole _ _ : _) ->
          interpretTxAsync' settings st (next (Just argHole))
interpretTxAsync' !settings !st (Free (CurTyTx next)) =
    {-# SCC curTyTx #-}
    case asyncCurZipper st of
      Zipper _ curTy _ _ -> interpretTxAsync' settings st (next (curTy, asyncCurSchema settings))
interpretTxAsync' !settings !st (Free (CutTx next)) =
    interpretTxAsync' settings st (next (removeCtxt (asyncCurZipper st)))
    where removeCtxt (Zipper modState ty d _) = Zipper modState ty d []
interpretTxAsync' !settings !st (Free (MoveOOBTx zipper mvmt next)) =
    do (zipper', res, TxAsyncDiskState cache' _ _ _) <- moveZipper (asyncDiskState settings st) (asyncCurSchema settings) mvmt zipper
       interpretTxAsync' settings (st { asyncDiskCache = cache' }) (next (zipper', res))
interpretTxAsync' !settings !st (Free (LogActionTx act next)) =
    do asyncLogAction settings act
       interpretTxAsync' settings st next

-- | The asynchronous interpreter is like the synchronous one, except it also keeps track of
--   a copy of the disk cache. It uses that copy to quickly respond to read requests. When
--   it cannot find a piece of data in the cache, it asks the transaction coordinator to look
--   in the newest version of the cache. The transaction coordinator will look for the data
--   in cache or read it in from disk and return it to the interpreter, along with the newest
--   cache.
--
--   This means that this interpreter will also keep track of all zipper movements that take
--   place. It then uses the TxnCommitLog TxnStep to send the log to the transaction coordinator
--   where it will be replayed over the latest root, and an appropriate commit status returned.
interpretTxAsync :: ZippySchema -> ShouldResync -> TxnStepsChan -> (TxLogAction -> IO ()) -> TxnId -> Tx a -> IO a
interpretTxAsync sch shouldResync txnsChan logFunc txnId tx =
    do curResult <- newEmptyMVar
       commitStatusResult <- newEmptyMVar
       diskResult <- newEmptyMVar

       writeChan txnsChan (TxnStepDesynchronize txnId curResult)
       (z, diskCache, txLog) <- takeMVar curResult

       let settings = TxAsyncInterpretSettings
                    { asyncCommitStatusMVar = commitStatusResult
                    , asyncDiskResultMVar = diskResult

                    , asyncCurSchema = sch

                    , asyncTxnsChan = txnsChan
                    , asyncTxnId = txnId

                    , asyncLogAction = logFunc }

           st = TxAsyncInterpretState
                { asyncDiskCache = diskCache
                , asyncCurZipper = z
                , asyncInterpreterLog = txLog }
       (TxAsyncInterpretState _ z' txLog', ret) <- interpretTxAsync' settings st (fromF tx)

       case shouldResync of
         ResyncAfterTx -> do waitV <- newEmptyMVar
                             writeChan txnsChan (TxnStepSynchronize txnId z' txLog' waitV)
                             takeMVar waitV
                             return ret
         DontResyncAfterTx -> return ret

canonicalBuilderForZipper :: TxAsyncDiskState -> ZippySchema -> Zipper -> IO (Builder, TxAsyncDiskState)
canonicalBuilderForZipper diskState _ (Zipper _ _ (InMemoryD (TextD x)) _) = pure (byteString (fromString (show x)), diskState)
canonicalBuilderForZipper diskState  _ (Zipper _ _ (InMemoryD (IntegerD i)) _) = pure (int64Dec i, diskState)
canonicalBuilderForZipper diskState _ (Zipper _ _ (InMemoryD (FloatingD f)) _) = pure (doubleDec f, diskState)
canonicalBuilderForZipper diskState _ (Zipper _ _ (InMemoryD (BinaryD b)) _) = pure (byteString (fromString (show b)), diskState)
canonicalBuilderForZipper diskState sch z@(Zipper _ (AlgebraicT (ZippyAlgebraicT _ cons)) (InMemoryD (CompositeD tag _)) _) =
    do let ZippyDataCon (ZippyDataConName conName) argTys = cons V.! fromIntegral tag
           parenthesized x = if V.length argTys > 0 then char8 '(' <> x <> char8 ')' else x

           buildCanonicalArg (mkArgBuilders, diskState) (i, argTy) =
               do (z', Moved argTy, diskState') <- moveZipper diskState sch (Down i) z
                  (argBuilder, diskState'') <- canonicalBuilderForZipper diskState sch z'
                  return ( mkArgBuilders . (argBuilder :), diskState'' )

       (mkArgBuilders, diskState') <- foldlM buildCanonicalArg (id, diskState) (V.indexed argTys)
       pure (parenthesized (TE.encodeUtf8Builder conName <> mconcat (map (char8 ' ' <>) (mkArgBuilders []))), diskState')
canonicalBuilderForZipper _ _ _ = error "Cannot match type to data"

emptyAsyncDiskState :: TxnStepsChan -> TxnId -> IO TxAsyncDiskState
emptyAsyncDiskState txnsChan txnId = TxAsyncDiskState (emptyDiskCache 0) txnsChan txnId <$> newEmptyMVar
