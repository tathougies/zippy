{-# LANGUAGE DeriveFunctor, DeriveTraversable, DeriveFoldable, TypeFamilies, ScopedTypeVariables, RankNTypes, FlexibleContexts, UndecidableInstances #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
module Database.Zippy.Zephyr.Types where

import Database.Zippy.Types

import Prelude hiding (mapM)

import Control.Applicative
import Control.Monad.Writer hiding (mapM)

import Debug.Trace

import Data.Int
import Data.String
import Data.Hashable
import Data.Word
import Data.Monoid
import Data.Semigroup
import Data.Proxy
import Data.Traversable (Traversable(traverse), mapM)
import Data.Foldable (Foldable(foldMap))
import Data.Vector (Vector)
import Data.DList (DList)
import Data.Text (Text)
import Data.ByteString (ByteString)
import qualified Data.HashMap.Strict as HM
import qualified Data.Set as S
import qualified Data.Map as M

import Text.Parsec.Pos (SourcePos)

import Unsafe.Coerce

data GenericZephyrAtom tyRef quote sym =
    IntegerZ !Int64
  | FloatingZ !Double
  | TextZ !Text
  | BinaryZ !ByteString

  | QuoteZ !quote
  | SymZ (Vector tyRef) !sym

  | ZipUpZ
  | ZipDownZ
  | ZipReplaceZ
  | CurTagZ
  | CurAtomZ
  | ArgHoleZ
  | EnterZipperZ
  | CutZ

  -- Primitives
  | SwapZ
  | DupZ
  | ZapZ
  | CatZ
  | ConsZ
  | UnConsZ
  | DeQuoteZ -- Joy i combinator
  | DipZ
  | IfThenElseZ
  | LengthZ

  | RandomZ

  | FailZ
  | LogZ
  | TraceZ
  | YieldZ

  | EqZ
  | LtZ
  | GtZ
  | PlusZ

  | AnswerZ (Vector tyRef)
  | DupAnswerZ

  | TagZ !tyRef !Word16 !Int
    deriving (Show, Functor)

data GenericZephyrSymbolDefinition zephyr =
    ZephyrSymbolDefinition !ZephyrWord !zephyr
    deriving (Show, Functor, Traversable, Foldable)

zephyrSymbolName :: GenericZephyrSymbolDefinition zephyr -> ZephyrWord
zephyrSymbolName (ZephyrSymbolDefinition name _) = name
zephyrSymbolDefinition :: GenericZephyrSymbolDefinition zephyr -> zephyr
zephyrSymbolDefinition (ZephyrSymbolDefinition _ def) = def

data GenericZephyrProgram a =
    ZephyrProgram
    { zephyrEntry     :: !Int
    , zephyrSymbolTbl :: !(Vector a) }
    deriving Show
type ZephyrProgram = GenericZephyrProgram CompiledZephyrSymbol

data ZephyrQualifiedWord = ZephyrQualifiedWord !ZephyrWord !ZephyrWord
                           deriving Show

newtype ZephyrAskRef = ZephyrAskRef Int deriving (Show, Read, Eq, Ord)

zephyrAskRefIndex :: ZephyrAskRef -> Int
zephyrAskRefIndex (ZephyrAskRef i) = i

type CompiledZephyrAtom = GenericZephyrAtom (Either ZippyTyRef ZephyrAskRef) CompiledZephyr Int
newtype CompiledZephyr = CompiledZephyr (Vector CompiledZephyrAtom)
    deriving Show
data CompiledZephyrSymbol = CompiledZephyrSymbol !ZephyrQualifiedWord !CompiledZephyr deriving Show

newtype ZephyrWord = ZephyrWord Text deriving (Show, Eq, Ord, IsString, Hashable)

data SourceRange = SourceRange !SourcePos !SourcePos
                   deriving Show

type ZephyrBuilderAtom = GenericZephyrAtom (ZephyrT ZephyrStackAtomK ZippyTyVarName) ZephyrBuilder ZephyrWord
data ZephyrBuilderOp = ZephyrStateAssertion !(ZephyrExecState ZippyTyVarName) !SourceRange
                     | ZephyrAtom !ZephyrBuilderAtom !SourceRange
                       deriving Show
newtype ZephyrBuilder = ZephyrBuilder (DList ZephyrBuilderOp)
    deriving (Show, Monoid, Semigroup)

type ZephyrTyCheckedAtom = GenericZephyrAtom (ZephyrT ZephyrStackAtomK ZephyrTyVar) ZephyrTyChecked ZephyrWord
newtype ZephyrTyChecked = ZephyrTyChecked [ZephyrTyCheckedAtom]
    deriving Show

symbolBytecode :: CompiledZephyrSymbol -> Vector CompiledZephyrAtom
symbolBytecode (CompiledZephyrSymbol _ (CompiledZephyr bc)) = bc

mapQuote :: (q -> q') -> GenericZephyrAtom ask q a -> GenericZephyrAtom ask q' a
mapQuote f (QuoteZ q) = QuoteZ (f q)
mapQuote _ (IntegerZ i) = IntegerZ i
mapQuote _ (FloatingZ d) = FloatingZ d
mapQuote _ (TextZ t) = TextZ t
mapQuote _ (BinaryZ b) = BinaryZ b
mapQuote _ (SymZ a s) = SymZ a s
mapQuote _ ZipUpZ = ZipUpZ
mapQuote _ ZipDownZ = ZipDownZ
mapQuote _ ZipReplaceZ = ZipReplaceZ
mapQuote _ CurTagZ = CurTagZ
mapQuote _ CurAtomZ = CurAtomZ
mapQuote _ ArgHoleZ = ArgHoleZ
mapQuote _ EnterZipperZ = EnterZipperZ
mapQuote _ CutZ = CutZ
mapQuote _ SwapZ = SwapZ
mapQuote _ DupZ = DupZ
mapQuote _ ZapZ = ZapZ
mapQuote _ CatZ = CatZ
mapQuote _ ConsZ = ConsZ
mapQuote _ UnConsZ = UnConsZ
mapQuote _ DeQuoteZ = DeQuoteZ
mapQuote _ DipZ = DipZ
mapQuote _ IfThenElseZ = IfThenElseZ
mapQuote _ LengthZ = LengthZ
mapQuote _ RandomZ = RandomZ
mapQuote _ FailZ = FailZ
mapQuote _ LogZ = LogZ
mapQuote _ TraceZ = TraceZ
mapQuote _ YieldZ = YieldZ
mapQuote _ EqZ = EqZ
mapQuote _ LtZ = LtZ
mapQuote _ GtZ = GtZ
mapQuote _ PlusZ = PlusZ
mapQuote _ (TagZ ty tag argCnt) = TagZ ty tag argCnt
mapQuote _ (AnswerZ a) = AnswerZ a
mapQuote _ DupAnswerZ = DupAnswerZ

mapAsk :: (ask -> ask') -> GenericZephyrAtom ask q a -> GenericZephyrAtom ask' q a
mapAsk _ (QuoteZ q) = QuoteZ q
mapAsk _ (IntegerZ i) = IntegerZ i
mapAsk _ (FloatingZ d) = FloatingZ d
mapAsk _ (TextZ t) = TextZ t
mapAsk _ (BinaryZ b) = BinaryZ b
mapAsk f (SymZ a s) = SymZ (fmap f a) s
mapAsk _ ZipUpZ = ZipUpZ
mapAsk _ ZipDownZ = ZipDownZ
mapAsk _ ZipReplaceZ = ZipReplaceZ
mapAsk _ CurTagZ = CurTagZ
mapAsk _ CurAtomZ = CurAtomZ
mapAsk _ ArgHoleZ = ArgHoleZ
mapAsk _ EnterZipperZ = EnterZipperZ
mapAsk _ CutZ = CutZ
mapAsk _ SwapZ = SwapZ
mapAsk _ DupZ = DupZ
mapAsk _ ZapZ = ZapZ
mapAsk _ CatZ = CatZ
mapAsk _ ConsZ = ConsZ
mapAsk _ UnConsZ = UnConsZ
mapAsk _ DeQuoteZ = DeQuoteZ
mapAsk _ DipZ = DipZ
mapAsk _ IfThenElseZ = IfThenElseZ
mapAsk _ LengthZ = LengthZ
mapAsk _ RandomZ = RandomZ
mapAsk _ FailZ = FailZ
mapAsk _ LogZ = LogZ
mapAsk _ TraceZ = TraceZ
mapAsk _ YieldZ = YieldZ
mapAsk _ EqZ = EqZ
mapAsk _ LtZ = LtZ
mapAsk _ GtZ = GtZ
mapAsk _ PlusZ = PlusZ
mapAsk f (TagZ askRef tag argCnt) = TagZ (f askRef) tag argCnt
mapAsk f (AnswerZ a) = AnswerZ (fmap f a)
mapAsk _ DupAnswerZ = DupAnswerZ

-- * Program execution

data ZephyrEvalError = CatZExpectsTwoQuotes
                     | ConsZExpectsAnAtomAndQuote
                     | DeQuoteZExpectsQuotedBlock
                     | DipZExpectsQuoteAndSomethingElse
                     | HitFail !String
                     | ConditionMustReturn0Or1
                     | CurHasNoTag
                     | CurIsNotAtom
                     | ExpectingTwoIntegersForArithmetic ZephyrStack
                     | ZipDownNeeds1Argument
                     | EnterZipperExpects1Zipper
                     | CannotYieldNonZipper
                     | NeedAtomOrZipperAtRoot
                     | UnConsZExpectsQuote
                       deriving Show

type ZephyrStack = [ZephyrD]
data ZephyrContinuation = JustContinue !(Vector CompiledZephyrAtom)
                        | PushAndContinue !ZephyrD !(Vector CompiledZephyrAtom)
                        | IfThenElseAndContinue !(Vector CompiledZephyrAtom) !(Vector ZippyTyRef) !(Vector CompiledZephyrAtom) !(Vector ZippyTyRef)
                        | ExitZipper !(Vector CompiledZephyrAtom)
                        | PopAnswer
                          deriving Show
data ZephyrContext = ZephyrContext
                   { zephyrContinuations :: [ZephyrContinuation]
                   , zephyrStack         :: ZephyrStack
                   , zephyrZippers       :: [Zipper]
                   , zephyrAsksStack     :: [Vector ZippyTyRef] }
                     deriving Show

data ZephyrD where
    ZephyrD :: !(ZippyD InMemory Atom a) -> ZephyrD
    ZephyrZ :: Zipper -> ZephyrD
    ZephyrQ :: !(Vector CompiledZephyrAtom) -> !(Vector ZippyTyRef) -> ZephyrD
deriving instance Show ZephyrD

type ZephyrExports = HM.HashMap ZephyrWord ZephyrProgram

-- * Types

type RecZippyFieldType = GenericZippyTyCon ZephyrScopedTy
newtype RecZippyTyCon = RecZippyTyCon { unRecTy :: GenericZippyTyCon (ZippyFieldType RecZippyTyCon) }
    deriving (Show, Ord, Eq)

data ZephyrScopedTy = Local !ZippyTyVarName
                    | Global !(ZippyFieldType RecZippyFieldType)
                      deriving Show


-- * Packages

data GenericZephyrPackage zephyr =
     ZephyrPackage
     { zephyrPackageName  :: !ZephyrWord

     , zephyrDependencies :: [ZephyrWord]
     , zephyrExports      :: [ZephyrWord]
     , zephyrTypes        :: [GenericZippyAlgebraicT ZippyTyVarName ZephyrScopedTy]
     , zephyrSymbols      :: [GenericZephyrSymbolDefinition zephyr] }
    deriving (Show, Functor, Foldable, Traversable)

type ZephyrPackage = GenericZephyrPackage ZephyrBuilder
type ZephyrTyCheckedPackage = GenericZephyrPackage ZephyrTyChecked

-- * Type system

data ZephyrExecState tyVar = ZephyrExecState !(ZephyrT ZephyrZipperK tyVar) !(ZephyrT ZephyrStackK tyVar)
                             deriving (Show, Eq, Functor, Traversable, Foldable)

data ZephyrKind = ZephyrZipperK    -- Kind '%'
                | ZephyrStackAtomK -- Kind '*'. All types of kind '%' are of kind '*'

                | ZephyrStackK     -- Kind 'S'. This kind is mutually exclusive with the union of the other two

                | ZephyrBottomK    -- An uninhabited kind
                  deriving (Show, Eq, Ord)

class IsKind (k :: ZephyrKind) where
    getKind :: Proxy k -> ZephyrKind
instance IsKind ZephyrZipperK where
    getKind _ = ZephyrZipperK
instance IsKind ZephyrStackAtomK where
    getKind _ = ZephyrStackAtomK
instance IsKind ZephyrStackK where
    getKind _ = ZephyrStackK
instance IsKind ZephyrBottomK where
    getKind _ = ZephyrBottomK

type family IsStackAtomKind (k :: ZephyrKind) :: Bool where
    IsStackAtomKind ZephyrZipperK = True
    IsStackAtomKind ZephyrStackAtomK = True
    IsStackAtomKind ZephyrBottomK = True

    IsStackAtomKind x = False

kindOf :: IsKind kind => ZephyrT kind tyVar -> ZephyrKind
kindOf (z :: ZephyrT kind tyVar) = getKind (Proxy :: Proxy kind)

sameKinded :: (IsKind k1, IsKind k2) => ZephyrT k1 tyVar -> ZephyrT k2 tyVar -> (forall k. IsKind k => Maybe (ZephyrT k tyVar, ZephyrT k tyVar) -> a) -> a
sameKinded z1 z2 f = case safeCoercedKind z2 of
                       Just z2 -> f $ Just (z1, z2)
                       Nothing -> case (z1, kindOf z1, z2, kindOf z2) of
                                    (ZephyrVarT v, ZephyrStackAtomK, z2, ZephyrZipperK) ->
                                        f (Just (ZephyrVarT v, z2))
                                    (ZephyrZipperT z, ZephyrStackAtomK, z2, ZephyrZipperK) ->
                                        case safeCoercedKind z2 of
                                          Just z2 -> f (Just (zipperKindedZephyrZipper z, z2))
                                          Nothing -> failing
                                    (z1, ZephyrZipperK, ZephyrVarT v, ZephyrStackAtomK) ->
                                        f (Just (z1, ZephyrVarT v))
                                    (z1, ZephyrZipperK, ZephyrZipperT z, ZephyrStackAtomK) ->
                                        case safeCoercedKind z1 of
                                          Just z1 -> f (Just (z1, zipperKindedZephyrZipper z))
                                          Nothing -> failing
                                    (ZephyrVarT v, ZephyrBottomK, z2, _) ->
                                        f (Just (ZephyrVarT v, z2))
                                    (z1, _, ZephyrVarT v, ZephyrBottomK) ->
                                        f (Just (z1, ZephyrVarT v))
                                    _ -> failing
    where failing = f (Nothing :: Maybe (ZephyrT ZephyrBottomK tyVar, ZephyrT ZephyrBottomK tyVar))

isStackAtomKind :: IsKind k => ZephyrT k tyVar -> (forall k. (IsKind k, IsStackAtomKind k ~ True) => Maybe (ZephyrT k tyVar) -> a) -> a
isStackAtomKind (ty :: ZephyrT k tyVar) next
    | kindOf ty == ZephyrStackAtomK = next (Just (unsafeCoerce ty :: ZephyrT ZephyrStackAtomK tyVar))
    | kindOf ty == ZephyrZipperK = next (Just (unsafeCoerce ty :: ZephyrT ZephyrZipperK tyVar))
    | kindOf ty == ZephyrBottomK = case ty of
                                     ZephyrVarT v -> next (Just (ZephyrVarT v :: ZephyrT ZephyrStackAtomK tyVar))
                                     _ -> error "encountered bottom kind, but this variable is not free"
    | otherwise = next (Nothing :: Maybe (ZephyrT ZephyrBottomK tyVar))

safeCoercedKind :: (IsKind k1, IsKind k2) => ZephyrT k1 tyVar -> Maybe (ZephyrT k2 tyVar)
safeCoercedKind (z :: ZephyrT k1 tyVar)
    | kindOf ret == kindOf z = Just ret
    | otherwise = case (z, kindOf z, kindOf ret) of
                    (ZephyrVarT z, ZephyrZipperK, ZephyrStackAtomK) -> Just (ZephyrVarT z)
                    (ZephyrZipperT z, ZephyrZipperK, ZephyrStackAtomK) -> Just (unsafeCoerce (stackAtomKindedZephyrZipper z))
                    (ZephyrZipperT z, ZephyrStackAtomK, ZephyrZipperK) -> Just (unsafeCoerce (zipperKindedZephyrZipper z))
                    (ZephyrVarT v, ZephyrBottomK, ZephyrStackAtomK) -> Just (unsafeCoerce (ZephyrVarT v :: ZephyrT ZephyrStackAtomK tyVar))
                    (ZephyrVarT v, ZephyrBottomK, ZephyrStackK) -> Just (unsafeCoerce (ZephyrVarT v :: ZephyrT ZephyrStackK tyVar))
                    (ZephyrVarT v, ZephyrBottomK, ZephyrZipperK) -> Just (unsafeCoerce (ZephyrVarT v :: ZephyrT ZephyrZipperK tyVar))
                    _ -> trace ("Cannot coerce " ++ show (kindOf z) ++ " " ++ show (kindOf ret)) Nothing
    where ret = unsafeCoerce z

data ZephyrT (k :: ZephyrKind) tyVar where
    ZephyrVarT :: IsKind k => tyVar -> ZephyrT k tyVar

    ZephyrZipperT :: (IsStackAtomKind k ~ True, IsKind k) => ZippyFieldType (RecZephyrType tyVar) -> ZephyrT k tyVar

    ZephyrQuoteT :: ZephyrEffect tyVar -> ZephyrT ZephyrStackAtomK tyVar

    ZephyrStackBottomT ::  ZephyrT ZephyrStackK tyVar
    (:>) :: (IsStackAtomKind stackAtom ~ True, IsKind stackAtom) => ZephyrT ZephyrStackK tyVar -> ZephyrT stackAtom tyVar -> ZephyrT ZephyrStackK tyVar

    ZephyrForAll :: ZephyrKind -> tyVar -> ZephyrT k tyVar -> ZephyrT k tyVar
deriving instance Show tyVar => Show (ZephyrT k tyVar)

zipperKindedZephyrZipper :: ZippyFieldType (RecZephyrType tyVar) -> ZephyrT ZephyrZipperK tyVar
stackAtomKindedZephyrZipper :: ZippyFieldType (RecZephyrType tyVar) -> ZephyrT ZephyrStackAtomK tyVar
zipperKindedZephyrZipper = ZephyrZipperT
stackAtomKindedZephyrZipper = ZephyrZipperT

type ZephyrStackT = ZephyrT ZephyrStackK
type ZephyrStackAtomT = ZephyrT ZephyrStackAtomK
type ZephyrZipperT = ZephyrT ZephyrZipperK

stackVarT :: tyVar -> ZephyrT ZephyrStackK tyVar
stackAtomVarT :: tyVar -> ZephyrT ZephyrStackAtomK tyVar
zipperVarT :: tyVar -> ZephyrT ZephyrZipperK tyVar
stackVarT = ZephyrVarT
stackAtomVarT = ZephyrVarT
zipperVarT = ZephyrVarT

instance Eq tyVar => Eq (ZephyrT k tyVar) where
    ZephyrVarT a == ZephyrVarT b = a == b
    ZephyrZipperT a == ZephyrZipperT b = a == b
    ZephyrQuoteT a == ZephyrQuoteT b = a == b
    ZephyrStackBottomT == ZephyrStackBottomT = True
    (aStk :> ZephyrZipperT aAtom) == (bStk :> ZephyrZipperT bAtom) = aAtom == bAtom && aStk == bStk
    (aStk :> ZephyrQuoteT aAtom) == (bStk :> ZephyrQuoteT bAtom) = aAtom == bAtom && aStk == bStk
    ZephyrForAll k1 v1 t1 == ZephyrForAll k2 v2 t2 = undefined
    _ == _ = False

instance Ord tyVar => Ord (ZephyrT k tyVar) where
    compare ZephyrStackBottomT ZephyrStackBottomT = EQ
    compare (ZephyrVarT a) (ZephyrVarT b) = compare a b
    compare (ZephyrZipperT a) (ZephyrZipperT b) = compare a b
    compare (ZephyrQuoteT a) (ZephyrQuoteT b) = compare a b
    compare (a :> ZephyrZipperT aAtom) (b :> ZephyrZipperT bAtom)
            | a == b = compare aAtom bAtom
            | otherwise = compare a b
    compare (a :> ZephyrQuoteT aAtom) (b :> ZephyrQuoteT bAtom)
            | a == b = compare aAtom bAtom
            | otherwise = compare a b
    compare (ZephyrForAll k1 v1 t1) (ZephyrForAll k2 v2 t2) = compare (k1, v1, t1) (k2, v2, t2)
    compare ZephyrStackBottomT _ = LT
    compare _ ZephyrStackBottomT = GT
    compare (ZephyrVarT _) _ = LT
    compare _ (ZephyrVarT _) = GT
    compare (ZephyrZipperT _) _ = LT
    compare _ (ZephyrZipperT _) = GT
    compare (ZephyrQuoteT _) _ = LT
    compare _ (ZephyrQuoteT _) = GT
    compare (a :> aAtom) _ = LT
    compare _ (b :> bAtom) = GT
    compare (ZephyrForAll k _ _) _ = LT
    compare _ (ZephyrForAll k _ _) = GT

instance Ord tyVar => Ord (ZephyrEffect tyVar) where
    compare (ZephyrEffect aZ aStkBef aStkAfter) (ZephyrEffect bZ bStkBef bStkAfter)
        | aZ == bZ = if aStkBef == bStkBef then compare aStkAfter bStkAfter else compare aStkBef bStkBef
        | otherwise = compare aZ bZ

instance Functor (ZephyrT k) where
    fmap f (ZephyrVarT v) = ZephyrVarT (f v)
    fmap _ (ZephyrZipperT (SimpleFieldT s)) = ZephyrZipperT (SimpleFieldT s)
    fmap f (ZephyrZipperT (RefFieldT field)) = ZephyrZipperT (RefFieldT (fmap (fmap f) field))
    fmap f (ZephyrQuoteT eff) = ZephyrQuoteT (fmap f eff)
    fmap _ ZephyrStackBottomT = ZephyrStackBottomT
    fmap f (stk :> atom) = fmap f stk :> fmap f atom
    fmap f (ZephyrForAll k v t) = ZephyrForAll k (f v) (fmap f t)

instance Traversable (ZephyrT k) where
    traverse f (ZephyrVarT v) = ZephyrVarT <$> f v
    traverse _ (ZephyrZipperT (SimpleFieldT s)) = pure (ZephyrZipperT (SimpleFieldT s))
    traverse f (ZephyrZipperT (RefFieldT field)) = ZephyrZipperT . RefFieldT <$> traverse (traverse f) field
    traverse f (ZephyrQuoteT eff) = ZephyrQuoteT <$> traverse f eff
    traverse _ ZephyrStackBottomT = pure ZephyrStackBottomT
    traverse f (stk :> atom) = (:>) <$> traverse f stk <*> traverse f atom
    traverse f (ZephyrForAll k v ty) = ZephyrForAll k <$> f v <*> traverse f ty

instance Foldable (ZephyrT k) where
    foldMap f (ZephyrVarT v) = f v
    foldMap _ (ZephyrZipperT (SimpleFieldT _)) = mempty
    foldMap f (ZephyrZipperT (RefFieldT field)) = foldMap (foldMap f) field
    foldMap f (ZephyrQuoteT eff) = foldMap f eff
    foldMap _ ZephyrStackBottomT = mempty
    foldMap f (stk :> atom) = foldMap f stk <> foldMap f atom
    foldMap f (ZephyrForAll k v ty) = f v <> foldMap f ty

type RecZephyrType tyVar = GenericZippyTyCon (ZephyrT ZephyrZipperK tyVar)
infixl 7 :>

data ZephyrEffect tyVar = ZephyrEffect (ZephyrT ZephyrZipperK tyVar) (ZephyrT ZephyrStackK tyVar) (ZephyrT ZephyrStackK tyVar)
                               deriving (Show, Eq, Functor, Traversable, Foldable)

newtype ZephyrTyVar = ZephyrTyVar Int
    deriving (Show, Eq, Ord, Hashable)

newtype ZephyrEffectWithNamedVars = ZephyrEffectWithNamedVars (ZephyrEffect ZippyTyVarName)

allTyVariables :: (Traversable f, Ord a) => f a -> [a]
allTyVariables (eff :: f a) = S.toList (execWriter (mapM collectName eff))
    where collectName :: a -> Writer (S.Set a) ()
          collectName name = tell (S.singleton name)

kindedVariables :: Ord v => ZephyrT k v -> M.Map v ZephyrKind
kindedVariables t = go t
    where go :: Ord v => ZephyrT k v -> M.Map v ZephyrKind
          go ty@(ZephyrVarT v) = M.singleton v (kindOf ty)
          go (ZephyrZipperT (SimpleFieldT _)) = mempty
          go (ZephyrZipperT (RefFieldT field)) = foldMap go field
          go (ZephyrQuoteT (ZephyrEffect stk bef aft)) = go stk <> go bef <> go aft
          go ZephyrStackBottomT = mempty
          go (a :> b) = go a <> go b
          go (ZephyrForAll k v ty) = go ty

-- * HasSourceRange class and instances

class HasSourceRange entity where
    sourceRange :: entity -> SourceRange

instance HasSourceRange ZephyrBuilderOp where
    sourceRange (ZephyrStateAssertion _ range) = range
    sourceRange (ZephyrAtom _ range) = range
