module Database.Zippy.Zephyr.Types where

import Database.Zippy.Types

import Data.Int
import Data.String
import Data.Hashable
import Data.Word
import Data.Monoid
import Data.Vector (Vector)
import Data.DList (DList)
import Data.Text (Text)
import Data.ByteString (ByteString)
import qualified Data.HashMap.Strict as HM

data GenericZephyrAtom quote sym =
    IntegerZ !Int64
  | FloatingZ !Double
  | TextZ !Text
  | BinaryZ !ByteString

  | QuoteZ !quote
  | SymZ !sym

  | ZipUpZ
  | ZipDownZ
  | ZipReplaceZ
  | CurTagZ
  | CurAtomZ
  | ArgHoleZ
  | EnterZipperZ
  | CutZ

  -- Work with data on the stack
  | CheckTagZ !Word16

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

  | FailZ
  | LogZ
  | YieldZ

  | EqZ
  | LtZ
  | GtZ
  | PlusZ

  | TagZ !ZippyTyRef !Word16 !Int
    deriving (Show, Functor)

data ZephyrSymbolDefinition =
    ZephyrSymbolDefinition !ZephyrWord !ZephyrBuilder
    deriving Show

zephyrSymbolName :: ZephyrSymbolDefinition -> ZephyrWord
zephyrSymbolName (ZephyrSymbolDefinition name _) = name

data ZephyrProgram =
    ZephyrProgram
    { zephyrEntry     :: !Int
    , zephyrSymbolTbl :: !(Vector CompiledZephyrSymbol) }
    deriving Show

data ZephyrQualifiedWord = ZephyrQualifiedWord !ZephyrWord !ZephyrWord
                           deriving Show

type CompiledZephyrAtom = GenericZephyrAtom CompiledZephyr Int
newtype CompiledZephyr = CompiledZephyr (Vector CompiledZephyrAtom)
    deriving Show
data CompiledZephyrSymbol = CompiledZephyrSymbol !ZephyrQualifiedWord !CompiledZephyr deriving Show

newtype ZephyrWord = ZephyrWord Text deriving (Show, Eq, Ord, IsString, Hashable)
type ZephyrBuilderAtom = GenericZephyrAtom ZephyrBuilder ZephyrWord
newtype ZephyrBuilder = ZephyrBuilder (DList ZephyrBuilderAtom)
    deriving (Show, Monoid)

symbolBytecode :: CompiledZephyrSymbol -> Vector CompiledZephyrAtom
symbolBytecode (CompiledZephyrSymbol _ (CompiledZephyr bc)) = bc

mapQuote :: (q -> q') -> GenericZephyrAtom q a -> GenericZephyrAtom q' a
mapQuote f (QuoteZ q) = QuoteZ (f q)
mapQuote _ (IntegerZ i) = IntegerZ i
mapQuote _ (FloatingZ d) = FloatingZ d
mapQuote _ (TextZ t) = TextZ t
mapQuote _ (BinaryZ b) = BinaryZ b
mapQuote _ (SymZ s) = SymZ s
mapQuote _ ZipUpZ = ZipUpZ
mapQuote _ ZipDownZ = ZipDownZ
mapQuote _ ZipReplaceZ = ZipReplaceZ
mapQuote _ CurTagZ = CurTagZ
mapQuote _ CurAtomZ = CurAtomZ
mapQuote _ ArgHoleZ = ArgHoleZ
mapQuote _ EnterZipperZ = EnterZipperZ
mapQuote _ CutZ = CutZ
mapQuote _ (CheckTagZ tag) = CheckTagZ tag
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
mapQuote _ FailZ = FailZ
mapQuote _ LogZ = LogZ
mapQuote _ YieldZ = YieldZ
mapQuote _ EqZ = EqZ
mapQuote _ LtZ = LtZ
mapQuote _ GtZ = GtZ
mapQuote _ PlusZ = PlusZ
mapQuote _ (TagZ ty tag argCnt) = TagZ ty tag argCnt

-- * Program execution

data ZephyrEvalError = CatZExpectsTwoQuotes
                     | ConsZExpectsAnAtomAndQuote
                     | DeQuoteZExpectsQuotedBlock
                     | DipZExpectsQuoteAndSomethingElse
                     | HitFail !String
                     | ConditionMustReturn0Or1
                     | CurHasNoTag
                     | CurIsNotAtom
                     | ExpectingTwoIntegersForArithmetic
                     | ZipDownNeeds1Argument
                     | EnterZipperExpects1Zipper
                     | CannotYieldNonZipper
                     | NeedAtomOrZipperAtRoot
                       deriving Show

type ZephyrStack = [ZephyrD]
data ZephyrContinuation = JustContinue !(Vector CompiledZephyrAtom)
                        | PushAndContinue !ZephyrD !(Vector CompiledZephyrAtom)
                        | IfThenElseAndContinue !(Vector CompiledZephyrAtom) !(Vector CompiledZephyrAtom)
                        | ExitZipper !(Vector CompiledZephyrAtom)
                          deriving Show
data ZephyrContext = ZephyrContext
                   { zephyrContinuations :: [ZephyrContinuation]
                   , zephyrStack         :: ZephyrStack
                   , zephyrZippers       :: [Zipper] }
                     deriving Show

data ZephyrD where
    ZephyrD :: !(ZippyD InMemory Atom a) -> ZephyrD
    ZephyrZ :: Zipper -> ZephyrD
    ZephyrQ :: !(Vector CompiledZephyrAtom) -> ZephyrD
deriving instance Show ZephyrD

type ZephyrExports = HM.HashMap ZephyrWord ZephyrProgram

-- * Types

data QualificationType = Unambiguous Text
                       | Ambiguous [Text]
                         deriving Show

type RecZippyFieldType = GenericZippyTyCon ZephyrScopedTy
newtype RecZippyTyCon = RecZippyTyCon { unRecTy :: GenericZippyTyCon (ZippyFieldType RecZippyTyCon) }
    deriving (Show, Ord, Eq)

data ZephyrScopedTy = Local !ZippyTyVarName
                    | Global !(ZippyFieldType RecZippyFieldType)
                      deriving Show


-- * Packages

data ZephyrPackage =
     ZephyrPackage
     { zephyrPackageName  :: !ZephyrWord

     , zephyrDependencies :: [ZephyrWord]
     , zephyrExports      :: [ZephyrWord]
     , zephyrTypes        :: [GenericZippyAlgebraicT ZippyTyVarName ZephyrScopedTy]
     , zephyrSymbols      :: [ZephyrSymbolDefinition] }
    deriving Show
