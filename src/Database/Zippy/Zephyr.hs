{-# LANGUAGE GeneralizedNewtypeDeriving, BangPatterns, TupleSections, OverloadedStrings, RankNTypes #-}
module Database.Zippy.Zephyr where

import Database.Zippy.Types

import Control.Applicative hiding ((<|>), many, optional)
import qualified Control.Applicative as A
import Control.Monad
import Control.Arrow

import Data.Char (digitToInt, ord)
import Data.Vector (Vector)
import Data.String
import Data.Int
import Data.Monoid
import Data.DList (DList)
import Data.ByteString (ByteString)
import Data.Text (Text)
import Data.Hashable
import Data.Maybe
import Data.Word
import qualified Data.DList as D
import qualified Data.Vector as V
import qualified Data.HashMap.Strict as HM

import Text.Parsec
import Text.Parsec.ByteString

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

  | EqZ
  | LtZ
  | GtZ
  | PlusZ

  | TagZ !ZippyTyRef !Word16 !Int
    deriving (Show, Functor)

data ZephyrPackage =
     ZephyrPackage
     { zephyrPackageName  :: !ZephyrWord

     , zephyrDependencies :: [ZephyrWord]
     , zephyrExports      :: [ZephyrWord]
     , zephyrTypes        :: [GenericZippyAlgebraicT ZippyTyName]
     , zephyrSymbols      :: [ZephyrSymbolDefinition] }
    deriving Show

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

-- * Program execution

data ZephyrError = CatZExpectsTwoQuotes
                 | ConsZExpectsAnAtomAndQuote
                 | DeQuoteZExpectsQuotedBlock
                 | DipZExpectsQuoteAndSomethingElse
                 | HitFail !String
                 | ConditionMustReturn0Or1
                 | CurHasNoTag
                 | CurIsNotAtom
                 | ExpectingTwoIntegersForArithmetic
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
mapQuote _ EqZ = EqZ
mapQuote _ LtZ = LtZ
mapQuote _ GtZ = GtZ
mapQuote _ PlusZ = PlusZ
mapQuote _ (TagZ ty tag argCnt) = TagZ ty tag argCnt

genDefinitionsForType :: ZippyTyRef -> GenericZippyAlgebraicT ZippyTyName -> [ZephyrSymbolDefinition]
genDefinitionsForType tyRef (ZippyAlgebraicT tyName cons) = concatMap genDefinitionsForCon (zip [0..] (V.toList cons))
    where genDefinitionsForCon (conIndex, ZippyTyCon (ZippyTyConName conName) argTys) =
              [ ZephyrSymbolDefinition (ZephyrWord ("IS-" <> conName <> "?"))
                ( ZephyrBuilder . D.fromList $
                  [ CheckTagZ (fromIntegral conIndex) ] )

              , ZephyrSymbolDefinition (ZephyrWord ("CUR-IS-" <> conName <> "?"))
                ( ZephyrBuilder . D.fromList $
                  [ CurTagZ
                  , IntegerZ (fromIntegral conIndex)
                  , EqZ ] )

              , ZephyrSymbolDefinition (ZephyrWord conName)
                ( ZephyrBuilder . D.fromList $
                  [ TagZ tyRef (fromIntegral conIndex) (V.length argTys) ] ) ] ++
              concatMap genDefinitionsForArg (zip [0..] (V.toList argTys))

          genDefinitionsForArg (i, ZippyUnnamedField _) = []
          genDefinitionsForArg (i, ZippyNamedField (ZippyTyArgName argName) _) =
              [ ZephyrSymbolDefinition (ZephyrWord ("VISIT-" <> argName))
                ( ZephyrBuilder . D.fromList $
                  [ IntegerZ i
                  , ZipDownZ

                  , DeQuoteZ

                  , ZipUpZ ])

              , ZephyrSymbolDefinition (ZephyrWord ("MOVETO-" <> argName))
                ( ZephyrBuilder . D.fromList $
                  [ IntegerZ i, ZipDownZ ])

              , ZephyrSymbolDefinition (ZephyrWord ("CHK-HOLE-" <> argName))
                ( ZephyrBuilder . D.fromList $
                  [ ArgHoleZ
                  , IntegerZ i
                  , EqZ ] ) ]

compilePackages :: [ZephyrPackage] -> ZippyTyName -> (HM.HashMap ZephyrWord ZephyrProgram, ZippySchema)
compilePackages pkgs rootTyName =
    let namesToInts = HM.fromList (zip names [0..])
        qualifiedSymbols = mconcat (map (\pkg -> map (zephyrPackageName pkg,) (zephyrSymbols pkg ++ concatMap genDefinitionsForType' (zephyrTypes pkg))) pkgs)
        symbols = map snd qualifiedSymbols
        names = map zephyrSymbolName symbols

        resolveSymbol symbol = fromJust (HM.lookup symbol namesToInts A.<|> error ("Cannot find " ++ show symbol))

        compiled = map compiledSymbol symbols
        compiledSymbol (ZephyrSymbolDefinition _ builder) = compiledBuilder builder
        compiledBuilder (ZephyrBuilder d) =
            let shallowResolved = map (fmap resolveSymbol) (D.toList d)
                resolved = map (mapQuote compiledBuilder) shallowResolved
            in CompiledZephyr . V.fromList $ resolved

        qualifiedWords = map (uncurry ZephyrQualifiedWord . second zephyrSymbolName ) qualifiedSymbols

        allTypes = concatMap zephyrTypes pkgs
        tyNamesToTyRef = HM.fromList $
                         zip (map (\(ZippyAlgebraicT qTyName _) -> tyName qTyName) allTypes) (map ZippyTyRef [0..])

        compiledTypes = map (fmap (fromJust . flip HM.lookup tyNamesToTyRef . tyName)) allTypes
        Just rootTy = HM.lookup (tyName rootTyName) tyNamesToTyRef
        schema = ZippySchema rootTy (V.fromList (map AlgebraicT compiledTypes))

        genDefinitionsForType' ty@(ZippyAlgebraicT qTyName _) =
            let Just tyRef = HM.lookup (tyName qTyName) tyNamesToTyRef
            in genDefinitionsForType tyRef ty

        allExports = concatMap zephyrExports pkgs
        progs = HM.fromList $
                map (\export -> (export, ZephyrProgram (fromJust (HM.lookup export namesToInts)) symbolTbl)) allExports

        symbolTbl = V.fromList (zipWith CompiledZephyrSymbol qualifiedWords compiled)
    in (progs, schema)

zephyrCtxtWithStack :: ZephyrStack -> ZephyrContext
zephyrCtxtWithStack stk = ZephyrContext
                        { zephyrContinuations = []
                        , zephyrStack = stk
                        , zephyrZippers = [] }

zephyrPush :: ZephyrD -> ZephyrContext -> ZephyrContext
zephyrPush d (ZephyrContext conts stk zs) = ZephyrContext conts (d:stk) zs

zephyrPushContinuation :: Vector CompiledZephyrAtom -> ZephyrContext -> ZephyrContext
zephyrPushContinuation next (ZephyrContext conts stk zs) = ZephyrContext ((JustContinue next):conts) stk zs

zephyrPushIf :: Vector CompiledZephyrAtom -> Vector CompiledZephyrAtom -> ZephyrContext -> ZephyrContext
zephyrPushIf ifTrue ifFalse (ZephyrContext conts stk zs) =
    ZephyrContext ((IfThenElseAndContinue ifTrue ifFalse):conts) stk zs

zephyrPushExitZipper :: Vector CompiledZephyrAtom -> ZephyrContext -> ZephyrContext
zephyrPushExitZipper next (ZephyrContext conts stk zs) =
    ZephyrContext ((ExitZipper next):conts) stk zs

zephyrPushDippedContinuation :: ZephyrD -> Vector CompiledZephyrAtom -> ZephyrContext -> ZephyrContext
zephyrPushDippedContinuation d next (ZephyrContext conts stk zs) = ZephyrContext ((PushAndContinue d next):conts) stk zs

zephyrModifyStack :: (ZephyrStack -> ZephyrStack) -> ZephyrContext -> ZephyrContext
zephyrModifyStack f (ZephyrContext conts stk zs) = ZephyrContext conts (f stk) zs

zTrue, zFalse :: ZephyrD
zFalse = ZephyrZ $ Zipper OnlyInMemory boolT (InMemoryD (CompositeD 0 V.empty)) []
zTrue = ZephyrZ $ Zipper OnlyInMemory boolT (InMemoryD (CompositeD 1 V.empty)) []

isZFalse, isZTrue :: Zipper -> Bool

isZFalse (Zipper _ (AlgebraicT (ZippyAlgebraicT (ZippyTyName pkg tyName) _)) (InMemoryD (CompositeD 0 _)) _) = pkg == "base" && tyName == "Bool"
isZFalse _ = False

isZTrue (Zipper _ (AlgebraicT (ZippyAlgebraicT (ZippyTyName pkg tyName) _)) (InMemoryD (CompositeD 1 _)) _) = pkg == "base" && tyName == "Bool"
isZTrue _ = False

boolT :: ZippyT
boolT = AlgebraicT $
        ZippyAlgebraicT (ZippyTyName "base" "Bool")
                        (V.fromList [ ZippyTyCon (ZippyTyConName "False") V.empty
                                    , ZippyTyCon (ZippyTyConName "True") V.empty ])

runZephyr :: ZephyrProgram -> ZippySchema -> ZephyrStack -> Tx (Either ZephyrError ZephyrStack)
runZephyr (ZephyrProgram entry symbols) sch initialStk =
    either Left (Right . zephyrStack) <$>
    go (symbolBytecode (symbols V.! entry)) (zephyrCtxtWithStack initialStk)
    where go :: Vector CompiledZephyrAtom -> ZephyrContext -> Tx (Either ZephyrError ZephyrContext)
          go bc initialCtxt
              | V.length bc == 0 =
                  case zephyrContinuations initialCtxt of
                    [] -> return (Right initialCtxt)
                    ((JustContinue next):conts) -> go next (initialCtxt { zephyrContinuations = conts })
                    ((PushAndContinue dipped next):conts) -> go next (initialCtxt { zephyrContinuations = conts, zephyrStack = dipped:zephyrStack initialCtxt })
                    ((IfThenElseAndContinue ifTrue ifFalse):conts) ->
                        case zephyrStack initialCtxt of
                          (ZephyrZ cond):stk
                              | isZFalse cond -> go ifFalse (initialCtxt { zephyrContinuations = conts, zephyrStack = stk })
                              | isZTrue cond -> go ifTrue (initialCtxt { zephyrContinuations = conts, zephyrStack = stk })
                          _ -> return (Left ConditionMustReturn0Or1)
                    ((ExitZipper next):conts) ->
                        go next (initialCtxt { zephyrContinuations = conts, zephyrStack = (ZephyrZ (head (zephyrZippers initialCtxt))):zephyrStack initialCtxt, zephyrZippers = tail (zephyrZippers initialCtxt) })
              | curOp <- V.head bc, bc' <- V.tail bc = interpret curOp bc' initialCtxt

          interpret :: CompiledZephyrAtom -> Vector CompiledZephyrAtom -> ZephyrContext -> Tx (Either ZephyrError ZephyrContext)
          interpret (IntegerZ i) next ctxt = go next (zephyrPush (ZephyrD (IntegerD i)) ctxt)
          interpret (FloatingZ f) next ctxt = go next (zephyrPush (ZephyrD (FloatingD f)) ctxt)
          interpret (TextZ t) next ctxt = go next (zephyrPush (ZephyrD (TextD t)) ctxt)
          interpret (BinaryZ b) next ctxt = go next (zephyrPush (ZephyrD (BinaryD b)) ctxt)
          interpret (QuoteZ (CompiledZephyr q)) next  ctxt = go next (zephyrPush (ZephyrQ q) ctxt)
          interpret (SymZ sym) next ctxt = go (symbolBytecode (symbols V.! sym)) (zephyrPushContinuation next ctxt)

          interpret SwapZ next ctxt = go next (zephyrModifyStack (\(a:b:xs) -> (b:a:xs)) ctxt)
          interpret DupZ next ctxt = go next (zephyrModifyStack (\(a:xs) -> a:a:xs) ctxt)
          interpret ZapZ next ctxt = go next (zephyrModifyStack (\(_:xs) -> xs) ctxt)
          interpret CatZ next ctxt =
              case zephyrStack ctxt of
                (ZephyrQ a):(ZephyrQ b):xs -> go next (ctxt { zephyrStack = (ZephyrQ (a V.++ b)):xs })
                _ -> return (Left CatZExpectsTwoQuotes)
          interpret ConsZ next ctxt =
              case zephyrStack ctxt of
                (ZephyrQ qXs):qX:xs ->
                    let qX' = case qX of
                                ZephyrD (IntegerD i) -> IntegerZ i
                                ZephyrD (FloatingD f) -> FloatingZ f
                                ZephyrD (BinaryD b) -> BinaryZ b
                                ZephyrD (TextD t) -> TextZ t
                                ZephyrQ c -> QuoteZ (CompiledZephyr c)
                    in go next (ctxt { zephyrStack = (ZephyrQ (qX' `V.cons` qXs)):xs })
                _ -> return (Left ConsZExpectsAnAtomAndQuote)
          interpret UnConsZ next ctxt =
              case zephyrStack ctxt of
                (ZephyrQ qXs):stk ->
                    let head = case V.head qXs of
                                 QuoteZ (CompiledZephyr c) -> ZephyrQ c
                                 IntegerZ i -> ZephyrD (IntegerD i)
                                 FloatingZ f -> ZephyrD (FloatingD f)
                                 BinaryZ b -> ZephyrD (BinaryD b)
                                 TextZ t -> ZephyrD (TextD t)
                                 x -> ZephyrQ (V.singleton x)
                    in go next (ctxt { zephyrStack = head:(ZephyrQ (V.tail qXs)):stk })
          interpret DeQuoteZ next ctxt =
              case zephyrStack ctxt of
                (ZephyrQ next'):xs ->
                    go next' (zephyrPushContinuation next (ctxt { zephyrStack = xs }))
                _ -> return (Left DeQuoteZExpectsQuotedBlock)
          interpret DipZ next ctxt =
              case zephyrStack ctxt of
                (ZephyrQ next'):dipped:xs ->
                    go next' (zephyrPushDippedContinuation dipped next (ctxt { zephyrStack = xs}))
                _ -> return (Left DipZExpectsQuoteAndSomethingElse)
          interpret ZipUpZ next ctxt =
              case zephyrZippers ctxt of
                [] -> move Up >> go next ctxt
                _:_ -> moveCutZipper next ctxt Up
          interpret ZipDownZ next ctxt =
              case zephyrStack ctxt of
                (ZephyrD (IntegerD t)):stk ->
                    case zephyrZippers ctxt of
                      [] -> move (Down (fromIntegral t)) >>
                            go next (ctxt { zephyrStack = stk })
                      _:_ -> moveCutZipper next (ctxt { zephyrStack = stk }) (Down (fromIntegral t))
                _ -> fail "Need 1 argument"
          interpret ZipReplaceZ next ctxt =
              case zephyrStack ctxt of
                top:stk -> do let d = zephyrDToInMemoryD top
                              case zephyrZippers ctxt of
                                [] -> move (Replace d) >>
                                      go next (ctxt { zephyrStack = stk })
                                _:_ -> moveCutZipper next (ctxt { zephyrStack = stk }) (Replace d)
          interpret CurTagZ next ctxt =
              case zephyrZippers ctxt of
                [] -> do curRes <- cur
                         case curRes of
                           CurIsAtom _ -> return (Left CurHasNoTag)
                           CurHasTag t -> go next (zephyrPush (ZephyrD (IntegerD (fromIntegral t))) ctxt)
                (Zipper _ _ (InMemoryD (CompositeD tag _)) _):_ ->
                    go next (zephyrPush (ZephyrD (IntegerD (fromIntegral tag))) ctxt)
                _ -> return (Left CurHasNoTag)
          interpret CurAtomZ next ctxt =
              case zephyrZippers ctxt of
                [] -> do curRes <- cur
                         case curRes of
                           CurIsAtom (InMemoryAtomD a) -> go next (zephyrPush (ZephyrD a) ctxt)
                           CurHasTag _ -> return (Left CurIsNotAtom)
                (Zipper _ _ (InMemoryD dt) _):_ ->
                    case dt of
                      CompositeD _ _ -> return (Left CurIsNotAtom)
                      a@(IntegerD _) -> go next (zephyrPush (ZephyrD a) ctxt)
                      a@(TextD _) -> go next (zephyrPush (ZephyrD a) ctxt)
                      a@(BinaryD _) -> go next (zephyrPush (ZephyrD a) ctxt)
                      a@(FloatingD _) -> go next (zephyrPush (ZephyrD a) ctxt)
          interpret ArgHoleZ next ctxt =
              case zephyrZippers ctxt of
                [] -> do Just i <- parentArgHole
                         go next (zephyrPush (ZephyrD (IntegerD (fromIntegral i))) ctxt)
                (Zipper _ _ _ (Within _ _ hole _ _:_)):_ ->
                    go next (zephyrPush (ZephyrD (IntegerD (fromIntegral hole))) ctxt)
          interpret EnterZipperZ next ctxt =
              case zephyrStack ctxt of
                (ZephyrQ next'):(ZephyrZ z):stk ->
                    go next' (zephyrPushExitZipper next (ctxt { zephyrStack = stk, zephyrZippers = z:zephyrZippers ctxt }))
                _ -> fail "can only enter zippers"
          interpret CutZ next ctxt =
              do z <- cut
                 go next (zephyrPush (ZephyrZ z) ctxt)
          interpret (CheckTagZ tag) next ctxt =
              case zephyrStack ctxt of
                (ZephyrZ (Zipper _ _ (InMemoryD (CompositeD actTag _)) _):stk) ->
                    let res = if tag == actTag
                              then zTrue
                              else zFalse
                    in go next (ctxt { zephyrStack = res:stk })
          interpret IfThenElseZ next ctxt =
              case zephyrStack ctxt of
                (ZephyrQ else_):(ZephyrQ then_):(ZephyrQ if_):stk ->
                    go if_ (zephyrPushIf then_ else_ (ctxt { zephyrStack = stk }))
          interpret LengthZ next ctxt =
              case zephyrStack ctxt of
                (ZephyrQ b):stk ->
                    go next (ctxt { zephyrStack = ZephyrD (IntegerD (fromIntegral (V.length b))):stk })
          interpret FailZ next ctxt =
              case zephyrStack ctxt of
                x:_ -> return (Left (HitFail (show x)))
                _ -> return (Left (HitFail "Nothing on stack for FAIL"))
          interpret EqZ next ctxt =
              arithmetic (\a b -> if a == b then zTrue else zFalse) next ctxt
          interpret LtZ next ctxt =
              arithmetic (\a b -> if a < b then zTrue else zFalse) next ctxt
          interpret GtZ next ctxt =
              arithmetic (\a b -> if a > b then zTrue else zFalse) next ctxt
          interpret PlusZ next ctxt =
              arithmetic (\a b -> ZephyrD (IntegerD (a + b))) next ctxt

          -- Internal only... TagZ can be used to construct literal zippers
          interpret (TagZ (ZippyTyRef tyRef) tag argCnt) next ctxt =
              let stk = zephyrStack ctxt
                  args = reverse (take argCnt stk)
                  zippyArgs = spineStrictMap (eraseInMemoryD . zephyrDToInMemoryD) args
              in go next (zephyrPush (ZephyrZ (Zipper OnlyInMemory (zippyTypes sch V.! tyRef) (InMemoryD (CompositeD tag (V.fromList zippyArgs))) [])) ctxt)

          interpret x next ctxt = fail ("can't interpret " ++ show x)

          arithmetic :: (Int64 -> Int64 -> ZephyrD) -> Vector CompiledZephyrAtom -> ZephyrContext -> Tx (Either ZephyrError ZephyrContext)
          arithmetic f next ctxt =
              case zephyrStack ctxt of
                (ZephyrD (IntegerD b)):(ZephyrD (IntegerD a)):stk ->
                    go next (ctxt { zephyrStack = (f a b):stk })
                _ -> return (Left ExpectingTwoIntegersForArithmetic)


          zephyrDToInMemoryD d =
              case d of
                ZephyrD x -> InMemoryD x
                ZephyrZ (Zipper _ _ x []) -> x
                _ -> error "Need atom or zipper at root"

          moveCutZipper next ctxt mvmt =
              case zephyrZippers ctxt of
                zipper:zippers ->
                    do (zipper', _) <- moveOOB zipper mvmt
                       go next (ctxt { zephyrZippers = zipper':zippers })

-- * Zephyr parsing and compilation
zephyrIdentifier = try $
                   do name <- many1 (satisfy (\c -> c /= ' ' && c /= '\t' && c /= '\v' &&
                                                    c /= '\r' && c /= '\n' && c /= ']' &&
                                                    c /= '[' && c /= '$'))
                      if name == "DEFINE" ||
                         name == "EXPORT" ||
                         name == "DATA"   then mzero else pure name

zephyrConsIdentifier = do name <- many1 (satisfy (\c -> c /= ' ' && c /= '\t' && c /= '\v' &&
                                                    c /= '\r' && c /= '\n' && c /= ']' &&
                                                    c /= '[' && c /= '$' && c /= '='))
                          if name == "DEFINE" ||
                             name == "EXPORT" ||
                             name == "DATA"   ||
                             name == "CONS"   then mzero else pure name

whitespace :: Parser ()
whitespace = (oneOf " \t\v\r\n" *> optional whitespace) <|> (char '{' *> consumeComment *> optional whitespace) <|> pure ()
    where consumeComment = many (satisfy (/= '}')) *> char '}'

atomP :: Parser ZephyrBuilderAtom
atomP = unquotedAtomP <|>
        symbol <|>
        (char '[' *> whitespace *> (QuoteZ <$> zephyrP) <* char ']') <?>
        "atom"
        where symbol = do identifier <- zephyrIdentifier
                          case identifier of
                            "SWAP"     -> pure SwapZ
                            "DUP"      -> pure DupZ
                            "ZAP"      -> pure ZapZ
                            "CAT"      -> pure CatZ
                            "CONS"     -> pure ConsZ
                            "UNCONS"   -> pure UnConsZ
                            "I"        -> pure DeQuoteZ
                            "DIP"      -> pure DipZ
                            "ZIP-UP"   -> pure ZipUpZ
                            "ZIP-DOWN" -> pure ZipDownZ
                            "ZIP-REPLACE" -> pure ZipReplaceZ
                            "CUR-TAG"  -> pure CurTagZ
                            "CUR-ATOM" -> pure CurAtomZ
                            "ARG-HOLE" -> pure ArgHoleZ
                            "ENTER-ZIPPER" -> pure EnterZipperZ
                            "CUT" -> pure CutZ
                            "IFTE"     -> pure IfThenElseZ
                            "FAIL"     -> pure FailZ
                            "LENGTH"   -> pure LengthZ
                            "=="       -> pure EqZ
                            ">"        -> pure GtZ
                            "<"        -> pure LtZ
                            "+"        -> pure PlusZ
                            _          -> pure (SymZ (fromString identifier))

literalP :: Parser ZephyrD
literalP = do res <- unquotedAtomP
              case res of
                IntegerZ i -> return (ZephyrD (IntegerD i))
                FloatingZ f -> return (ZephyrD (FloatingD f))
                TextZ t -> return (ZephyrD (TextD t))
                BinaryZ b -> return (ZephyrD (BinaryD b))

unquotedAtomP :: Parser (GenericZephyrAtom a b)
unquotedAtomP = (either (IntegerZ . fromIntegral) FloatingZ <$> signedNatFloat) <|>
                (TextZ . fromString <$> (stringLiteral :: Parser String)) <|>
                (BinaryZ . fromString <$> (char '$' *> (stringLiteral :: Parser String)))  <?> "unquoted atom"
        where stringLiteral   = do { str <- between (char '"')
                                            (char '"' <?> "end of string")
                                            (many stringChar)
                                   ; return (foldr (maybe id (:)) "" str)
                                   }
                                <?> "literal string"

              stringChar      = do { c <- stringLetter; return (Just c) }
                                <|> stringEscape
                                <?> "string character"

              stringLetter    = satisfy (\c -> (c /= '"') && (c /= '\\') && (c > '\026'))

              stringEscape    = do{ char '\\'
                                  ;     do{ escapeGap  ; return Nothing }
                                    <|> do{ escapeEmpty; return Nothing }
                                    <|> do{ esc <- escapeCode; return (Just esc) }
                                  }

              escapeEmpty     = char '&'
              escapeGap       = do{ many1 space
                                  ; char '\\' <?> "end of string gap"
                                  }

              -- escape codes
              escapeCode      = charEsc <|> charNum <|> charAscii <|> charControl
                                <?> "escape code"

              charControl     = do{ char '^'
                                  ; code <- upper
                                  ; return (toEnum (fromEnum code - fromEnum 'A'))
                                  }

              charNum         = do{ code <- decimal
                                            <|> do{ char 'o'; number 8 octDigit }
                                            <|> do{ char 'x'; number 16 hexDigit }
                                  ; return (toEnum (fromIntegral code))
                                  }

              charEsc         = choice (map parseEsc escMap)
                              where
                                parseEsc (c,code)     = do{ char c; return code }

              charAscii       = choice (map parseAscii asciiMap)
                              where
                                parseAscii (asc,code) = try (do{ string asc; return code })

              -- escape code tables
              escMap          = zip ("abfnrtv\\\"\'") ("\a\b\f\n\r\t\v\\\"\'")
              asciiMap        = zip (ascii3codes ++ ascii2codes) (ascii3 ++ ascii2)

              ascii2codes     = ["BS","HT","LF","VT","FF","CR","SO","SI","EM",
                                 "FS","GS","RS","US","SP"]
              ascii3codes     = ["NUL","SOH","STX","ETX","EOT","ENQ","ACK","BEL",
                                 "DLE","DC1","DC2","DC3","DC4","NAK","SYN","ETB",
                                 "CAN","SUB","ESC","DEL"]

              ascii2          = ['\BS','\HT','\LF','\VT','\FF','\CR','\SO','\SI',
                                 '\EM','\FS','\GS','\RS','\US','\SP']
              ascii3          = ['\NUL','\SOH','\STX','\ETX','\EOT','\ENQ','\ACK',
                                 '\BEL','\DLE','\DC1','\DC2','\DC3','\DC4','\NAK',
                                 '\SYN','\ETB','\CAN','\SUB','\ESC','\DEL']

              signedNatFloat  = do isNeg <- ( (char '-' >> pure True) <|>
                                              pure False )
                                   let f :: Num a => a -> a
                                       f = if isNeg then negate else id
                                   either (Left . f) (Right . f) <$> natFloat

              natFloat        = do{ char '0'
                                  ; zeroNumFloat
                                  }
                                <|> decimalFloat

              zeroNumFloat    =  do{ n <- hexadecimal <|> octal
                                   ; return (Left n)
                                   }
                              <|> decimalFloat
                              <|> fractFloat 0
                              <|> return (Left 0)

              decimalFloat    = do{ n <- decimal
                                  ; option (Left n)
                                           (fractFloat n)
                                  }

              fractFloat n    = do{ f <- fractExponent n
                                  ; return (Right f)
                                  }

              fractExponent n = do{ fract <- fraction
                                  ; expo  <- option 1.0 exponent'
                                  ; return ((fromInteger n + fract)*expo)
                                  }
                              <|>
                                do{ expo <- exponent'
                                  ; return ((fromInteger n)*expo)
                                  }

              fraction        = do{ char '.'
                                  ; digits <- many1 digit <?> "fraction"
                                  ; return (foldr op 0.0 digits)
                                  }
                                <?> "fraction"
                              where
                                op d f    = (f + fromIntegral (digitToInt d))/10.0

              exponent'       = do{ oneOf "eE"
                                  ; f <- sign
                                  ; e <- decimal <?> "exponent"
                                  ; return (power (f e))
                                  }
                                <?> "exponent"
                              where
                                 power e  | e < 0      = 1.0/power(-e)
                                          | otherwise  = fromInteger (10^e)


              -- integers and naturals
              int             = do{ f <- sign
                                  ; n <- nat
                                  ; return (f n)
                                  }

              sign            =   (char '-' >> return negate)
                              <|> (char '+' >> return id)
                              <|> return id

              nat             = zeroNumber <|> decimal

              zeroNumber      = do{ char '0'
                                  ; hexadecimal <|> octal <|> decimal <|> return 0
                                  }
                                <?> ""

              decimal         = number 10 digit
              hexadecimal     = do{ oneOf "xX"; number 16 hexDigit }
              octal           = do{ oneOf "oO"; number 8 octDigit  }

              number base baseDigit
                  = do{ digits <- many1 baseDigit
                      ; let n = foldl (\x d -> base*x + toInteger (digitToInt d)) 0 digits
                      ; seq n (return n)
                      }

parseZephyrStack :: ByteString -> Either ParseError [ZephyrD]
parseZephyrStack bs = parse (many (literalP <* whitespace)) "<network>" bs

zephyrP :: Parser ZephyrBuilder
zephyrP = (whitespace <|> pure ()) *> go (ZephyrBuilder mempty) <?> "definition"
    where go b@(ZephyrBuilder rest) =
              ((atomP <* whitespace) >>= \atom ->
                   go (ZephyrBuilder (rest <> D.singleton atom))) <|>
              pure b

dependency :: Parser ZephyrWord
dependency = fromString <$> (string "IMPORT" *> whitespace *> zephyrIdentifier)

packageP :: Parser ZephyrPackage
packageP = do whitespace <|> pure ()
              string "PACKAGE"
              whitespace
              pkgName <- fromString <$> zephyrIdentifier
              whitespace
              dependencies <- many (dependency <* whitespace)
              (symbols, exports, dataTypes) <- mconcat <$> many1 (fstP symbolDef <|> sndP export <|> thdP (dataType pkgName))
              return (ZephyrPackage (ZephyrWord pkgName) dependencies (map fromString exports) dataTypes symbols)
    where symbolDef = try (string "DEFINE") *> whitespace *>
                      (ZephyrSymbolDefinition
                       <$> (fromString <$> zephyrIdentifier <* whitespace <* string "==" <* whitespace)
                       <*> zephyrP)
          export = string "EXPORT" *> whitespace *> zephyrIdentifier <* whitespace
          dataType pkgName =
              string "DATA" *> whitespace *>
              ( ZippyAlgebraicT
                <$> (ZippyTyName pkgName . fromString <$> (zephyrConsIdentifier <* whitespace <* string "==" <* whitespace))
                <*> (V.fromList <$>
                     many1 dataTypeCon) )
          dataTypeCon = string "CONS" *> whitespace *>
                        (ZippyTyCon <$> (ZippyTyConName . fromString <$> ((zephyrConsIdentifier <?> "constructor name") <* whitespace))
                                    <*> (V.fromList <$> many dataConArg))
          dataConArg = do f <- try (ZippyNamedField <$> ((ZippyTyArgName . fromString <$> zephyrConsIdentifier) <* char '=')) <|> pure ZippyUnnamedField
                          f <$> (try (Left <$> (simpleZippyTP <* whitespace)) <|>
                                 try (Right . ZippyTyName "" . fromString <$> (zephyrConsIdentifier <* whitespace) <?> "type name" ))

          simpleZippyTP = (string "Text"     *> pure TextT)     <|>
                          (string "Integer"  *> pure IntegerT)  <|>
                          (string "Binary"   *> pure BinaryT)   <|>
                          (string "Floating" *> pure FloatingT) <?> "simple type"

          fstP = (>>= \x -> pure ([x], [], []))
          sndP = (>>= \x -> pure ([], [x], []))
          thdP = (>>= \x -> pure ([], [], [x]))

readZephyrPackage :: FilePath -> IO (Either ParseError ZephyrPackage)
readZephyrPackage fp = parseFromFile packageP fp
