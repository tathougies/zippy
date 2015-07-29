{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE OverloadedStrings #-}
module Database.Zippy.Zephyr.Eval where

import Database.Zippy.Types
import Database.Zippy.Zephyr.Types

import Control.Applicative
import Control.Monad

import Data.Maybe
import Data.Int
import Data.Vector (Vector)
import qualified Data.Vector as V
import qualified Data.HashMap.Strict as HM
import qualified Data.Map as M

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

isZFalse (Zipper _ (AlgebraicT (ZippyAlgebraicT (ZippyTyCon (ZippyTyName pkg tyName) tyArgs) _)) (InMemoryD (CompositeD 0 _)) _) = V.null tyArgs && pkg == "base" && tyName == "Bool"
isZFalse _ = False

isZTrue (Zipper _ (AlgebraicT (ZippyAlgebraicT (ZippyTyCon (ZippyTyName pkg tyName) tyArgs) _)) (InMemoryD (CompositeD 1 _)) _) = V.null tyArgs && pkg == "base" && tyName == "Bool"
isZTrue _ = False

boolT :: ZippyT
boolT = AlgebraicT $
        ZippyAlgebraicT (ZippyTyCon (ZippyTyName "base" "Bool") V.empty)
                        (V.fromList [ ZippyDataCon (ZippyDataConName "False") V.empty
                                    , ZippyDataCon (ZippyDataConName "True") V.empty ])

runZephyr :: ZephyrProgram -> ZippySchema -> ZephyrStack -> Tx (Either ZephyrEvalError ZephyrStack)
runZephyr (ZephyrProgram entry symbols) sch initialStk =
    either Left (Right . zephyrStack) <$>
    go (symbolBytecode (symbols V.! entry)) (zephyrCtxtWithStack initialStk)
    where go :: Vector CompiledZephyrAtom -> ZephyrContext -> Tx (Either ZephyrEvalError ZephyrContext)
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

          interpret :: CompiledZephyrAtom -> Vector CompiledZephyrAtom -> ZephyrContext -> Tx (Either ZephyrEvalError ZephyrContext)
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
                _ -> return (Left ZipDownNeeds1Argument)
          interpret ZipReplaceZ next ctxt =
              case zephyrStack ctxt of
                top:stk -> case zephyrDToInMemoryD top of
                             Right d ->
                                 case zephyrZippers ctxt of
                                   [] -> move (Replace d) >>
                                         go next (ctxt { zephyrStack = stk })
                                   _:_ -> moveCutZipper next (ctxt { zephyrStack = stk }) (Replace d)
                             Left err -> return (Left err)
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
                _ -> return (Left EnterZipperExpects1Zipper)
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
          interpret YieldZ next ctxt =
              case zephyrStack ctxt of
                (ZephyrZ z):stk -> logAction (TxLogResult z) >>
                                   go next (ctxt { zephyrStack = stk })
                _ -> return (Left CannotYieldNonZipper)
          interpret LogZ next ctxt =
              case zephyrStack ctxt of
                x:stk -> logAction (TxLogMessage (show x)) >>
                         go next (ctxt { zephyrStack = stk })
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
              in case spineStrictMapM (liftM eraseInMemoryD . zephyrDToInMemoryD) args of
                   Right zippyArgs ->
                       go next (zephyrPush (ZephyrZ (Zipper OnlyInMemory (zippyTypes sch V.! tyRef) (InMemoryD (CompositeD tag (V.fromList zippyArgs))) [])) ctxt)
                   Left err -> return (Left err)

--          interpret x next ctxt = fail ("can't interpret " ++ show x)

          arithmetic :: (Int64 -> Int64 -> ZephyrD) -> Vector CompiledZephyrAtom -> ZephyrContext -> Tx (Either ZephyrEvalError ZephyrContext)
          arithmetic f next ctxt =
              case zephyrStack ctxt of
                (ZephyrD (IntegerD b)):(ZephyrD (IntegerD a)):stk ->
                    go next (ctxt { zephyrStack = (f a b):stk })
                _ -> return (Left ExpectingTwoIntegersForArithmetic)


          zephyrDToInMemoryD d =
              case d of
                ZephyrD x -> Right (InMemoryD x)
                ZephyrZ (Zipper _ _ x []) -> Right x
                _ -> Left NeedAtomOrZipperAtRoot

          moveCutZipper next ctxt mvmt =
              case zephyrZippers ctxt of
                zipper:zippers ->
                    do (zipper', _) <- moveOOB zipper mvmt
                       go next (ctxt { zephyrZippers = zipper':zippers })
