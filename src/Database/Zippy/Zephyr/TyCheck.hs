{-# LANGUAGE RecordWildCards, TupleSections, RankNTypes, OverloadedStrings, MultiParamTypeClasses, LambdaCase, ScopedTypeVariables #-}
module Database.Zippy.Zephyr.TyCheck where

import Database.Zippy.Zephyr.Types
import Database.Zippy.Zephyr.Parse
import Database.Zippy.Zephyr.Internal
import Database.Zippy.Types

import Prelude hiding (mapM)

import Control.Applicative
import Control.Monad.ST
import Control.Monad.State hiding (mapM)

import Data.Proxy
import Data.STRef
import Data.Traversable (mapM)
import Data.Foldable (Foldable, foldlM)
import Data.List (intercalate)
import Data.Monoid
import Data.Maybe
import Data.UnionFind.ST
import qualified Data.Text as T
import qualified Data.Vector as V
import qualified Data.DList as D
import qualified Data.HashMap.Strict as HM
import qualified Data.HashTable.ST.Basic as HT

import Debug.Trace

data ZephyrTyCheckState s = ZephyrTyCheckState
                          { nextVar :: ST s ZephyrTyVar

                          , tyCheckTyVars :: HT.HashTable s ZephyrTyVar (Point s ZephyrTyDesc)

                          , unifyIndent :: Int }

newtype ZephyrTyErrorLocation = ZephyrTyErrorLocation (ZephyrTyCheckLocation -> ZephyrTyCheckLocation)

instance Monoid ZephyrTyErrorLocation where
    mempty = ZephyrTyErrorLocation id
    mappend (ZephyrTyErrorLocation a) (ZephyrTyErrorLocation b) = ZephyrTyErrorLocation $ a . b

instance Show ZephyrTyErrorLocation where
    show (ZephyrTyErrorLocation loc) = show (loc Here)

data ZephyrTyDesc where
    ZephyrTyDesc :: IsKind k => ZephyrT k ZephyrTyVar -> [ZephyrTyCheckLocation] -> ZephyrTyDesc
    ZephyrTyDescFree :: Maybe ZephyrKind -> ZephyrTyVar -> [ZephyrTyCheckLocation]-> ZephyrTyDesc
deriving instance Show ZephyrTyDesc

descKind :: ZephyrTyDesc -> Maybe ZephyrKind
descKind (ZephyrTyDescFree k _ _) = k
descKind (ZephyrTyDesc z _) = Just $ kindOf z

descKindsMatch :: ZephyrTyDesc -> ZephyrTyDesc -> Bool
descKindsMatch a b = case (descKind a, descKind b) of
                       (Nothing, _) -> True
                       (_, Nothing) -> True
                       (Just a, Just b) -> a == b

descLoc :: ZephyrTyDesc -> [ZephyrTyCheckLocation]
descLoc (ZephyrTyDesc _ loc) = loc
descLoc (ZephyrTyDescFree _ _ loc) = loc

data ZephyrTyCheckOp = ZephyrTyCheckCheckState !ZephyrTyErrorLocation !(ZephyrExecState ZephyrTyVar)
                     | ZephyrTyCheckCheckEffect !ZephyrTyErrorLocation !(ZephyrEffect ZephyrTyVar)
                     | ZephyrTyCheckCheckSymbol !ZephyrTyErrorLocation !ZephyrTyVar
                       deriving Show

data ZephyrTyCheckError where
    InfinitelyRecursiveType :: !ZephyrTyVar -> !ZephyrTyDesc -> ZephyrTyCheckError
    KindMismatch :: (IsKind k1, IsKind k2) => !(ZephyrT k1 ZephyrTyVar) -> !(ZephyrT k2 ZephyrTyVar) -> ZephyrTyCheckError
    ExpectingKind :: !ZephyrKind -> !ZephyrKind -> ZephyrTyCheckError
    InvalidDemotion :: !(ZephyrT ZephyrStackAtomK ZephyrTyVar) -> ZephyrTyCheckError -- ^ Cannot demote stack atom to zipper atom
    CannotUnify :: !ZephyrTyDesc {- actual -} -> !ZephyrTyDesc {- expected -} -> ZephyrTyCheckError
    HitStackBottom :: ZephyrTyCheckError
    UncheckableOp :: ZephyrTyCheckError

    GenericFail :: !String -> ZephyrTyCheckError
deriving instance Show ZephyrTyCheckError
data ZephyrTyCheckLocation = LocatedAt !SourceRange !ZephyrTyCheckLocation
                           | WhileCheckingAtom !(GenericZephyrAtom ZephyrBuilder ZephyrWord) !ZephyrTyCheckLocation
                           | WhileCheckingStateAssertion !(ZephyrExecState ZippyTyVarName) !ZephyrTyCheckLocation
                           | Here
                             deriving Show

newtype ZephyrTyCheckM s a = ZephyrTyCheckM { runZephyrTyCheckM :: ZephyrTyErrorLocation ->
                                                                   ZephyrTyCheckState s ->
                                                                   ST s (Either ([ZephyrTyCheckLocation], ZephyrTyCheckError) a, ZephyrTyCheckState s) }

instance Monad (ZephyrTyCheckM s) where
    return = pure
    a >>= b = ZephyrTyCheckM $ \loc s -> do (x, s') <- runZephyrTyCheckM a loc s
                                            case x of
                                              Left err -> pure (Left err, s')
                                              Right x  -> runZephyrTyCheckM (b x) loc s'
    fail x = dieTyCheck [] (GenericFail x)

instance Functor (ZephyrTyCheckM s) where
    fmap f a = pure . f =<< a

instance Applicative (ZephyrTyCheckM s) where
    pure x = ZephyrTyCheckM $ \_ s -> pure (Right x, s)
    f <*> x = do f' <- f
                 x' <- x
                 pure (f' x')

instance MonadState (ZephyrTyCheckState s) (ZephyrTyCheckM s) where
    get = ZephyrTyCheckM $ \_ s -> pure (Right s, s)
    put s = ZephyrTyCheckM $ \_ _ -> pure (Right (), s)

tyDescLoc :: ZephyrTyDesc -> [ZephyrTyCheckLocation]
tyDescLoc (ZephyrTyDescFree _ _ loc) = loc
tyDescLoc (ZephyrTyDesc _ loc) = loc

dieTyCheck :: [ZephyrTyCheckLocation] -> ZephyrTyCheckError -> ZephyrTyCheckM s a
dieTyCheck otherLocs err = ZephyrTyCheckM $ \(ZephyrTyErrorLocation loc) s -> pure (Left (loc Here:otherLocs, err), s)

catchTyCheck :: ZephyrTyCheckM s a -> (ZephyrTyCheckError -> ZephyrTyCheckM s a) -> ZephyrTyCheckM s a
catchTyCheck action onExc =
    ZephyrTyCheckM $ \loc s ->
    do (res, s') <- runZephyrTyCheckM action loc s
       case res of
         Left (locs, err) -> do (res', s'') <- runZephyrTyCheckM (onExc err) loc s'
                                case res' of
                                  Left (locs', err') -> pure (Left (locs ++ locs', err'), s'')
                                  Right res -> pure (Right res, s'')
         Right res -> pure (Right res, s')

zephyrST :: ST s a -> ZephyrTyCheckM s a
zephyrST action = ZephyrTyCheckM $ \loc s ->
                  do res <- action
                     pure (Right res, s)

certifyPackage :: ZephyrPackage -> ZephyrTyCheckedPackage
certifyPackage pkg = fmap unwrapBuilder pkg
    where unwrapBuilder (ZephyrBuilder ops) = ZephyrTyChecked [mapQuote unwrapBuilder atom | ZephyrAtom atom _ <- D.toList ops]

runInNewTyCheckM :: (forall s. ZephyrTyCheckM s x) -> Either ([ZephyrTyCheckLocation], ZephyrTyCheckError) x
runInNewTyCheckM f = runST $
                     do st <- newTyCheckState
                        (res, _) <- runZephyrTyCheckM f mempty st
                        return res

inNestedLocation :: ZephyrTyErrorLocation -> ZephyrTyCheckM s a -> ZephyrTyCheckM s a
inNestedLocation nestedLoc action =
    ZephyrTyCheckM $ \loc s -> runZephyrTyCheckM action (loc <> nestedLoc) s

newTyCheckState :: ST s (ZephyrTyCheckState s)
newTyCheckState = do var <- newSTRef 0
                     tyVars <- HT.new
                     return (ZephyrTyCheckState
                             { nextVar = do ret <- readSTRef var
                                            modifySTRef' var (+ 1)
                                            return (ZephyrTyVar ret)
                             , tyCheckTyVars = tyVars
                             , unifyIndent = 0 })

getPointForVariable :: ZephyrTyVar -> ZephyrTyCheckM s (Point s ZephyrTyDesc)
getPointForVariable tyVar =
    do tyVars <- gets tyCheckTyVars
       tyVarPoint <- zephyrST (HT.lookup tyVars tyVar)
       case tyVarPoint of
         Nothing -> zephyrST $
                    do newPoint <- fresh (ZephyrTyDescFree Nothing tyVar mempty)
                       HT.insert tyVars tyVar newPoint
                       return newPoint
         Just tyVarPoint -> return tyVarPoint

tyCheckPackages :: ZephyrSymbolEnv (ZephyrEffect ZephyrTyVar) -> ZephyrTypeLookupEnv -> [ZephyrPackage] -> ZephyrTyCheckM s [ZephyrTyCheckedPackage]
tyCheckPackages pretypedSymbols types pkgs = tyCheck
    -- Basic type checking steps
    --
    -- (1) First, replace every atom with its effect assertion before and after
    --     For built-ins, we look up the effect assertions in a table. For top-level
    --     definitions, we build a general effect definition (Z | S --> Z' | S') which
    --     later gets unified. All type variables are instantiated at this point
    -- (2) then we go through the effects 1-by-1 and generate all unification statements
    where tyCheck = do typedSymbols <- mkTypedSymbols

                       typedSymbolOps <- mkTypedSymbolOps typedSymbols
                       symbolEffects <- trace ("Got typed ops: " ++ ppTypedSymbols typedSymbolOps ++ "\n") (assertSymbols typedSymbolOps)
                       unifySymbols typedSymbols symbolEffects

                       tyDescs <- gets tyCheckTyVars
                       tyDescs <- zephyrST (HT.foldM (\assocs (key, val) -> descriptor val >>= \val -> pure ((key, val):assocs)) [] tyDescs)
                       symbolTypes <- trace (intercalate "\n" (map ppTyDesc tyDescs) ++ "\nDone") (mapM (mapM (\(ZephyrSymbolDefinition name ty) -> ZephyrSymbolDefinition name <$> simplifyEffect ty) . zephyrSymbols) symbolEffects)
                       trace ("Got typed symbols: " ++ ppSymbolTypes symbolTypes ++ "\n") (return ())
                       pure (fmap certifyPackage pkgs)


          allSymbols = map zephyrSymbols pkgs
          ppTypedSymbols typedPkgs = intercalate "\n=======\n" $
                                     concatMap (\typedPkg ->
                                                map (\(ZephyrSymbolDefinition (ZephyrWord name) code) ->
                                                         concat [ "DEFINE ", T.unpack name, " == \n"
                                                                , intercalate "\n" $ map ppTyCheckOp code ]) (zephyrSymbols typedPkg)) typedPkgs
          ppSymbolTypes typedPkgs = intercalate "\n=======\n" $
                                    concatMap (\typedPkg ->
                                               map (\(ZephyrSymbolDefinition (ZephyrWord name) effect) ->
                                                    concat [ "TY ", T.unpack name, " ", ppEffect effect, "\n"]) typedPkg) typedPkgs

          assertSymbols typedOps = mapM (mapM assertSymbol) typedOps

          mkTypedSymbols :: ZephyrTyCheckM s (ZephyrSymbolEnv ZephyrTyVar)
          mkTypedSymbols = let typePackageSymbols pkg =
                                   map (\(name, tyRef) -> ((zephyrPackageName pkg, name), tyRef)) <$>
                                   mapM (\(ZephyrSymbolDefinition name _) ->
                                             (name,) <$> newTyVar) (zephyrSymbols pkg)
                           in buildSymbolEnv . concat <$> mapM typePackageSymbols pkgs

          mkTypedSymbolOps :: ZephyrSymbolEnv ZephyrTyVar -> ZephyrTyCheckM s [GenericZephyrPackage [ZephyrTyCheckOp]]
          mkTypedSymbolOps typedSymbols = mapM (mapM (mkTypedZephyrBuilder types pretypedSymbols typedSymbols)) pkgs

type TyCheckEndoM s x = x -> ZephyrTyCheckM s x

simplifyTyDesc :: TyCheckEndoM s ZephyrTyDesc
simplifyTyDesc (ZephyrTyDescFree k v loc) = pure (ZephyrTyDescFree k v loc)
simplifyTyDesc (ZephyrTyDesc z loc) = ZephyrTyDesc <$> simplifyZephyrT z <*> pure loc

simplifyEffect :: TyCheckEndoM s (ZephyrEffect ZephyrTyVar)
simplifyEffect eff@(ZephyrEffect zipper before after) = trace ("Simplify effect " ++ show eff) (ZephyrEffect <$> simplifyZephyrT zipper
                                                                                                             <*> simplifyZephyrT before
                                                                                                             <*> simplifyZephyrT after)

simplifyZephyrT :: TyCheckEndoM s (ZephyrT k ZephyrTyVar)
simplifyZephyrT z | trace ("simplify " ++ show z) False = undefined
simplifyZephyrT (ZephyrZipperT (SimpleFieldT s)) = pure (ZephyrZipperT (SimpleFieldT s))
simplifyZephyrT (ZephyrZipperT (RefFieldT r)) = ZephyrZipperT . RefFieldT <$> simplifyZipperTyCon r
simplifyZephyrT (ZephyrQuoteT eff) = ZephyrQuoteT <$> simplifyEffect eff
simplifyZephyrT ZephyrStackBottomT = pure ZephyrStackBottomT
simplifyZephyrT (st :> top) = ((:>) <$> simplifyZephyrT st <*> simplifyZephyrT top)
simplifyZephyrT (ZephyrVarT tyVar) =
    do tyDesc <- zephyrST . descriptor =<< getPointForVariable tyVar
       case tyDesc of
         ZephyrTyDescFree _ tyVar _ -> pure (ZephyrVarT tyVar)
         ZephyrTyDesc (ZephyrVarT v) _
             | v == tyVar -> pure (ZephyrVarT v)
         ZephyrTyDesc ty _ -> case safeCoercedKind ty of
                                Just ty -> simplifyZephyrT ty
                                Nothing -> fail "Kind mismatch during simplification"

simplifyZipperTyCon :: TyCheckEndoM s (GenericZippyTyCon (ZephyrT ZephyrZipperK ZephyrTyVar))
simplifyZipperTyCon (ZippyTyCon tyName tyArgs) =
    ZippyTyCon tyName <$> mapM simplifyZephyrT tyArgs

unifySymbols :: ZephyrSymbolEnv ZephyrTyVar -> [GenericZephyrPackage (ZephyrEffect ZephyrTyVar)] -> ZephyrTyCheckM s ()
unifySymbols env typedPackages =
    mapM (\pkg -> mapM (unifyPkgSymbol (zephyrPackageName pkg)) (zephyrSymbols pkg)) typedPackages >> return ()
    where unifyPkgSymbol pkgName (ZephyrSymbolDefinition sym eff) =
              let Just tyVar = lookupInSymbolEnv (Right (pkgName, sym)) env
              in assertTyVarUnifies' tyVar (ZephyrQuoteT eff)

assertSymbol :: [ZephyrTyCheckOp] -> ZephyrTyCheckM s (ZephyrEffect ZephyrTyVar)
assertSymbol typedOps = do initialZipper <- newTyVar
                           initialStack <- newTyVar

                           assertTyVarUnifies' initialZipper =<< (zipperVarT <$> newTyVar)
                           assertTyVarUnifies' initialStack =<< (stackVarT <$> newTyVar)

                           let initialState = ZephyrExecState zipper initialStackVar
                               zipper = zipperVarT initialZipper
                               initialStackVar = stackVarT initialStack
                           ZephyrExecState _ finalStack <- foldlM assertTyCheckOp initialState typedOps
                           return (ZephyrEffect zipper initialStackVar finalStack)

assertTyCheckOp :: ZephyrExecState ZephyrTyVar -> ZephyrTyCheckOp -> ZephyrTyCheckM s (ZephyrExecState ZephyrTyVar)
assertTyCheckOp actNow (ZephyrTyCheckCheckState loc expNow) =
    inNestedLocation loc $
    do assertState actNow expNow
       pure expNow
assertTyCheckOp (ZephyrExecState actZipper actBefore) (ZephyrTyCheckCheckEffect loc (ZephyrEffect expZipper expBefore after)) =
    inNestedLocation loc $
    do assertState (ZephyrExecState actZipper actBefore) (ZephyrExecState expZipper expBefore)
       pure (ZephyrExecState expZipper after)
assertTyCheckOp (ZephyrExecState actZipper actBefore) (ZephyrTyCheckCheckSymbol loc symVar) =
    inNestedLocation loc $
    do afterStk <- stackVarT <$> newTyVar
       assertTyVarUnifies' symVar (ZephyrQuoteT (ZephyrEffect actZipper actBefore afterStk))
       pure (ZephyrExecState actZipper afterStk)

assertState :: ZephyrExecState ZephyrTyVar -> ZephyrExecState ZephyrTyVar -> ZephyrTyCheckM s (ZephyrExecState ZephyrTyVar)
assertState (ZephyrExecState actualZipper actualStack) (ZephyrExecState expZipper expStack) =
    ZephyrExecState <$> unifyZephyrT actualZipper expZipper
                    <*> unifyZephyrT actualStack expStack

unifyEffect :: ZephyrEffect ZephyrTyVar -> ZephyrEffect ZephyrTyVar -> ZephyrTyCheckM s (ZephyrEffect ZephyrTyVar)
unifyEffect (ZephyrEffect actZipper actBefore actAfter) (ZephyrEffect expZipper expBefore expAfter) =
    do zipper <- unifyZephyrT actZipper expZipper
       before <- unifyZephyrT actBefore expBefore
       after <- unifyZephyrT actAfter expAfter
       return (ZephyrEffect zipper before after)

unifyZipperField :: ZippyFieldType (RecZephyrType ZephyrTyVar) -> ZippyFieldType (RecZephyrType ZephyrTyVar) -> ZephyrTyCheckM s (ZippyFieldType (RecZephyrType ZephyrTyVar))
unifyZipperField (SimpleFieldT act) (SimpleFieldT exp)
    | act == exp = return (SimpleFieldT act)
    | otherwise = fail ("Cannot unify simple types " ++ ppSimpleT act ++ " and " ++ ppSimpleT exp)
unifyZipperField (RefFieldT (ZippyTyCon actName actArgs)) (RefFieldT (ZippyTyCon expName expArgs))
    | actName == expName = RefFieldT . ZippyTyCon actName <$> mapM (uncurry unifyZephyrT) (V.zip actArgs expArgs)
    | otherwise = fail ("Cannot match " ++ ppTyName actName ++ " with " ++ ppTyName expName)
unifyZipperField act exp =
    fail ("Cannot unify simple and composite types " ++ ppField act ++ " and " ++ ppField exp)

assertTyVarEquality :: IsKind k => ZephyrTyVar -> ZephyrTyVar -> ZephyrTyCheckM s (ZephyrT k ZephyrTyVar)
assertTyVarEquality act exp =
    increaseIndent $ \indent ->
    do actP <- trace (indent ("Unify vars " ++ ppTyVar act ++ " with " ++ ppTyVar exp)) (getPointForVariable act)
       expP <- getPointForVariable exp
       areEqual <- zephyrST (equivalent actP expP)
       newDesc <- if areEqual
                  then trace (indent "Done unify vars") (zephyrST (descriptor expP))
                  else do actDesc <- zephyrST (descriptor actP)
                          expDesc <- zephyrST (descriptor expP)
                          actExpNonRecursive <- isNonRecursive act expDesc
                          expActNonRecursive <- isNonRecursive exp actDesc
                          if actExpNonRecursive && expActNonRecursive
                            then do newDesc <- trace (indent ("Performing a unify between " ++ ppTyDesc (act, actDesc) ++ " and " ++ ppTyDesc (exp, expDesc))) (unifyTyDesc actDesc expDesc)
                                    zephyrST (union' actP expP (\_ _ -> pure newDesc))
                                    trace (indent "Done unify vars (unified)") $ pure newDesc
                            else if actExpNonRecursive
                                 then dieOnRecursiveType exp actDesc
                                 else dieOnRecursiveType act expDesc

       case newDesc of
         ZephyrTyDescFree _ var _ -> pure (ZephyrVarT var)
         ZephyrTyDesc ty _ -> case safeCoercedKind ty of
                                Nothing -> fail ("Kind mismatch during type var matching. had " ++ show (kindOf ty))
                                Just t -> pure t

andM :: (Foldable f, Monad m) => (a -> m Bool) -> f a -> m Bool
andM f x = foldlM doAnd True x
    where doAnd False _ = return False
          doAnd True x = f x

isFree _ (ZephyrTyDescFree _ _ _) = True
isFree v (ZephyrTyDesc (ZephyrVarT v') _)
    | trace ("Check free " ++ show v) (v == v') = True
isFree _ _ = False

isNonRecursive :: ZephyrTyVar -> ZephyrTyDesc -> ZephyrTyCheckM s Bool
isNonRecursive v x | trace ("isNonRecursive (" ++ ppTyDesc (v, x) ++ ")") False = undefined
isNonRecursive v x | isFree v x = return True
isNonRecursive v (ZephyrTyDesc s _) = andM (ensureNotVar v) s

ensureNotVar :: ZephyrTyVar -> ZephyrTyVar -> ZephyrTyCheckM s Bool
ensureNotVar v act = do vP <- getPointForVariable v
                        actP <- getPointForVariable act
                        areEqual <- zephyrST (equivalent vP actP)
                        if areEqual
                           then pure False
                           else do actTyDesc <- zephyrST (descriptor actP)
                                   if isFree act actTyDesc
                                      then pure True
                                      else isNonRecursive v actTyDesc

withResultKind :: IsKind k => (ZephyrKind -> ZephyrTyCheckM s (ZephyrT k ZephyrTyVar)) -> ZephyrTyCheckM s (ZephyrT k ZephyrTyVar)
withResultKind f = let res = f (getKind (proxy res))
                       proxy :: ZephyrTyCheckM s (ZephyrT k ZephyrTyVar) -> Proxy k
                       proxy _ =  Proxy
                   in res

assertTyVarUnifies' :: IsKind k => ZephyrTyVar -> ZephyrT k ZephyrTyVar -> ZephyrTyCheckM s (ZephyrT k ZephyrTyVar)
assertTyVarUnifies' tyVar expTy = assertTyVarUnifies tyVar (ZephyrTyDesc expTy mempty)

assertTyVarUnifies :: IsKind k => ZephyrTyVar -> ZephyrTyDesc -> ZephyrTyCheckM s (ZephyrT k ZephyrTyVar)
assertTyVarUnifies tyVar expTyDesc =
    withResultKind $ \kind ->
    increaseIndent $ \indent ->
    do tyVarP <- trace (indent ("Unify " ++ ppTyDesc (tyVar, expTyDesc))) (getPointForVariable tyVar)
       actTyDesc <- zephyrST (descriptor tyVarP)
       nonRecursive <- isNonRecursive tyVar expTyDesc
       if nonRecursive
          then do unifiedDesc <- unifyTyDesc actTyDesc expTyDesc
                  trace (indent "Done unifying") (zephyrST (setDescriptor tyVarP unifiedDesc))
                  case unifiedDesc of
                    ZephyrTyDesc t loc ->
                        case safeCoercedKind t of
                          Nothing -> dieTyCheck loc (ExpectingKind kind (kindOf t))
                          Just t -> pure t
                    ZephyrTyDescFree Nothing v _ -> pure (ZephyrVarT v)
                    ZephyrTyDescFree (Just k) v loc
                        | k == kind -> pure (ZephyrVarT v)
                        | otherwise -> dieTyCheck loc (ExpectingKind k kind)
          else dieOnRecursiveType tyVar expTyDesc

dieOnRecursiveType :: ZephyrTyVar -> ZephyrTyDesc -> ZephyrTyCheckM s a
dieOnRecursiveType tyVar tyDesc = do pt <- getPointForVariable tyVar
                                     tyDesc' <- simplifyTyDesc tyDesc
                                     dieTyCheck (descLoc tyDesc (InfinitelyRecursiveType tyVar tyDesc')

increaseIndent :: ((String -> String) -> ZephyrTyCheckM s a) -> ZephyrTyCheckM s a
increaseIndent a = do indentN <- gets unifyIndent
                      modify (\st -> st { unifyIndent = unifyIndent st + 2 })
                      r <- a ((replicate indentN ' ') ++)
                      modify (\st -> st { unifyIndent = unifyIndent st - 2 })
                      return r

unifyZephyrT :: IsKind k => ZephyrT k ZephyrTyVar -> ZephyrT k ZephyrTyVar -> ZephyrTyCheckM s (ZephyrT k ZephyrTyVar)
unifyZephyrT (ZephyrVarT actualVar) (ZephyrVarT expVar) = assertTyVarEquality actualVar expVar
unifyZephyrT (ZephyrVarT actualVar) exp = assertTyVarUnifies actualVar (ZephyrTyDesc exp mempty)
unifyZephyrT act (ZephyrVarT expVar) = assertTyVarUnifies expVar (ZephyrTyDesc act mempty)
unifyZephyrT (ZephyrZipperT act) (ZephyrZipperT exp) = ZephyrZipperT <$> unifyZipperField act exp
unifyZephyrT ZephyrStackBottomT (_ :> _) = dieTyCheck [] HitStackBottom
unifyZephyrT (_ :> _) ZephyrStackBottomT = dieTyCheck [] HitStackBottom
unifyZephyrT (actBelow :> actTop) (expBelow :> expTop) =
    sameKinded actTop expTop $ \case
      Just (actTop, expTop) ->
          do top <- unifyZephyrT actTop expTop
             below <- unifyZephyrT actBelow expBelow
             isStackAtomKind top $ \case
               Just top -> pure (below :> top)
               Nothing -> trace "die at stack atom coercion" (dieTyCheck [] (KindMismatch actTop expTop))
      Nothing -> trace "die at stack top coercion" ( dieTyCheck [] (KindMismatch actTop expTop))
unifyZephyrT (ZephyrQuoteT act) (ZephyrQuoteT exp) = ZephyrQuoteT <$> unifyEffect act exp
unifyZephyrT act exp = trace "Die at unify" (dieTyCheck [] (KindMismatch act exp))

unifyTyDesc :: ZephyrTyDesc -> ZephyrTyDesc -> ZephyrTyCheckM s ZephyrTyDesc
unifyTyDesc x y | trace ("unifyTyDesc (" ++ show x ++ ") (" ++ show y ++ ")") False = undefined
unifyTyDesc f@(ZephyrTyDescFree k _ _) x
    | descKindsMatch f x = pure x
    | otherwise = dieTyCheck [] (ExpectingKind (fromJust k) (fromJust $descKind x))
unifyTyDesc x f@(ZephyrTyDescFree k _ _)
    | descKindsMatch f x = pure x
    | otherwise = dieTyCheck [] (ExpectingKind (fromJust k) (fromJust $ descKind x))
unifyTyDesc (ZephyrTyDesc act actLoc) (ZephyrTyDesc exp expLoc) =
    sameKinded act exp $ \case
      Just (act, exp) -> do newTy <- unifyZephyrT act exp
                            return (ZephyrTyDesc newTy (actLoc <> expLoc))
      Nothing -> trace "Die at ty desc unify" (dieTyCheck (actLoc <> expLoc) (KindMismatch act exp))

mkTypedZephyrBuilder :: ZephyrTypeLookupEnv -> ZephyrSymbolEnv (ZephyrEffect ZephyrTyVar) -> ZephyrSymbolEnv ZephyrTyVar -> ZephyrBuilder -> ZephyrTyCheckM s [ZephyrTyCheckOp]
mkTypedZephyrBuilder types pretypedSymbols typedSymbols (ZephyrBuilder ops) = mapM (mkAtomType types pretypedSymbols typedSymbols) (D.toList ops)

mkAtomType :: ZephyrTypeLookupEnv -> ZephyrSymbolEnv (ZephyrEffect ZephyrTyVar) -> ZephyrSymbolEnv ZephyrTyVar -> ZephyrBuilderOp -> ZephyrTyCheckM s ZephyrTyCheckOp
mkAtomType types pretypedSymbols typedSymbols (ZephyrAtom a loc) = either (ZephyrTyCheckCheckEffect locAtom) (ZephyrTyCheckCheckSymbol locAtom) <$> atomType types pretypedSymbols typedSymbols a
    where locAtom = ZephyrTyErrorLocation (WhileCheckingAtom a . LocatedAt loc)
mkAtomType types _ _ (ZephyrStateAssertion s loc) = ZephyrTyCheckCheckState loc' <$> instantiateState (qualifyState types s)
    where loc' = ZephyrTyErrorLocation (WhileCheckingStateAssertion s . LocatedAt loc)

qualifyState :: ZephyrTypeLookupEnv -> ZephyrExecState v -> ZephyrExecState v
qualifyState types (ZephyrExecState zipper stack) = ZephyrExecState (qualifyZephyrT zipper) (qualifyZephyrT stack)
    where qualifyZephyrT :: ZephyrT k v -> ZephyrT k v
          qualifyZephyrT (ZephyrVarT v) = ZephyrVarT v
          qualifyZephyrT (ZephyrZipperT (SimpleFieldT s)) = ZephyrZipperT (SimpleFieldT s)
          qualifyZephyrT (ZephyrZipperT (RefFieldT (ZippyTyCon tyName tyArgs))) =
              ZephyrZipperT (RefFieldT (ZippyTyCon (qualifyTy tyName types) (fmap qualifyZephyrT tyArgs)))
          qualifyZephyrT (ZephyrQuoteT (ZephyrEffect zipper stack1 stack2)) = ZephyrQuoteT (ZephyrEffect (qualifyZephyrT zipper)
                                                                                                         (qualifyZephyrT stack1)
                                                                                                         (qualifyZephyrT stack2))
          qualifyZephyrT ZephyrStackBottomT = ZephyrStackBottomT
          qualifyZephyrT (stk :> atom) = qualifyZephyrT stk :> qualifyZephyrT atom

atomType :: ZephyrTypeLookupEnv -> ZephyrSymbolEnv (ZephyrEffect ZephyrTyVar) -> ZephyrSymbolEnv ZephyrTyVar -> GenericZephyrAtom ZephyrBuilder ZephyrWord -> ZephyrTyCheckM s (Either (ZephyrEffect ZephyrTyVar) ZephyrTyVar)
atomType _ _ _ (IntegerZ _) = Left <$> instantiate "z | *s -->  *s Integer"
atomType _ _ _ (TextZ _) = Left <$> instantiate "z | *s --> *s Text"
atomType _ _ _ (FloatingZ _) = Left <$> instantiate "z | *s --> *s Floating"
atomType _ _ _ (BinaryZ _) = Left <$> instantiate "z | *s --> *s Binary"
atomType types pretyped syms (QuoteZ q) = do typedQ <- mkTypedZephyrBuilder types pretyped syms q
                                             quoteEffect <- assertSymbol typedQ
                                             stk <- stackVarT <$> newTyVar
                                             zipper <- zipperVarT <$> newTyVar
                                             trace ("Find quote " ++ show q ++ " has type " ++ ppEffect quoteEffect) (pure (Left (ZephyrEffect zipper stk (stk :> ZephyrQuoteT quoteEffect))))
atomType _ pretyped syms (SymZ sym) = case lookupInSymbolEnv (Left sym) pretyped of
                                        Nothing -> case lookupInSymbolEnv (Left sym) syms of
                                                     Nothing -> error ("Could not resolve symbol " ++ show sym ++ "\n" ++ show pretyped ++ "\n" ++ show syms)
                                                     Just v -> pure (Right v)
                                        Just eff -> trace ("Looked up " ++ show sym ++ ": has effect " ++ ppEffect eff) (pure (Left eff))
atomType _ _ _ ZipUpZ = error "ZipUpZ is un-typable"
atomType _ _ _ ZipDownZ = error "Cannot handle ZipDownZ yet"
atomType _ _ _ ZipReplaceZ = Left <$> instantiate "focus | *s focus -->  *s"
atomType _ _ _ CurAtomZ = Left <$> instantiate "focus | *s --> *s focus"
atomType _ _ _ CurTagZ = Left <$> instantiate "focus | *s --> *s Integer"
atomType _ _ _ ArgHoleZ = Left <$> instantiate "z | *s --> *s Integer"
atomType _ _ _ EnterZipperZ = Left <$> instantiate "z | *s z' (z' | *s --> *s') --> *s' z'"
atomType _ _ _ CutZ = Left <$> instantiate "z | *s --> *s z"
atomType _ _ _ DipZ = Left <$> instantiate "z | *s t (z | *s --> *s') -->  *s' t"
atomType _ _ _ ZapZ = Left <$> instantiate "z | *s t --> *s"
atomType _ _ _ DupZ = Left <$> instantiate "z | *s t --> *s t t"
atomType _ _ _ SwapZ = Left <$> instantiate "z | *s a b --> *s b a"
atomType _ _ _ DeQuoteZ = Left <$> instantiate "z | *s (z | *s --> *t) --> *t"
atomType _ _ _ IfThenElseZ = Left <$> instantiate "z | *s (z | *s --> *s' base:Bool) (z | *s' --> *s'') (z | *s' --> *s'') --> *s''"
atomType _ _ _ PlusZ = Left <$> instantiate "z | *s Integer Integer --> *s Integer"
atomType _ _ _ EqZ = Left <$> instantiate "z | *s a a --> *s base:Bool"
atomType _ _ _ LtZ = Left <$> instantiate "z | *s a a --> *s base:Bool"
atomType _ _ _ GtZ = Left <$> instantiate "z | *s a a --> *s base:Bool"
atomType _ _ _ op = fail ("No clue how to handle op " ++ show op)

newTyVar :: ZephyrTyCheckM s ZephyrTyVar
newTyVar = gets nextVar >>= zephyrST

ppTyVar :: ZephyrTyVar -> String
ppTyVar (ZephyrTyVar i) = 'v':show i

ppTyCheckOp :: ZephyrTyCheckOp -> String
ppTyCheckOp (ZephyrTyCheckCheckState _ st) = "Check state: " ++ ppState st
ppTyCheckOp (ZephyrTyCheckCheckEffect _ eff) = "Check effect: " ++ ppEffect eff

ppState :: ZephyrExecState ZephyrTyVar -> String
ppState (ZephyrExecState zipper stk) = concat [ ppZephyrTy zipper
                                              , ppZephyrTy stk ]
ppEffect :: ZephyrEffect ZephyrTyVar -> String
ppEffect (ZephyrEffect zipper before after) = concat [ ppZephyrTy zipper, " | "
                                                     , ppZephyrTy before, " --> "
                                                     , ppZephyrTy after ]

ppSimpleT :: ZippySimpleT -> String
ppSimpleT IntegerT = "Integer"
ppSimpleT FloatingT = "Floating"
ppSimpleT TextT = "Text"
ppSimpleT BinaryT = "Binary"

ppField :: ZippyFieldType (RecZephyrType ZephyrTyVar) -> String
ppField (SimpleFieldT s) = ppSimpleT s
ppField (RefFieldT r) = ppRecZephyrTy r

ppRecZephyrTy :: RecZephyrType ZephyrTyVar -> String
ppRecZephyrTy (ZippyTyCon tyName args)
    | V.null args = ppTyName tyName
    | otherwise = concat [ "(", ppTyName tyName, " " ] ++
                  intercalate " " (map ppZephyrTy (V.toList args)) ++
                  ")"

ppZephyrTy :: IsKind k => ZephyrT k ZephyrTyVar -> String
ppZephyrTy z@(ZephyrVarT v) = case kindOf z of
                                ZephyrStackK -> "*" <> ppTyVar v
                                _ -> ppTyVar v
ppZephyrTy (ZephyrZipperT z) = ppField z
ppZephyrTy (ZephyrQuoteT eff) = concat ["(", ppEffect eff, ")"]
ppZephyrTy ZephyrStackBottomT = "0"
ppZephyrTy (stk :> top) = concat [ppZephyrTy stk, " ", ppZephyrTy top]

ppTyName :: ZippyTyName -> String
ppTyName (ZippyTyName mod name) = concat [T.unpack mod, ":", T.unpack name]

ppTyDesc (tyVar, desc) = ppTyVar tyVar ++ ": " ++ ppDesc desc
    where ppDesc (ZephyrTyDesc ty locs) = ppZephyrTy ty
          ppDesc (ZephyrTyDescFree _ var _) = "FREE (" ++ ppTyVar var ++ ")"

instantiate :: ZephyrEffectWithNamedVars -> ZephyrTyCheckM s (ZephyrEffect ZephyrTyVar)
instantiate (ZephyrEffectWithNamedVars eff) =
    do let tyVars = allTyVariables eff
       instantiatedVars <- HM.fromList <$> mapM (\tyVar -> (tyVar,) <$> newTyVar) tyVars
       return (fmap (fromJust . flip HM.lookup instantiatedVars) eff)

instantiateState :: ZephyrExecState ZippyTyVarName -> ZephyrTyCheckM s (ZephyrExecState ZephyrTyVar)
instantiateState st =
    do let tyVars = allTyVariables st
       instantiatedVars <- HM.fromList <$> mapM (\tyVar -> (tyVar,) <$> newTyVar) tyVars
       return (fmap (fromJust . flip HM.lookup instantiatedVars) st)
