{-# LANGUAGE RecordWildCards, TupleSections, RankNTypes, OverloadedStrings, MultiParamTypeClasses #-}
module Database.Zippy.Zephyr.TyCheck where

import Database.Zippy.Zephyr.Types
import Database.Zippy.Zephyr.Parse
import Database.Zippy.Zephyr.Internal
import Database.Zippy.Types

import Prelude hiding (mapM)

import Control.Applicative
import Control.Monad.ST
import Control.Monad.State hiding (mapM)

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

                          , unifyIndent :: Int}

newtype ZephyrTyErrorLocation = ZephyrTyErrorLocation (ZephyrTyCheckLocation -> ZephyrTyCheckLocation)

instance Monoid ZephyrTyErrorLocation where
    mempty = ZephyrTyErrorLocation id
    mappend (ZephyrTyErrorLocation a) (ZephyrTyErrorLocation b) = ZephyrTyErrorLocation $ a . b

instance Show ZephyrTyErrorLocation where
    show (ZephyrTyErrorLocation loc) = show (loc Here)

data ZephyrTyDesc = ZephyrTyDescStack (ZephyrStackTy ZephyrTyVar) [ZephyrTyCheckLocation]
                  | ZephyrTyDescZipper (ZephyrZipperTy ZephyrTyVar) [ZephyrTyCheckLocation]
                  | ZephyrTyDescStackAtom (ZephyrStackAtomTy ZephyrTyVar) [ZephyrTyCheckLocation]
                  | ZephyrTyDescFree ZephyrTyVar [ZephyrTyCheckLocation]
                    deriving Show

data ZephyrTyCheckOp = ZephyrTyCheckCheckState !(ZephyrExecState ZephyrTyVar)
                     | ZephyrTyCheckCheckEffect !(ZephyrEffect ZephyrTyVar)
                     | ZephyrTyCheckCheckSymbol !ZephyrTyVar
                       deriving Show

data ZephyrTyCheckError = InfinitelyRecursiveType !ZephyrTyVar !ZephyrTyDesc
                        | KindMismatch !ZephyrTyDesc !ZephyrTyDesc
                        | InvalidDemotion !(ZephyrStackAtomTy ZephyrTyVar) -- ^ Cannot demote stack atom to zipper atom
                        | CannotUnify !ZephyrTyDesc {- actual -} !ZephyrTyDesc {- expected -}
                        | HitStackBottom
                        | UncheckableOp

                        | GenericFail !String
                          deriving Show
data ZephyrTyCheckLocation = LocatedAt !SourceRange !ZephyrTyCheckLocation
                           | Here
                             deriving Show

newtype ZephyrTyCheckM s a = ZephyrTyCheckM { runZephyrTyCheckM :: ZephyrTyCheckState s -> ST s (Either ([ZephyrTyCheckLocation], ZephyrTyCheckError) a, ZephyrTyCheckState s) }
-- type ZephyrTyCheckM s = StateT (ZephyrTyCheckState s) (ST s)

instance Monad (ZephyrTyCheckM s) where
    return = pure
    a >>= b = ZephyrTyCheckM $ \s -> do (x, s') <- runZephyrTyCheckM a s
                                        case x of
                                          Left err -> pure (Left err, s')
                                          Right x  -> runZephyrTyCheckM (b x) s'
    fail x = dieTyCheck [] (GenericFail x)

instance Functor (ZephyrTyCheckM s) where
    fmap f a = pure . f =<< a

instance Applicative (ZephyrTyCheckM s) where
    pure x = ZephyrTyCheckM $ \s -> pure (Right x, s)
    f <*> x = do f' <- f
                 x' <- x
                 pure (f' x')

instance MonadState (ZephyrTyCheckState s) (ZephyrTyCheckM s) where
    get = ZephyrTyCheckM $ \s -> pure (Right s, s)
    put s = ZephyrTyCheckM $ \_ -> pure (Right (), s)

tyDescLoc :: ZephyrTyDesc -> [ZephyrTyCheckLocation]
tyDescLoc (ZephyrTyDescFree _ loc) = loc
tyDescLoc (ZephyrTyDescStack _ loc) = loc
tyDescLoc (ZephyrTyDescStackAtom _ loc) = loc
tyDescLoc (ZephyrTyDescZipper _ loc) = loc

dieTyCheck :: [ZephyrTyCheckLocation] -> ZephyrTyCheckError -> ZephyrTyCheckM s a
dieTyCheck otherLocs err = ZephyrTyCheckM $ \s -> pure (Left (otherLocs, err), s)

catchTyCheck :: ZephyrTyCheckM s a -> (ZephyrTyCheckError -> ZephyrTyCheckM s a) -> ZephyrTyCheckM s a
catchTyCheck action onExc =
    ZephyrTyCheckM $ \s ->
    do (res, s') <- runZephyrTyCheckM action s
       case res of
         Left (locs, err) -> do (res', s'') <- runZephyrTyCheckM (onExc err) s'
                                case res' of
                                  Left (locs', err') -> pure (Left (locs ++ locs', err'), s'')
                                  Right res -> pure (Right res, s'')
         Right res -> pure (Right res, s')

zephyrST :: ST s a -> ZephyrTyCheckM s a
zephyrST action = ZephyrTyCheckM $ \s ->
                  do res <- action
                     pure (Right res, s)

certifyPackage :: ZephyrPackage -> ZephyrTyCheckedPackage
certifyPackage pkg = fmap unwrapBuilder pkg
    where unwrapBuilder (ZephyrBuilder ops) = ZephyrTyChecked [mapQuote unwrapBuilder atom | ZephyrAtom atom _ <- D.toList ops]

runInNewTyCheckM :: (forall s. ZephyrTyCheckM s x) -> Either ([ZephyrTyCheckLocation], ZephyrTyCheckError) x
runInNewTyCheckM f = runST $
                     do st <- newTyCheckState
                        (res, _) <- runZephyrTyCheckM f st
                        return res

-- simpleTyCheckPackages :: ZephyrTypeLookupEnv -> [ZephyrPackage] -> [ZephyrTyCheckedPackage]
-- simpleTyCheckPackages types pkgs = runST (newTyCheckState >>= evalStateT (tyCheckPackages types pkgs))

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
                    do newPoint <- fresh (ZephyrTyDescFree tyVar mempty)
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
simplifyTyDesc (ZephyrTyDescFree v loc) = pure (ZephyrTyDescFree v loc)
simplifyTyDesc (ZephyrTyDescZipper z loc) = ZephyrTyDescZipper <$> simplifyZipper z <*> pure loc
simplifyTyDesc (ZephyrTyDescStack s loc) = ZephyrTyDescStack <$> simplifyStkState s <*> pure loc
simplifyTyDesc (ZephyrTyDescStackAtom s loc) = ZephyrTyDescStackAtom <$> simplifyStackAtom s <*> pure loc

simplifyEffect :: TyCheckEndoM s (ZephyrEffect ZephyrTyVar)
simplifyEffect eff@(ZephyrEffect zipper before after) = trace ("Simplify effect " ++ show eff) (ZephyrEffect <$> simplifyZipper zipper <*> simplifyStkState before <*> simplifyStkState after)

simplifyStkState :: TyCheckEndoM s (ZephyrStackTy ZephyrTyVar)
simplifyStkState StackBottom = pure StackBottom
simplifyStkState k@(st :> stackTy) = trace ("Simplify stack " ++ show k) ((:>) <$> simplifyStkState st
                                                                               <*> simplifyStackAtom stackTy)
simplifyStkState (StackVar tyVar) =
    do tyDesc <- zephyrST . descriptor =<< getPointForVariable tyVar
       case tyDesc of
         ZephyrTyDescFree tyVar _ -> pure (StackVar tyVar)
         ZephyrTyDescStack s _ -> case s of
                                    StackVar sVar
                                        | sVar == tyVar -> pure (StackVar sVar)
                                    _ -> simplifyStkState s
         tyDesc -> dieTyCheck [] (GenericFail "Kind mismatch during simplification")

simplifyStackAtom :: TyCheckEndoM s (ZephyrStackAtomTy ZephyrTyVar)
simplifyStackAtom (StackAtomQuote eff) = StackAtomQuote <$> trace ("Simplify atom " ++ show eff) (simplifyEffect eff)
simplifyStackAtom (StackAtomZipper zip) = StackAtomZipper <$> simplifyZipper zip
simplifyStackAtom (StackAtomVar tyVar) =
    do tyDesc <- zephyrST . descriptor =<< getPointForVariable tyVar
       case tyDesc of
         ZephyrTyDescFree tyVar _ -> pure (StackAtomVar tyVar)
         ZephyrTyDescStackAtom s _ -> case s of
                                       StackAtomVar sVar
                                           | sVar == tyVar -> pure (StackAtomVar sVar)
                                       _ -> trace ("Simplifying stack atom " ++ show s ++ " from " ++ show tyVar) (simplifyStackAtom s)
         ZephyrTyDescZipper z _ -> simplifyStackAtom (StackAtomZipper z)
         _ -> fail "Kind mismatch during simplification (stack atom)"
simplifyStackAtom x = pure x

simplifyZipper :: TyCheckEndoM s (ZephyrZipperTy ZephyrTyVar)
simplifyZipper (ZipperConcrete (SimpleFieldT s)) = pure (ZipperConcrete (SimpleFieldT s))
simplifyZipper (ZipperConcrete (RefFieldT r)) = ZipperConcrete . RefFieldT <$> simplifyZipperTyCon r
simplifyZipper (ZipperVar tyVar) =
    do tyDesc <- zephyrST . descriptor =<< getPointForVariable tyVar
       case tyDesc of
         ZephyrTyDescFree tyVar _ -> pure (ZipperVar tyVar)
         ZephyrTyDescZipper s _ -> case s of
                                    ZipperVar sVar
                                        | sVar == tyVar -> pure (ZipperVar sVar)
                                    _ -> simplifyZipper s
         ZephyrTyDescStackAtom stkAtom _ -> simplifyZipper =<< demoteStackAtom stkAtom
         _ -> fail "Kind mismatch during simplification (zip atom)"

simplifyZipperTyCon :: TyCheckEndoM s (GenericZippyTyCon (ZephyrZipperTy ZephyrTyVar))
simplifyZipperTyCon (ZippyTyCon tyName tyArgs) =
    ZippyTyCon tyName <$> mapM simplifyZipper tyArgs

unifySymbols :: ZephyrSymbolEnv ZephyrTyVar -> [GenericZephyrPackage (ZephyrEffect ZephyrTyVar)] -> ZephyrTyCheckM s ()
unifySymbols env typedPackages =
    mapM (\pkg -> mapM (unifyPkgSymbol (zephyrPackageName pkg)) (zephyrSymbols pkg)) typedPackages >> return ()
    where unifyPkgSymbol pkgName (ZephyrSymbolDefinition sym eff) =
              let Just tyVar = lookupInSymbolEnv (Right (pkgName, sym)) env
              in assertTyVarUnifies tyVar (ZephyrTyDescStackAtom (StackAtomQuote eff) mempty)

assertSymbol :: [ZephyrTyCheckOp] -> ZephyrTyCheckM s (ZephyrEffect ZephyrTyVar)
assertSymbol typedOps = do initialZipper <- newTyVar
                           initialStack <- newTyVar

                           assertTyVarUnifies initialZipper =<< ZephyrTyDescZipper <$> (ZipperVar <$> newTyVar) <*> pure mempty
                           assertTyVarUnifies initialStack =<< ZephyrTyDescStack <$> (StackVar <$> newTyVar) <*> pure mempty

                           let initialState = ZephyrExecState zipper initialStackVar
                               zipper = ZipperVar initialZipper
                               initialStackVar = StackVar initialStack
                           ZephyrExecState _ finalStack <- foldlM assertTyCheckOp initialState typedOps
                           return (ZephyrEffect zipper initialStackVar finalStack)

assertTyCheckOp :: ZephyrExecState ZephyrTyVar -> ZephyrTyCheckOp -> ZephyrTyCheckM s (ZephyrExecState ZephyrTyVar)
assertTyCheckOp actNow (ZephyrTyCheckCheckState expNow) =
    do assertState actNow expNow
       pure expNow
assertTyCheckOp (ZephyrExecState actZipper actBefore) (ZephyrTyCheckCheckEffect (ZephyrEffect expZipper expBefore after)) =
    do assertState (ZephyrExecState actZipper actBefore) (ZephyrExecState expZipper expBefore)
       pure (ZephyrExecState expZipper after)
assertTyCheckOp (ZephyrExecState actZipper actBefore) (ZephyrTyCheckCheckSymbol symVar) =
    do afterStk <- StackVar <$> newTyVar
       assertTyVarUnifies symVar (ZephyrTyDescStackAtom (StackAtomQuote (ZephyrEffect actZipper actBefore afterStk)) mempty)
       pure (ZephyrExecState actZipper afterStk)

assertState :: ZephyrExecState ZephyrTyVar -> ZephyrExecState ZephyrTyVar -> ZephyrTyCheckM s (ZephyrExecState ZephyrTyVar)
assertState (ZephyrExecState actualZipper actualStack) (ZephyrExecState expZipper expStack) =
    ZephyrExecState <$> unifyZipperTy actualZipper expZipper
                    <*> unifyStackTy actualStack expStack

assertIsStack :: ZephyrTyVar -> ZephyrTyDesc -> ZephyrTyCheckM s (ZephyrStackTy ZephyrTyVar)
assertIsStack _ (ZephyrTyDescStack s _) = pure s
assertIsStack _ (ZephyrTyDescFree tyVar _) = pure (StackVar tyVar)
assertIsStack _ _ = fail "Kind mismatch... Expected stack"

assertIsStackAtom :: ZephyrTyVar -> ZephyrTyDesc -> ZephyrTyCheckM s (ZephyrStackAtomTy ZephyrTyVar)
assertIsStackAtom _ (ZephyrTyDescStackAtom s _) = pure s
assertIsStackAtom _ (ZephyrTyDescZipper z _) = pure (StackAtomZipper z)
assertIsStackAtom _ (ZephyrTyDescFree tyVar _) = pure (StackAtomVar tyVar)
assertIsStackAtom tyVar (ZephyrTyDescStack stk loc) = do top <- newTyVar
                                                         below <- newTyVar
                                                         assertTyVarUnifies tyVar (ZephyrTyDescStack (StackVar below :> StackAtomVar top) mempty)
                                                         return (StackAtomVar top)

assertIsZipper (ZephyrTyDescZipper s _) = pure s
                                            -- TODO This should break open a zipper variable
assertIsZipper (ZephyrTyDescStackAtom s _) = demoteStackAtom s
assertIsZipper (ZephyrTyDescFree tyVar _) = pure (ZipperVar tyVar)
assertIsZipper x = fail ("Kind mismatch... Expected zipper atom. Got " ++ show x)

demoteStackAtom :: ZephyrStackAtomTy ZephyrTyVar -> ZephyrTyCheckM s (ZephyrZipperTy ZephyrTyVar)
demoteStackAtom (StackAtomSimple s) = pure (ZipperConcrete (SimpleFieldT s))
demoteStackAtom (StackAtomVar v) = pure (ZipperVar v)
demoteStackAtom x = dieTyCheck [] (InvalidDemotion x)

unifyEffect :: ZephyrEffect ZephyrTyVar -> ZephyrEffect ZephyrTyVar -> ZephyrTyCheckM s (ZephyrEffect ZephyrTyVar)
unifyEffect (ZephyrEffect actZipper actBefore actAfter) (ZephyrEffect expZipper expBefore expAfter) =
    do zipper <- unifyZipperTy actZipper expZipper
       before <- unifyStackTy actBefore expBefore
       after <- unifyStackTy actAfter expAfter
       return (ZephyrEffect zipper before after)

unifyZipperTy :: ZephyrZipperTy ZephyrTyVar -> ZephyrZipperTy ZephyrTyVar -> ZephyrTyCheckM s (ZephyrZipperTy ZephyrTyVar)
unifyZipperTy (ZipperVar actualVar) (ZipperVar expVar) =
    assertTyVarEquality actualVar expVar >>=
    assertIsZipper
unifyZipperTy (ZipperVar actualVar) exp =
    assertTyVarUnifies actualVar (ZephyrTyDescZipper exp mempty) >>=
    assertIsZipper
unifyZipperTy act (ZipperVar expVar) =
    assertTyVarUnifies expVar (ZephyrTyDescZipper act mempty) >>=
    assertIsZipper
unifyZipperTy (ZipperConcrete act) (ZipperConcrete exp) =
    ZipperConcrete <$> unifyZipperField act exp

unifyZipperField :: ZippyFieldType (RecZephyrType ZephyrTyVar) -> ZippyFieldType (RecZephyrType ZephyrTyVar) -> ZephyrTyCheckM s (ZippyFieldType (RecZephyrType ZephyrTyVar))
unifyZipperField (SimpleFieldT act) (SimpleFieldT exp)
    | act == exp = return (SimpleFieldT act)
    | otherwise = fail ("Cannot unify simple types " ++ ppSimpleT act ++ " and " ++ ppSimpleT exp)
unifyZipperField (RefFieldT (ZippyTyCon actName actArgs)) (RefFieldT (ZippyTyCon expName expArgs))
    | actName == expName = RefFieldT . ZippyTyCon actName <$> mapM (uncurry unifyZipperTy) (V.zip actArgs expArgs)
    | otherwise = fail ("Cannot match " ++ ppTyName actName ++ " with " ++ ppTyName expName)
unifyZipperField act exp =
    fail ("Cannot unify simple and composite types " ++ ppField act ++ " and " ++ ppField exp)

unifyStackTy :: ZephyrStackTy ZephyrTyVar -> ZephyrStackTy ZephyrTyVar -> ZephyrTyCheckM s (ZephyrStackTy ZephyrTyVar)
unifyStackTy (StackVar actualVar) (StackVar expVar) = assertTyVarEquality actualVar expVar >>=
                                                      assertIsStack expVar
unifyStackTy (StackVar actualVar) exp = assertTyVarUnifies actualVar (ZephyrTyDescStack exp mempty) >>=
                                        assertIsStack actualVar
unifyStackTy act (StackVar expectedVar) = assertTyVarUnifies expectedVar (ZephyrTyDescStack act mempty) >>=
                                               assertIsStack expectedVar
unifyStackTy StackBottom (_ :> _) = fail "Hit stack bottom while typechecking"
unifyStackTy (_ :> _) StackBottom = fail "Hit stack bottom while typechecking"
unifyStackTy (actBelow :> actTop) (expBelow :> expTop) = do top <- unifyStackAtomTy actTop expTop
                                                            below <- unifyStackTy actBelow expBelow
                                                            return (below :> top)

unifyStackAtomTy :: ZephyrStackAtomTy ZephyrTyVar -> ZephyrStackAtomTy ZephyrTyVar -> ZephyrTyCheckM s (ZephyrStackAtomTy ZephyrTyVar)
unifyStackAtomTy (StackAtomVar actualVar) (StackAtomVar expVar) = assertTyVarEquality actualVar expVar >>=
                                                                  assertIsStackAtom expVar
unifyStackAtomTy (StackAtomVar actualVar) exp = assertTyVarUnifies actualVar (ZephyrTyDescStackAtom exp mempty) >>=
                                                 assertIsStackAtom actualVar
unifyStackAtomTy actual (StackAtomVar expVar) = assertTyVarUnifies expVar (ZephyrTyDescStackAtom actual mempty) >>=
                                                 assertIsStackAtom expVar
unifyStackAtomTy (StackAtomQuote actualEff) (StackAtomQuote expEff) = StackAtomQuote <$> unifyEffect actualEff expEff
unifyStackAtomTy (StackAtomZipper actualZipper) (StackAtomZipper expZipper) = StackAtomZipper <$> unifyZipperTy actualZipper expZipper
unifyStackAtomTy a b
    | a == b = return a
    | otherwise = fail ("Cannot unify stack types " ++ ppStackAtomTy a ++ " and " ++ ppStackAtomTy b)

assertTyVarEquality :: ZephyrTyVar -> ZephyrTyVar -> ZephyrTyCheckM s ZephyrTyDesc
assertTyVarEquality act exp =
    increaseIndent $ \indent ->
    do actP <- trace (indent ("Unify vars " ++ ppTyVar act ++ " with " ++ ppTyVar exp)) (getPointForVariable act)
       expP <- getPointForVariable exp
       areEqual <- zephyrST (equivalent actP expP)
       if areEqual
         then trace (indent "Done unify vars") (zephyrST (descriptor expP))
         else do actDesc <- zephyrST (descriptor actP)
                 expDesc <- zephyrST (descriptor expP)
                 actExpNonRecursive <- isNonRecursive act expDesc
                 expActNonRecursive <- isNonRecursive exp actDesc
                 if actExpNonRecursive && expActNonRecursive
                    then do newDesc <- trace (indent ("Performing a unify between " ++ ppTyDesc (act, actDesc) ++ " and " ++ ppTyDesc (exp, expDesc))) (unifyTyDesc actDesc expDesc)
                            zephyrST (union' actP expP (\_ _ -> pure newDesc))
                            trace (indent "Done unify vars (unified)") (pure newDesc)
                    else if actExpNonRecursive
                            then dieOnRecursiveType exp actDesc
                            else dieOnRecursiveType act expDesc

andM :: (Foldable f, Monad m) => (a -> m Bool) -> f a -> m Bool
andM f x = foldlM doAnd True x
    where doAnd False _ = return False
          doAnd True x = f x

isFree _ (ZephyrTyDescFree _ _) = True
isFree v (ZephyrTyDescStack (StackVar sv) _) | v == sv = True
isFree v (ZephyrTyDescZipper (ZipperVar zv) _) | v == zv = True
isFree v (ZephyrTyDescStackAtom (StackAtomVar sav) _) | v == sav = True
isFree _ _ = False

isNonRecursive :: ZephyrTyVar -> ZephyrTyDesc -> ZephyrTyCheckM s Bool
isNonRecursive v x | trace ("isNonRecursive (" ++ ppTyDesc (v, x) ++ ")") False = undefined
isNonRecursive v x | isFree v x = return True
isNonRecursive v (ZephyrTyDescStack s _) = andM (ensureNotVar v) s
isNonRecursive v (ZephyrTyDescZipper z _) = andM (ensureNotVar v) z
isNonRecursive v (ZephyrTyDescStackAtom a _) = andM (ensureNotVar v) a

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

assertTyVarUnifies :: ZephyrTyVar -> ZephyrTyDesc -> ZephyrTyCheckM s ZephyrTyDesc
assertTyVarUnifies tyVar expTyDesc =
    increaseIndent $ \indent ->
    do tyVarP <- trace (indent ("Unify " ++ ppTyDesc (tyVar, expTyDesc))) (getPointForVariable tyVar)
       actTyDesc <- zephyrST (descriptor tyVarP)
       nonRecursive <- isNonRecursive tyVar expTyDesc
       if nonRecursive
          then do unifiedDesc <- unifyTyDesc actTyDesc expTyDesc
                  trace (indent "Done unifying") (zephyrST (setDescriptor tyVarP unifiedDesc))
                  return unifiedDesc
          else dieOnRecursiveType tyVar expTyDesc

dieOnRecursiveType :: ZephyrTyVar -> ZephyrTyDesc -> ZephyrTyCheckM s a
dieOnRecursiveType tyVar tyDesc = do pt <- getPointForVariable tyVar
                                     tyDesc' <- simplifyTyDesc tyDesc
                                     fail ("Cannot construct recursive type " ++ ppTyDesc (tyVar, tyDesc'))

increaseIndent :: ((String -> String) -> ZephyrTyCheckM s a) -> ZephyrTyCheckM s a
increaseIndent a = do indentN <- gets unifyIndent
                      modify (\st -> st { unifyIndent = unifyIndent st + 2 })
                      r <- a ((replicate indentN ' ') ++)
                      modify (\st -> st { unifyIndent = unifyIndent st - 2 })
                      return r

unifyTyDesc :: ZephyrTyDesc -> ZephyrTyDesc -> ZephyrTyCheckM s ZephyrTyDesc
unifyTyDesc x y | trace ("unifyTyDesc (" ++ show x ++ ") (" ++ show y ++ ")") False = undefined
unifyTyDesc (ZephyrTyDescFree _ _) x = pure x
unifyTyDesc x (ZephyrTyDescFree _ _) = pure x
unifyTyDesc (ZephyrTyDescZipper actZip actLoc) (ZephyrTyDescZipper expZip expLoc) =
    ZephyrTyDescZipper <$> unifyZipperTy actZip expZip <*> pure (actLoc ++ expLoc)
unifyTyDesc (ZephyrTyDescStackAtom (StackAtomZipper actZip) actLoc) (ZephyrTyDescZipper expZip expLoc) =
    ZephyrTyDescZipper <$> unifyZipperTy actZip expZip <*> pure (actLoc ++ expLoc)
unifyTyDesc (ZephyrTyDescZipper actZip actLoc) (ZephyrTyDescStackAtom (StackAtomZipper expZip) expLoc) =
    ZephyrTyDescZipper <$> unifyZipperTy actZip expZip <*> pure (actLoc ++ expLoc)
unifyTyDesc (ZephyrTyDescStack actStk actLoc) (ZephyrTyDescStack expStk expLoc) =
    ZephyrTyDescStack <$> unifyStackTy actStk expStk <*> pure (actLoc ++ expLoc)
unifyTyDesc (ZephyrTyDescStackAtom actStk actLoc) (ZephyrTyDescStackAtom expStk expLoc) =
    ZephyrTyDescStackAtom <$> unifyStackAtomTy actStk expStk <*> pure (actLoc ++ expLoc)
unifyTyDesc act exp = dieTyCheck [] (KindMismatch act exp)

mkTypedZephyrBuilder :: ZephyrTypeLookupEnv -> ZephyrSymbolEnv (ZephyrEffect ZephyrTyVar) -> ZephyrSymbolEnv ZephyrTyVar -> ZephyrBuilder -> ZephyrTyCheckM s [ZephyrTyCheckOp]
mkTypedZephyrBuilder types pretypedSymbols typedSymbols (ZephyrBuilder ops) = mapM (mkAtomType types pretypedSymbols typedSymbols) (D.toList ops)

mkAtomType :: ZephyrTypeLookupEnv -> ZephyrSymbolEnv (ZephyrEffect ZephyrTyVar) -> ZephyrSymbolEnv ZephyrTyVar -> ZephyrBuilderOp -> ZephyrTyCheckM s ZephyrTyCheckOp
mkAtomType types pretypedSymbols typedSymbols (ZephyrAtom a _) = either ZephyrTyCheckCheckEffect ZephyrTyCheckCheckSymbol <$> atomType types pretypedSymbols typedSymbols a
mkAtomType types _ _ (ZephyrStateAssertion s _) = ZephyrTyCheckCheckState <$> instantiateState (qualifyState types s)

qualifyState :: ZephyrTypeLookupEnv -> ZephyrExecState v -> ZephyrExecState v
qualifyState types (ZephyrExecState zipper stack) = ZephyrExecState (qualifyZipper zipper) (qualifyStack stack)
    where qualifyZipper (ZipperVar v) = ZipperVar v
          qualifyZipper (ZipperConcrete (SimpleFieldT s)) = ZipperConcrete (SimpleFieldT s)
          qualifyZipper (ZipperConcrete (RefFieldT (ZippyTyCon tyName tyArgs))) =
              ZipperConcrete (RefFieldT (ZippyTyCon (qualifyTy tyName types) (fmap qualifyZipper tyArgs)))

          qualifyStack StackBottom = StackBottom
          qualifyStack (StackVar tyVar) = StackVar tyVar
          qualifyStack (stk :> atom) = qualifyStack stk :> qualifyStackAtom atom

          qualifyStackAtom (StackAtomSimple s) = StackAtomSimple s
          qualifyStackAtom (StackAtomQuote eff) = StackAtomQuote (qualifyEffect eff)
          qualifyStackAtom (StackAtomVar v) = StackAtomVar v
          qualifyStackAtom (StackAtomZipper z) = StackAtomZipper (qualifyZipper z)

          qualifyEffect (ZephyrEffect zipper stack1 stack2) = ZephyrEffect (qualifyZipper zipper) (qualifyStack stack1) (qualifyStack stack2)

atomType :: ZephyrTypeLookupEnv -> ZephyrSymbolEnv (ZephyrEffect ZephyrTyVar) -> ZephyrSymbolEnv ZephyrTyVar -> GenericZephyrAtom ZephyrBuilder ZephyrWord -> ZephyrTyCheckM s (Either (ZephyrEffect ZephyrTyVar) ZephyrTyVar)
atomType _ _ _ (IntegerZ _) = Left <$> instantiate "z | *s -->  *s Integer"
atomType _ _ _ (TextZ _) = Left <$> instantiate "z | *s --> *s Text"
atomType _ _ _ (FloatingZ _) = Left <$> instantiate "z | *s --> *s Floating"
atomType _ _ _ (BinaryZ _) = Left <$> instantiate "z | *s --> *s Binary"
atomType types pretyped syms (QuoteZ q) = do typedQ <- mkTypedZephyrBuilder types pretyped syms q
                                             quoteEffect <- assertSymbol typedQ
                                             stk <- StackVar <$> newTyVar
                                             zipper <- ZipperVar <$> newTyVar
                                             trace ("Find quote " ++ show q ++ " has type " ++ ppEffect quoteEffect) (pure (Left (ZephyrEffect zipper stk (stk :> StackAtomQuote quoteEffect))))
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
ppTyCheckOp (ZephyrTyCheckCheckState st) = "Check state: " ++ ppState st
ppTyCheckOp (ZephyrTyCheckCheckEffect eff) = "Check effect: " ++ ppEffect eff

ppState :: ZephyrExecState ZephyrTyVar -> String
ppState (ZephyrExecState zipper stk) = concat [ ppZipperTy zipper
                                              , ppStackTy stk ]
ppEffect :: ZephyrEffect ZephyrTyVar -> String
ppEffect (ZephyrEffect zipper before after) = concat [ ppZipperTy zipper, " | "
                                                     , ppStackTy before, " --> "
                                                     , ppStackTy after ]

ppSimpleT :: ZippySimpleT -> String
ppSimpleT IntegerT = "Integer"
ppSimpleT FloatingT = "Floating"
ppSimpleT TextT = "Text"
ppSimpleT BinaryT = "Binary"

ppZipperTy :: ZephyrZipperTy ZephyrTyVar -> String
ppZipperTy (ZipperVar var) = ppTyVar var
ppZipperTy (ZipperConcrete ty) = ppField ty

ppField :: ZippyFieldType (RecZephyrType ZephyrTyVar) -> String
ppField (SimpleFieldT s) = ppSimpleT s
ppField (RefFieldT r) = ppZephyrTy r

ppZephyrTy :: RecZephyrType ZephyrTyVar -> String
ppZephyrTy (ZippyTyCon tyName args)
    | V.null args = ppTyName tyName
    | otherwise = concat [ "(", ppTyName tyName, " " ] ++
                  intercalate " " (map ppZipperTy (V.toList args)) ++
                  ")"

ppStackTy :: ZephyrStackTy ZephyrTyVar -> String
ppStackTy StackBottom = "0"
ppStackTy (StackVar var) = ppTyVar var
ppStackTy (up :> top) = concat [ppStackTy up, " ", ppStackAtomTy top]

ppStackAtomTy :: ZephyrStackAtomTy ZephyrTyVar -> String
ppStackAtomTy (StackAtomSimple t) = ppSimpleT t
ppStackAtomTy (StackAtomQuote eff) = concat ["(", ppEffect eff, ")"]
ppStackAtomTy (StackAtomZipper zip) = ppZipperTy zip
ppStackAtomTy (StackAtomVar var) = ppTyVar var

ppTyName :: ZippyTyName -> String
ppTyName (ZippyTyName mod name) = concat [T.unpack mod, ":", T.unpack name]

ppTyDesc (tyVar, desc) = ppTyVar tyVar ++ ": " ++ ppDesc
    where ppDesc = case desc of
                     ZephyrTyDescZipper z _ -> ppZipperTy z
                     ZephyrTyDescStack s _ -> ppStackTy s
                     ZephyrTyDescStackAtom s _  -> ppStackAtomTy s
                     ZephyrTyDescFree var _ -> "FREE (" ++ ppTyVar var ++ ")"

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
