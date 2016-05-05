{-# LANGUAGE RecordWildCards, TupleSections, RankNTypes, OverloadedStrings, MultiParamTypeClasses, LambdaCase, ScopedTypeVariables #-}
module Database.Zippy.Zephyr.TyCheck where

import Database.Zippy.Zephyr.Types
import Database.Zippy.Zephyr.Parse
import Database.Zippy.Zephyr.Internal
import Database.Zippy.Types

import Prelude hiding (mapM)

import Control.Applicative
import Control.Arrow
import Control.Monad.ST
import Control.Monad.State hiding (mapM)

import Data.Proxy
import Data.STRef
import Data.Traversable (mapM)
import Data.Foldable (Foldable, foldlM, foldrM)
import Data.List (intercalate)
import Data.Monoid
import Data.Maybe
import Data.UnionFind.ST
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Vector as V
import qualified Data.DList as D
import qualified Data.HashMap.Strict as HM
import qualified Data.HashTable.ST.Basic as HT
import qualified Data.HashTable.Class as HTC

import Debug.Trace

data ZephyrTyCheckState s = ZephyrTyCheckState
                          { nextVar :: ST s ZephyrTyVar
                          , allocVar :: ZephyrTyVar -> ST s ()

                          , tyCheckTyVars :: HT.HashTable s ZephyrTyVar (Point s ZephyrTyDesc)
                          , tyCheckInstances :: [(ZephyrTyVar, ZephyrTyDesc)]

                          , unifyIndent :: Int }

type DetailedTyCheckedPackage = GenericZephyrPackage (ZephyrT ZephyrStackAtomK ZephyrTyVar, [ZephyrOpComment], [ZephyrTyCheckOp], ZephyrTyChecked)

newtype ZephyrTyErrorLocation = ZephyrTyErrorLocation (ZephyrTyCheckLocation -> ZephyrTyCheckLocation)

instance Monoid ZephyrTyErrorLocation where
    mempty = ZephyrTyErrorLocation id
    mappend (ZephyrTyErrorLocation a) (ZephyrTyErrorLocation b) = ZephyrTyErrorLocation $ a . b

instance Show ZephyrTyErrorLocation where
    show (ZephyrTyErrorLocation loc) = show (loc Here)

data ZephyrTyDesc where
    ZephyrTyDesc :: IsKind k => ZephyrT k ZephyrTyVar -> [ZephyrTyCheckLocation] -> ZephyrTyDesc
deriving instance Show ZephyrTyDesc

descKind :: ZephyrTyDesc -> ZephyrKind
descKind (ZephyrTyDesc z _) = kindOf z

descKindsMatch :: ZephyrTyDesc -> ZephyrTyDesc -> Bool
descKindsMatch a b = case (descKind a, descKind b) of
                       (ZephyrBottomK, _) -> True
                       (_, ZephyrBottomK) -> True
                       (a, b) -> a == b

descLoc :: ZephyrTyDesc -> [ZephyrTyCheckLocation]
descLoc (ZephyrTyDesc _ loc) = loc

data ZephyrTyCheckOp = ZephyrTyCheckCheckState !ZephyrTyErrorLocation !(ZephyrExecState ZephyrTyVar)
                     | ZephyrTyCheckCheckEffect !ZephyrTyErrorLocation !(ZephyrEffect ZephyrTyVar)
                     | ZephyrTyCheckCheckQuote !ZephyrTyErrorLocation !(ZephyrEffect ZephyrTyVar) [ZephyrOpComment]
                     | ZephyrTyCheckCheckSymbol !ZephyrTyErrorLocation !ZephyrTyVar !ZephyrTyVar
                     | ZephyrTyCheckCheckBuiltin !ZephyrTyErrorLocation !(ZephyrT ZephyrStackAtomK ZephyrTyVar) !ZephyrTyVar
                       deriving Show

data OpTypes = UserDefined [ZephyrTyCheckOp]
             | Builtin
               deriving Show

data ZephyrOpComment = ZephyrNoComment
                     | ZephyrSymbolType (ZephyrT ZephyrStackAtomK ZephyrTyVar)
                     | ZephyrQuoteComments [ZephyrOpComment]

instance Show ZephyrOpComment where
    show ZephyrNoComment = "ZephyrNoComment"
    show (ZephyrSymbolType ty) = concat ["ZephyrSymbolType (", ppZephyrTy ty, ")"]
    show (ZephyrQuoteComments cs) = concat ["ZephyrQuoteComments ", show cs]

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
                           | WhileCheckingAtom !ZephyrBuilderAtom !ZephyrTyCheckLocation
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
certifyPackage pkg = fmap certifyZephyr pkg

certifyZephyr (ZephyrBuilder ops) = ZephyrTyChecked [mapAsk (const (error "Ask in zephyr builder")) $ mapQuote certifyZephyr atom | ZephyrAtom atom _ <- D.toList ops]

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
                             , allocVar = \(ZephyrTyVar a) ->
                                 do ret <- readSTRef var
                                    when (ret < a) (writeSTRef var (a + 1))
                             , tyCheckTyVars = tyVars
                             , tyCheckInstances = []
                             , unifyIndent = 0 })

getPointForVariable :: ZephyrTyVar -> ZephyrTyCheckM s (Point s ZephyrTyDesc)
getPointForVariable tyVar =
    do tyVars <- gets tyCheckTyVars
       tyVarPoint <- zephyrST (HT.lookup tyVars tyVar)
       case tyVarPoint of
         Nothing -> zephyrST $
                    do newPoint <- fresh (ZephyrTyDesc (ZephyrVarT tyVar :: ZephyrT ZephyrBottomK ZephyrTyVar) mempty)
                       HT.insert tyVars tyVar newPoint
                       return newPoint
         Just tyVarPoint -> return tyVarPoint

zipWith4 :: (a -> b -> c -> d -> e) -> [a] -> [b] -> [c] -> [d] -> [e]
zipWith4 f a b c d = let ZipList e = f <$> ZipList a <*> ZipList b <*> ZipList c <*> ZipList d
                     in e

tyCheckPackages :: ZephyrSymbolEnv (ZephyrT ZephyrStackAtomK ZephyrTyVar) -> ZephyrTypeLookupEnv -> [ZephyrPackage] -> ZephyrTyCheckM s [DetailedTyCheckedPackage]
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

                       tyDescs <- gets tyCheckTyVars
                       tyDescs <- zephyrST (HT.foldM (\assocs (key, val) -> descriptor val >>= \val -> pure ((key, val):assocs)) [] tyDescs)
                       symbolTypes <- trace (intercalate "\n" (map ppTyDesc tyDescs) ++ "\nDone") (mapM (mapM simplifyEffect) symbolEffects)
                       symbolTypes' <- mapM (mapM generalizeType) symbolTypes
                       unifySymbols typedSymbols symbolTypes'

                       trace ("Got typed symbols: " ++ ppSymbolTypes (map zephyrSymbols symbolTypes') ++ "\n") (return ())

                       symbolTypes' <- instantiateAll typedSymbols symbolEffects symbolTypes'

                       trace ("Got typed symbols: " ++ ppSymbolTypes (map zephyrSymbols symbolTypes') ++ "\n") (return ())

                       commentedOps <- mapM (mapM (commentOps . zephyrSymbolDefinition) . zephyrSymbols) typedSymbolOps
                       -- We also want to return simplified versions of the symbol types and the typed operations
                       pure (zipWith4 (\tyPkg  opCommentss pkg typedOpsPkg ->
                                       pkg { zephyrSymbols =
                                                 zipWith4 (\(ZephyrSymbolDefinition _ ty) opComments (ZephyrSymbolDefinition name bc) (ZephyrSymbolDefinition _ typedOps) ->
                                                           ZephyrSymbolDefinition name (ty, opComments, typedOps, certifyZephyr bc))
                                                          (zephyrSymbols tyPkg) opCommentss (zephyrSymbols pkg) (zephyrSymbols typedOpsPkg)} )
                             symbolTypes' commentedOps pkgs typedSymbolOps)

          instantiateAll typedSymbols symbolEffects symbolTypes =
              do instancesToCheck <- gets tyCheckInstances
                 forM_ instancesToCheck $ \(symVar, ty) -> do
                   symP <- getPointForVariable symVar
                   sym <- zephyrST (descriptor symP)
                   trace ("Symbol " ++ ppTyDesc (symVar, sym)) (
                     trace ("Instantiating " ++ ppTyDesc (symVar, ty)) (assertTyVarUnifies symVar ty :: ZephyrTyCheckM s (ZephyrT ZephyrStackAtomK ZephyrTyVar)))

                 symbolEffects' <- mapM (mapM simplifyEffect) symbolEffects
                 symbolTypes' <- mapM (mapM generalizeType) symbolEffects'
                 let oldRanks = concatMap (map (rank . zephyrSymbolDefinition) . zephyrSymbols) symbolTypes
                     newRanks = concatMap (map (rank . zephyrSymbolDefinition) . zephyrSymbols) symbolTypes'
                     rank (ZephyrForAll _ _ t) = 1 + rank t
                     rank _ = 0 :: Int
                 unifySymbols typedSymbols symbolTypes'

                 if oldRanks == newRanks then pure symbolTypes' else instantiateAll typedSymbols symbolEffects' symbolTypes'

          allFreeVariables = do vars <- gets tyCheckTyVars
                                S.fromList . map fst . filter (uncurry isFree) <$> zephyrST (mapM (\(key, val) -> (key,) <$> descriptor val) =<< HTC.toList vars)
          allSymbols = map zephyrSymbols pkgs
          ppTypedSymbols typedPkgs = intercalate "\n=======\n" $
                                     concatMap (\typedPkg ->
                                                map (\(ZephyrSymbolDefinition (ZephyrWord name) code) ->
                                                         concat [ "DEFINE ", T.unpack name, " == \n"
                                                                , intercalate "\n" $ map ppTyCheckOp code ]) (zephyrSymbols typedPkg)) typedPkgs
          ppSymbolTypes typedPkgs = intercalate "\n=======\n" $
                                    concatMap (\typedPkg ->
                                               map (\(ZephyrSymbolDefinition (ZephyrWord name) ty) ->
                                                    concat [ "TY ", T.unpack name, " ", ppZephyrTy ty, "\n"]) typedPkg) typedPkgs

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

generalizeType :: ZephyrEffect ZephyrTyVar -> ZephyrTyCheckM s (ZephyrT ZephyrStackAtomK ZephyrTyVar)
generalizeType ty = foldrM (\v t ->
                            do pt <- getPointForVariable v
                               ZephyrTyDesc vTy _ <- zephyrST (descriptor pt)
                               pure (ZephyrForAll (kindOf vTy) v t)) (ZephyrQuoteT ty) (allTyVariables ty)

commentOps ops = catMaybes <$> mapM commentOp ops

commentOp :: ZephyrTyCheckOp -> ZephyrTyCheckM s (Maybe ZephyrOpComment)
commentOp (ZephyrTyCheckCheckSymbol _ _ tyVar) =
    Just . ZephyrSymbolType <$> simplifyZephyrT (ZephyrVarT tyVar)
commentOp (ZephyrTyCheckCheckBuiltin _ _ tyVar) =
    Just . ZephyrSymbolType <$> simplifyZephyrT (ZephyrVarT tyVar)
commentOp (ZephyrTyCheckCheckQuote _ _ comments) = Just . ZephyrQuoteComments <$> mapM simplifyComment comments
    where simplifyComment (ZephyrSymbolType ty) = ZephyrSymbolType <$> simplifyZephyrT ty
          simplifyComment (ZephyrQuoteComments comments) = ZephyrQuoteComments <$> mapM simplifyComment comments
          simplifyComment x = pure x
commentOp (ZephyrTyCheckCheckState _ _) = pure Nothing
commentOp _ = pure (Just ZephyrNoComment)

forceTyVars :: [ZephyrTyVar] -> ZephyrT k ZephyrTyVar -> ZephyrTyCheckM s (ZephyrT k ZephyrTyVar)
forceTyVars vars ty =
    do points <- mapM getPointForVariable vars
       descriptors <- mapM (zephyrST . descriptor) points
       let varMapping = mconcat (zipWith descMapping vars descriptors)
           descMapping var (ZephyrTyDesc (ZephyrVarT mappedVar) _) = HM.singleton mappedVar var
           descMapping _ _ = mempty

           forceVar var = case HM.lookup var varMapping of
                            Just oldVar -> oldVar
                            Nothing -> var
       trace ("Forced vars " ++ show varMapping) (pure (fmap forceVar ty))

simplifyTyDesc :: TyCheckEndoM s ZephyrTyDesc
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
         ZephyrTyDesc (ZephyrVarT v) _
             | v == tyVar -> pure (ZephyrVarT v)
         ZephyrTyDesc ty _ -> case safeCoercedKind ty of
                                Just ty -> simplifyZephyrT ty
                                Nothing -> fail "Kind mismatch during simplification"
simplifyZephyrT (ZephyrForAll k v ty) =
    do v' <- newTyVar
       ZephyrForAll k v' <$> simplifyZephyrT (fmap (\oldV -> if oldV == v then v' else oldV) ty)

simplifyZipperTyCon :: TyCheckEndoM s (GenericZippyTyCon (ZephyrT ZephyrZipperK ZephyrTyVar))
simplifyZipperTyCon (ZippyTyCon tyName tyArgs) =
    ZippyTyCon tyName <$> mapM simplifyZephyrT tyArgs

unifySymbols :: ZephyrSymbolEnv ZephyrTyVar -> [GenericZephyrPackage (ZephyrT ZephyrStackAtomK ZephyrTyVar)] -> ZephyrTyCheckM s ()
unifySymbols env typedPackages =
    mapM (\pkg -> mapM (unifyPkgSymbol (zephyrPackageName pkg)) (zephyrSymbols pkg)) typedPackages >> return ()
    where unifyPkgSymbol pkgName (ZephyrSymbolDefinition sym ty) =
              do let Just tyVar = lookupInSymbolEnv (Right (pkgName, sym)) env
                 tyP <- getPointForVariable tyVar
                 trace ("Set descriptor " ++ show tyVar ++ " to " ++ ppZephyrTy ty) (zephyrST (setDescriptor tyP (ZephyrTyDesc ty mempty)))

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
assertTyCheckOp st (ZephyrTyCheckCheckQuote loc eff _) =
    assertTyCheckOp st (ZephyrTyCheckCheckEffect loc eff)
assertTyCheckOp (ZephyrExecState actZipper actBefore) (ZephyrTyCheckCheckEffect loc (ZephyrEffect expZipper expBefore after)) =
    inNestedLocation loc $
    do assertState (ZephyrExecState actZipper actBefore) (ZephyrExecState expZipper expBefore)
       pure (ZephyrExecState expZipper after)
assertTyCheckOp (ZephyrExecState actZipper actBefore) (ZephyrTyCheckCheckSymbol loc symVar monoVar) =
    inNestedLocation loc $
    do afterStk <- stackVarT <$> newTyVar
       let monoType = ZephyrQuoteT (ZephyrEffect actZipper actBefore afterStk)
       assertTyVarInstantiates' symVar monoType
       unifyZephyrT (ZephyrVarT monoVar) monoType
       pure (ZephyrExecState actZipper afterStk)
assertTyCheckOp st (ZephyrTyCheckCheckBuiltin loc ty monoType) =
    do eff <- instantiateEffect ty
       unifyZephyrT (ZephyrVarT monoType) (ZephyrQuoteT eff)
       assertTyCheckOp st (ZephyrTyCheckCheckEffect loc eff)
    where instantiateEffect :: ZephyrT ZephyrStackAtomK ZephyrTyVar -> ZephyrTyCheckM s (ZephyrEffect ZephyrTyVar)
          instantiateEffect (ZephyrForAll _ v ty) =
              do subVar <- newTyVar
                 instantiateEffect (fmap (\var -> if var == v then subVar else var) ty)
          instantiateEffect (ZephyrQuoteT x) = pure x

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
         ZephyrTyDesc ty _ -> case safeCoercedKind ty of
                                Nothing -> fail ("Kind mismatch during type var matching. had " ++ show (kindOf ty))
                                Just t -> pure t

andM :: (Foldable f, Monad m) => (a -> m Bool) -> f a -> m Bool
andM f x = foldlM doAnd True x
    where doAnd False _ = return False
          doAnd True x = f x

isFree v (ZephyrTyDesc (ZephyrVarT v') _)
    | trace ("Check free " ++ show v ++ " " ++ show v') (v == v') = True
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

assertTyVarInstantiates' :: IsKind k => ZephyrTyVar -> ZephyrT k ZephyrTyVar -> ZephyrTyCheckM s ()
assertTyVarInstantiates' tyVar expTy = modify $ \st -> st { tyCheckInstances = (tyVar, ZephyrTyDesc expTy mempty):tyCheckInstances st }

assertTyVarUnifies' :: IsKind k => ZephyrTyVar -> ZephyrT k ZephyrTyVar -> ZephyrTyCheckM s (ZephyrT k ZephyrTyVar)
assertTyVarUnifies' tyVar expTy = assertTyVarUnifies tyVar (ZephyrTyDesc expTy mempty)

assertTyVarUnifies ::  IsKind k => ZephyrTyVar -> ZephyrTyDesc -> ZephyrTyCheckM s (ZephyrT k ZephyrTyVar)
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
          else dieOnRecursiveType tyVar expTyDesc

dieOnRecursiveType :: ZephyrTyVar -> ZephyrTyDesc -> ZephyrTyCheckM s a
dieOnRecursiveType tyVar tyDesc = do pt <- getPointForVariable tyVar
                                     tyDesc' <- simplifyTyDesc tyDesc
                                     dieTyCheck (descLoc tyDesc) (InfinitelyRecursiveType tyVar tyDesc')

increaseIndent :: ((String -> String) -> ZephyrTyCheckM s a) -> ZephyrTyCheckM s a
increaseIndent a = do indentN <- gets unifyIndent
                      modify (\st -> st { unifyIndent = unifyIndent st + 2 })
                      r <- a ((replicate indentN ' ') ++)
                      modify (\st -> st { unifyIndent = unifyIndent st - 2 })
                      return r

unifyZephyrT :: IsKind k => ZephyrT k ZephyrTyVar -> ZephyrT k ZephyrTyVar -> ZephyrTyCheckM s (ZephyrT k ZephyrTyVar)
unifyZephyrT actTy@(ZephyrForAll k v act) exp = do subVar <- newTyVar
                                                   unifyZephyrT (fmap (\var -> if var == v then subVar else var) act) exp
                                                   return actTy
unifyZephyrT act expTy@(ZephyrForAll k v exp) = do subVar <- newTyVar
                                                   unifyZephyrT act (fmap (\var -> if var == v then subVar else var) exp)
                                                   return expTy
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
unifyTyDesc (ZephyrTyDesc act@(ZephyrVarT _) actLoc) expDesc@(ZephyrTyDesc exp expLoc) =
    sameKinded act exp $ \case
      Just (act, exp) -> pure expDesc
      Nothing -> dieTyCheck (actLoc <> expLoc) (KindMismatch act exp)
unifyTyDesc actDesc@(ZephyrTyDesc act actLoc) (ZephyrTyDesc exp@(ZephyrVarT _) expLoc) =
    sameKinded act exp $ \case
      Just (act, exp) -> pure actDesc
      Nothing -> dieTyCheck (actLoc <> expLoc) (KindMismatch act exp)
unifyTyDesc (ZephyrTyDesc act actLoc) (ZephyrTyDesc exp expLoc) =
    sameKinded act exp $ \case
      Just (act, exp) -> do newTy <- unifyZephyrT act exp
                            return (ZephyrTyDesc newTy (actLoc <> expLoc))
      Nothing -> trace "Die at ty desc unify" (dieTyCheck (actLoc <> expLoc) (KindMismatch act exp))

mkTypedZephyrBuilder :: ZephyrTypeLookupEnv -> ZephyrSymbolEnv (ZephyrT ZephyrStackAtomK ZephyrTyVar) -> ZephyrSymbolEnv ZephyrTyVar -> ZephyrBuilder -> ZephyrTyCheckM s [ZephyrTyCheckOp]
mkTypedZephyrBuilder types pretypedSymbols typedSymbols (ZephyrBuilder ops) = mapM (mkAtomType types pretypedSymbols typedSymbols) (D.toList ops)

mkAtomType :: ZephyrTypeLookupEnv -> ZephyrSymbolEnv (ZephyrT ZephyrStackAtomK ZephyrTyVar) -> ZephyrSymbolEnv ZephyrTyVar -> ZephyrBuilderOp -> ZephyrTyCheckM s ZephyrTyCheckOp
mkAtomType types pretypedSymbols typedSymbols (ZephyrAtom a loc) = atomType locAtom types pretypedSymbols typedSymbols a
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

atomType :: ZephyrTyErrorLocation -> ZephyrTypeLookupEnv -> ZephyrSymbolEnv (ZephyrT ZephyrStackAtomK ZephyrTyVar) -> ZephyrSymbolEnv ZephyrTyVar -> ZephyrBuilderAtom -> ZephyrTyCheckM s ZephyrTyCheckOp
atomType l _ _ _ (IntegerZ _) = ZephyrTyCheckCheckEffect l <$> instantiate "z | *s -->  *s Integer"
atomType l _ _ _ (TextZ _) = ZephyrTyCheckCheckEffect l <$> instantiate "z | *s --> *s Text"
atomType l _ _ _ (FloatingZ _) = ZephyrTyCheckCheckEffect l <$> instantiate "z | *s --> *s Floating"
atomType l _ _ _ (BinaryZ _) = ZephyrTyCheckCheckEffect l <$> instantiate "z | *s --> *s Binary"
atomType l types pretyped syms (QuoteZ q) = do typedQ <- mkTypedZephyrBuilder types pretyped syms q
                                               quoteEffect <- assertSymbol typedQ
                                               stk <- stackVarT <$> newTyVar
                                               zipper <- zipperVarT <$> newTyVar
                                               comments <- commentOps typedQ
                                               trace ("Find quote " ++ show q ++ " has type " ++ ppEffect quoteEffect) (pure (ZephyrTyCheckCheckQuote l (ZephyrEffect zipper stk (stk :> ZephyrQuoteT quoteEffect)) comments))
atomType l _ pretyped syms (SymZ _ sym) = case lookupInSymbolEnv (Left sym) pretyped of
                                            Nothing -> case lookupInSymbolEnv (Left sym) syms of
                                                         Nothing -> error ("Could not resolve symbol " ++ show sym ++ "\n" ++ show pretyped ++ "\n" ++ show syms)
                                                         Just v -> do monoType <- newTyVar
                                                                      pure (ZephyrTyCheckCheckSymbol l v monoType)
                                            Just ty -> do monoType <- newTyVar
                                                          trace ("Looked up " ++ show sym ++ ": has effect " ++ ppZephyrTy ty) (pure (ZephyrTyCheckCheckBuiltin l ty monoType))
atomType l _ _ _ ZipUpZ = error "ZipUpZ is un-typable"
atomType l _ _ _ ZipDownZ = error "Cannot handle ZipDownZ yet"
atomType l _ _ _ ZipReplaceZ = ZephyrTyCheckCheckEffect l <$> instantiate "focus | *s focus -->  *s"
atomType l _ _ _ CurAtomZ = ZephyrTyCheckCheckEffect l <$> instantiate "focus | *s --> *s focus"
atomType l _ _ _ CurTagZ = ZephyrTyCheckCheckEffect l <$> instantiate "focus | *s --> *s Integer"
atomType l _ _ _ ArgHoleZ = ZephyrTyCheckCheckEffect l <$> instantiate "z | *s --> *s Integer"
atomType l _ _ _ EnterZipperZ = ZephyrTyCheckCheckEffect l <$> instantiate "z | *s z' (z' | *s --> *s') --> *s' z'"
atomType l _ _ _ CutZ = ZephyrTyCheckCheckEffect l <$> instantiate "z | *s --> *s z"
atomType l _ _ _ DipZ = ZephyrTyCheckCheckEffect l <$> instantiate "z | *s t (z | *s --> *s') -->  *s' t"
atomType l _ _ _ ZapZ = ZephyrTyCheckCheckEffect l <$> instantiate "z | *s t --> *s"
atomType l _ _ _ DupZ = ZephyrTyCheckCheckEffect l <$> instantiate "z | *s t --> *s t t"
atomType l _ _ _ SwapZ = ZephyrTyCheckCheckEffect l <$> instantiate "z | *s a b --> *s b a"
atomType l _ _ _ DeQuoteZ = ZephyrTyCheckCheckEffect l <$> instantiate "z | *s (z | *s --> *t) --> *t"
atomType l _ _ _ IfThenElseZ = ZephyrTyCheckCheckEffect l <$> instantiate "z | *s (z | *s --> *s' base:Bool) (z | *s' --> *s'') (z | *s' --> *s'') --> *s''"
atomType l _ _ _ PlusZ = ZephyrTyCheckCheckEffect l <$> instantiate "z | *s Integer Integer --> *s Integer"
atomType l _ _ _ EqZ = ZephyrTyCheckCheckEffect l <$> instantiate "z | *s a a --> *s base:Bool"
atomType l _ _ _ LtZ = ZephyrTyCheckCheckEffect l <$> instantiate "z | *s a a --> *s base:Bool"
atomType l _ _ _ GtZ = ZephyrTyCheckCheckEffect l <$> instantiate "z | *s a a --> *s base:Bool"
atomType l _ _ _ FailZ = ZephyrTyCheckCheckEffect l <$> instantiate "z | *s a --> *s"
atomType l _ _ _ YieldZ = ZephyrTyCheckCheckEffect l <$> instantiate "z | *s a --> *s"
atomType l _ _ _ RandomZ = ZephyrTyCheckCheckEffect l <$> instantiate "z | *s --> *s Integer"
atomType l _ _ _ LogZ = ZephyrTyCheckCheckEffect l <$> instantiate "z | *s a --> *s"
atomType l _ _ _ TraceZ = ZephyrTyCheckCheckEffect l <$> instantiate "z | *s --> *s"
atomType l _ _ _ op = fail ("No clue how to handle op " ++ show op)

allocateTyVariable :: ZephyrTyVar -> ZephyrTyCheckM s ()
allocateTyVariable tyVar = gets allocVar >>= zephyrST . ($ tyVar)

newTyVar :: ZephyrTyCheckM s ZephyrTyVar
newTyVar = gets nextVar >>= zephyrST

ppTyVar :: ZephyrTyVar -> String
ppTyVar (ZephyrTyVar i) = 'v':show i

ppTyCheckOp :: ZephyrTyCheckOp -> String
ppTyCheckOp (ZephyrTyCheckCheckState _ st) = "Check state: " ++ ppState st
ppTyCheckOp (ZephyrTyCheckCheckQuote _ eff _) = "Check quote: " ++ ppEffect eff
ppTyCheckOp (ZephyrTyCheckCheckEffect _ eff) = "Check effect: " ++ ppEffect eff
ppTyCheckOp (ZephyrTyCheckCheckSymbol _ tyVar _) = "Check symbol: " ++ ppTyVar tyVar
ppTyCheckOp (ZephyrTyCheckCheckBuiltin _ ty _) = "Check builtin: " ++ ppZephyrTy ty

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
ppZephyrTy (ZephyrForAll k v ty) = concat [ "∀(", ppTyVar v, "::", show k, "). ", ppZephyrTy ty ]

ppTyName :: ZippyTyName -> String
ppTyName (ZippyTyName mod name) = concat [T.unpack mod, ":", T.unpack name]

ppTyDesc (tyVar, desc) = ppTyVar tyVar ++ ": " ++ ppDesc desc
    where ppDesc (ZephyrTyDesc ty locs) = ppZephyrTy ty

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
