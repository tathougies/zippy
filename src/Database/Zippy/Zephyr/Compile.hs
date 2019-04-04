{-# LANGUAGE TupleSections, OverloadedStrings, TypeFamilies, LambdaCase #-}
module Database.Zippy.Zephyr.Compile where

import Prelude hiding (foldl)

import Database.Zippy.Types
import Database.Zippy.Zephyr.Types
import Database.Zippy.Zephyr.TyCheck
import Database.Zippy.Zephyr.Internal
import Database.Zippy.Zephyr.JIT

import Control.Arrow
import Control.Applicative
import Control.Monad.State

import Data.Maybe
import Data.Monoid
import Data.Int
import Data.Foldable (foldl)
import Data.Graph (stronglyConnComp, topSort, graphFromEdges, SCC(..))
import Data.List (intercalate)
import qualified Data.HashMap.Strict as HM
import qualified Data.Map as M
import qualified Data.Vector as V
import qualified Data.Text as T
import qualified Data.Set as S
import qualified Data.DList as D

import Text.Parsec.Pos (newPos)

import Debug.Trace

boolAtomTy = stackAtomKindedZephyrZipper (RefFieldT (ZippyTyCon (ZippyTyName "base" "Bool") mempty))
scopedTyToZipper (Local var) = ZephyrVarT var
scopedTyToZipper (Global (SimpleFieldT s)) = ZephyrZipperT (SimpleFieldT s)
scopedTyToZipper (Global (RefFieldT r)) = ZephyrZipperT (RefFieldT (fmap scopedTyToZipper r))

genDefinitionsForType :: ZippyTyRef -> GenericZippyAlgebraicT ZippyTyVarName ZephyrScopedTy -> [(ZephyrEffect ZippyTyVarName, [ZephyrT ZephyrStackAtomK ZippyTyVarName], GenericZephyrSymbolDefinition CompiledZephyr)]
genDefinitionsForType tyRef (ZippyAlgebraicT tyCon cons) = concatMap genDefinitionsForCon (zip [0..] (V.toList cons))
    where tyConZ = ZephyrZipperT (RefFieldT (fmap ZephyrVarT tyCon))
          tyConStackAtomZ = ZephyrZipperT (RefFieldT (fmap ZephyrVarT tyCon))

          build = CompiledZephyr . V.fromList

          genDefinitionsForCon :: (Int, GenericZippyDataCon ZephyrScopedTy) -> [(ZephyrEffect ZippyTyVarName, [ZephyrT ZephyrStackAtomK ZippyTyVarName], GenericZephyrSymbolDefinition CompiledZephyr)]
          genDefinitionsForCon (conIndex, ZippyDataCon (ZippyDataConName conName) argTys) =
              [ ( ZephyrEffect (ZephyrVarT "$z") (ZephyrVarT "$s" :> tyConZ) (ZephyrVarT "$s" :> boolAtomTy), []
                , ZephyrSymbolDefinition (ZephyrWord ("IS-" <> conName <> "?"))
                  ( build $
                    [ QuoteZ (build $
                              [ CurTagZ
                              , IntegerZ (fromIntegral conIndex)
                              , EqZ ])
                    , EnterZipperZ
                    , ZapZ] ))

              , ( ZephyrEffect tyConZ (ZephyrVarT "$s") (ZephyrVarT "$s" :> boolAtomTy), []
                , ZephyrSymbolDefinition (ZephyrWord ("CUR-IS-" <> conName <> "?"))
                  ( build $
                    [ CurTagZ
                    , IntegerZ (fromIntegral conIndex)
                    , EqZ ] ) )

              , ( ZephyrEffect (ZephyrVarT "$z") (foldl (:>) (ZephyrVarT "$s") (map (scopedTyToZipper . zippyFieldType) (V.toList argTys))) (ZephyrVarT "$s" :> tyConZ), [tyConStackAtomZ]
                , ZephyrSymbolDefinition (ZephyrWord conName)
                  ( build $
                    [ TagZ (Right (ZephyrAskRef 0)) (fromIntegral conIndex) (V.length argTys) ] ) ) ] ++
              concatMap (genDefinitionsForArg conName) (zip [0..] (V.toList argTys))

          genDefinitionsForArg :: T.Text -> (Int64, GenericZippyField ZephyrScopedTy) -> [(ZephyrEffect ZippyTyVarName, [ZephyrT ZephyrStackAtomK ZippyTyVarName], GenericZephyrSymbolDefinition CompiledZephyr)]
          genDefinitionsForArg _ (i, ZippyUnnamedField _) = []
          genDefinitionsForArg conName (i, ZippyNamedField (ZippyDataArgName argName) fieldTy) =
              [ ( ZephyrEffect tyConZ (ZephyrVarT "$s" :> ZephyrQuoteT (ZephyrEffect (scopedTyToZipper fieldTy) (ZephyrVarT "$s") (ZephyrVarT "$s'"))) (ZephyrVarT "$s'"), []
                , ZephyrSymbolDefinition (ZephyrWord ("VISIT-" <> conName <> "-" <> argName))
                  ( build $
                    [ IntegerZ i
                    , ZipDownZ

                    , DeQuoteZ

                    , ZipUpZ ]) )

              , ( ZephyrEffect tyConZ (ZephyrVarT "$s") (ZephyrVarT "$s" :> boolAtomTy), []
                , ZephyrSymbolDefinition (ZephyrWord ("CHK-HOLE-" <> conName <> "-" <> argName))
                  ( build $
                    [ ArgHoleZ
                    , IntegerZ i
                    , EqZ ] ) ) ]

instantiateAllTypes :: ZephyrTypeLookupEnv -> ZephyrTypeInstantiationEnv -> [GenericZippyAlgebraicT ZippyTyVarName ZephyrScopedTy] -> ZephyrTypeInstantiationEnv
instantiateAllTypes allTypes env types = foldl instantiateType env types
    where instantiateType env ty@(ZippyAlgebraicT (ZippyTyCon tyName args) cons)
              | V.null args = let env' = snd (internType allTypes env (ZephyrInstantiatedType (ZippyTyCon tyName mempty)))
                                  env'' = foldl (instantiateTypesFromCon HM.empty) env' cons
                              in env''
              | otherwise = env

          instantiateTypesFromCon tyVars env (ZippyDataCon conName args) =
              foldl (instantiateTypesForArg tyVars) env (fmap zippyFieldType args)

          instantiateTypesForArg tyVars env (Local var) =
              case HM.lookup var tyVars of
                Nothing -> error "Encountered unbound type variable in type"
                Just ty -> env
          instantiateTypesForArg tyVars env (Global (SimpleFieldT _)) = env
          instantiateTypesForArg tyVars env (Global (RefFieldT r)) =
              instantiate env tyVars r

          instantiate env tyVars (ZippyTyCon tyName tyArgs) =
              -- First we intern the fully instantiated type to prevent cycles...
              let instantiatedType =  ZephyrInstantiatedType $ ZippyTyCon tyName args'
                  args' = fmap (resolveTyVars tyVars) tyArgs
              -- Then we lookup the type by name, so that we can recursively instantiate types we find in its constructors
              in if alreadyInstantiatedInEnv instantiatedType allTypes env
                 then env
                 else let env' = snd (internType allTypes env instantiatedType)
                      in case lookupInTyEnv tyName allTypes of
                           Nothing -> error ("Cannot find type " ++ show tyName)
                           Just (ZippyAlgebraicT (ZippyTyCon _ expArgs) cons)
                               | V.length expArgs == V.length tyArgs ->
                                   let tyVars' = HM.fromList $
                                                 zip (V.toList expArgs) (V.toList args')
                                   in foldl (instantiateTypesFromCon tyVars') env' cons
                               | otherwise -> error ("Type constructor arity mismatch: " ++ show tyName)

          resolveTyVars tyVars (Local var) =
              case HM.lookup var tyVars of
                Nothing -> error "Encountered unbound type variable in type"
                Just x -> x
          resolveTyVars tyVars (Global (SimpleFieldT s)) = SimpleFieldT s
          resolveTyVars tyVars (Global (RefFieldT (ZippyTyCon tyName tyArgs))) = RefFieldT (ZephyrInstantiatedType (ZippyTyCon tyName (fmap (resolveTyVars tyVars) tyArgs)))

data ZephyrCompileError = ZephyrCompileErrorTy ([ZephyrTyCheckLocation], ZephyrTyCheckError)
                        | ZephyrCompileErrorGeneric String
                          deriving Show

newtype ZephyrBeforeAskInference = ZephyrBeforeAskInference [ZephyrBeforeAskInferenceAtom] deriving Show
type ZephyrBeforeAskInferenceAtom = GenericZephyrAtom (ZephyrT ZephyrStackAtomK ZephyrTyVar) ZephyrBeforeAskInference Int

monomorphicTy :: ZephyrT k var -> ZephyrT k var
monomorphicTy (ZephyrForAll _ _ x) = monomorphicTy x
monomorphicTy x = x

existentials :: ZephyrT k var -> [var]
existentials ty = existentials' ty []
    where existentials' (ZephyrForAll k v ty) a = existentials' ty (v:a)
          existentials' _ a = a

instantiateTy :: ZephyrT k ZephyrTyVar -> ZephyrTyCheckM s (ZephyrT k ZephyrTyVar, HM.HashMap ZephyrTyVar ZephyrTyVar)
instantiateTy ty = instantiateTy' ty mempty
    where instantiateTy' (ZephyrForAll k v ty) a =
              do v' <- newTyVar
                 instantiateTy' (fmap (\var -> if var == v then v' else var) ty) (HM.insert v v' a)
          instantiateTy' ty a = pure (ty, a)

subVars :: HM.HashMap ZephyrTyVar ZephyrTyVar -> ZephyrT k ZephyrTyVar -> ZephyrT k ZephyrTyVar
subVars subs ty = fmap doSub ty
    where doSub var = HM.lookupDefault var var subs

inferAsks :: ZephyrTypeLookupEnv -> ZephyrTypeInstantiationEnv ->
             [(ZephyrWord, ZephyrWord, ZephyrT ZephyrStackAtomK ZephyrTyVar, OpTypes, [ZephyrT ZephyrStackAtomK ZephyrTyVar], [ZephyrOpComment], ZephyrBeforeAskInference)] ->
             ([(ZephyrWord, ZephyrWord, ZephyrT ZephyrStackAtomK ZephyrTyVar, [ZephyrT ZephyrStackAtomK ZephyrTyVar], OpTypes, CompiledZephyr)], ZephyrTypeInstantiationEnv)
inferAsks typeLookupEnv typeInstantiationEnv initialSt =
    let askInferenceGroups = map resolveSCC $ stronglyConnComp (map (\(i, (_, _, _, _, ops)) -> (i, i, S.toList (referredSyms ops))) allReferredSyms)
        allReferredSyms = zip [0..] (map (\(_, _, ty, opTypes, asks, comments, ops) -> (ty, opTypes, asks, comments, ops)) initialSt)
        allReferredSymsMap = HM.fromList allReferredSyms

        resolveSCC (AcyclicSCC v) = [v]
        resolveSCC (CyclicSCC vs) = vs

        referredSyms (ZephyrBeforeAskInference ops) = mconcat (map symsForOp ops)
        symsForOp (SymZ _ sym) = S.singleton sym
        symsForOp (QuoteZ ops) = referredSyms ops
        symsForOp _ = mempty

        symAsks = foldl inferGroupAsks HM.empty askInferenceGroups
        inferGroupAsks asks [sym] =
            let Just (symTy, _, symAsks, symComments, ZephyrBeforeAskInference symOps) = HM.lookup sym allReferredSymsMap
                -- Now go through the zipped up comments and operations, and find any symz or quotes that have asks
                inferredAsks = mconcat $ zipWith createAsk symComments symOps

                createAsk (ZephyrSymbolType ty@(ZephyrForAll _ _ _)) (SymZ _ x) = error ("Cannot create asks for expected polymorphic type: " ++ show ty)
                createAsk (ZephyrSymbolType monoTy) (SymZ _ x)
                    | x /= sym = let Just (referredTy, _, _, _, _) = HM.lookup x allReferredSymsMap
                                     Just referredAsks = HM.lookup x asks

                                     Right askTys = runInNewTyCheckM $ do
                                                      (monoReferredTy, instantiatedVars) <- instantiateTy referredTy
                                                      mapM_ allocateTyVariable (allTyVariables monoTy)
                                                      mapM_ allocateTyVariable (allTyVariables monoReferredTy)
                                                      unifyZephyrT monoTy monoReferredTy
                                                      referredAsks' <- mapM simplifyZephyrT (map (subVars instantiatedVars) (S.toList referredAsks))
                                                      trace ("sym ty " ++ ppZephyrTy monoTy ++ " generic: " ++ ppZephyrTy referredTy) (mapM (forceTyVars (allTyVariables symTy)) referredAsks')
                                 in S.fromList askTys
                createAsk (ZephyrQuoteComments comments) (QuoteZ (ZephyrBeforeAskInference q)) = mconcat $ zipWith createAsk comments q
                createAsk _ _ = mempty

                asks' = HM.insert sym (S.fromList symAsks <> inferredAsks) asks
            in asks'

        (res, typeInstantiationEnv') = runState (mapM compileSymbol (zip [0..] initialSt)) typeInstantiationEnv

        compileSymbol (i, (pkg, symName, symTy, symOpTypes, _, symComments, symOps)) =
            case HM.lookup i symAsks of
              Nothing -> error "Cannot find symbol"
              Just asks ->
                  let boundInTy = S.fromList (existentials symTy)
                      askHasBoundVariables ty = any (`S.member` boundInTy) (allTyVariables ty)
                      asks' = S.filter askHasBoundVariables asks

                      asksList = S.toList asks'
                      askToAskIndex = M.fromList (zip asksList [0..])

                      compileOps :: ZephyrWord -> [ZephyrOpComment] -> ZephyrBeforeAskInference -> State ZephyrTypeInstantiationEnv CompiledZephyr
                      compileOps nm comments (ZephyrBeforeAskInference ops) = trace ("Compile " ++ show nm ++ " (" ++ show ops ++ ") with comments " ++ show comments)
                                                                              (CompiledZephyr . V.fromList . mconcat <$> mapM (uncurry compileOp) (zip comments ops))

                      compileOp (ZephyrSymbolType monoTy) (SymZ _ x) =
                          do let Just (referredTy, _, _, _, _) = HM.lookup x allReferredSymsMap
                                 Just referredAsks = HM.lookup x symAsks

                                 askTyRes = trace ("XXXXXXXXXXXX Going to unify " ++ ppZephyrTy monoTy ++ " with " ++ ppZephyrTy referredTy) $
                                            runInNewTyCheckM $ do
                                              (monoReferredTy, instantiatedVars) <- instantiateTy referredTy
                                              mapM_ allocateTyVariable (allTyVariables monoTy)
                                              mapM_ allocateTyVariable (allTyVariables monoReferredTy)
                                              unifyZephyrT monoTy monoReferredTy
                                              referredAsks' <- mapM simplifyZephyrT (map (subVars instantiatedVars) (S.toList referredAsks))
                                              mapM (forceTyVars (allTyVariables symTy)) referredAsks'

                                 resolveAsk fullTy@(ZephyrZipperT ty)
                                   | null (allTyVariables fullTy) =
                                       do env <- get
                                          let (tyRef, env') = internType typeLookupEnv env (zephyrTyToInstantiatedTy ty)
                                          put env'
                                          pure (Left tyRef)
                                   | otherwise = case M.lookup fullTy askToAskIndex of
                                                   Just i -> pure (Right (ZephyrAskRef i))
                                                   Nothing -> error ("Could not answer ask for symbol " ++ show i ++ ". Looking for " ++ show fullTy ++ ". Have " ++ show askToAskIndex ++ ". Likely an ambiguous variable")
                                 resolveAsk _ = error "bad type form in ask"
                             case askTyRes of
                               Right askTys -> do resolvedAsks <- mapM resolveAsk askTys
                                                  pure [ SymZ (V.fromList resolvedAsks) x ]
                               Left err -> error ("Error resolving types: " ++ show err)

                      compileOp (ZephyrQuoteComments comments) (QuoteZ ops) = do op <- QuoteZ <$> compileOps "" comments ops
                                                                                 pure [op, DupAnswerZ]
                      compileOp comment (QuoteZ q) = error ("Got quote but no comment? " ++ show comment ++ ". Symbols are " ++ show q)
                      compileOp _ op = pure [mapAsk (error "unsupported ask") . mapQuote (error "unsupported quote") $ op]
                  in (pkg, symName, symTy, asksList, symOpTypes,) <$> compileOps symName symComments symOps

    in trace ("Inferring in " ++ intercalate "\n" (zipWith (\i sym -> show i ++ ": " ++ show sym) [0..] initialSt)) $
       trace ("Ask groups: " ++ show askInferenceGroups) $
       trace (" and ask map: " ++ show (HM.toList symAsks)) (res, typeInstantiationEnv')

compilePackages :: [ZephyrPackage] -> ZippyTyCon -> Either ZephyrCompileError (HM.HashMap ZephyrWord ZephyrProgram, ZippySchema)
compilePackages pkgs rootTy =
    let allTypes = tyEnvFromList allTypesList
        allTypesList = map (qualifyConArgTypes allTypes) (concatMap zephyrTypes pkgs)

        uninstantiatedDefs = concatMap (\ty@(ZippyAlgebraicT (ZippyTyCon (ZippyTyName pkg _) _) _) -> map (pkg,) $
                                                                                                      genDefinitionsForType (ZippyTyRef 0) ty) allTypesList

        instantiateDef :: (T.Text, (ZephyrEffect ZippyTyVarName, [ZephyrT ZephyrStackAtomK ZippyTyVarName], GenericZephyrSymbolDefinition CompiledZephyr)) ->
                          ZephyrTyCheckM s (T.Text, (ZephyrT ZephyrStackAtomK ZephyrTyVar, [ZephyrT ZephyrStackAtomK ZephyrTyVar], GenericZephyrSymbolDefinition CompiledZephyr))
        instantiateDef (pkg, (ty, asks, def)) =
            do let tyVars = allTyVariables ty
               instantiatedVars <- HM.fromList <$> mapM (\tyVar -> (tyVar,) <$> newTyVar) tyVars
               let ty' = fmap (fromJust . flip HM.lookup instantiatedVars) ty
                   asks' = map (fmap (fromJust . flip HM.lookup instantiatedVars)) asks
               genTy <- generalizeType ty'
               pure (pkg, (genTy, asks', def))

        tyInstantiationEnv = foldl (\env pkg -> instantiateAllTypes allTypes env (zephyrTypes pkg)) emptyZephyrTypeInstantiationEnv pkgs
        tyChecked = runInNewTyCheckM $ do
                      definitions <- mapM instantiateDef uninstantiatedDefs
                      traceM ("Got definitions " ++ show definitions)
                      let pretypedSymbols = buildSymbolEnv $
                                            map (\(pkgName, (ty, _, ZephyrSymbolDefinition symName _)) -> ((ZephyrWord pkgName, symName), ty)) definitions
                      tyCheckedPkgs <- tyCheckPackages pretypedSymbols allTypes pkgs

                      let (schema, symEnv, symTbl') = compileSymbolTable tyCheckedPkgs definitions
                          exportedSymbols = concatMap (\pkg -> map (zephyrPackageName pkg,) (zephyrExports pkg)) tyCheckedPkgs

                          programs = mapM (\(pkgName, sym) -> (sym,) <$> lookupInSymbolEnv (Right (pkgName, sym)) symEnv) exportedSymbols
                          symTbl = fmap (\(_, _, sym) -> sym) symTbl'

                      generateJitEndpoints symEnv symTbl'

                      case programs of
                        Nothing -> pure (Left (ZephyrCompileErrorGeneric ("could not find exported symbols: " ++ show exportedSymbols)))
                        Just programs -> do let programs' = map (\(sym, index) -> (sym, ZephyrProgram index symTbl)) programs
--                                            trace ("Got asks: " ++ show inferredAsks) $ Right (HM.fromList programs', schema)

                                            pure (Right (HM.fromList programs', schema))

        compileSymbolTable tyCheckedPkgs definitions =
            let (rootTyRef, tyInstantiationEnv'') = internType allTypes tyInstantiationEnv' instantiatedRootTy
                instantiatedRootTy = ZephyrInstantiatedType $ fmap instantiateTy rootTy
                instantiateTy _ = error "root type must be 0-arity"

                schema = ZippySchema rootTyRef (V.fromList (getTypesAsZippyT allTypes tyInstantiationEnv''))

                resolvedSymbols = concatMap (\pkg -> map (\(ZephyrSymbolDefinition symName (ty, opComments, opTypes, def)) -> (zephyrPackageName pkg, symName, (ty, opComments, opTypes, resolveDef def))) (zephyrSymbols pkg)) tyCheckedPkgs

                allSymbolNames = map (\(pkg, symName, _) -> (pkg, symName)) resolvedSymbols ++
                                 map (\(pkg, (_, _, ZephyrSymbolDefinition symName _)) -> (ZephyrWord pkg, symName)) definitions

                symEnv = buildSymbolEnv (zip allSymbolNames [0..])

                (inferredAsks, tyInstantiationEnv') = inferAsks allTypes tyInstantiationEnv initialAsks
                initialAsks = map (\(pkg, symName, (ty, comments, opTypes, def)) -> (pkg, symName, ty, UserDefined opTypes, [], comments, def)) resolvedSymbols ++
                              map (\(pkg, (ty, asks, ZephyrSymbolDefinition symName def)) ->
                                        (ZephyrWord pkg, symName, ty, Builtin, asks, [], ZephyrBeforeAskInference [])) definitions

                symTbl' = V.fromList ((map snd $ zip resolvedSymbols $
                                      map (\(pkg, symName, symTy, _, opTypes, compiled) -> (symTy, opTypes, CompiledZephyrSymbol (ZephyrQualifiedWord pkg symName) compiled)) inferredAsks) ++
                                      map (\(pkg, (ty, _, ZephyrSymbolDefinition symName def)) -> (ty, Builtin, CompiledZephyrSymbol (ZephyrQualifiedWord (ZephyrWord pkg) symName) def)) definitions)
                resolveDef (ZephyrTyChecked atoms) =
                    ZephyrBeforeAskInference $ map (mapQuote resolveDef . fmap resolveSymbol) atoms
                resolveSymbol sym = case lookupInSymbolEnv (Left sym) symEnv of
                                      Nothing -> error ("Could not find symbol " ++ show sym)
                                      Just i -> i
            in trace ("Got symbol names " ++ show allSymbolNames) $
               (schema, symEnv, symTbl')

    in case tyChecked of
         Left err -> Left (ZephyrCompileErrorTy err)
         Right res -> res
         -- Left err -> Left (ZephyrCompileErrorTy err)
         -- Right (tyCheckedPkgs, definitions) ->
         --     let (rootTyRef, tyInstantiationEnv'') = internType allTypes tyInstantiationEnv' instantiatedRootTy
         --         instantiatedRootTy = ZephyrInstantiatedType $ fmap instantiateTy rootTy
         --         instantiateTy _ = error "root type must be 0-arity"

         --         schema = ZippySchema rootTyRef (V.fromList (getTypesAsZippyT allTypes tyInstantiationEnv''))

         --         resolvedSymbols = concatMap (\pkg -> map (\(ZephyrSymbolDefinition symName (ty, opComments, opTypes, def)) -> (zephyrPackageName pkg, symName, (ty, opComments, opTypes, resolveDef def))) (zephyrSymbols pkg)) tyCheckedPkgs

         --         allSymbolNames = map (\(pkg, symName, _) -> (pkg, symName)) resolvedSymbols ++
         --                          map (\(pkg, (_, _, ZephyrSymbolDefinition symName _)) -> (ZephyrWord pkg, symName)) definitions

         --         symEnv = buildSymbolEnv (zip allSymbolNames [0..])

         --         (inferredAsks, tyInstantiationEnv') = inferAsks allTypes tyInstantiationEnv initialAsks
         --         initialAsks = map (\(pkg, symName, (ty, comments, opTypes, def)) -> (pkg, symName, ty, UserDefined opTypes, [], comments, def)) resolvedSymbols ++
         --                       map (\(pkg, (ty, asks, ZephyrSymbolDefinition symName _)) -> (ZephyrWord pkg, symName, ty, Builtin, asks, [], ZephyrBeforeAskInference [])) definitions

         --         symTbl' = V.fromList (map (\(pkg, symName, symTy, opTypes, compiled) -> (symTy, opTypes, CompiledZephyrSymbol (ZephyrQualifiedWord pkg symName) compiled)) inferredAsks ++
         --                               map (\(pkg, (ty, _, ZephyrSymbolDefinition symName def)) -> (ty, Builtin, CompiledZephyrSymbol (ZephyrQualifiedWord (ZephyrWord pkg) symName) def)) definitions)
         --         symTbl = fmap (\(_, _, sym) -> sym) symTbl'
         --         resolveDef (ZephyrTyChecked atoms) =
         --             ZephyrBeforeAskInference $ map (mapQuote resolveDef . fmap resolveSymbol) atoms
         --         resolveSymbol sym = case lookupInSymbolEnv (Left sym) symEnv of
         --                               Nothing -> error ("Could not find symbol " ++ show sym)
         --                               Just i -> i

         --         exportedSymbols = concatMap (\pkg -> map (zephyrPackageName pkg,) (zephyrExports pkg)) tyCheckedPkgs

         --         programs = mapM (\(pkgName, sym) -> (sym,) <$> lookupInSymbolEnv (Right (pkgName, sym)) symEnv) exportedSymbols
         --     in case programs of
         --          Nothing -> Left (ZephyrCompileErrorGeneric ("could not find exported symbols: " ++ show exportedSymbols))
         --          Just programs -> let programs' = map (\(sym, index) -> (sym, ZephyrProgram index symTbl)) programs
         --                           in trace ("Got asks: " ++ show inferredAsks) $ Right (HM.fromList programs', schema)
