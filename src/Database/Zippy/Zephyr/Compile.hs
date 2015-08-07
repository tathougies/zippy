{-# LANGUAGE TupleSections, OverloadedStrings #-}
module Database.Zippy.Zephyr.Compile where

import Prelude hiding (foldl)

import Database.Zippy.Types
import Database.Zippy.Zephyr.Types
import Database.Zippy.Zephyr.TyCheck
import Database.Zippy.Zephyr.Internal

import Control.Arrow
import Control.Applicative
import Control.Monad.State

import Data.Maybe
import Data.Monoid
import Data.Int
import Data.Foldable (foldl)
import qualified Data.HashMap.Strict as HM
import qualified Data.Map as M
import qualified Data.Vector as V
import qualified Data.Text as T
import qualified Data.Set as S

import Debug.Trace

boolAtomTy = stackAtomKindedZephyrZipper (RefFieldT (ZippyTyCon (ZippyTyName "base" "Bool") mempty))
scopedTyToZipper (Local var) = ZephyrVarT var
scopedTyToZipper (Global (SimpleFieldT s)) = ZephyrZipperT (SimpleFieldT s)
scopedTyToZipper (Global (RefFieldT r)) = ZephyrZipperT (RefFieldT (fmap scopedTyToZipper r))

genDefinitionsForType :: ZippyTyRef -> GenericZippyAlgebraicT ZippyTyVarName ZephyrScopedTy -> [(ZephyrEffect ZippyTyVarName, GenericZephyrSymbolDefinition ZephyrTyChecked)]
genDefinitionsForType tyRef (ZippyAlgebraicT tyCon cons) = concatMap genDefinitionsForCon (zip [0..] (V.toList cons))
    where tyConZ = ZephyrZipperT (RefFieldT (fmap ZephyrVarT tyCon))

          genDefinitionsForCon :: (Int, GenericZippyDataCon ZephyrScopedTy) -> [(ZephyrEffect ZippyTyVarName, GenericZephyrSymbolDefinition ZephyrTyChecked)]
          genDefinitionsForCon (conIndex, ZippyDataCon (ZippyDataConName conName) argTys) =
              [ ( ZephyrEffect (ZephyrVarT "$z") (ZephyrVarT "$s" :> tyConZ) (ZephyrVarT "$s" :> boolAtomTy)
                , ZephyrSymbolDefinition (ZephyrWord ("IS-" <> conName <> "?"))
                  ( ZephyrTyChecked $
                    [ QuoteZ (ZephyrTyChecked $
                              [ CurTagZ
                              , IntegerZ (fromIntegral conIndex)
                              , EqZ ])
                    , EnterZipperZ
                    , SwapZ ] ))

              , ( ZephyrEffect tyConZ (ZephyrVarT "$s") (ZephyrVarT "$s" :> boolAtomTy)
                , ZephyrSymbolDefinition (ZephyrWord ("CUR-IS-" <> conName <> "?"))
                  ( ZephyrTyChecked $
                    [ CurTagZ
                    , IntegerZ (fromIntegral conIndex)
                    , EqZ ] ) )

              , ( ZephyrEffect (ZephyrVarT "$z") (ZephyrVarT "$s") (ZephyrVarT "$s" :> tyConZ)
                , ZephyrSymbolDefinition (ZephyrWord conName)
                  ( ZephyrTyChecked $
                    [ TagZ tyRef (fromIntegral conIndex) (V.length argTys) ] ) ) ] ++
              concatMap genDefinitionsForArg (zip [0..] (V.toList argTys))

          genDefinitionsForArg :: (Int64, GenericZippyField ZephyrScopedTy) -> [(ZephyrEffect ZippyTyVarName, GenericZephyrSymbolDefinition ZephyrTyChecked)]
          genDefinitionsForArg (i, ZippyUnnamedField _) = []
          genDefinitionsForArg (i, ZippyNamedField (ZippyDataArgName argName) fieldTy) =
              [ ( ZephyrEffect tyConZ (ZephyrVarT "$s" :> ZephyrQuoteT (ZephyrEffect (scopedTyToZipper fieldTy) (ZephyrVarT "$s") (ZephyrVarT "$s'"))) (ZephyrVarT "$s'")
                , ZephyrSymbolDefinition (ZephyrWord ("VISIT-" <> argName))
                  ( ZephyrTyChecked $
                    [ IntegerZ i
                    , ZipDownZ

                    , DeQuoteZ

                    , ZipUpZ ]) )

              , ( ZephyrEffect tyConZ (ZephyrVarT "$s") (ZephyrVarT "$s" :> boolAtomTy)
                , ZephyrSymbolDefinition (ZephyrWord ("CHK-HOLE-" <> argName))
                  ( ZephyrTyChecked $
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

compilePackages :: [ZephyrPackage] -> ZippyTyCon -> (HM.HashMap ZephyrWord ZephyrProgram, ZippySchema)
compilePackages pkgs rootTy =
    let allTypes = tyEnvFromList allTypesList
        allTypesList = map (qualifyConArgTypes allTypes) (concatMap zephyrTypes pkgs)

        definitions = concatMap (\ty@(ZippyAlgebraicT (ZippyTyCon (ZippyTyName pkg _) _) _) -> map (pkg,) $
                                                                                               genDefinitionsForType (ZippyTyRef 0) ty) allTypesList

        tyInstantiationEnv = foldl (\env pkg -> instantiateAllTypes allTypes env (zephyrTypes pkg)) emptyZephyrTypeInstantiationEnv pkgs
        tyChecked = trace ("Got definitions " ++ show definitions) $
                    runInNewTyCheckM $ do
                      pretypedSymbols <- buildSymbolEnv <$>
                                         mapM (\(pkgName, (ty, ZephyrSymbolDefinition symName _)) -> ((ZephyrWord pkgName, symName),) <$> instantiate (ZephyrEffectWithNamedVars ty)) definitions
                      tyCheckPackages pretypedSymbols allTypes pkgs

        showError (locs, err) = "At " ++ show locs ++ ":\n" ++ showError' err
        showError' (KindMismatch ty1 ty2) = "Kind mismatch between " ++ show (kindOf ty1) ++ " and " ++ show (kindOf ty2) ++ " " ++ show ty1 ++ " " ++ show ty2
        showError' x = show x
    in trace ("Type checked " ++ either (("ERROR\n" ++) . showError) show tyChecked ++ ". With types " ++ show tyInstantiationEnv) undefined


    --     namesToInts = HM.fromList (zip names [0..])
    --     qualifiedSymbols = mconcat (map (\pkg -> map (zephyrPackageName pkg,) (zephyrSymbols pkg ++ concatMap genDefinitionsForType' (zephyrTypes pkg))) pkgs)
    --     symbols = map snd qualifiedSymbols
    --     names = map zephyrSymbolName symbols

    --     resolveSymbol symbol = fromJust (HM.lookup symbol namesToInts <|> error ("Cannot find " ++ show symbol))

    --     compiled = map compiledSymbol symbols
    --     compiledSymbol (ZephyrSymbolDefinition _ builder) = compiledBuilder builder
    --     compiledBuilder (ZephyrTyChecked d) =
    --         let shallowResolved = map (fmap resolveSymbol) d
    --             resolved = map (mapQuote compiledBuilder) shallowResolved
    --         in CompiledZephyr . V.fromList $ resolved

    --     qualifiedWords = map (uncurry ZephyrQualifiedWord . second zephyrSymbolName ) qualifiedSymbols

    --     allInstantiatedTypes = collectInstantiatedTypes allTypes
    --     tyToTyRef :: M.Map (GenericZippyTyCon (ZippyFieldType RecZippyTyCon)) ZippyTyRef
    --     tyToTyRef = M.fromList $
    --                 zip (map (\(ZippyAlgebraicT qTy _) -> qTy) allInstantiatedTypes) (map ZippyTyRef [0..])

    --     Just rootTy = M.lookup (ZippyTyCon (qualifyTy rootTyName allTypes) V.empty) tyToTyRef
    --     schema = let lookupFieldTy (SimpleFieldT s) = SimpleFieldT s
    --                  lookupFieldTy (RefFieldT ty) =
    --                      case M.lookup (unRecTy ty) tyToTyRef of
    --                        Just x -> RefFieldT x
    --                        Nothing -> error ("Could not find instantiation of " ++ show ty)
    --              in ZippySchema rootTy (V.fromList (map (AlgebraicT . mapZippyAlgebraicT lookupFieldTy lookupFieldTy) allInstantiatedTypes))

    --     genDefinitionsForType' ty@(ZippyAlgebraicT qTy _) =
    --         --let Just tyRef = HM.lookup qTy tyToTyRef
    --         {-in-} genDefinitionsForType (ZippyTyRef 0) {- TODO How do we figure out the type reference if we don't know what the types are until run-time? -} ty

    --     allExports = concatMap zephyrExports pkgs
    --     progs = HM.fromList $
    --             map (\export -> (export, ZephyrProgram (fromJust (HM.lookup export namesToInts)) symbolTbl)) allExports

    --     symbolTbl = V.fromList (zipWith CompiledZephyrSymbol qualifiedWords compiled)
    -- in (progs, schema)
