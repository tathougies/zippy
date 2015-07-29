{-# LANGUAGE TupleSections, OverloadedStrings #-}
module Database.Zippy.Zephyr.Compile where

import Database.Zippy.Types
import Database.Zippy.Zephyr.Types

import Control.Arrow
import Control.Applicative
import Control.Monad.State

import Data.Maybe
import Data.Monoid
import qualified Data.HashMap.Strict as HM
import qualified Data.Map as M
import qualified Data.Vector as V
import qualified Data.Text as T
import qualified Data.Set as S
import qualified Data.DList as D

genDefinitionsForType :: ZippyTyRef -> GenericZippyAlgebraicT ZippyTyVarName ZephyrScopedTy -> [ZephyrSymbolDefinition]
genDefinitionsForType tyRef (ZippyAlgebraicT tyName cons) = concatMap genDefinitionsForCon (zip [0..] (V.toList cons))
    where genDefinitionsForCon (conIndex, ZippyDataCon (ZippyDataConName conName) argTys) =
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
          genDefinitionsForArg (i, ZippyNamedField (ZippyDataArgName argName) _) =
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

collectInstantiatedTypes :: [GenericZippyAlgebraicT ZippyTyVarName ZephyrScopedTy] -> [GenericZippyAlgebraicT (ZippyFieldType RecZippyTyCon) (ZippyFieldType RecZippyTyCon)]
collectInstantiatedTypes zephyrTypes = S.toList (execState collectTypes S.empty)
    where collectTypes :: State (S.Set (GenericZippyAlgebraicT (ZippyFieldType RecZippyTyCon) (ZippyFieldType RecZippyTyCon))) ()
          collectTypes = mapM_ collectType zephyrTypes

          collectType :: GenericZippyAlgebraicT ZippyTyVarName ZephyrScopedTy -> State (S.Set (GenericZippyAlgebraicT (ZippyFieldType RecZippyTyCon) (ZippyFieldType RecZippyTyCon))) ()
          collectType ty@(ZippyAlgebraicT (ZippyTyCon tyName args) cons)
              | V.null args = collectType' HM.empty ty
              | otherwise = return ()

          collectType' :: HM.HashMap ZippyTyVarName (ZippyFieldType RecZippyTyCon) -> GenericZippyAlgebraicT ZippyTyVarName ZephyrScopedTy -> State (S.Set (GenericZippyAlgebraicT (ZippyFieldType RecZippyTyCon) (ZippyFieldType RecZippyTyCon))) ()
          collectType' locals ty@(ZippyAlgebraicT (ZippyTyCon tyName args) cons) =
              do let instantiatedTy = ZippyAlgebraicT (ZippyTyCon tyName (fmap resolveVar args)) instantiatedCons
                     instantiatedCons = fmap (fmap resolveScoped) cons

                     resolveVar varName = case HM.lookup varName locals of
                                            Nothing -> error ("cannot find type for " ++ show varName)
                                            Just x -> x
                     resolveScoped (Local varName) = resolveVar varName
                     resolveScoped (Global (SimpleFieldT s)) = SimpleFieldT s
                     resolveScoped (Global (RefFieldT (ZippyTyCon tyName args))) = RefFieldT (RecZippyTyCon (ZippyTyCon tyName (fmap resolveScoped args)))
                 modify (S.insert instantiatedTy)
                 V.mapM_ instantiateConstructorArgs instantiatedCons

          instantiateConstructorArgs :: GenericZippyDataCon (ZippyFieldType RecZippyTyCon) -> State (S.Set (GenericZippyAlgebraicT (ZippyFieldType RecZippyTyCon) (ZippyFieldType RecZippyTyCon))) ()
          instantiateConstructorArgs (ZippyDataCon conName args) = V.mapM_ (withFieldType instantiateConstructorArg) args

          withFieldType f (ZippyNamedField name x) = ZippyNamedField name <$> f x
          withFieldType f (ZippyUnnamedField x) = ZippyUnnamedField <$> f x

          instantiateConstructorArg :: ZippyFieldType RecZippyTyCon -> State (S.Set (GenericZippyAlgebraicT (ZippyFieldType RecZippyTyCon) (ZippyFieldType RecZippyTyCon))) ()
          instantiateConstructorArg (SimpleFieldT _) = return ()
          instantiateConstructorArg (RefFieldT (RecZippyTyCon (ZippyTyCon qTyName tyArgs))) =
              do case HM.lookup (tyName qTyName) allTypes of
                   Nothing -> fail ("Cannot find type " ++ show qTyName)
                   Just ty@(ZippyAlgebraicT (ZippyTyCon argTyName argNames) cons) ->
                       do let cons' = fmap (fmap (resolveTyVars locals)) cons
                              newType = ZippyAlgebraicT (ZippyTyCon argTyName tyArgs) cons'
                              locals = HM.fromList (V.toList (V.zip argNames tyArgs))
                          typesInstantiated <- get
                          if V.length argNames == V.length tyArgs
                             then if newType `S.member` typesInstantiated then return () else collectType' locals ty
                             else fail "Arity mismatch in type constructor"

                 return ()

          resolveTyVars :: HM.HashMap ZippyTyVarName (ZippyFieldType RecZippyTyCon) -> ZephyrScopedTy -> ZippyFieldType RecZippyTyCon
          resolveTyVars locals (Local name) =
              case HM.lookup name locals of
                Nothing -> error ("No such type variable: " ++ show name)
                Just x -> x
          resolveTyVars _ (Global (SimpleFieldT i)) = SimpleFieldT i
          resolveTyVars locals (Global (RefFieldT tyCon)) =
              let ZippyTyCon tyName tyArgs = tyCon
              in RefFieldT (RecZippyTyCon (ZippyTyCon tyName (fmap (resolveTyVars locals) tyArgs)))

          allTypes = HM.fromList $
                     map (\ty@(ZippyAlgebraicT (ZippyTyCon qTyName _) _) -> (tyName qTyName, ty)) zephyrTypes

compilePackages :: [ZephyrPackage] -> ZippyTyName -> (HM.HashMap ZephyrWord ZephyrProgram, ZippySchema)
compilePackages pkgs rootTyName =
    let namesToInts = HM.fromList (zip names [0..])
        qualifiedSymbols = mconcat (map (\pkg -> map (zephyrPackageName pkg,) (zephyrSymbols pkg ++ concatMap genDefinitionsForType' (zephyrTypes pkg))) pkgs)
        symbols = map snd qualifiedSymbols
        names = map zephyrSymbolName symbols

        resolveSymbol symbol = fromJust (HM.lookup symbol namesToInts <|> error ("Cannot find " ++ show symbol))

        compiled = map compiledSymbol symbols
        compiledSymbol (ZephyrSymbolDefinition _ builder) = compiledBuilder builder
        compiledBuilder (ZephyrBuilder d) =
            let shallowResolved = map (fmap resolveSymbol) (D.toList d)
                resolved = map (mapQuote compiledBuilder) shallowResolved
            in CompiledZephyr . V.fromList $ resolved

        qualifiedWords = map (uncurry ZephyrQualifiedWord . second zephyrSymbolName ) qualifiedSymbols

        qualifyType (ZippyAlgebraicT tyName cons) =
            ZippyAlgebraicT tyName (fmap (fmap qualifyScoped) cons)
        qualifyScoped (Local name) = Local name
        qualifyScoped (Global (SimpleFieldT s)) = Global (SimpleFieldT s)
        qualifyScoped (Global (RefFieldT (ZippyTyCon tyName args))) =
            Global (RefFieldT (ZippyTyCon (qualifyTyName tyName) (fmap qualifyScoped args) ))
        qualifyTyName tyName@(ZippyTyName pkg name)
            | T.null pkg = case HM.lookup name unqualifiedTypes of
                             Nothing -> error ("No package mentions the type " ++ show name)
                             Just (Unambiguous pkg)  -> ZippyTyName pkg name
                             Just (Ambiguous   pkgs) -> error ("The type " ++ show name ++ " is ambiguous. It is declared in " ++ show pkgs ++ ". Qualify the type using <pkg>:<name> syntax")
            | otherwise = tyName

        unqualifiedTypes = foldl insertQualifiedType HM.empty allTypes
        insertQualifiedType typeMap (ZippyAlgebraicT (ZippyTyCon (ZippyTyName pkg name) _) _) =
            case HM.lookup name typeMap of
              Nothing -> HM.insert name (Unambiguous pkg) typeMap
              Just (Ambiguous pkgs) -> HM.insert name (Ambiguous (pkg:pkgs)) typeMap
              Just (Unambiguous pkg') -> HM.insert name (Ambiguous [pkg, pkg']) typeMap

        allTypes = concatMap zephyrTypes pkgs
        allQualifiedTypes = fmap qualifyType allTypes
        allInstantiatedTypes = collectInstantiatedTypes allQualifiedTypes
        tyToTyRef :: M.Map (GenericZippyTyCon (ZippyFieldType RecZippyTyCon)) ZippyTyRef
        tyToTyRef = M.fromList $
                    zip (map (\(ZippyAlgebraicT qTy _) -> qTy) allInstantiatedTypes) (map ZippyTyRef [0..])

        Just rootTy = M.lookup (ZippyTyCon (qualifyTyName rootTyName) V.empty) tyToTyRef
        schema = let lookupFieldTy (SimpleFieldT s) = SimpleFieldT s
                     lookupFieldTy (RefFieldT ty) =
                         case M.lookup (unRecTy ty) tyToTyRef of
                           Just x -> RefFieldT x
                           Nothing -> error ("Could not find instantiation of " ++ show ty)
                 in ZippySchema rootTy (V.fromList (map (AlgebraicT . mapZippyAlgebraicT lookupFieldTy lookupFieldTy) allInstantiatedTypes))

        genDefinitionsForType' ty@(ZippyAlgebraicT qTy _) =
            --let Just tyRef = HM.lookup qTy tyToTyRef
            {-in-} genDefinitionsForType (ZippyTyRef 0) {- TODO How do we figure out the type reference if we don't know what the types are until run-time? -} ty

        allExports = concatMap zephyrExports pkgs
        progs = HM.fromList $
                map (\export -> (export, ZephyrProgram (fromJust (HM.lookup export namesToInts)) symbolTbl)) allExports

        symbolTbl = V.fromList (zipWith CompiledZephyrSymbol qualifiedWords compiled)
    in (progs, schema)
