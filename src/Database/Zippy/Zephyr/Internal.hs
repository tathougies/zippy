{-# LANGUAGE GeneralizedNewtypeDeriving, OverloadedStrings #-}
module Database.Zippy.Zephyr.Internal where

import Prelude hiding (mapM)

import Database.Zippy.Types
import Database.Zippy.Zephyr.Types

import Control.Applicative
import Control.Monad.State hiding (mapM)

import Data.Monoid
import Data.Text (Text)
import Data.Traversable (mapM)
import qualified Data.DList as D
import qualified Data.Map as M
import qualified Data.HashMap.Strict as HM
import qualified Data.Text as T
import qualified Data.Vector as V

import Debug.Trace

data QualificationType = Unambiguous Text
                       | Ambiguous [Text]
                         deriving Show

newtype ZephyrInstantiatedType = ZephyrInstantiatedType { unwrapInstantiatedType ::
                                                              GenericZippyTyCon (ZippyFieldType ZephyrInstantiatedType) }
    deriving (Show, Eq, Ord)

type ZephyrUninstantiatedType = GenericZippyAlgebraicT ZippyTyVarName ZephyrScopedTy

type ZephyrInternedType = GenericZippyTyCon (ZippyFieldType ZippyTyRef)

data ZephyrTypeLookupEnv =
    ZephyrTypeLookupEnv
    { qualifiedUninstantiatedTypes :: HM.HashMap ZippyTyName ZephyrUninstantiatedType
    , unqualifiedTypePackages :: HM.HashMap Text QualificationType }
    deriving Show

data ZephyrSymbolEnv v =
    ZephyrSymbolEnv
    { qualifiedSymbols :: HM.HashMap (ZephyrWord, ZephyrWord) v
    , unqualifiedSymbolPackages :: HM.HashMap ZephyrWord QualificationType }
    deriving Show

data ZephyrTypeInstantiationEnv =
    ZephyrTypeInstantiationEnv
    { alreadyInstantiated :: M.Map ZephyrInstantiatedType Int
    , instantiatedTypesList :: D.DList ZephyrInstantiatedType
    , instantiatedCount :: Int }
    deriving (Show)

tyEnvFromList :: [ZephyrUninstantiatedType] -> ZephyrTypeLookupEnv
tyEnvFromList types = ZephyrTypeLookupEnv allTypes qualified
    where allTypes = HM.fromList $
                     map (\ty@(ZippyAlgebraicT (ZippyTyCon name _) _) -> (name, ty)) types
          qualified = foldl insertQualified HM.empty types

          insertQualified types (ZippyAlgebraicT (ZippyTyCon (ZippyTyName pkg unqualifiedName) _) _) =
              case HM.lookup unqualifiedName types of
                Just (Ambiguous pkgs) -> HM.insert unqualifiedName (Ambiguous (pkg:pkgs)) types
                Just (Unambiguous pkg') -> HM.insert unqualifiedName (Ambiguous [pkg, pkg']) types
                Nothing -> HM.insert unqualifiedName (Unambiguous pkg) types

emptyZephyrTypeInstantiationEnv = ZephyrTypeInstantiationEnv mempty mempty 0

lookupInTyEnv :: ZippyTyName -> ZephyrTypeLookupEnv -> Maybe ZephyrUninstantiatedType
lookupInTyEnv (ZippyTyName "" unqualified) env =
    case HM.lookup unqualified (unqualifiedTypePackages env) of
      Nothing -> fail ("Could not find unqualified type " ++ T.unpack unqualified)
      Just (Unambiguous pkg) -> lookupInTyEnv (ZippyTyName pkg unqualified) env
      Just (Ambiguous pkgs) -> fail ("Unqualified type " ++ T.unpack unqualified ++ " is ambiguous. Exists in " ++ show pkgs)
lookupInTyEnv tyName env = HM.lookup tyName (qualifiedUninstantiatedTypes env)

qualifyTy :: ZippyTyName -> ZephyrTypeLookupEnv -> ZippyTyName
qualifyTy name env = case lookupInTyEnv name env of
                       Just (ZippyAlgebraicT (ZippyTyCon qName _) _) -> qName
                       Nothing -> error ("Could not find " ++ show name)

fullyQualifyTy :: ZephyrTypeLookupEnv -> ZephyrInstantiatedType -> ZephyrInstantiatedType
fullyQualifyTy types (ZephyrInstantiatedType (ZippyTyCon tyName args)) =
    ZephyrInstantiatedType (ZippyTyCon (qualifyTy tyName types) (fmap qualifyTyArg args))
    where qualifyTyArg (SimpleFieldT s) = SimpleFieldT s
          qualifyTyArg (RefFieldT r) = RefFieldT $ fullyQualifyTy types r

qualifyConArgTypes :: ZephyrTypeLookupEnv -> GenericZippyAlgebraicT ZippyTyVarName ZephyrScopedTy -> GenericZippyAlgebraicT ZippyTyVarName ZephyrScopedTy
qualifyConArgTypes types (ZippyAlgebraicT tyName cons) = ZippyAlgebraicT tyName (fmap qualifyCon cons)
    where qualifyCon (ZippyDataCon conName conArgs) =
              ZippyDataCon conName (fmap (fmap (qualifyArg types)) conArgs)

qualifyTyCon :: ZephyrTypeLookupEnv -> GenericZippyTyCon ZephyrScopedTy -> GenericZippyTyCon ZephyrScopedTy
qualifyTyCon types (ZippyTyCon tyName tyArgs) = ZippyTyCon (qualifyTy tyName types) (fmap (qualifyArg types) tyArgs)

qualifyArg :: ZephyrTypeLookupEnv -> ZephyrScopedTy -> ZephyrScopedTy
qualifyArg _ (Local x) = Local x
qualifyArg types (Global f) = Global $ qualifyField types f

qualifyField _ (SimpleFieldT s) = SimpleFieldT s
qualifyField types (RefFieldT tyCon) = RefFieldT (qualifyTyCon types tyCon)

typesInEnv :: ZephyrTypeLookupEnv -> [ZephyrUninstantiatedType]
typesInEnv = HM.elems . qualifiedUninstantiatedTypes

alreadyInstantiatedInEnv :: ZephyrInstantiatedType -> ZephyrTypeLookupEnv -> ZephyrTypeInstantiationEnv -> Bool
alreadyInstantiatedInEnv ty types (ZephyrTypeInstantiationEnv { alreadyInstantiated = alreadyInstantiated }) =
    fullyQualifyTy types ty `M.member` alreadyInstantiated

internType :: ZephyrTypeLookupEnv -> ZephyrTypeInstantiationEnv -> ZephyrInstantiatedType -> (ZippyTyRef, ZephyrTypeInstantiationEnv)
internType types env ty = runState (collectType ty) env
    where collectType :: ZephyrInstantiatedType -> State ZephyrTypeInstantiationEnv ZippyTyRef
          collectType ty =
              let qTy = fullyQualifyTy types ty
              in M.lookup qTy <$> gets alreadyInstantiated >>= \typeRes ->
                  case typeRes of
                    Nothing -> doInstantiation qTy
                    Just i -> pure (ZippyTyRef i)

          doInstantiation ty@(ZephyrInstantiatedType (ZippyTyCon tyName args)) =
              do newRef <- insertType ty
                 mapM collectTypeArg args
                 return newRef

          collectTypeArg (SimpleFieldT s) = pure (SimpleFieldT s)
          collectTypeArg (RefFieldT argTy) =
              RefFieldT <$> collectType argTy

          insertType :: ZephyrInstantiatedType -> State ZephyrTypeInstantiationEnv ZippyTyRef
          insertType internedType = modify (\env ->
                                            let newTyRef = instantiatedCount env
                                            in env { alreadyInstantiated = M.insert internedType newTyRef (alreadyInstantiated env)
                                                   , instantiatedTypesList = instantiatedTypesList env <> D.singleton internedType
                                                   , instantiatedCount = newTyRef + 1 }) >>
                                    collectType internedType

lookupInSymbolEnv :: Either ZephyrWord (ZephyrWord, ZephyrWord) -> ZephyrSymbolEnv v -> Maybe v
lookupInSymbolEnv (Right qualified) env = HM.lookup qualified (qualifiedSymbols env)
lookupInSymbolEnv (Left unqualified) env =
    case HM.lookup unqualified (unqualifiedSymbolPackages env) of
      Just (Unambiguous pkg) -> lookupInSymbolEnv (Right (ZephyrWord pkg, unqualified)) env
      Just (Ambiguous pkgs) -> error ("The symbol " ++ show unqualified ++ " is ambiguous and appears in " ++ show pkgs)
      Nothing -> Nothing

buildSymbolEnv :: [((ZephyrWord, ZephyrWord), v)] -> ZephyrSymbolEnv v
buildSymbolEnv symbols = ZephyrSymbolEnv (HM.fromList symbols) qualifiedInfo
    where qualifiedInfo = foldl insertQualificationInfo HM.empty symbols

          insertQualificationInfo qualifiedInfo ((ZephyrWord pkg, name), v) =
              case HM.lookup name qualifiedInfo of
                Nothing -> HM.insert name (Unambiguous pkg) qualifiedInfo
                Just (Unambiguous pkg') -> HM.insert name (Ambiguous [pkg, pkg']) qualifiedInfo
                Just (Ambiguous pkgs) -> HM.insert name (Ambiguous (pkg:pkgs)) qualifiedInfo

