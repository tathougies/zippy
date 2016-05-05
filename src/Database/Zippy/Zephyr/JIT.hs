{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Database.Zippy.Zephyr.JIT where

import Prelude hiding (mapM, mapM_)

import Database.Zippy.Zephyr.Types
import Database.Zippy.Zephyr.TyCheck
import Database.Zippy.Zephyr.Internal

import Control.Monad.State
import Control.Monad.ST

import qualified Data.Map as M
import qualified Data.Vector as V
import Data.List (sortBy)
import Data.Ord (comparing)
import Data.Traversable (mapM)
import Data.Foldable (foldrM)
import Data.Monoid
import Data.STRef

import Debug.Trace

-- newtype JITGen s a = JITGen { runJITGen' :: JITGenState s -> ST s a }
--     deriving (Functor, Applicative, Monad, MonadFix)

-- data JITGenState s = JITGenState
--                    { jitGenStateCurName :: STRef s Int }

-- runJITGen :: JITGen s a -> ST s a
-- runJITGen (JITGen go) = do curName <- newSTRef 0
--                            go (JITGenState curName)

separateForAll :: ZephyrT k v -> ([v], ZephyrT k v)
separateForAll (ZephyrForAll k v t) = let (vs, t') = separateForAll t
                                      in (v:vs, t')
separateForAll t = ([], t)

generateJitEndpoints :: ZephyrSymbolEnv Int
                     -> V.Vector (ZephyrT ZephyrStackAtomK ZephyrTyVar, OpTypes, CompiledZephyrSymbol)
                     -> ZephyrTyCheckM s ()
generateJitEndpoints env syms =
    do mapM doCompile syms
       pure ()

    where doCompile (ty, UserDefined opTypes, CompiledZephyrSymbol name ops) =
              do ty' <- simplifyZephyrT ty
                 let (existentialVars, nonExistentialType) = separateForAll ty'
                     varKinds = kindedVariables ty'

                     onlyStack = all (\var -> case M.lookup var varKinds of
                                                Just ZephyrStackK -> True
                                                _ -> False) existentialVars
                 if onlyStack
                    then trace ("[JIT] Symbol " <> show name <> ": " <> ppZephyrTy ty') (pure ())
                    else trace ("[JIT] Symbol " <> show name <> ": trampoline") (pure ())
          doCompile (_, Builtin, CompiledZephyrSymbol name _) =
              trace ("[JIT] Symbol " <> show name <> ": builtin") (pure ())
