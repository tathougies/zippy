{-# LANGUAGE OverloadedStrings #-}
module Main where

import Database.Zippy.Data
import Database.Zippy.Schema
import Database.Zippy.Persist
import Database.Zippy.Types
import Database.Zippy.Zephyr
import Database.Zippy.Serve

import Data.String
import Data.Monoid

import System.IO
import System.Environment

main :: IO ()
main = do [pkgsPath, rootTyName, roots, db] <- getArgs
          packages <- loadZephyrPackages pkgsPath
          case compilePackages packages (ZippyTyCon (ZippyTyName "" (fromString rootTyName)) mempty) of
            Left (ZephyrCompileErrorTy err) ->
                let showError (locs, err) = "At " ++ show locs ++ ":\n" ++ showError' err
                    showError' (KindMismatch ty1 ty2) = "Kind mismatch between " ++ show (kindOf ty1) ++ " and " ++ show (kindOf ty2) ++ " " ++ show ty1 ++ " " ++ show ty2
                    showError' x = show x
                in putStrLn (showError err)
            Right (_, schema) ->
                withBinaryFile roots AppendMode $ \rootsH ->
                    withBinaryFile db ReadWriteMode $ \dbH ->
                        do let def = defaultForSchema schema
                           putStrLn ("Going to default db to " ++ showZippyD schema (eraseInMemoryD def))
                           (_, newRoot) <- writeZippyDToDisk dbH def
                           updateRoot rootsH newRoot
                           putStrLn ("Wrote root at " ++ show newRoot)
