{-# LANGUAGE OverloadedStrings #-}
module Main where

import Database.Zippy.Data
import Database.Zippy.Schema
import Database.Zippy.Persist
import Database.Zippy.Types

import Data.String

import System.IO
import System.Environment

main :: IO ()
main = do [schemaPath, roots, db] <- getArgs
          schema <- readSchemaFromFile schemaPath
          withBinaryFile roots AppendMode $ \rootsH ->
              withBinaryFile db ReadWriteMode $ \dbH ->
                  do let def = defaultForSchema schema
                     putStrLn ("Going to default db to " ++ showZippyD schema (eraseInMemoryD def))
                     (_, newRoot) <- writeZippyDToDisk dbH def
                     updateRoot rootsH newRoot
                     putStrLn ("Wrote root at " ++ show newRoot)