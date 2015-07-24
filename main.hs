{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Concurrent
import Control.Concurrent.MVar

import Database.Zippy.Serve (ZippyServeSettings (..), serveZippy)
import Database.Zippy.Persist
import Database.Zippy.Disk

import Data.String
import Data.IORef

import Options.Applicative

import System.Log.Logger
import System.Posix.Signals (installHandler, Handler(Catch), sigINT, sigTERM)
import System.Exit

data Verbosity = Normal | Verbose
data StatsRecording = StatsOn | StatsOff
data ZippyServeCmdLine = ZippyServeCmdLine ZippyServeSettings Verbosity StatsRecording

opts :: ParserInfo ZippyServeCmdLine
opts = info (helper <*> (ZippyServeCmdLine <$> settings <*> verbosity <*> stats)) (fullDesc <> progDesc "Run a zippy server for the given data structure" <> header "zippy-serve -- run zippy database servers")
    where settings = ZippyServeSettings
                 <$> (strOption (long "roots-path" <> short 'r' <> metavar "ROOTPATH" <> help "Path to roots.db") <|> pure "roots.db")
                 <*> (strOption (long "data-path" <> short 'd' <> metavar "DATAPATH" <> help "Path to data.db") <|> pure "data.db")
                 <*> (strOption (long "schema-path" <> short 's' <> metavar "SCHEMAPATH" <> help "Path to schema.txt") <|> pure "schema.txt")
                 <*> (fromString <$> (strOption (long "host" <> short 'h' <> metavar "HOST" <> help "host to bind on") <|> pure "*"))
                 <*> (argument auto (metavar "PORT" <> help "Port to bind to"))
                 <*> (read <$> strOption (long "cache-size" <> short 'C' <> metavar "SIZE" <> help "Cache size") <|> pure 1000000)
                 <*> (strOption (long "zephyr-dir" <> short 'Z' <> metavar "ZEPHYR-PATH" <> help "Path to zephyr packages"))

          verbosity = flag Normal Verbose (long "verbose" <> short 'v')
          stats = flag StatsOff StatsOn (long "stats" <> short 'S')

handler :: MVar () -> IO ()
handler x = do putStrLn "Terminating..."

               readTimeT <- readIORef readTime
               writeTimeT <- readIORef writeTime
               cacheMissesT <- readIORef cacheMissesV
               cacheHitsT <- readIORef cacheHitsV

               putStrLn ("\tread time: " ++ show readTimeT)
               putStrLn ("\twrite time: " ++ show writeTimeT)
               putStrLn "CACHE:"
               putStrLn ("\tcache hits: " ++ show cacheHitsT)
               putStrLn ("\tcache misses: " ++ show cacheMissesT)
               putMVar x ()

main :: IO ()
main = do ZippyServeCmdLine serveSettings verbosity stats <- execParser opts
          case verbosity of
            Verbose -> updateGlobalLogger rootLoggerName (setLevel DEBUG)
            _ -> return ()
          case stats of
            StatsOn -> do doExit <- newEmptyMVar
                          installHandler sigINT (Catch (handler doExit)) Nothing
                          forkIO (serveZippy serveSettings)
                          takeMVar doExit
            _ -> serveZippy serveSettings
