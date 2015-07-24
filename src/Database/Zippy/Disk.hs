module Database.Zippy.Disk
    ( --zippyDiskCoordinator,

      coordinateCommitRoot
    , coordinateReadZippyD
    , coordinateWriteZippyD

    , peekCache
    , lookupCache

    , cacheHitsV, cacheMissesV ) where

import Database.Zippy.Persist
import Database.Zippy.Types

import Control.Applicative
import Control.Monad
import Control.Concurrent.Chan
import Control.Concurrent.MVar

import Data.Word
import Data.List (foldl')
import Data.Time.Clock.POSIX
import Data.IORef
import qualified Data.HashPSQ as PSQ

import System.IO.Unsafe

cacheHitsV, cacheMissesV :: IORef Int
{-# NOINLINE cacheHitsV #-}
{-# NOINLINE cacheMissesV #-}
cacheHitsV = unsafePerformIO (newIORef 0)
cacheMissesV = unsafePerformIO (newIORef 0)

lookupCache :: ZippyDiskCache -> Word64 -> IO (Maybe (InMemoryD, ZippyDiskCache))
lookupCache cache offset =
    case PSQ.lookup offset (diskCache cache) of
      Just (_, v) -> do modifyIORef' cacheHitsV (+1)
                        curTime <- getPOSIXTime
                        let cache' = cache { diskCache = PSQ.insert offset curTime v (diskCache cache) }
                        return (Just (v, cache'))
      Nothing -> do modifyIORef' cacheMissesV (+1)
                    return Nothing

peekCache :: Word64 -> ZippyDiskCache -> Maybe InMemoryD
peekCache diskOffs cache = snd <$> PSQ.lookup diskOffs (diskCache cache)

inMemoryDSize :: InMemoryD -> Word64
inMemoryDSize _ = 1

insertIntoCache :: ZippyDiskCache -> POSIXTime -> Word64 -> InMemoryD -> ZippyDiskCache
insertIntoCache cache time offs dt =
    let cache' = cache { diskCache = PSQ.insert offs time dt (diskCache cache)
                       , diskCacheSize = diskCacheSize cache + inMemoryDSize dt }
        cache'' = evictLRU cache'
    in cache''

evictLRU :: ZippyDiskCache -> ZippyDiskCache
evictLRU !cache
    | diskCacheSize cache > diskCacheMaxSize cache =
        let Just (_, _, deleted, cache') = PSQ.minView (diskCache cache)
        in evictLRU (cache { diskCache = cache', diskCacheSize = diskCacheSize cache - inMemoryDSize deleted })
    | otherwise = cache

coordinateCommitRoot :: ZippyDiskState -> Word64 -> IO ZippyDiskState
coordinateCommitRoot st@(ZippyDiskState rootsH _ _) newRoot =
    do updateRoot rootsH newRoot
       return st

coordinateReadZippyD :: ZippyDiskState -> ZippyT -> Word64 -> IO (InMemoryD, ZippyDiskState)
coordinateReadZippyD (ZippyDiskState rootsH dataH cache) dataType diskOffs =
    do res <- lookupCache cache diskOffs
       case res of
         Just (x, cache') -> return (x, ZippyDiskState rootsH dataH cache')
         Nothing -> do ret <- readZippyDFromDisk dataH dataType diskOffs
                       curTime <- getPOSIXTime
                       let cache' = insertIntoCache cache curTime diskOffs ret
                       return (ret, ZippyDiskState rootsH dataH cache')

coordinateWriteZippyD :: ZippyDiskState -> InMemoryD -> IO (Word64, ZippyDiskState)
coordinateWriteZippyD (ZippyDiskState rootsH dataH cache) zippyD =
                       do (onDiskEntities, pos) <- writeZippyDToDisk dataH zippyD
                          curTime <- getPOSIXTime
                          let cache' = foldl' (\cache (diskOff, diskEnt) -> insertIntoCache cache curTime diskOff diskEnt) cache onDiskEntities
                          return (pos, ZippyDiskState rootsH dataH cache')
