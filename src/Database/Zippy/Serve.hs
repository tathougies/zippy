{-# LANGUAGE RecordWildCards, OverloadedStrings #-}
module Database.Zippy.Serve where

import Database.Zippy.Schema
import Database.Zippy.Types
import Database.Zippy.Transaction
import Database.Zippy.Data
import Database.Zippy.Containers.Treap
import Database.Zippy.Disk
import Database.Zippy.Zephyr

import Prelude hiding (lines)

import Control.Applicative
import Control.Concurrent hiding (yield)
import Control.Concurrent.Chan
import Control.Monad.Free
import Control.Monad
import Control.Monad.Trans

import Data.ByteString (ByteString)
import Data.Conduit
import Data.Char
import Data.Conduit.Binary
import Data.Conduit.Network (sourceSocket, sinkSocket)
import Data.IORef
import Data.String hiding (lines)
import Data.Word
import Data.Int
import Data.Monoid
import Data.Text (Text)
import qualified Data.Text.Encoding as TE

import Data.Attoparsec as Atto
import Data.Attoparsec.ByteString

import qualified Data.HashMap.Strict as HM
import qualified Data.Conduit.List as CL
import qualified Data.ByteString.Char8 as BS

import Foreign.Marshal.Alloc
import Foreign.Storable

import Network.Simple.TCP (listen, HostPreference(..))
import Network.Socket hiding (listen)

import System.IO
import System.Log.Logger
import System.Random
import System.Directory
import System.FilePath

import Text.Read hiding (lift)
import qualified Text.Parsec as Parsec
--import Text.Parsec.ByteString

data ZippyServeSettings =
    ZippyServeSettings
    { rootsPath  :: FilePath
    , dataPath   :: FilePath

    , serverAddress :: HostPreference
    , serverPort    :: Int

    , dataCacheSize :: Word64

    , zephyrPackageDirectory :: FilePath
    , zephyrRootTyName :: ZippyTyName}

data ServeCmd = MoveUpCmd
              | MoveDownCmd !Int
              | CurCmd
              | ReplaceCmd !ByteString
              | CommitCmd
              | FindInTreapCmd !Int64
              | InsertInTreapCmd !Int64 !Text
              | ZephyrQueryCmd !Text !ByteString
              | ListZephyrCmds
                deriving (Show)

type ServeM = IO

data TxAbortReason = TxCannotMerge
                   | TxUserAborted
                     deriving Show

data TxStatus a = TxReturned a
                | TxAborted !TxAbortReason
                | TxCommitted
                  deriving Show

commitAndWaitForStatus :: TxnStepsChan -> TxnId -> IO TxCommitStatus
commitAndWaitForStatus txnsChan txnId =
    do status <- newEmptyMVar
       writeChan txnsChan (TxnStepCommit txnId status)
       takeMVar status -- The MVar will be updated when the commit goes through

cmdP :: ZippySchema -> ZippyT -> Parser ServeCmd
cmdP sch curTy = {-# SCC cmdP #-}
                 (pure MoveUpCmd <* string "up") <|>
                 (MoveDownCmd <$> (string "down " *> decimal)) <|>
                 (ReplaceCmd <$> (string "replace" *> spaces *> Atto.takeWhile (const True))) <|>
                 (FindInTreapCmd <$> (string "find" *> spaces *> decimal)) <|>
                 (InsertInTreapCmd <$> (string "insert" *> spaces *> decimal) <*> (spaces *> parseTextD)) <|>
                 (pure CurCmd <* string "cur") <|>
                 (pure CommitCmd <* string "commit") <|>
                 (pure ListZephyrCmds <* string "list-queries") <|>
                 (ZephyrQueryCmd . TE.decodeUtf8  <$> (string "query" *> spaces *> Atto.takeWhile1 (not . isSpace . chr . fromIntegral)) <*> (spaces *> Atto.takeWhile (const True)))
                 <?> "Zippy command"

           where spaces = takeWhile1 (\c -> c == fromIntegral (ord ' ') || c == fromIntegral (ord '\t'))
                 decimal :: Integral a => Parser a
                 decimal = do c <- satisfy (isDigit . chr . fromIntegral)
                              decimal' (fromIntegral (fromIntegral c - ord '0'))
                 decimal' i = do next <- peekWord8
                                 case next of
                                   Just c
                                     | isDigit (chr (fromIntegral c)) ->
                                         anyWord8 *> decimal' (i * 10 + fromIntegral (fromIntegral c - ord '0'))
                                   _ -> return i

                 parseTextD = TE.decodeUtf8 <$>
                              (word8 (fromIntegral (ord '"')) *>
                               Atto.takeWhile (\c -> c /= fromIntegral (ord '"'))
                               <* word8 (fromIntegral (ord '"')))

serveRequest :: TxnStepsChan -> TxnId -> ZephyrExports -> ZippySchema -> (ZippyT, ByteString) -> ByteString -> ServeM (ZippyT, ByteString)
serveRequest txnsChan txnId exportedZephyr sch (curTy, _) cmd =
    case parseOnly (cmdP sch curTy) cmd of
      Left err -> return (curTy, fromString ("Cannot parse this cmd: " ++ show err ++ "\n"))
      Right MoveUpCmd -> do res <- interpretTxAsync sch ResyncAfterTx txnsChan txnId (move Up)
                            let (res', newTy) = case res of
                                                  Moved newTy -> ("Moved\n", newTy)
                                                  _ -> (fromString (show res ++ "\n"), curTy)
                            return (newTy, res')
      Right (MoveDownCmd i) -> do res <- interpretTxAsync sch ResyncAfterTx txnsChan txnId (move (Down i))
                                  let (res', newTy) = case res of
                                                        Moved newTy -> ("Moved\n", newTy)
                                                        _ -> (fromString (show res ++ "\n"), curTy)
                                  return (newTy, res')
      Right CurCmd -> do infoM "serveRequest" "Running CurCmd"
                         res <- interpretTxAsync sch ResyncAfterTx txnsChan txnId cur
                         return (curTy, fromString (show res ++ "\n"))
      Right (ReplaceCmd d) ->
          case Parsec.parse (parseZippyD curTy sch) "<network>" d of
            Left err -> return (curTy, "Could not parse data of type " <> fromString (show curTy))
            Right d -> do infoM "serveRequest" ("Replace with " ++ show d)
                          res <- interpretTxAsync sch ResyncAfterTx txnsChan txnId (move (Replace d))
                          return (curTy, fromString (show res ++ "\n"))
      Right (FindInTreapCmd i) -> do infoM "serveRequest" ("Find in treap " ++ show i)
                                     res <- interpretTxAsync sch ResyncAfterTx txnsChan txnId (treapFind 0 (atomCmp (InMemoryD (IntegerD i))))
                                     return (curTy, fromString (show res ++ "\n"))
      Right (InsertInTreapCmd i t) -> do infoM "serveRequest" ("Insert in treap " ++ show i ++ " " ++ show t)
                                         prio <- randomIO
                                         res <- interpretTxAsync sch DontResyncAfterTx txnsChan txnId (treapInsert prio (InMemoryD (IntegerD i)) (InMemoryD (TextD t)) >> commit)
                                         return (curTy, fromString (show res ++ "\n"))
      Right CommitCmd -> do infoM "serveRequest" "Requesting commit"
                            status <- commitAndWaitForStatus txnsChan txnId
                            return (curTy, fromString (show status ++ "\n"))
      Right ListZephyrCmds ->
          do let keys = map (\(ZephyrWord t) -> TE.encodeUtf8 t) (HM.keys exportedZephyr)
             return (curTy, "QUERIES " <> BS.intercalate " " keys <> "\n")
      Right (ZephyrQueryCmd cmdName stk) ->
          do infoM "serveRequest" "testing zephyr"
             case parseZephyrStack stk of
               Left err -> return (curTy, fromString ("error parsing stack: " ++ show err ++ "\n"))
               Right stk ->
                   case HM.lookup (ZephyrWord cmdName) exportedZephyr of
                     Just zephyrProg -> do res <- interpretTxAsync sch ResyncAfterTx txnsChan txnId (runZephyr zephyrProg sch stk)
                                           return (curTy, fromString (show res ++ "\n"))
                     Nothing -> return (curTy, fromString ("No such zephyr query: " ++ show cmdName))

statefulConduit :: Monad m => (b -> a -> m b) -> b -> Conduit a m b
statefulConduit f st = await >>= \x ->
                       case x of
                         Nothing -> return ()
                         Just x  -> do st' <- lift (f st x)
                                       yield st'
                                       statefulConduit f st'

serveClient :: TxnStepsChan -> TxnId -> ZephyrExports -> ZippySchema -> (Socket, SockAddr) -> ServeM ()
serveClient txnsChan txnId exportedZephyr sch (sock, sockAddr) =
    do infoM "serveClient" ("New connection from " ++ show sockAddr)
       sourceSocket sock $= lines $= statefulConduit (serveRequest txnsChan txnId exportedZephyr sch) (zippySchemaRootType sch, BS.empty) $= CL.map snd $$ sinkSocket sock
       close sock

findRootFromRootsFile :: FilePath -> IO Word64
findRootFromRootsFile fp = withBinaryFile fp ReadWriteMode $ \h ->
                           do hSeek h SeekFromEnd (-8)
                              alloca $ \p ->
                                  do b <- hGetBuf h p 8
                                     infoM "findRootFromRootsFile" ("Read " ++ show b ++ " bytes")
                                     peek p

loadZephyrPackages :: FilePath -> IO [ZephyrPackage]
loadZephyrPackages zephyrDir =
    do files <- getDirectoryContents zephyrDir
       let zephyrFiles = filter ((== ".zephyr") . takeExtension) files
           loadZephyrPackage fp = do res <- readZephyrPackage (zephyrDir </> fp)
                                     case res of
                                       Left err -> fail (show err)
                                       Right x -> pure x
       mapM loadZephyrPackage zephyrFiles

serveZippy :: ZippyServeSettings -> IO ()
serveZippy (ZippyServeSettings { .. }) =
    do infoM "serveZippy" "Looking for initial root..."
       initialRoot <- findRootFromRootsFile rootsPath
       infoM "serveZippy" ("Found root at " ++ show initialRoot)

       rootH <- openBinaryFile rootsPath AppendMode
       dataH <- openBinaryFile dataPath ReadWriteMode

       stepsChan <- newChan
       txns <- newIORef HM.empty
       rootsPtr <- newIORef initialRoot
       diskStateRef <- newIORef (ZippyDiskState rootH dataH (emptyDiskCache dataCacheSize))
       txnIds <- newMVar (TxnId 0)
       let nextTxnId = do ret@(TxnId id) <- takeMVar txnIds
                          let nextId = TxnId (id + 1)
                          putMVar txnIds (nextId `seq` nextId)
                          return ret

       zephyrPackages <- loadZephyrPackages zephyrPackageDirectory
       let (exports, schema) = compilePackages zephyrPackages zephyrRootTyName

       infoM "serveZippy" ("Loaded packages " ++ show (map zephyrPackageName zephyrPackages))

       let st = ZippyState txns rootsPtr diskStateRef schema

       -- Start transaction server
       infoM "serveZippy" "Starting transaction coordinator thread..."
       forkIO (txnServe stepsChan st)

       -- Start network server
       listen serverAddress (show serverPort) $ \(sock, listenAddr) ->
           do infoM "serveZippy" ("Starting server on " ++ show listenAddr)
              forever $ do
                info <- accept sock
                txnId <- nextTxnId
                forkIO (serveClient stepsChan txnId exports schema info)
