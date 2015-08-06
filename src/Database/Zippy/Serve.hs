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
import qualified Control.Exception as E

import Data.ByteString (ByteString)
import Data.ByteString.Builder hiding (word8)
import Data.Conduit
import Data.Char
import Data.Conduit.Binary
import Data.Conduit.Network (sourceSocket, sinkSocket)
import Data.Conduit.ByteString.Builder
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
              | NewTxnCmd
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
                 (ZephyrQueryCmd . TE.decodeUtf8  <$> (string "query" *> spaces *> Atto.takeWhile1 (not . isSpace . chr . fromIntegral)) <*> (spaces *> Atto.takeWhile (const True))) <|>
                 (pure NewTxnCmd <* string "begin")
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

requestServer :: TxnStepsChan -> TxnId -> IO TxnId -> ZephyrExports -> ZippySchema -> ZippyT -> Conduit ByteString ServeM ByteString
requestServer txnsChan txnId nextTxnId exportedZephyr sch curTy =
    await >>= \x ->
    case x of
      Nothing -> return ()
      Just cmd ->
        case parseOnly (cmdP sch curTy) cmd of
          Left err -> yield (fromString ("Cannot parse this cmd: " ++ show err ++ "\n")) >>
                      continueWithType curTy
          Right MoveUpCmd -> do res <- lift $ interpretTxAsync sch ResyncAfterTx txnsChan simpleTxActionLogger txnId (move Up)
                                let (res', newTy) = case res of
                                                      Moved newTy -> ("Moved\n", newTy)
                                                      _ -> (fromString (show res ++ "\n"), curTy)
                                yield res'
                                continueWithType newTy
          Right (MoveDownCmd i) -> do res <- lift $ interpretTxAsync sch ResyncAfterTx txnsChan simpleTxActionLogger txnId (move (Down i))
                                      let (res', newTy) = case res of
                                                            Moved newTy -> ("Moved\n", newTy)
                                                            _ -> (fromString (show res ++ "\n"), curTy)
                                      yield res'
                                      continueWithType newTy
          Right CurCmd -> do liftIO $ infoM "serveRequest" "Running CurCmd"
                             res <- lift $ interpretTxAsync sch ResyncAfterTx txnsChan simpleTxActionLogger txnId cur
                             yield (fromString (show res ++ "\n"))
                             continueWithType curTy
          Right (ReplaceCmd d) ->
              case Parsec.parse (parseZippyD curTy sch) "<network>" d of
                Left err -> yield ("Could not parse data of type " <> fromString (show curTy)) >>
                            continueWithType curTy
                Right d -> do liftIO $ infoM "serveRequest" ("Replace with " ++ show d)
                              res <- lift $ interpretTxAsync sch ResyncAfterTx txnsChan simpleTxActionLogger txnId (move (Replace d))
                              yield (fromString (show res ++ "\n"))
                              continueWithType curTy
          Right (FindInTreapCmd i) -> do liftIO $ infoM "serveRequest" ("Find in treap " ++ show i)
                                         res <- lift $ interpretTxAsync sch ResyncAfterTx txnsChan simpleTxActionLogger txnId (treapFind 0 (atomCmp (InMemoryD (IntegerD i))))
                                         yield (fromString (show res ++ "\n"))
                                         continueWithType curTy
          Right (InsertInTreapCmd i t) -> do liftIO $ infoM "serveRequest" ("Insert in treap " ++ show i ++ " " ++ show t)
                                             prio <- liftIO randomIO
                                             res <- lift $ interpretTxAsync sch DontResyncAfterTx txnsChan simpleTxActionLogger txnId (treapInsert prio (InMemoryD (IntegerD i)) (InMemoryD (TextD t)) >> commit)
                                             yield (fromString (show res ++ "\n"))
                                             continueWithType curTy
          Right CommitCmd -> do liftIO $ infoM "serveRequest" "Requesting commit"
                                status <- lift $ commitAndWaitForStatus txnsChan txnId
                                yield (fromString (show status ++ "\n"))
                                continueWithType curTy
          Right NewTxnCmd -> do txnId <- liftIO nextTxnId
                                yield "BEGIN\n"
                                requestServer txnsChan txnId nextTxnId exportedZephyr sch (zippySchemaRootType sch)
          Right ListZephyrCmds ->
              do let keys = map (\(ZephyrWord t) -> TE.encodeUtf8 t) (HM.keys exportedZephyr)
                 yield ("QUERIES " <> BS.intercalate " " keys <> "\n")
                 continueWithType curTy
          Right (ZephyrQueryCmd cmdName stk) ->
              do liftIO $ infoM "serveRequest" "testing zephyr"
                 case parseZephyrStack stk of
                   Left err -> yield (fromString ("error parsing stack: " ++ show err ++ "\n")) >>
                               continueWithType curTy
                   Right stk ->
                       case HM.lookup (ZephyrWord cmdName) exportedZephyr of
                         Just zephyrProg -> do rawLogChan <- liftIO newChan
                                               wireLogChan <- liftIO newChan
                                               resV <- liftIO newEmptyMVar

                                               liftIO (forkIO (interpretTxAsync sch ResyncAfterTx txnsChan (txResultActionLogger rawLogChan) txnId (runZephyr zephyrProg sch stk) >>= \res ->
                                                               writeChan rawLogChan Nothing >> putMVar resV res))
                                               liftIO (forkIO (buildWireBuilders curTy sch txnId txnsChan rawLogChan wireLogChan))

                                               let getBuilders = do res <- liftIO (readChan wireLogChan)
                                                                    case res of
                                                                      Just builder -> yield builder >>
                                                                                      getBuilders
                                                                      Nothing -> return ()
                                                   liftYield = await >>= \x ->
                                                               case x of
                                                                 Nothing -> return ()
                                                                 Just x -> lift (yield x) >> liftYield

                                               getBuilders $= CL.map (\x -> byteString "RES " <> x <> byteString "\n") $= builderToByteString $$ liftYield
                                               res <- liftIO (takeMVar resV)
                                               yield ("ALL DONE" <> fromString (show res) <> "\n")
                                               continueWithType curTy
                         Nothing -> yield (fromString ("No such zephyr query: " ++ show cmdName ++ "\n")) >>
                                    continueWithType curTy

    where continueWithType curTy' = requestServer txnsChan txnId nextTxnId exportedZephyr sch curTy

buildWireBuilders :: ZippyT -> ZippySchema -> TxnId -> TxnStepsChan -> Chan (Maybe Zipper) -> Chan (Maybe Builder) -> IO ()
buildWireBuilders curTy sch txnId txnsChan zChan builderChan = emptyAsyncDiskState txnsChan txnId >>=
                                                               buildWireBuilders'
    where buildWireBuilders' diskState =
              do z <- readChan zChan
                 case z of
                   Nothing -> writeChan builderChan Nothing >> return ()
                   Just z  ->
                       do (b, diskState') <- canonicalBuilderForZipper diskState sch z
                          writeChan builderChan (Just b)
                          buildWireBuilders' diskState

statefulConduit :: Monad m => (b -> a -> m b) -> b -> Conduit a m b
statefulConduit f st = await >>= \x ->
                       case x of
                         Nothing -> return ()
                         Just x  -> do st' <- lift (f st x)
                                       yield st'
                                       statefulConduit f st'

serveClient :: TxnStepsChan -> IO TxnId -> ZephyrExports -> ZippySchema -> (Socket, SockAddr) -> ServeM ()
serveClient txnsChan nextTxnId exportedZephyr sch (sock, sockAddr) =
    do infoM "serveClient" ("New connection from " ++ show sockAddr)
       txnId <- nextTxnId
       sourceSocket sock $= lines $= requestServer txnsChan txnId nextTxnId exportedZephyr sch (zippySchemaRootType sch) $$ sinkSocket sock

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
       let (exports, schema) = compilePackages zephyrPackages (ZippyTyCon zephyrRootTyName mempty)

       infoM "serveZippy" ("Loaded packages " ++ show (map zephyrPackageName zephyrPackages))

       let st = ZippyState txns rootsPtr diskStateRef schema

       -- Start transaction server
       infoM "serveZippy" "Starting transaction coordinator thread..."
       forkIO (txnServe stepsChan st)

       -- Start network server
       listen serverAddress (show serverPort) $ \(sock, listenAddr) ->
           do infoM "serveZippy" ("Starting server on " ++ show listenAddr)
              forever $ do
                info@(clientSock, _) <- accept sock
                forkIO (serveClient stepsChan nextTxnId exports schema info `E.finally` close clientSock)
