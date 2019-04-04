{-# LANGUAGE RecordWildCards, OverloadedStrings #-}
module Database.Zippy.Serve where

import           Database.Zippy.Schema
import           Database.Zippy.Types
import           Database.Zippy.Transaction
import           Database.Zippy.Data
import           Database.Zippy.Containers.Treap
import           Database.Zippy.Disk
import           Database.Zippy.Zephyr

import           Prelude hiding (lines)

import           Control.Applicative
import           Control.Concurrent hiding (yield)
import           Control.Concurrent.Chan
import           Control.Monad.Free
import           Control.Monad
import           Control.Monad.Trans
import qualified Control.Exception as E

import           Data.ByteString (ByteString)
import           Data.ByteString.Builder hiding (word8)
import qualified Data.ByteString.Streaming.Char8 as SBS
import           Data.Char
-- import Data.Conduit.Binary
-- import Data.Conduit.Network (sourceSocket, sinkSocket)
-- import Data.Conduit.ByteString.Builder
import           Data.IORef
import           Data.String hiding (lines)
import           Data.Word
import           Data.Int
import           Data.Monoid
import           Data.Text (Text)
import qualified Data.Text.Encoding as TE

import           Data.Attoparsec as Atto
import           Data.Attoparsec.ByteString
import qualified Data.Attoparsec.ByteString.Streaming as A

import qualified Data.HashMap.Strict as HM
import qualified Data.ByteString.Char8 as BS

import           Foreign.Marshal.Alloc
import           Foreign.Storable

import           Network.Simple.TCP ( Socket, SockAddr
                                    , HostPreference(..)
                                    , withSocketsDo, serve, send)
import qualified Network.Socket.ByteString as NSB

import           Streaming as S ( Of(..), Stream, inspect )

import           System.IO
import           System.Log.Logger
import           System.Random
import           System.Directory
import           System.FilePath

import qualified Text.Parsec as Parsec
import           Text.Read hiding (lift)
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
              | ZephyrQueryCmd !Bool !Text !ByteString
              | ListZephyrCmds
              | NewTxnCmd

              | CurTyCmd
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
                 (pure CurTyCmd <* string "ty") <|>
                 (pure MoveUpCmd <* string "up") <|>
                 (MoveDownCmd <$> (string "down " *> decimal)) <|>
                 (ReplaceCmd <$> (string "replace" *> spaces *> Atto.takeWhile (const True))) <|>
                 (FindInTreapCmd <$> (string "find" *> spaces *> decimal)) <|>
                 (InsertInTreapCmd <$> (string "insert" *> spaces *> decimal) <*> (spaces *> parseTextD)) <|>
                 (pure CurCmd <* string "cur") <|>
                 (pure CommitCmd <* string "commit") <|>
                 (pure ListZephyrCmds <* string "list-queries") <|>
                 (ZephyrQueryCmd False . TE.decodeUtf8  <$> (string "query" *> spaces *> Atto.takeWhile1 (not . isSpace . chr . fromIntegral)) <*> (spaces *> Atto.takeWhile (const True))) <|>
                 (ZephyrQueryCmd True . TE.decodeUtf8  <$> (string "txquery" *> spaces *> Atto.takeWhile1 (not . isSpace . chr . fromIntegral)) <*> (spaces *> Atto.takeWhile (const True))) <|>
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

requestServer :: TxnStepsChan -> TxnId -> IO TxnId -> ZephyrExports -> ZippySchema -> ZippyT
              -> Stream (SBS.ByteString ServeM) ServeM ()
              -> SBS.ByteString ServeM ()
requestServer txnsChan txnId nextTxnId exportedZephyr sch curTy input =
    do res <- lift (inspect input)
       case res of
         Left () -> pure ()
         Right cmdBytes -> do
           (res, input') <- lift (A.parse (cmdP sch curTy) cmdBytes)
           isNull S.:> input'' <- lift (SBS.null input')

           let continueWithType curTy' =
                   requestServer txnsChan txnId nextTxnId exportedZephyr sch curTy' input''
           if not isNull then SBS.chunk "Extra at end of command\n" >> continueWithType curTy
             else case res of
               Left err -> do
                 SBS.chunk (fromString ("Cannot parse this cmd: " ++ show err ++ "\n"))
                 continueWithType curTy
               Right CurTyCmd -> do
                 SBS.chunk (fromString (show curTy ++ "\n"))
                 continueWithType curTy
               Right MoveUpCmd -> do
                 res <- lift $ interpretTxAsync sch ResyncAfterTx txnsChan simpleTxActionLogger txnId (move Up)
                 let (res', newTy) = case res of
                                       Moved newTy -> ("Moved\n", newTy)
                                       _ -> (fromString (show res ++ "\n"), curTy)
                 SBS.chunk res'
                 continueWithType newTy
               Right (MoveDownCmd i) -> do
                 res <- lift $ interpretTxAsync sch ResyncAfterTx txnsChan simpleTxActionLogger txnId (move (Down i))
                 let (res', newTy) = case res of
                                       Moved newTy -> ("Moved\n", newTy)
                                       _ -> (fromString (show res ++ "\n"), curTy)
                 SBS.chunk res'
                 continueWithType newTy
               Right CurCmd -> do
                 liftIO $ infoM "serveRequest" "Running CurCmd"
                 res <- lift $ interpretTxAsync sch ResyncAfterTx txnsChan simpleTxActionLogger txnId cur
                 SBS.chunk (fromString (show res ++ "\n"))
                 continueWithType curTy
               Right (ReplaceCmd d) ->
                 case Parsec.parse (parseZippyD curTy sch) "<network>" d of
                   Left err -> do
                     SBS.chunk ("Could not parse data of type " <> fromString (show curTy) <> "\n")
                     continueWithType curTy
                   Right d -> do
                     liftIO $ infoM "serveRequest" ("Replace with " ++ show d)
                     res <- lift $ interpretTxAsync sch ResyncAfterTx txnsChan simpleTxActionLogger txnId (move (Replace d))
                     SBS.chunk (fromString (show res ++ "\n"))
                     continueWithType curTy
               Right (FindInTreapCmd i) -> do
                 liftIO $ infoM "serveRequest" ("Find in treap " ++ show i)
                 res <- lift $ interpretTxAsync sch ResyncAfterTx txnsChan simpleTxActionLogger txnId (treapFind 0 (atomCmp (InMemoryD (IntegerD i))))
                 SBS.chunk (fromString (show res ++ "\n"))
                 continueWithType curTy
               Right (InsertInTreapCmd i t) -> do
                 liftIO $ infoM "serveRequest" ("Insert in treap " ++ show i ++ " " ++ show t)
                 prio <- liftIO randomIO
                 res <- lift $ interpretTxAsync sch DontResyncAfterTx txnsChan simpleTxActionLogger txnId (treapInsert prio (InMemoryD (IntegerD i)) (InMemoryD (TextD t)) >> commit)
                 SBS.chunk (fromString (show res ++ "\n"))
                 continueWithType curTy
               Right CommitCmd -> do
                 liftIO $ infoM "serveRequest" "Requesting commit"
                 status <- lift $ commitAndWaitForStatus txnsChan txnId
                 SBS.chunk (fromString (show status ++ "\n"))
                 continueWithType curTy
               Right NewTxnCmd -> do
                 txnId <- liftIO nextTxnId
                 SBS.chunk "BEGIN\n"
                 continueWithType (zippySchemaRootType sch)
               Right ListZephyrCmds -> do
                 let keys = map (\(ZephyrWord t) -> TE.encodeUtf8 t) (HM.keys exportedZephyr)
                 SBS.chunk ("QUERIES " <> BS.intercalate " " keys <> "\n")
                 continueWithType curTy
               Right (ZephyrQueryCmd commitAfter cmdName stk) ->
                   do liftIO $ infoM "serveRequest" "testing zephyr"
                      case parseZephyrStack stk of
                        Left err -> SBS.chunk (fromString ("error parsing stack: " ++ show err ++ "\n")) >>
                                    continueWithType curTy
                        Right stk ->
                          case HM.lookup (ZephyrWord cmdName) exportedZephyr of
                            Just zephyrProg -> do
                              rawLogChan <- liftIO newChan
                              wireLogChan <- liftIO newChan
                              resV <- liftIO newEmptyMVar

                              liftIO . forkIO $ do
                                res <- interpretTxAsync sch (if commitAfter then DontResyncAfterTx else ResyncAfterTx) txnsChan (txResultActionLogger rawLogChan) txnId $
                                       do res <- runZephyr zephyrProg sch (reverse stk)
                                          commitRes <- if commitAfter then Just <$> commit else pure Nothing
                                          return (res, commitRes)

                                writeChan rawLogChan Nothing
                                putMVar resV res

                              liftIO (forkIO (buildWireBuilders curTy sch txnId txnsChan rawLogChan wireLogChan))

                              let getBuilders = do res <- liftIO (readChan wireLogChan)
                                                   liftIO (infoM "serveRequest" ("Got result " ++ (show (() <$ res))))
                                                   case res of
                                                     Just builder -> do
                                                       SBS.chunk "RES "
                                                       SBS.toStreamingByteString builder
                                                       SBS.chunk "\n"
                                                       getBuilders
                                                     Nothing -> return ()
  --                                liftYield = await >>= \x ->
  --                                            case x of
  --                                              Nothing -> return ()
  --                                              Just x -> lift (yield x) >> liftYield

                              getBuilders
                              (res, commitRes) <- liftIO (takeMVar resV)
                              SBS.chunk ("ALL DONE" <> fromString (show res) <> "\n")
                              case commitRes of
                                Nothing -> pure ()
                                Just commitRes -> SBS.chunk (fromString (show commitRes <> "\n"))
                              continueWithType curTy
                            Nothing -> do
                              SBS.chunk (fromString ("No such zephyr query: " ++ show cmdName ++ "\n"))
                              continueWithType curTy

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
--
--statefulConduit :: Monad m => (b -> a -> m b) -> b -> Conduit a m b
--statefulConduit f st = await >>= \x ->
--                       case x of
--                         Nothing -> return ()
--                         Just x  -> do st' <- lift (f st x)
--                                       yield st'
--                                       statefulConduit f st'

serveClient :: TxnStepsChan -> IO TxnId -> ZephyrExports
            -> ZippySchema -> (Socket, SockAddr) -> ServeM ()
serveClient txnsChan nextTxnId exportedZephyr sch (sock, sockAddr) =
    do infoM "serveClient" ("New connection from " ++ show sockAddr)
       txnId <- nextTxnId
       toSocket sock (requestServer txnsChan txnId nextTxnId exportedZephyr sch (zippySchemaRootType sch) (SBS.lines (fromSocket sock 4096)))

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
       case compilePackages zephyrPackages (ZippyTyCon zephyrRootTyName mempty) of
         Left (ZephyrCompileErrorTy err) ->
             let showError (locs, err) = "At " ++ show locs ++ ":\n" ++ showError' err
                 showError' (KindMismatch ty1 ty2) = "Kind mismatch between " ++ show (kindOf ty1) ++ " and " ++ show (kindOf ty2) ++ " " ++ show ty1 ++ " " ++ show ty2
                 showError' x = show x
             in putStrLn (showError err)
         Left (ZephyrCompileErrorGeneric err) ->
             putStrLn ("Generic compile error: " ++ err)
         Right (exports, schema) ->
             do infoM "serveZippy" ("Loaded packages " ++ show (map zephyrPackageName zephyrPackages))

                let st = ZippyState txns rootsPtr diskStateRef schema

                -- Start transaction server
                infoM "serveZippy" ("Schema is " ++ show schema)
                infoM "serveZippy" "Starting transaction coordinator thread..."
                forkIO (txnServe stepsChan st)

                -- Start network server
                withSocketsDo $ serve HostAny (show serverPort)
                      (serveClient stepsChan nextTxnId exports schema)

fromSocket
  :: MonadIO m
  => Socket     -- ^Connected socket.
  -> Int        -- ^Maximum number of bytes to receive and send
                -- dowstream at once. Renzo recommends
                -- using @4096@ if you don't have a special purpose.
  -> SBS.ByteString m ()
fromSocket sock nbytes = loop where
  loop = do
    bs <- liftIO (NSB.recv sock nbytes)
    if BS.null bs
      then return ()
      else SBS.chunk bs >> loop
{-# INLINABLE fromSocket #-}

toSocket
  :: MonadIO m
  => Socket  -- ^Connected socket.
  -> SBS.ByteString m r
  -> m r
toSocket sock = loop where
  loop bs = do
    e <- SBS.nextChunk bs
    case e of
      Left r -> return r
      Right (b,rest) -> send sock b >> loop rest
{-# INLINABLE toSocket #-}
