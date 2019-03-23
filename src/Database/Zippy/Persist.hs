{-# LANGUAGE TupleSections #-}
module Database.Zippy.Persist
    ( readZippyDFromDisk, writeZippyDToDisk, updateRoot, readTime, writeTime ) where

import           Database.Zippy.Types

import           Prelude hiding (mapM, foldl)

import           Control.Applicative
import           Control.Monad hiding (mapM)
import           Control.Arrow (second)
import           Control.DeepSeq

import           Data.Bits
import           Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import           Data.ByteString.Builder (Builder, int64LE, doubleLE, word64LE, word16LE, int32LE)
import qualified Data.ByteString.Builder as BS
import           Data.Foldable (foldl)
import           Data.IORef
import           Data.Int
import           Data.Monoid
import           Data.Semigroup
import           Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import           Data.Traversable (mapM)
import qualified Data.Vector as V
import           Data.Word

import           Foreign.Marshal.Alloc
import           Foreign.Ptr
import           Foreign.Storable

import           System.IO

import           Data.IORef
import           System.CPUTime
import           System.IO.Unsafe

data FixedLengthBuilder = FixedLengthBuilder !Word64 !Builder

instance Semigroup FixedLengthBuilder where
    (<>) = mappend

instance Monoid FixedLengthBuilder where
    mempty = FixedLengthBuilder 0 mempty
    mappend (FixedLengthBuilder aLen aS) (FixedLengthBuilder bLen bS) = FixedLengthBuilder (aLen + bLen) (aS <> bS)

fixedLengthByteString :: ByteString -> FixedLengthBuilder
fixedLengthByteString bs = FixedLengthBuilder (fromIntegral (BS.length bs)) (BS.byteString bs)

fixedLengthAtom :: Builder -> FixedLengthBuilder
fixedLengthAtom = FixedLengthBuilder (fromIntegral kATOM_SIZE)

fixedLengthTag :: Word16 -> FixedLengthBuilder
fixedLengthTag tag = FixedLengthBuilder 2 (word16LE tag) <> fixedLengthByteString (BS.take 6 zeroAtomBS)

fixedLengthBuilderSize :: FixedLengthBuilder -> Word64
fixedLengthBuilderSize (FixedLengthBuilder sz _) = sz

zeroAtomBS :: ByteString
zeroAtomBS = BS.pack (replicate kATOM_SIZE 0)

-- | All on-disk addresses must be 8-bytes aligned
kADDR_ALIGNMENT :: Word64
kADDR_ALIGNMENT = 8

kADDR_ALIGNMENT_MASK :: Word64
kADDR_ALIGNMENT_MASK = complement (kADDR_ALIGNMENT - 1)

kATOM_SIZE :: Int
kATOM_SIZE = 8
kTAG_SIZE :: Int
kTAG_SIZE = 2

{-# NOINLINE readTime #-}
{-# NOINLINE writeTime #-}
readTime, writeTime :: IORef Integer
readTime = unsafePerformIO (newIORef 0)
writeTime = unsafePerformIO (newIORef 0)

readZippyDFromDisk :: Handle -> ZippyT -> Word64 -> IO InMemoryD
readZippyDFromDisk hdl dataType addr =
    do start <- getCPUTime
       let alignedAddr = addr .&. kADDR_ALIGNMENT_MASK
       seekAbs hdl alignedAddr
       ret <- case dataType of
         SimpleT IntegerT  -> readIntegerD   hdl
         SimpleT TextT     -> readTextDUtf8  hdl
         SimpleT FloatingT -> readFloatingD  hdl
         SimpleT BinaryT   -> readBinaryD    hdl
         AlgebraicT tyInfo -> readAlgebraicD hdl tyInfo
       end <- getCPUTime
       modifyIORef' readTime (+ (end - start))
       return ret

sizeOfP :: Storable p => Ptr p -> Int
sizeOfP ptr = sizeOf (deref ptr)
    where deref :: Ptr p -> p
          deref _ = undefined

seekAbs :: Handle -> Word64 -> IO ()
seekAbs hdl addr = hSeek hdl AbsoluteSeek (fromIntegral addr)

readIntegerD :: Handle ->IO InMemoryD
readIntegerD hdl = alloca $ \retP -> do
                     bytesRead <- hGetBuf hdl retP (sizeOfP retP)
                     if bytesRead /= sizeOfP retP
                       then fail "Could not read enough bytes for IntegerD"
                       else InMemoryD . IntegerD <$> peek retP

readTextDUtf8 :: Handle -> IO InMemoryD
readTextDUtf8 hdl = do txtSz <- alloca $ \retP -> do
                                  bytesRead <- hGetBuf hdl retP (sizeOfP retP)
                                  if bytesRead /= sizeOfP retP
                                    then fail "Could not read enough bytes for Int size for TextD"
                                    else peek retP
                       utf8Encoded <- BS.hGet hdl (fromIntegral (txtSz :: Int32))
                       let decoded = TE.decodeUtf8 utf8Encoded
                       return (decoded `seq` InMemoryD (TextD decoded))

readFloatingD :: Handle -> IO InMemoryD
readFloatingD hdl = alloca $ \retP -> do
                      bytesRead <- hGetBuf hdl retP (sizeOfP retP)
                      if bytesRead /= sizeOfP retP
                        then fail "Could not read enough bytes for FloatingD"
                        else InMemoryD . FloatingD <$> peek retP

readBinaryD :: Handle -> IO InMemoryD
readBinaryD hdl = do binarySz <- alloca $ \retP -> do
                                   bytesRead <- hGetBuf hdl retP (sizeOfP retP)
                                   if bytesRead /= sizeOfP retP
                                     then fail "Could not read enough bytes for Int size for BinaryD"
                                     else peek retP
                     InMemoryD . BinaryD <$> BS.hGet hdl (binarySz :: Int)

readArg :: Handle -> ZippyFieldType ZippyTyRef -> IO SZippyD
readArg hdl (SimpleFieldT IntegerT) = eraseInMemoryD <$> readIntegerD hdl
readArg hdl (SimpleFieldT FloatingT) = eraseInMemoryD <$> readFloatingD hdl
readArg hdl _ = alloca $ \retP -> do
                  bytesRead <- hGetBuf hdl retP (sizeOfP retP)
                  if bytesRead /= sizeOfP retP
                    then fail "Could not read enough bytes for offset"
                    else SZippyD . OnDiskD <$> peek retP

readAlgebraicD :: Handle -> ZippyAlgebraicT -> IO InMemoryD
readAlgebraicD hdl (ZippyAlgebraicT tyName cons) =
    do tag <- alloca $ \retP -> do
                bytesRead <- hGetBuf hdl retP (sizeOfP retP)
                if bytesRead /= sizeOfP retP
                   then fail ("Could not read enough bytes for algebraic tag for composite type: " ++ show tyName)
                   else peek retP :: IO Word16
       hSeek hdl RelativeSeek (fromIntegral (kATOM_SIZE - kTAG_SIZE))
       case cons V.!? fromIntegral tag of
         Just (ZippyDataCon _ args) ->
             InMemoryD . CompositeD tag <$> mapM (readArg hdl . zippyFieldType) args
         Nothing -> fail (concat ["Received an invalid tag(", show tag, ") for composite type: ", show tyName])

writeZippyDToDisk :: Handle -> InMemoryD -> IO ([(Word64, InMemoryD)], Word64)
writeZippyDToDisk hdl mem =
    do start <- getCPUTime
       ret <- writeZippyDToDisk' hdl mem
       hFlush hdl
       end <- getCPUTime
       modifyIORef' writeTime (+ (end - start))
       return ret

writeZippyDToDisk' :: Handle -> InMemoryD -> IO ([(Word64, InMemoryD)], Word64)
writeZippyDToDisk' hdl dt =
    do hSeek hdl SeekFromEnd 0
       ret <- fromIntegral <$> hTell hdl
       let (entities, FixedLengthBuilder builderSz builder) =
               case dt of
                 InMemoryD (IntegerD i) -> ([(ret, dt)], writeIntegerD i)
                 InMemoryD (TextD t) -> ([(ret, dt)], writeTextD t)
                 InMemoryD (FloatingD f) -> ([(ret, dt)], writeFloatingD f)
                 InMemoryD (BinaryD b) -> ([(ret, dt)], writeBinaryD b)

                 InMemoryD (CompositeD tag args) -> let (entities, memD, builder) = writeCompositeD ret tag args
                                                    in ((ret, memD):entities, builder)
       BS.hPutBuilder hdl builder
       donePos <- fromIntegral <$> hTell hdl
--       putStrLn ("Writing " ++ show entities)
       when ((donePos - ret) /= builderSz) $ fail ("Only wrote " ++ show (donePos - ret) ++ " bytes, but expected " ++ show builderSz)
       return (entities, ret)

writeIntegerD :: Int64 -> FixedLengthBuilder
writeIntegerD i = fixedLengthAtom (int64LE i)

writeFloatingD :: Double -> FixedLengthBuilder
writeFloatingD f = fixedLengthAtom (doubleLE f)

writeBinaryD :: ByteString -> FixedLengthBuilder
writeBinaryD = writeBSAligned

writeTextD :: Text -> FixedLengthBuilder
writeTextD txt = let encoded = TE.encodeUtf8 txt
                 in writeBSAligned encoded

writeBSAligned :: ByteString -> FixedLengthBuilder
writeBSAligned bs = let padCount = fromIntegral kADDR_ALIGNMENT - ((BS.length bs + 4) .&. fromIntegral (complement kADDR_ALIGNMENT_MASK))
                    in FixedLengthBuilder 4 (int32LE (fromIntegral (BS.length bs))) <>
                       fixedLengthByteString bs <>
                       fixedLengthByteString (BS.take padCount zeroAtomBS)

putWord64 :: Word64 -> FixedLengthBuilder
putWord64 w = fixedLengthAtom (word64LE w)

writeCompositeD :: Word64 -> Word16 -> V.Vector SZippyD -> ([(Word64, InMemoryD)], InMemoryD, FixedLengthBuilder)
writeCompositeD eofPos tag args = ( entities
                                  , inMemoryD
                                  , fixedLengthTag tag <>
                                    argsBuilder <> complexArgsBuilder)
    where compositeSize = fromIntegral (kATOM_SIZE * (V.length args + 1))
          (_, entities, mkArgs', complexArgsBuilder) = foldl writeArg (eofPos + compositeSize, [], id, mempty) args
          args' = mkArgs' []

          argsBuilder = mconcat (map writeInMemoryArg args')
          !inMemoryD = InMemoryD (CompositeD tag (V.fromList args'))

          writeInMemoryArg :: SZippyD -> FixedLengthBuilder
          writeInMemoryArg (SZippyD (OnDiskD diskOffs)) = fixedLengthAtom (word64LE diskOffs)
          writeInMemoryArg (SZippyD (FloatingD f)) = writeFloatingD f
          writeInMemoryArg (SZippyD (IntegerD i)) = writeIntegerD i
          writeInMemoryArg _ = error "Should have written complex args to disk"

          writeArg (!eofPos, entities, args, argsBuilder) argD =
              case argD of
                SZippyD arg@(TextD t) -> let txtBuilder = writeTextD t
                                         in ( eofPos + fixedLengthBuilderSize txtBuilder
                                            , (eofPos, InMemoryD arg):entities
                                            , args . (SZippyD (OnDiskD eofPos) :)
                                            , argsBuilder <> txtBuilder)
                SZippyD arg@(BinaryD b) -> let bsBuilder = writeBinaryD b
                                           in (eofPos + fixedLengthBuilderSize bsBuilder
                                              , (eofPos, InMemoryD arg):entities
                                              , args . (SZippyD (OnDiskD eofPos) :)
                                              , argsBuilder <> bsBuilder)
                SZippyD (CompositeD tag argArgs) ->
                    let (argEntities, inMemoryD, compBuilder) = writeCompositeD eofPos tag argArgs
                    in (eofPos + fixedLengthBuilderSize compBuilder,
                        (eofPos, inMemoryD):(argEntities <> entities),
                        args . (SZippyD (OnDiskD eofPos) :),
                        argsBuilder <> compBuilder)
                _ -> (eofPos, entities, args . (argD :), argsBuilder)

updateRoot :: Handle -> Word64 -> IO ()
updateRoot hdl newRoot = alloca $ \p -> do poke p newRoot
                                           hPutBuf hdl p (sizeOf newRoot)
                                           hFlush hdl
