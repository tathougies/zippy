{-# LANGUAGE OverloadedStrings, FlexibleContexts #-}
module Database.Zippy.Data ( parseZippyD, decimal, parseTextD, defaultForSchema, showZippyD ) where

import Database.Zippy.Types

import Prelude hiding (mapM)

import Control.Applicative hiding ((<|>), many)

import Data.Char (digitToInt, ord)
import Data.Either
import Data.Int
import Data.String
import Data.Text (Text)
import Data.Traversable (mapM)
import Data.Vector ((!))
import Data.Vector (Vector, (!), findIndex)
import Data.List (intercalate)

import qualified Data.Vector as V
import qualified Data.Text as T
import qualified Data.ByteString.Char8 as BS

import Text.Parsec
import Text.Parsec.ByteString

import Numeric

parseZippyD :: ZippyT -> ZippySchema -> Parser InMemoryD
parseZippyD ty sch = spaces *> parseZippyD' ty sch

parseZippyD' :: ZippyT -> ZippySchema -> Parser InMemoryD
parseZippyD' (SimpleT TextT) _ = InMemoryD . TextD <$> parseTextD
parseZippyD' (SimpleT IntegerT) _ = InMemoryD . IntegerD <$> parseIntegerD
parseZippyD' (SimpleT FloatingT) _ = fail "Can't parse floatingT yet" -- InMemoryD . FloatingD <$> parseFloatingD
parseZippyD' (SimpleT BinaryT) _ = fail "Can't parse BinaryT yet" -- InMemoryD . BinaryD <$> parseBinaryD
parseZippyD' (AlgebraicT (ZippyAlgebraicT tyName cons)) sch =
    parseAlgebraicD tyName cons sch

parseAlgebraicD :: GenericZippyTyCon (ZippyFieldType ZippyTyRef) -> Vector (GenericZippyDataCon (ZippyFieldType ZippyTyRef)) -> ZippySchema -> Parser InMemoryD
parseAlgebraicD tyName cons sch =
    do conName <- fromString <$> many1 (letter <|> digit)
       spaces
       case findIndex (\(ZippyDataCon (ZippyDataConName name) _) -> name == conName) cons of
         Nothing -> fail ("Couldn't find constructor '" ++ T.unpack conName ++ "' for type " ++ show tyName)
         Just tag -> do let ZippyDataCon _ args = cons ! tag
                        argData <- mapM (\argTy -> parseArgD (zippyFieldType argTy) <* spaces) args
                        return (InMemoryD (CompositeD (fromIntegral tag) argData))

    where parseArgD (RefFieldT (ZippyTyRef tyRef)) =
              let argTy = zippyTypes sch ! tyRef
              in between (char '(') (char ')') (eraseInMemoryD <$> parseZippyD' argTy sch)
          parseArgD (SimpleFieldT TextT) = SZippyD . TextD <$> parseTextD
          parseArgD (SimpleFieldT IntegerT) = SZippyD . IntegerD <$> parseIntegerD

parseIntegerD :: Parser Int64
parseIntegerD = int
    where int :: Parser Int64
          int             = do{ f <- (sign <* spaces)
                              ; n <- (nat <* spaces)
                              ; return (f n)
                              }

          sign            =   (char '-' >> return negate)
                          <|> (char '+' >> return id)
                          <|> return id

          nat :: Parser Int64
          nat             = zeroNumber <|> decimal

          zeroNumber :: Parser Int64
          zeroNumber      = do{ char '0'
                              ; hexadecimal <|> octal <|> decimal <|> return 0
                              }
                            <?> ""
          hexadecimal, octal :: Parser Int64
          hexadecimal     = do{ oneOf "xX"; number 16 hexDigit }
          octal           = do{ oneOf "oO"; number 8 octDigit  }

decimal :: Integral a => Parser a
decimal         = number 10 digit

number :: Integral a => a -> Parser Char -> Parser a
number base baseDigit
    = do{ digits <- many1 baseDigit
        ; let n = foldl (\x d -> base*x + fromIntegral (digitToInt d)) 0 digits
        ; seq n (return n)
        }

parseTextD :: Parser Text
parseTextD = fromString <$> (stringLiteral <* spaces)
    -- stringLiteral taken from parsec...
    where stringLiteral   = do { str <- between (char '"')
                                                (char '"' <?> "end of string")
                                                (many stringChar)
                               ; return (foldr (maybe id (:)) "" str)
                               }
                            <?> "literal string"

          stringChar      = do { c <- stringLetter; return (Just c) }
                          <|> stringEscape
                          <?> "string character"

          stringLetter    = satisfy (\c -> (c /= '"') && (c /= '\\') && (c > '\026'))

          stringEscape    = do{ char '\\'
                              ;     do{ escapeGap  ; return Nothing }
                                <|> do{ escapeEmpty; return Nothing }
                                <|> do{ esc <- escapeCode; return (Just esc) }
                              }

          escapeEmpty     = char '&'
          escapeGap       = do{ many1 space
                              ; char '\\' <?> "end of string gap"
                              }

          -- escape codes
          escapeCode      = charEsc <|> charNum <|> charAscii <|> charControl
                          <?> "escape code"

          charControl     = do{ char '^'
                              ; code <- upper
                              ; return (toEnum (fromEnum code - fromEnum 'A'))
                              }

          charNum         = do{ code <- decimal
                                        <|> do{ char 'o'; number 8 octDigit }
                                        <|> do{ char 'x'; number 16 hexDigit }
                              ; return (toEnum code)
                              }

          charEsc         = choice (map parseEsc escMap)
                          where
                            parseEsc (c,code)     = do{ char c; return code }

          charAscii       = choice (map parseAscii asciiMap)
                          where
                            parseAscii (asc,code) = try (do{ string asc; return code })

          -- escape code tables
          escMap          = zip ("abfnrtv\\\"\'") ("\a\b\f\n\r\t\v\\\"\'")
          asciiMap        = zip (ascii3codes ++ ascii2codes) (ascii3 ++ ascii2)

          ascii2codes     = ["BS","HT","LF","VT","FF","CR","SO","SI","EM",
                             "FS","GS","RS","US","SP"]
          ascii3codes     = ["NUL","SOH","STX","ETX","EOT","ENQ","ACK","BEL",
                             "DLE","DC1","DC2","DC3","DC4","NAK","SYN","ETB",
                             "CAN","SUB","ESC","DEL"]

          ascii2          = ['\BS','\HT','\LF','\VT','\FF','\CR','\SO','\SI',
                             '\EM','\FS','\GS','\RS','\US','\SP']
          ascii3          = ['\NUL','\SOH','\STX','\ETX','\EOT','\ENQ','\ACK',
                             '\BEL','\DLE','\DC1','\DC2','\DC3','\DC4','\NAK',
                             '\SYN','\ETB','\CAN','\SUB','\ESC','\DEL']

reifyFieldType _ (SimpleFieldT s) = SimpleT s
reifyFieldType types (RefFieldT (ZippyTyRef i)) = types ! i

defaultForSchema :: ZippySchema -> InMemoryD
defaultForSchema (ZippySchema (ZippyTyRef rootTypeIndex) types) = defaultForType (types ! rootTypeIndex)
    where defaultForType (SimpleT IntegerT) = InMemoryD (IntegerD 0)
          defaultForType (SimpleT FloatingT) = InMemoryD (FloatingD 0)
          defaultForType (SimpleT TextT) = InMemoryD (TextD "")
          defaultForType (SimpleT BinaryT) = InMemoryD (BinaryD "")
          defaultForType (AlgebraicT (ZippyAlgebraicT _ cons)) =
              let ZippyDataCon _ argTys = cons ! 0
                  realArgTys = fmap (reifyFieldType types . zippyFieldType) argTys
              in InMemoryD (CompositeD 0 (fmap (eraseInMemoryD . defaultForType) realArgTys))

showZippyD :: ZippySchema -> SZippyD -> String
showZippyD (ZippySchema (ZippyTyRef rootTypeIndex) types) = showZippyD' (types ! rootTypeIndex)
    where showZippyD' ty (SZippyD (OnDiskD offs)) = concat ["<", prettyTyName ty, " on disk at 0x", showHex offs ">"]
          showZippyD' _ (SZippyD (IntegerD i)) = show i
          showZippyD' _ (SZippyD (FloatingD f)) = show f
          showZippyD' _ (SZippyD (TextD t)) = show (T.unpack t)
          showZippyD' _ (SZippyD (BinaryD bin)) = 'b':show (BS.unpack bin)
          showZippyD' (AlgebraicT (ZippyAlgebraicT tyName cons)) (SZippyD (CompositeD tag args)) =
              let ZippyDataCon (ZippyDataConName conName) argTys = cons ! fromIntegral tag
                  realArgTys = map (reifyFieldType types . zippyFieldType) (V.toList argTys)
              in concat ["(", T.unpack conName, concatMap (' ':) $ zipWith showZippyD' realArgTys (V.toList args), ")"]
          showZippyD' _ _ = error "Expecting algebraic type, but got atom"

          prettyFieldTyName (SimpleFieldT s) = prettyTyName (SimpleT s)
          prettyFieldTyName (RefFieldT (ZippyTyRef i)) = prettyTyName (types ! i)

          prettyTyName (AlgebraicT (ZippyAlgebraicT (ZippyTyCon (ZippyTyName pkgName dataName) tyArgs) _))
              | V.null tyArgs = T.unpack pkgName ++ ":" ++ T.unpack dataName
              | otherwise = "(" ++ T.unpack pkgName ++ ":" ++ T.unpack dataName ++ " " ++ intercalate " " (map prettyFieldTyName (V.toList tyArgs))
          prettyTyName (SimpleT IntegerT) = "atom:Integer"
          prettyTyName (SimpleT TextT) = "atom:Text"
          prettyTyName (SimpleT FloatingT) = "atom:Floating"
          prettyTyName (SimpleT BinaryT) = "atom:Binary"
