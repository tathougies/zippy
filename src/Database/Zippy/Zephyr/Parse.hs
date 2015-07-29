{-# LANGUAGE OverloadedStrings #-}
module Database.Zippy.Zephyr.Parse where

import Database.Zippy.Types
import Database.Zippy.Zephyr.Types

import Control.Applicative hiding (many, optional, (<|>))
import Control.Monad

import Data.String
import Data.Monoid
import Data.Char
import Data.ByteString (ByteString)
import qualified Data.Vector as V
import qualified Data.Set as S
import qualified Data.DList as D

import Text.Parsec hiding (State)
import Text.Parsec.ByteString

-- * Zephyr parsing and compilation

zephyrIdentifier = try $
                   do name <- many1 (satisfy (\c -> c /= ' ' && c /= '\t' && c /= '\v' &&
                                                    c /= '\r' && c /= '\n' && c /= ']' &&
                                                    c /= '[' && c /= '$' && c /= '(' && c /= ')'))
                      guard (name /= "DEFINE" &&
                             name /= "EXPORT" &&
                             name /= "DATA")
                      pure name

zephyrConsIdentifier = do name <- many1 (satisfy (\c -> c /= ' ' && c /= '\t' && c /= '\v' &&
                                                    c /= '\r' && c /= '\n' && c /= ']' &&
                                                    c /= '[' && c /= '$' && c /= '=' &&
                                                    c /= '(' && c /= ')'))
                          guard (name /= "DEFINE" &&
                                 name /= "EXPORT" &&
                                 name /= "DATA"   &&
                                 name /= "CONS")
                          pure name

whitespace :: Parser ()
whitespace = (oneOf " \t\v\r\n" *> optional whitespace) <|> (char '{' *> consumeComment *> optional whitespace) <|> pure ()
    where consumeComment = many (satisfy (/= '}')) *> char '}'

atomP :: Parser ZephyrBuilderAtom
atomP = unquotedAtomP <|>
        symbol <|>
        (char '[' *> whitespace *> (QuoteZ <$> zephyrP) <* char ']') <?>
        "atom"
        where symbol = do identifier <- zephyrIdentifier
                          case identifier of
                            "SWAP"     -> pure SwapZ
                            "DUP"      -> pure DupZ
                            "ZAP"      -> pure ZapZ
                            "CAT"      -> pure CatZ
                            "CONS"     -> pure ConsZ
                            "UNCONS"   -> pure UnConsZ
                            "I"        -> pure DeQuoteZ
                            "DIP"      -> pure DipZ
                            "ZIP-UP"   -> pure ZipUpZ
                            "ZIP-DOWN" -> pure ZipDownZ
                            "ZIP-REPLACE" -> pure ZipReplaceZ
                            "CUR-TAG"  -> pure CurTagZ
                            "CUR-ATOM" -> pure CurAtomZ
                            "ARG-HOLE" -> pure ArgHoleZ
                            "ENTER-ZIPPER" -> pure EnterZipperZ
                            "CUT" -> pure CutZ
                            "IFTE"     -> pure IfThenElseZ
                            "FAIL"     -> pure FailZ
                            "LOG"      -> pure LogZ
                            "YIELD"    -> pure YieldZ
                            "LENGTH"   -> pure LengthZ
                            "=="       -> pure EqZ
                            ">"        -> pure GtZ
                            "<"        -> pure LtZ
                            "+"        -> pure PlusZ
                            _          -> pure (SymZ (fromString identifier))

literalP :: Parser ZephyrD
literalP = do res <- unquotedAtomP
              case res of
                IntegerZ i -> return (ZephyrD (IntegerD i))
                FloatingZ f -> return (ZephyrD (FloatingD f))
                TextZ t -> return (ZephyrD (TextD t))
                BinaryZ b -> return (ZephyrD (BinaryD b))

unquotedAtomP :: Parser (GenericZephyrAtom a b)
unquotedAtomP = (either (IntegerZ . fromIntegral) FloatingZ <$> signedNatFloat) <|>
                (TextZ . fromString <$> (stringLiteral :: Parser String)) <|>
                (BinaryZ . fromString <$> (char '$' *> (stringLiteral :: Parser String)))  <?> "unquoted atom"
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
                                  ; return (toEnum (fromIntegral code))
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

              signedNatFloat  = do isNeg <- ( (char '-' >> pure True) <|>
                                              pure False )
                                   let f :: Num a => a -> a
                                       f = if isNeg then negate else id
                                   either (Left . f) (Right . f) <$> natFloat

              natFloat        = do{ char '0'
                                  ; zeroNumFloat
                                  }
                                <|> decimalFloat

              zeroNumFloat    =  do{ n <- hexadecimal <|> octal
                                   ; return (Left n)
                                   }
                              <|> decimalFloat
                              <|> fractFloat 0
                              <|> return (Left 0)

              decimalFloat    = do{ n <- decimal
                                  ; option (Left n)
                                           (fractFloat n)
                                  }

              fractFloat n    = do{ f <- fractExponent n
                                  ; return (Right f)
                                  }

              fractExponent n = do{ fract <- fraction
                                  ; expo  <- option 1.0 exponent'
                                  ; return ((fromInteger n + fract)*expo)
                                  }
                              <|>
                                do{ expo <- exponent'
                                  ; return ((fromInteger n)*expo)
                                  }

              fraction        = do{ char '.'
                                  ; digits <- many1 digit <?> "fraction"
                                  ; return (foldr op 0.0 digits)
                                  }
                                <?> "fraction"
                              where
                                op d f    = (f + fromIntegral (digitToInt d))/10.0

              exponent'       = do{ oneOf "eE"
                                  ; f <- sign
                                  ; e <- decimal <?> "exponent"
                                  ; return (power (f e))
                                  }
                                <?> "exponent"
                              where
                                 power e  | e < 0      = 1.0/power(-e)
                                          | otherwise  = fromInteger (10^e)


              -- integers and naturals
              int             = do{ f <- sign
                                  ; n <- nat
                                  ; return (f n)
                                  }

              sign            =   (char '-' >> return negate)
                              <|> (char '+' >> return id)
                              <|> return id

              nat             = zeroNumber <|> decimal

              zeroNumber      = do{ char '0'
                                  ; hexadecimal <|> octal <|> decimal <|> return 0
                                  }
                                <?> ""

              decimal         = number 10 digit
              hexadecimal     = do{ oneOf "xX"; number 16 hexDigit }
              octal           = do{ oneOf "oO"; number 8 octDigit  }

              number base baseDigit
                  = do{ digits <- many1 baseDigit
                      ; let n = foldl (\x d -> base*x + toInteger (digitToInt d)) 0 digits
                      ; seq n (return n)
                      }

parseZephyrStack :: ByteString -> Either ParseError [ZephyrD]
parseZephyrStack bs = parse (many (literalP <* whitespace)) "<network>" bs

zephyrP :: Parser ZephyrBuilder
zephyrP = (whitespace <|> pure ()) *> go (ZephyrBuilder mempty) <?> "definition"
    where go b@(ZephyrBuilder rest) =
              ((atomP <* whitespace) >>= \atom ->
                   go (ZephyrBuilder (rest <> D.singleton atom))) <|>
              pure b

dependency :: Parser ZephyrWord
dependency = fromString <$> (string "IMPORT" *> whitespace *> zephyrIdentifier)

packageP :: Parser ZephyrPackage
packageP = do whitespace <|> pure ()
              string "PACKAGE"
              whitespace
              pkgName <- fromString <$> zephyrIdentifier
              whitespace
              dependencies <- many (dependency <* whitespace)
              (symbols, exports, dataTypes) <- mconcat <$> many1 (fstP symbolDef <|> sndP export <|> thdP (dataType pkgName))
              return (ZephyrPackage (ZephyrWord pkgName) dependencies (map fromString exports) dataTypes symbols)
    where symbolDef = try (string "DEFINE") *> whitespace *>
                      (ZephyrSymbolDefinition
                       <$> (fromString <$> zephyrIdentifier <* whitespace <* string "==" <* whitespace)
                       <*> zephyrP)
          export = string "EXPORT" *> whitespace *> zephyrIdentifier <* whitespace
          dataType pkgName =
              string "DATA" *> whitespace *>
              ( scopeTypes <$>
                ( ZippyAlgebraicT
                  <$> (ZippyTyCon <$> (ZippyTyName pkgName <$>
                                       (fromString <$> (zephyrConsIdentifier <* whitespace)))
                                  <*> ((V.fromList <$> many (tyArg <* whitespace))))
                  <*> (string "==" *> whitespace *> (V.fromList <$> many1 dataTypeCon) ) ))
          dataTypeCon = string "CONS" *> whitespace *>
                        (ZippyDataCon <$> (ZippyDataConName . fromString <$> ((zephyrConsIdentifier <?> "constructor name") <* whitespace))
                                      <*> (V.fromList <$> many dataConArg))
          dataConArg = do f <- try (ZippyNamedField <$> ((ZippyDataArgName . fromString <$> zephyrConsIdentifier) <* char '=')) <|> pure ZippyUnnamedField
                          f . Global <$> (try (SimpleFieldT <$> (simpleZippyTP <* whitespace)) <|>
                                          try (RefFieldT <$> recTyConP) <?> "type name" )
          tyArg = ZippyTyVarName . fromString <$> zephyrConsIdentifier <?> "type variable"

          simpleZippyTP = (string "Text"     *> pure TextT)     <|>
                          (string "Integer"  *> pure IntegerT)  <|>
                          (string "Binary"   *> pure BinaryT)   <|>
                          (string "Floating" *> pure FloatingT) <?> "simple type"
          recTyConP = (ZippyTyCon
                       <$> (ZippyTyName "" . fromString <$> (zephyrConsIdentifier <* whitespace))
                       <*> pure V.empty) <|>
                      ( char '(' *> optional whitespace *>
                        (ZippyTyCon <$> (ZippyTyName "" . fromString <$> (zephyrConsIdentifier <* whitespace))
                                    <*> (V.fromList <$> (many (Global <$> (try (SimpleFieldT <$> (simpleZippyTP <* whitespace)) <|>
                                                                           try (RefFieldT <$> recTyConP))))))
                        <* optional whitespace <* char ')' <* optional whitespace )

          fstP = (>>= \x -> pure ([x], [], []))
          sndP = (>>= \x -> pure ([], [x], []))
          thdP = (>>= \x -> pure ([], [], [x]))

scopeTypes ty@(ZippyAlgebraicT (ZippyTyCon _ tyVars) _) =
    let tyVarSet = S.fromList (V.toList tyVars)

        scopeRef input@(ZippyTyCon (ZippyTyName "" tyName) args)
            | ZippyTyVarName tyName `S.member` tyVarSet =
                if V.null args then Local (ZippyTyVarName tyName)
                               else error "Zephyr does not support higher-kinded types"
            | otherwise = Global (RefFieldT (fmap scopeGlobal input))

        scopeGlobal (Global (SimpleFieldT s)) = Global (SimpleFieldT s)
        scopeGlobal (Global (RefFieldT r)) = scopeRef r
        scopeGlobal (Local _) = error "Local found in parsed type"
    in fmap scopeGlobal ty

readZephyrPackage :: FilePath -> IO (Either ParseError ZephyrPackage)
readZephyrPackage fp = parseFromFile packageP fp
