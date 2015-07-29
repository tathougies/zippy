{-# LANGUAGE OverloadedStrings #-}
module Database.Zippy.Schema where

-- import Database.Zippy.Types

-- import Control.Applicative hiding ((<|>), many)

-- import Data.ByteString.Lazy (ByteString)
-- import Data.Text (Text)
-- import Data.String
-- import Data.List (findIndex)
-- import Data.Char
-- import Data.Either
-- import qualified Data.Text as T
-- import qualified Data.ByteString.Lazy as BS
-- import qualified Data.Vector as V

-- import Text.Parsec
-- import Text.Parsec.Indent

-- type IParser a = IndentParser ByteString () a

-- data UserType = UserType Text [ParsedCon] deriving Show
-- data ParsedCon = ParsedCon Text [Either ZippySimpleT Text] deriving Show

-- schemaP :: IParser ZippySchema
-- schemaP = schemaFromPackageAndDecls <$> (packageDecl <* spaces) <*> withPos (many (checkIndent *> userTypeDecl <* spaces))
--     where schemaFromPackageAndDecls pkgName userTypeDecls =
--             do let types = map (AlgebraicT . mkZippyAlgebraicT) userTypeDecls

--                    mkZippyAlgebraicT (UserType tyName cons) =
--                        ZippyAlgebraicT (ZippyTyName pkgName tyName) (V.fromList (map mkZippyTyCon cons))
--                    mkZippyTyCon (ParsedCon conName args) =
--                        ZippyDataCon (ZippyDataConName conName) (V.fromList (map (mkArgType userTypeDecls) args))

--                case findIndex (\(UserType tyName _) -> tyName == "Database") userTypeDecls of
--                  Just i -> ZippySchema (ZippyTyRef i) (V.fromList types)
--                  Nothing -> error ("No 'Database' type specified. Got " ++ show userTypeDecls)

--           mkArgType typeDecls = ZippyUnnamedField . either Left (findDtByName typeDecls)

--           findDtByName typeDecls name =
--               case findIndex (\(UserType tyName _) -> tyName == name) typeDecls of
--                 Just i -> Right (ZippyTyRef i)
--                 Nothing -> error ("No such datatype: " ++ T.unpack name ++ " (looked in " ++ show typeDecls ++ ")")

-- packageDecl :: IParser Text
-- packageDecl = fromString <$> (string "Package" *> spaces *> many1 (satisfy (/= '\n')))

-- userTypeDecl :: IParser UserType
-- userTypeDecl =  UserType <$> (fromString <$> (many1 (satisfy (not . isSpace))) <* spaces) <*> withPos (many (checkIndent *> conDecl <* spaces))

-- conDecl :: IParser ParsedCon
-- conDecl = withPos (ParsedCon <$> (fromString <$> (many1 (satisfy (not . isSpace))) <* spaces) <*> many (sameOrIndented *> (try (Left <$> simpleType) <|> try (Right <$> dtName)) <* spaces))

-- dtName :: IParser Text
-- dtName = fromString <$> (many1 (letter <|> digit))

-- simpleType :: IParser ZippySimpleT
-- simpleType = go
--     where go = (string "Integer"  *> pure IntegerT)  <|>
--                (string "Text"     *> pure TextT)     <|>
--                (string "Floating" *> pure FloatingT) <|>
--                (string "Binary"   *> pure BinaryT)   <?>
--                "simple type"

-- readSchemaFromFile :: FilePath -> IO ZippySchema
-- readSchemaFromFile fp =
--     do fileContents <- BS.readFile fp
--        case runIndent fp $ runParserT schemaP () fp fileContents of
--          Left err -> fail (show err)
--          Right x -> return x
