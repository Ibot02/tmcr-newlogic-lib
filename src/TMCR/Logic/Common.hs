{-# Language OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveGeneric #-}
module TMCR.Logic.Common where

import Text.Megaparsec as MP
import Text.Megaparsec.Char as MP
import qualified Text.Megaparsec.Char.Lexer as MPL
import Control.Monad.Combinators.Expr

import qualified Data.Set as S

import Data.Text (Text())
import qualified Data.Text as T
import Data.Void

import Control.Monad.Reader
import Polysemy
import qualified Polysemy.Reader as PR
import Polysemy.Error
import Control.Monad.Identity
import GHC.Generics (Generic)
import Data.Hashable (Hashable)

--type ParserC c = ParsecT Void Text (Reader c)
type ParserC c = ParserCT c Identity
type ParserCT c m = ParsecT Void Text (ReaderT c m)

runParserC :: (Members [Error (ParseErrorBundle Text Void), PR.Reader c] r) => ParserC c a -> FilePath -> Text -> Sem r a
runParserC p l i = do
    x <- PR.ask
    either throw return $ runReader (runParserT p l i) x

sc :: ParserCT c m () 
sc = MPL.space MP.space1 (MPL.skipLineComment "--") (MPL.skipBlockComment "{-" "-}")

strErrorWithPos :: Int -> String -> ParserCT c m a
#if MIN_VERSION_megaparsec(8,0,0)
strErrorWithPos pos str = parseError $ FancyError pos $ S.singleton $ ErrorFail str
#else
strErrorWithPos _ str = fail str
#endif

assertEq :: (Eq a) => a -> a -> Int -> (a -> a -> String) -> ParserCT c m ()
assertEq x y pos msg | x == y = return ()
                     | otherwise = strErrorWithPos pos $ msg x y

type Name = Text

data PossiblyScopedName = Global Text
                        | ScopedName [Text]
                deriving (Eq, Ord, Show, Generic)

instance Hashable PossiblyScopedName where

parsePossiblyScopedName :: ParserCT c m PossiblyScopedName
parsePossiblyScopedName = MPL.lexeme sc parsePossiblyScopedName'
parsePossiblyScopedName' :: ParserCT c m PossiblyScopedName
parsePossiblyScopedName' = (Global <$> (MP.single 'g' *> parseVarName')) <|> (ScopedName <$> sepBy1' parseVarName' (MP.single '.')) where
    sepBy1' p sep = do
        x <- p
        (x:) <$> many (MP.try $ sep >> p)

parseName :: ParserCT c m Name
parseName = MPL.lexeme sc parseName'
parseName' :: ParserCT c m Name
parseName' = fmap T.pack $ (:) <$> MP.lowerChar <*> many MP.alphaNumChar

type VarName = Text

parseVarName :: ParserCT c m VarName
parseVarName = MPL.lexeme sc parseVarName'
parseVarName' :: ParserCT c m VarName
parseVarName' = unquoted <|> quoted where
    unquoted :: ParserCT c m VarName
    unquoted = fmap T.pack $ (:) <$> MP.upperChar <*> many MP.alphaNumChar
    quoted :: ParserCT c m VarName
    quoted = fmap T.pack $ MP.single '"' *> MP.manyTill MPL.charLiteral (MP.single '"')

data Nteger = Finite Int | Infinite deriving (Eq, Ord, Show)

parseNteger :: ParserCT c m Nteger
parseNteger = (Infinite <$ (MPL.symbol sc "inf" <|> MPL.symbol sc "∞")) <|> (Finite <$> MPL.lexeme sc (read <$> some MP.digitChar))

type RelName = Text

parseRelName :: ParserCT c m RelName
parseRelName = MPL.lexeme sc parseRelName'
parseRelName' :: ParserCT c m RelName
parseRelName' = fmap T.pack $ (:) <$> MP.upperChar <*> many MP.alphaNumChar

type Thingy = PossiblyScopedName
