{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module TMCR.Logic.Logic where

import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer

import Control.Monad.Reader

import Control.Monad

import Control.Lens.TH

import Data.Char (isSeparator)

import Data.Void
import Data.Text (Text())
import qualified Data.Text as T

data Sugar = SugarOpList Text Text
         deriving (Eq, Ord, Show)

data Name = PlainName Text
          | QuotedName Text
          | Wildcard
          deriving (Eq, Ord, Show)

type ScopeName = Text

data Value = Anon Text
           | NamedScoped Text ScopedName
           | NamedScoping Text Name
           | Edge ScopedName ScopedName
           | EdgeUndirected ScopedName ScopedName
           deriving (Eq, Ord, Show)

data ScopedName = Global Name
                | Scoped [Name]
                | FullWildcard
                deriving (Eq, Ord, Show)

data Mode = ModeDefault --select or new
          | ModeAppend
          | ModeReplace
          deriving (Eq, Ord, Show)

$(makePrisms ''Mode)

newtype Scopes = Scopes { getScopes :: [ScopeName] } deriving (Eq, Ord, Show)

type Forest = [Tree]
data Tree = Node Value Mode Forest
            deriving (Eq, Ord, Show)

defaultSugar :: [Sugar]
defaultSugar = [
      SugarOpList "and" "&&"
    , SugarOpList "or" "||"
    ]

nonLinebreakSpace :: Char -> Bool
nonLinebreakSpace c = isSeparator c && (c `notElem` ['\n','\r'])

sc :: (MonadParsec e Text m) => m ()
sc = Text.Megaparsec.Char.Lexer.space (void $ takeWhile1P (Just "space") nonLinebreakSpace) (skipLineComment "#") empty

scn :: (MonadParsec e Text m) => m ()
scn = Text.Megaparsec.Char.Lexer.space space1 (skipLineComment "#") empty

logicParser :: (MonadReader [Sugar] m, MonadParsec Void Text m) => Scopes -> m Forest
logicParser scopes = many $ nonIndented scn $ parseTree (getScopes scopes) where
    -- parseTree :: [ScopeName] -> ReaderT [Sugar] (Parsec Void Text) Tree
    parseTree [] = parseSugarOpList <|> parseTree' []
    parseTree scopes = parseTree' scopes
    -- parseTree' :: [ScopeName] -> ReaderT [Sugar] (Parsec Void Text) Tree
    parseTree' scopes = indentBlock scn $ parseValue scopes >>= \v -> parseTreeHeader v (drop 1 scopes) <|> return (IndentNone (Node v ModeDefault []))
    -- parseTreeHeader :: Value -> [ScopeName] -> ReaderT [Sugar] (Parsec Void Text) (IndentOpt (ReaderT [Sugar] (Parsec Void Text)) Tree Tree)
    parseTreeHeader v scopes = do
        m <- parseMode
        (IndentNone . Node v m <$> inlineChildren scopes) <|> (return $ IndentSome Nothing (return . Node v m) (parseTree scopes))
    -- parseValue :: [ScopeName] -> ReaderT [Sugar] (Parsec Void Text) Value
    parseValue [] = parseAnonOrScoped <|> try parseEdge <|> parseUndirectedEdge
    parseValue (scope:_) = do
        typename <- symbol sc scope
        scopeName <- parseName
        return $ NamedScoping typename scopeName
    parseAnonOrScoped = do
        typename <- parseType
        (NamedScoped typename <$> parseScopedName) <|> (return $ Anon typename)
    parseUndirectedEdge = label "edge" $ do
        source <- parseLocalName
        symbol sc "<->"
        target <- parseLocalName
        return $ EdgeUndirected source target
    parseEdge = label "edge" $ do
        source <- parseLocalName
        symbol sc "->"
        target <- parseLocalName
        return $ Edge source target
    parseType = fmap T.pack . lexeme sc $ (:) <$> lowerChar <*> many alphaNumChar
    -- parseScopedName :: ReaderT [Sugar] (Parsec Void Text) ScopedName
    parseScopedName = label "name" $ (char 'g' *> (Global <$> parseName)) <|> (try $ FullWildcard <$ symbol sc "**") <|> parseLocalName
    -- parseLocalName :: ReaderT [Sugar] (Parsec Void Text) ScopedName
    parseLocalName = (lexeme sc $ Scoped <$> (parseName' `sepBy1` char '.'))
    -- parseName :: ReaderT [Sugar] (Parsec Void Text) Name
    parseName = lexeme sc parseName' <?> "name"
    -- parseName' :: ReaderT [Sugar] (Parsec Void Text) Name
    parseName' = (QuotedName . T.pack <$> between (char '"') (char '"') (many possiblyEscapedChar)) <|> (PlainName . T.pack <$> ((:) <$> upperChar <*> many alphaNumChar)) <|> (Wildcard <$ char '*')
    --possiblyEscapedChar :: ReaderT [Sugar] (Parsec Void Text) Char
    possiblyEscapedChar = do
        c <- satisfy (/= '"')
        case c of
            '\\' -> anySingle
            _ -> return c
    -- parseMode :: ReaderT [Sugar] (Parsec Void Text) Mode
    parseMode = lexeme sc $ label "mode" $ (ModeDefault <$ char ':') <|> (ModeAppend <$ string "+:") <|> (ModeReplace <$ string "!:")
    -- inlineChildren :: [ScopeName] -> ReaderT [Sugar] (Parsec Void Text) Forest
    inlineChildren scopes = label "inlined Childen" $ inlineChild scopes `sepBy1` (symbol sc ",")
    -- inlineChild :: [ScopeName] -> ReaderT [Sugar] (Parsec Void Text) Tree
    inlineChild [] = parseSugarOpList <|> inlineChild' []
    inlineChild scopes = inlineChild' scopes
    -- inlineChild' :: [ScopeName] -> ReaderT [Sugar] (Parsec Void Text) Tree
    inlineChild' scopes = between (symbol sc "(") (symbol sc ")") (inlineChild scopes) <|> (do
        v <- parseValue scopes 
        (m,c) <- option (ModeDefault, []) $ do
            m <- parseMode
            c <- (inlineChildren $ drop 1 scopes)
            return (m,c)
        return $ Node v m c
        )
    -- parseSugarOpList :: ReaderT [Sugar] (Parsec Void Text) Tree
    parseSugarOpList = ask >>= choice . fmap (\(SugarOpList name sep) -> try $
        between (symbol sc "(") (symbol sc ")") $ Node (Anon name) ModeDefault <$> inlineChild [] `sepBy` (symbol sc sep))
