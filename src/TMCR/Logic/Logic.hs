{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveGeneric #-}
module TMCR.Logic.Logic where

import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer

import Control.Monad.Reader

import Control.Monad

import Control.Lens.TH

import Data.Char (isSeparator)

import Data.Hashable (Hashable)

import Data.Void
import Data.Text (Text())
import qualified Data.Text as T
import GHC.Generics (Generic)

data Sugar = SugarOpList Text Text
           | SugarMulti [Text] Text
         deriving (Eq, Ord, Show)

data Name = PlainName Text
          | QuotedName Text
          | Wildcard
          deriving (Eq, Ord, Show, Generic)

instance Hashable Name where

type ScopeName = Text

data Value = Anon Text
           | NamedScoped Text ScopedName
           | NamedScoping Text Name
           | Edge ScopedName ScopedName
           | EdgeUndirected ScopedName ScopedName
           deriving (Eq, Ord, Show)

type LogicNodeName = ScopedName
data ScopedName = Global Name
                | Scoped [Name]
                | FullWildcard
                deriving (Eq, Ord, Show, Generic)

instance Hashable ScopedName where

data Mode = ModeDefault --select or new
          | ModeAppend
          | ModeReplace
          | ModeAppendIfExists
          | ModeReplaceIfExists
          | ModeReplaceOrCreate
          deriving (Eq, Ord, Show)

$(makePrisms ''Mode)

newtype Scopes = Scopes { getScopes :: [ScopeName] } deriving (Eq, Ord, Show)

type Forest = [Tree]
data Tree = Node Value Mode Forest
            deriving (Eq, Ord, Show)

{-
defaultSugar :: [Sugar]
defaultSugar = [
      SugarOpList "and" "&&"
    , SugarOpList "or" "||"
    , SugarOpList "and" "&"
    , SugarOpList "or" "|"
    ]
-}

nonLinebreakSpace :: Char -> Bool
nonLinebreakSpace c = isSeparator c && (c `notElem` ['\n','\r'])

sc :: (MonadParsec e Text m) => m ()
sc = Text.Megaparsec.Char.Lexer.space (void $ takeWhile1P (Just "space") nonLinebreakSpace) (skipLineComment "#") empty

scn :: (MonadParsec e Text m) => m ()
scn = Text.Megaparsec.Char.Lexer.space space1 (skipLineComment "#") empty

logicParser :: forall m. (MonadReader [Sugar] m, MonadParsec Void Text m) => Scopes -> m Forest
logicParser scopes = fmap concat $ many $ nonIndented scn $ parseTree (getScopes scopes) where
    parseTree :: [ScopeName] -> m [Tree]
    parseTree [] = (fmap (:[]) parseSugarOpList) <|> parseTree' []
    parseTree scopes = parseTree' scopes
    parseTree' :: [ScopeName] -> m [Tree]
    parseTree' scopes = indentBlock scn $ parseValue scopes >>= \v -> parseTreeHeader v (drop 1 scopes) <|> return (IndentNone [Node v ModeDefault [] | v <- v])
    parseTreeHeader :: [Value] -> [ScopeName] -> m (IndentOpt m [Tree] [Tree])
    parseTreeHeader v scopes = do
        m <- parseMode
        (IndentNone . (\c -> fmap (\v -> Node v m c) v) <$> inlineChildren scopes) <|> (return $ IndentSome Nothing (\c -> return $ [Node v m (join c) | v <- v]) (parseTree scopes))
    parseValue :: [ScopeName] -> m [Value]
    parseValue [] = parseAnonOrScoped <|> try parseEdge <|> parseUndirectedEdge
    parseValue (scope:_) = do
        typename <- symbol sc scope
        scopeName <- parseName
        return $ [NamedScoping typename scopeName]
    parseAnonOrScoped = do
        typename <- parseType
        typenames <- resolveMultis typename
        ((\arg -> fmap (\typename -> NamedScoped typename arg) typenames) <$> parseScopedName) <|> (return $ Anon <$> typenames)
    resolveMultis name = do
        sugar <- ask
        case (filter (\case
                SugarOpList _ _ -> False
                SugarMulti _ name' -> name == name') sugar) of
            [] -> return [name]
            [SugarMulti re _] -> return re
            _ -> error "multiple sugar multis of the same name"
    -- parseUndirectedEdge = label "edge" $ do
    --     source <- parseLocalName
    --     symbol sc "<->"
    --     target <- parseLocalName
    --     return $ EdgeUndirected source target
    parseUndirectedEdge = label "edge" $ do
        source <- parseLocalName
        symbol sc "<->"
        target <- parseLocalName
        return $ [Edge source target, Edge target source]
    parseEdge = label "edge" $ do
        source <- parseLocalName
        symbol sc "->"
        target <- parseLocalName
        return $ [Edge source target]
    parseType = fmap T.pack . lexeme sc $ (:) <$> lowerChar <*> many alphaNumChar
    parseScopedName :: m ScopedName
    --parseScopedName = label "name" $ (char 'g' *> (Global <$> parseName)) <|> (try $ FullWildcard <$ symbol sc "**") <|> parseLocalName --wildcards are no longer a thing
    parseScopedName = label "name" $ (char 'g' *> (Global <$> parseName)) <|> parseLocalName
    parseLocalName :: m ScopedName
    parseLocalName = (lexeme sc $ Scoped <$> (parseName' `sepBy1` char '.'))
    parseName :: m Name
    parseName = lexeme sc parseName' <?> "name"
    parseName' :: m Name
    --parseName' = (QuotedName . T.pack <$> between (char '"') (char '"') (many possiblyEscapedChar)) <|> (PlainName . T.pack <$> ((:) <$> upperChar <*> many alphaNumChar)) <|> (Wildcard <$ char '*') --wildcards are no longer a thing
    parseName' = (QuotedName . T.pack <$> between (char '"') (char '"') (many possiblyEscapedChar)) <|> (PlainName . T.pack <$> ((:) <$> upperChar <*> many alphaNumChar))
    possiblyEscapedChar :: m Char
    possiblyEscapedChar = do
        c <- satisfy (/= '"')
        case c of
            '\\' -> anySingle
            _ -> return c
    parseMode :: m Mode
    parseMode = lexeme sc $ label "mode" $ (ModeDefault <$ char ':') <|> (ModeAppend <$ string "+:") <|> (ModeReplace <$ string "!:")
                                              <|> (ModeAppendIfExists <$ string "+?:") <|> (ModeReplaceIfExists <$ string "!?:") <|> (ModeReplaceOrCreate <$ string "!+:")
    inlineChildren :: [ScopeName] -> m [Tree]
    inlineChildren scopes = fmap concat $ label "inlined Childen" $ inlineChild scopes `sepBy1` (symbol sc ",")
    inlineChild :: [ScopeName] -> m [Tree]
    inlineChild [] = (fmap (:[]) parseSugarOpList) <|> inlineChild' []
    inlineChild scopes = inlineChild' scopes
    inlineChild' :: [ScopeName] -> m [Tree]
    inlineChild' scopes = between (symbol sc "(") (symbol sc ")") (inlineChild scopes) <|> (do
        v <- parseValue scopes 
        (m,c) <- option (ModeDefault, []) $ do
            m <- parseMode
            c <- (inlineChildren $ drop 1 scopes)
            return (m,c)
        return $ fmap (\v' -> Node v' m c) v
        )
    parseSugarOpList :: m Tree
    parseSugarOpList = ask >>= choice . fmap (\(SugarOpList name sep) -> try $
        between (symbol sc "(") (symbol sc ")") $ Node (Anon name) ModeDefault . concat <$> (inlineChild [] `sepBy` (symbol sc sep))) . filter (\case
            SugarOpList _ _ -> True
            _ -> False)
