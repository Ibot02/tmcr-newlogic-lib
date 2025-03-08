{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module TMCR.Parser.Shuffle where

import TMCR.Logic.Common
import TMCR.Parser.Common

import TMCR.Logic.Shuffle

import Text.Megaparsec as MP
import Text.Megaparsec.Char as MP
import qualified Text.Megaparsec.Char.Lexer as MPL
import Control.Monad.Combinators.Expr

import Control.Monad.State
import Control.Monad.Except

import Data.Text (Text())
import qualified Data.Text as T

import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as MM
import Data.Traversable (for)
import Data.Foldable (toList)

import Data.Functor.Foldable
import Data.Functor.Foldable.TH

import System.Random

import Control.Monad
import Control.Lens
import Control.Lens.TH
import Control.Monad.Reader (MonadReader, runReader, ReaderT(..))
import Data.List (partition)
import Data.Maybe (catMaybes)
import TMCR.Logic.Data (LogicData, DataLookup, evalDataLookup)
import TMCR.Parser.Data (parseDataLookup)

import GHC.Generics (Generic)
import Data.Hashable (Hashable)

import Data.Void

type Parser = ParserC ()

parseShuffleInstruction :: Parser ShuffleInstruction
parseShuffleInstruction = makeExprParser terms ops where
    terms = parseShuffleDataLookup <|> parseShuffleSetSpec <|> parseShuffleCountLiteral <|> parseShufflePlaceholder <|> parseShuffleCall <|> parseShuffleMatch <|> parseShuffleMap <|> between (MPL.symbol sc "(") (MPL.symbol sc ")") parseShuffleInstruction
    ops = [ [ binUnion ]
          , [ binThen ]
          , [ prefixRepeats, prefixReverse ]
          , [ binConnect ]
          ]
    prefixReverse = Prefix $ op "from" ShuffleReverse
    binUnion = InfixR $ op "union" ShuffleUnion
    binThen = InfixR $ op "then" ShuffleThen
    prefixRepeats = Prefix $ do
        MPL.symbol sc "repeat"
        MP.option ShuffleRepeat $ do
            MPL.symbol sc "individually"
            return ShuffleRepeatIndividually
    binConnect = InfixR $ op "connect" ShuffleConnect
    op n f = f <$ MPL.symbol sc n


parseShuffleMap = parseShuffleMap' <|> parseShuffleTake
parseShuffleMap' = do
    MPL.symbol sc "map"
    s1 <- parseShuffleInstruction
    MPL.symbol sc "to"
    s2 <- parseShuffleInstruction
    sIncl <- MP.option [] $ do
        MPL.symbol sc "including"
        parseShuffleInstruction `sepBy` MPL.symbol sc ","
    return $ ShuffleMap s1 s2 sIncl

parseShuffleTake = do
    MPL.symbol sc "take"
    s1 <- parseShuffleInstruction
    s2 <- parseShuffleInstruction
    return $ ShuffleMap s1 s2 []

parseShuffleDataLookup = do
    MPL.symbol sc "data"
    ShuffleDataLookup <$> parseDataLookup

parseShuffleSetSpec = ShuffleSetSpec <$> parseSetSpec
parseSetSpec = fmap (SetSpec . M.fromList) $ between (MPL.symbol sc "{") (MPL.symbol sc "}") $ parseShuffleSetSpecEntry `sepBy` MPL.symbol sc "," where
    parseShuffleSetSpecEntry = do
        n <- parsePossiblyScopedName
        c <- MP.option (Finite 1) $ do
            MPL.symbol sc ":"
            parseNteger
        return (n,c)
parseShuffleCountLiteral = ShuffleCountLiteral <$> parseNteger
parseShufflePlaceholder = ShufflePlaceholder <$ (MPL.symbol sc "..." <|> MPL.symbol sc "…")
parseShuffleCall = ShuffleCall <$> parseRelName
parseShuffleMatch = do
    MPL.symbol sc "match"
    s1 <- parseSetSpec
    MPL.symbol sc "in"
    s2 <- parseShuffleInstruction
    MPL.symbol sc "with"
    s3 <- between (MPL.symbol sc "(") (MPL.symbol sc ")") $ many $ do
        ss <- parseSetSpec
        MPL.symbol sc "->" <|> MPL.symbol sc "→"
        res <- parseShuffleInstruction
        return (ss, res)
    return $ ShuffleMatch s1 s2 s3

parseShuffleStatements :: Parser [ShuffleStatement]
parseShuffleStatements = (many $ MPL.nonIndented sc $ parseShuffleStatementDef <|> parseShuffleStatementExt) <* eof

parseShuffleStatementDef :: Parser ShuffleStatement
parseShuffleStatementDef = do
    name <- parseRelName
    MPL.symbol sc ":"
    instr <- parseShuffleInstruction
    return $ DefineShuffle name instr 

parseShuffleStatementExt :: Parser ShuffleStatement
parseShuffleStatementExt = do
    MPL.symbol sc "extend"
    name <- parseRelName
    MPL.symbol sc "by"
    instr <- parseShuffleInstruction
    return $ ExpandShuffle name instr
    --todo validate no placeholders are used in extensions

