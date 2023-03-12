{-# LANGUAGE OverloadedStrings #-}
module TMCR.Logic.Shuffle where

import TMCR.Logic.Common

import Text.Megaparsec as MP
import Text.Megaparsec.Char as MP
import qualified Text.Megaparsec.Char.Lexer as MPL
import Control.Monad.Combinators.Expr

import Data.Text (Text())
import qualified Data.Text as T

import qualified Data.Set as S

type Parser = ParserC ()

data ShuffleInstruction =
      ShuffleDataLookup DataLookup
    | ShuffleSetSpec SetSpec
    | ShuffleCountLiteral Nteger
    | ShufflePlaceholder -- ...
    | ShuffleCall ShuffleName
    | ShuffleReverse ShuffleInstruction -- from
    | ShuffleRepeat ShuffleInstruction
    | ShuffleRepeatIndividually ShuffleInstruction
    | ShuffleMap ShuffleInstruction ShuffleInstruction [ShuffleInstruction]
    | ShuffleConnect ShuffleInstruction ShuffleInstruction
    | ShuffleUnion ShuffleInstruction ShuffleInstruction
    | ShuffleThen ShuffleInstruction ShuffleInstruction
    | ShuffleMatch SetSpec ShuffleInstruction [(SetSpec, ShuffleInstruction)]
    deriving (Eq, Ord, Show)

data ShuffleStatement =
      DefineShuffle Name ShuffleInstruction
    | ExpandShuffle Name ShuffleInstruction
    deriving (Eq, Ord, Show)

data SetSpec = SetSpec (S.Set (PossiblyScopedName, Nteger))
    deriving (Eq, Ord, Show)

type ShuffleName = Text

data DataLookup = DataLookup {
      location :: [DataStep]
    , foreach :: Maybe ([DataStep], DataTarget)
    , collect :: ([DataStep], DataTarget)
    } deriving (Eq, Ord, Show)

data DataStep =
      DataTraverse DataTraverseStep
    | DataFilter DataFilterStep
    deriving (Eq, Ord, Show)

data DataTraverseStep = DataTraverseStep {
      traverseAttribute :: Name
    , traversalScoping :: Maybe Name
    } deriving (Eq, Ord, Show)

data DataFilterStep = DataFilterStep {
      filterLocation :: [DataStep]
    , filterAttribute :: DataTarget
    , filterCondition :: FilterCondition
    } deriving (Eq, Ord, Show)

data FilterCondition = --do we want any other filters? e.g. matching regex?
    FilterEQ PossiblyScopedName
    deriving (Eq, Ord, Show)

data DataTarget = DataTarget {
      targetedAttribute :: Name
    , targetScoping :: TargetScoping
    } deriving (Eq, Ord, Show)

data TargetScoping = TargetUnscoped | TargetScoped | TargetGlobal
    deriving (Eq, Ord, Show, Enum, Bounded)

parseDataLookup :: Parser DataLookup
parseDataLookup = do
    loc <- parseDataSteps
    f <- MP.optional $ do
        MPL.symbol sc "foreach"
        parseDataStepsToTarget
    MPL.symbol sc "collect"
    c <- parseDataStepsToTarget
    return $ DataLookup loc f c

parseDataSteps :: Parser [DataStep]
parseDataSteps = parseDataStep `sepBy` MPL.symbol sc ","

parseDataStepsToTarget :: Parser ([DataStep], DataTarget)
parseDataStepsToTarget = do
    loc <- many (parseDataStep <* MPL.symbol sc ",")
    t <- parseDataTarget
    return (loc, t)

parseDataStep :: Parser DataStep
parseDataStep = (DataFilter <$> parseDataFilterStep) <|> (DataTraverse <$> parseDataTraverseStep)

parseDataFilterStep :: Parser DataFilterStep
parseDataFilterStep = do
    MPL.symbol sc "filter"
    MPL.symbol sc "any"
    (loc, t) <- parseDataStepsToTarget
    c <- parseFilterCondition
    return $ DataFilterStep loc t c

parseFilterCondition :: Parser FilterCondition
parseFilterCondition = parseFilterEq where
    parseFilterEq = do
        MPL.symbol sc "is"
        FilterEQ <$> parsePossiblyScopedName

parseDataTraverseStep :: Parser DataTraverseStep
parseDataTraverseStep = do
    n <- parseDataAttrName
    scope <- MP.optional $ do
                MPL.symbol sc "by"
                parseDataAttrName
    return $ DataTraverseStep n scope

parseDataTarget :: Parser DataTarget
parseDataTarget = do
    scope <- (TargetUnscoped <$ MPL.symbol sc "unscoped") <|> (TargetScoped <$ MPL.symbol sc "local") <|> (TargetGlobal <$ MPL.symbol sc "global")
    attr <- parseDataAttrName

    return $ DataTarget attr scope

parseDataAttrName :: Parser Name
parseDataAttrName = MPL.lexeme sc parseDataAttrName'
parseDataAttrName' :: Parser Name
parseDataAttrName' = fmap T.pack $ MP.single '\'' *> MP.manyTill MPL.charLiteral (MP.single '\'')

parseShuffleInstruction :: Parser ShuffleInstruction
parseShuffleInstruction = makeExprParser terms ops where
    terms = parseShuffleDataLookup <|> parseShuffleSetSpec <|> parseShuffleCountLiteral <|> parseShufflePlaceholder <|> parseShuffleCall <|> parseShuffleMatch <|> parseShuffleMap <|> between (MPL.symbol sc "(") (MPL.symbol sc ")") parseShuffleInstruction
    ops = [ [ prefixReverse ]
          , [ binUnion ]
          , [ binThen ]
          , [ prefixRepeats ]
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
parseSetSpec = fmap (SetSpec . S.fromList) $ between (MPL.symbol sc "{") (MPL.symbol sc "}") $ parseShuffleSetSpecEntry `sepBy` MPL.symbol sc "," where
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
parseShuffleStatements = many $ MPL.nonIndented sc $ parseShuffleStatementDef <|> parseShuffleStatementExt

parseShuffleStatementDef :: Parser ShuffleStatement
parseShuffleStatementDef = do
    name <- parseName
    MPL.symbol sc ":"
    instr <- parseShuffleInstruction
    return $ DefineShuffle name instr 

parseShuffleStatementExt :: Parser ShuffleStatement
parseShuffleStatementExt = do
    MPL.symbol sc "extend"
    name <- parseName
    MPL.symbol sc "by"
    instr <- parseShuffleInstruction
    return $ ExpandShuffle name instr
    --todo validate no placeholders are used in extensions