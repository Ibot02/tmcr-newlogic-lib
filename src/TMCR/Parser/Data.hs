{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
module TMCR.Parser.Data where

import TMCR.Logic.Data

import Data.Map (Map)
import qualified Data.Map as M
import Data.IntMap (IntMap)
import Data.Text (Text)
import TMCR.Logic.Logic (Mode (..))
import Data.Aeson (Value (..), Object, FromJSON (..), withObject, (.!=), (.:))
import Data.Aeson.Parser (decodeWith)
import qualified Data.Text as T
import Control.Lens (TraversableWithIndex(itraverse), FoldableWithIndex (ifoldMap), Traversal, _Right, _Left, _Just, coerced, at, Iso, filtered, (^..), Getting, LensLike, to, (^?))
import Control.Applicative (Alternative(..), Const (..))
import qualified Data.IntMap as IM
import Data.Aeson.TH(deriveJSON, defaultOptions)
import Text.Read (readMaybe)
import Data.Foldable (Foldable(..))

import Data.Aeson.Key (toString)
import Data.Aeson.KeyMap (toMapText, delete)
import qualified Text.Megaparsec.Char.Lexer as MPL
import Text.Megaparsec as MP
import TMCR.Logic.Common (Name, PossiblyScopedName (..), Nteger (Finite), Thingy)
import TMCR.Parser.Common (ParserC, ParserCT, parsePossiblyScopedName, parsePossiblyScopedName')
import Text.Megaparsec.Char as MP
import Control.Monad.Reader
import Data.Kind (Constraint, Type)
import Data.Monoid (Endo)
import Data.Maybe (fromMaybe)

import Data.Functor.Identity (Identity(..))



{-
{ "elements" : [
      { "id" : "64"
      , "name" : "EarthElement"
      }
    , {"name" : "WaterElement"}
    , {"name" : "FireElement"}
    , {"name" : "WindElement"}
    ]
, "areas" : [
      null
    , 
]}

{ "elements" : {
    "mode" :"replace",
    "1" : null
}}
-}

$(deriveJSON defaultOptions ''Mode)

instance FromJSON LogicData' where
    parseJSON = stepObj where
        stepObj = withObject "LogicData" $ fmap LogicData' . traverse step . toMapText
        stepObj' v = (Just <$> stepObj v) <|> withNull Nothing v
        step (String t) = return $ Left t
        step (Number n) = return $ Left $ T.pack $ show n
        step Null = fail "Data Values may not be null" --todo: reconsider, maybe interpret as ()?
        step (Array xs) = fmap (Right . (,) ModeDefault) $ sequenceA $ ifoldMap (\i -> IM.singleton i . stepObj') xs
        step (Object o) = do
            mode <- o .: "mode"
            let o' = delete "mode" o
            c <- fold <$> itraverse (\k v ->
                case readMaybe $ toString k of
                    Nothing -> fail "unexpected key"
                    Just n -> do
                        v' <- stepObj' v
                        return $ IM.singleton n v') o'
            return $ Right (mode, c)
        step v = fail $ "Unsupported Data Value " ++ show v

withNull a Null = pure a
withNull _ _ = fail "expected null"

type Parser = ParserC ()

sc :: ParserCT c m ()
sc = MPL.space MP.space1 (MPL.skipLineComment "--") (MPL.skipBlockComment "{-" "-}")

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
    loc <- MP.many (parseDataStep <* MPL.symbol sc ",")
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
