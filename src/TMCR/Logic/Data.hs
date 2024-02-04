{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE CPP #-}
module TMCR.Logic.Data where
import Data.Map (Map)
import qualified Data.Map as M
import Data.IntMap (IntMap)
import Data.Text (Text)
import TMCR.Logic.Logic (Mode (..))
import Data.Aeson (Value (..), Object, FromJSON (..), withObject, (.!=), (.:))
import Data.Aeson.Parser (decodeWith)
import qualified Data.Text as T
import Control.Lens (TraversableWithIndex(itraverse), FoldableWithIndex (ifoldMap))
import Control.Applicative (Alternative(..))
import qualified Data.IntMap as IM
import Data.Aeson.TH(deriveJSON, defaultOptions)
import Text.Read (readMaybe)
import Data.Foldable (Foldable(..))
#if MIN_VERSION_aeson(2,0,0)
import Data.Aeson.Key (toString)
import Data.Aeson.KeyMap (toMapText, delete)
import qualified Text.Megaparsec.Char.Lexer as MPL
import Text.Megaparsec as MP
import TMCR.Logic.Common (Name, ParserC, PossiblyScopedName, ParserCT, parsePossiblyScopedName, Nteger, Thingy)
import Text.Megaparsec.Char as MP
#else
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
#endif

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

newtype LogicData = LogicData (Map Text (Either Text (IntMap LogicData))) deriving (Eq, Ord, Show)
newtype LogicData' = LogicData' (Map Text (Either Text (Mode, IntMap (Maybe LogicData')))) deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''Mode)

instance FromJSON LogicData' where
#if MIN_VERSION_aeson(2,0,0)
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
#else
    parseJSON = stepObj where
        stepObj = withObject "LogicData" $ fmap LogicData' . traverse step . M.fromList . HM.toList
        stepObj' v = (Just <$> stepObj v) <|> withNull Nothing v
        step (String t) = return $ Left t
        step (Number n) = return $ Left $ T.pack $ show n
        step Null = fail "Data Values may not be null" --todo: reconsider, maybe interpret as ()?
        step (Array xs) = fmap (Right . (,) ModeDefault) $ sequenceA $ ifoldMap (\i -> IM.singleton i . stepObj') xs
        step (Object o) = do
            mode <- o .: "mode"
            let o' = HM.delete "mode" o
            c <- fold <$> itraverse (\k v ->
                case readMaybe $ T.unpack k of
                    Nothing -> fail "unexpected key"
                    Just n -> do
                        v' <- stepObj' v
                        return $ IM.singleton n v') o'
            return $ Right (mode, c)
#endif

withNull a Null = pure a
withNull _ _ = fail "expected null"

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


evalDataLookup :: LogicData -> DataLookup -> [(Thingy, Nteger, Thingy)]
evalDataLookup = undefined