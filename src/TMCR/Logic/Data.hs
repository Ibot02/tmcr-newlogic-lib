{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
module TMCR.Logic.Data where
import Data.Map (Map)
import Data.IntMap (IntMap)
import Data.Text (Text)
import TMCR.Logic.Logic (Mode (..))
import Data.Aeson (Value (..), Object, FromJSON (..), withObject, (.!=), (.:))
import Data.Aeson.Parser (decodeWith)
import Data.Aeson.KeyMap (toMapText, delete)
import qualified Data.Text as T
import Control.Lens (TraversableWithIndex(itraverse), FoldableWithIndex (ifoldMap))
import Control.Applicative (Alternative(..))
import qualified Data.IntMap as IM
import Data.Aeson.TH(deriveJSON, defaultOptions)
import Text.Read (readMaybe)
import Data.Aeson.Key (toString)
import Data.Foldable (Foldable(..))

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

withNull a Null = pure a
withNull _ _ = fail "expected null"