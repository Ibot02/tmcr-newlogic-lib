{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
module TMCR.Module where

import Data.Text (Text())
import qualified Data.Text as T

import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE

import Data.Aeson
    ( FromJSON(parseJSON),
      ToJSON(toJSON),
      Value(String),
      withText,
      camelTo2,
      defaultOptions,
      Options(constructorTagModifier, fieldLabelModifier,
              omitNothingFields, rejectUnknownFields) )
import Data.Aeson.TH
import Data.Char

import Data.Map (Map())
import qualified Data.Map as Map

import Data.Maybe
import Data.Either
import Text.Read (readMaybe)

import Control.Monad
import Control.Applicative

import Data.Void

import qualified Text.Megaparsec as MP
import qualified Text.Megaparsec.Char as MP

import Control.Lens.TH
import TMCR.Logic.Logic (Forest)
import TMCR.Logic.Data (LogicData')
import TMCR.Logic.Shuffle (ShuffleStatement)
import TMCR.Logic.Descriptor
import Data.Dependent.Map (DMap)

data Module = Module {
      _moduleName :: Text
    , _moduleVersion :: Version
    , _moduleSyntaxVersion :: Version
    , _moduleDependencies :: [(Text, VersionSpec)]
    , _moduleSoftDependency :: [(Text, VersionSpec)]
    , _moduleProvides :: ModuleContent
    } deriving (Eq, Ord, Show)

data ModuleFull = ModuleFull {
      _moduleFullName :: Text
    , _moduleFullVersion :: Version
    , _moduleFullDependencies :: [(Text, VersionSpec)]
    , _moduleFullSoftDependency :: [(Text, VersionSpec)]
    , _moduleFullProvides :: ModuleFullContent
    }

newtype Version = Version { getVersion :: [Int] } deriving (Eq, Ord, Show)

data VersionSpec = VersionSpecRange (Maybe Version) (Maybe Version) deriving (Eq, Ord, Show)

versionMatches :: VersionSpec -> Version -> Bool
versionMatches (VersionSpecRange minV maxV) v = maybe True (<= v) minV && maybe True (v <) maxV

data ModuleContent = ModuleContent {
      _moduleContentDescriptors :: Map DescriptorName DescriptorDeclaration
    , _moduleContentDescriptorDefinitions :: [ResourceSpecifier]
    , _moduleContentLogic :: [ResourceSpecifier]
    , _moduleContentPatches :: [ResourceSpecifier]
    , _moduleContentData :: [ResourceSpecifier]
    , _moduleContentShuffles :: [ResourceSpecifier]
    } deriving (Eq, Ord, Show)

data ModuleFullContent = ModuleFullContent {
      _moduleFullContentDescriptors :: Map DescriptorName DescriptorDeclaration
    , _moduleFullContentDescriptorDefinitions :: DMap DescriptorIdent Descriptors
    , _moduleFullContentLogic :: [Forest]
    , _moduleFullContentPatches :: [ResourceSpecifier]
    , _moduleFullContentData :: [LogicData']
    , _moduleFullContentShuffles :: [ShuffleStatement]
    }

type ResourceSpecifier = Text

instance ToJSON Version where
    toJSON (Version v) = String $ T.pack $ foldr1 (\x y -> x <> "." <> y) $ fmap show v

instance FromJSON Version where
    parseJSON = withText "Version" $ either (fail . show) return . MP.parse parseVersion ""

instance ToJSON VersionSpec where
    toJSON (VersionSpecRange Nothing Nothing) = String "*"
    toJSON (VersionSpecRange x y) = String $ case (fmap (h ">=") x, fmap (h "<") y) of
        (Nothing, Just y) -> y
        (Just x, Nothing) -> x
        (Just x, Just y) -> x <> " , " <> y
        where 
            h :: Text -> Version -> Text
            h t (Version x) = t <> " " <> (T.intercalate "." . fmap (T.pack . show) $ x)

instance FromJSON VersionSpec where
    parseJSON = withText "Version Specification" $ (either (fail . show) return . MP.parse parser "") where
        parser :: MP.Parsec Void Text VersionSpec
        parser = (parseAny <|> parseRange) <* MP.eof
        parseAny = fmap (const (VersionSpecRange Nothing Nothing)) $ MP.single '*'
        parseRange = fmap (uncurry VersionSpecRange) $ ((,) . Just <$> parseRangeLower <*> MP.option Nothing (fmap Just $ MP.single ',' *> MP.space *> parseRangeUpper)) <|> fmap ((,) Nothing . Just) parseRangeUpper
        parseRangeLower = parseRangePart ">="
        parseRangeUpper = parseRangePart "<"
        parseRangePart t = do
            MP.chunk t
            MP.space
            r <- parseVersion
            MP.space
            return r

parseVersion :: MP.Parsec Void Text Version
parseVersion = fmap Version $ flip MP.sepBy (MP.single '.') $ do
    ns <- some MP.digitChar
    return $ read ns

$(deriveJSON defaultOptions{ fieldLabelModifier = camelTo2 '-' . drop (T.length "_moduleContent"), omitNothingFields = True, rejectUnknownFields = True} ''ModuleContent)
$(deriveJSON defaultOptions{ fieldLabelModifier = camelTo2 '-' . drop (T.length "_module"), omitNothingFields = True, rejectUnknownFields = True} ''Module)
$(makeLenses ''Module)
$(makeLenses ''ModuleContent)
$(makeLenses ''ModuleFull)
$(makeLenses ''ModuleFullContent)
$(makePrisms ''Version)