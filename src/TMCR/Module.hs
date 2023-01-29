{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
module TMCR.Module where

import Data.Text (Text())
import qualified Data.Text as T

import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE

import Data.Aeson
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

data Module = Module {
      _moduleName :: Text
    , _moduleVersion :: Version
    , _moduleSyntaxVersion :: Version
    , _moduleDependencies :: [(Text, VersionSpec)]
    , _moduleSoftDependency :: [(Text, VersionSpec)]
    , _moduleProvides :: ModuleContent
    } deriving (Eq, Ord, Show)

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

type ResourceSpecifier = Text

data DescriptorDeclaration = DescriptorDeclaration {
      _descriptorDeclarationExport :: Maybe DescriptorExport
    , _descriptorDeclarationStateful :: Maybe Bool
    , _descriptorDeclarationArguments :: [Scoping]
    , _descriptorDeclarationType :: DescriptorType
    , _descriptorDeclarationConsumes :: Maybe DescriptorConsumeSpec
    } deriving (Eq, Ord, Show)

data DescriptorExport = DescriptorExportNone | DescriptorExportEdge | DescriptorExportSelfEdge | DescriptorExportEdgeFromBeyondTheVoid | DescriptorExportTarget deriving (Eq, Ord, Show, Enum, Bounded)

type DescriptorName = Text

data Scoping = Unscoped | Scoped deriving (Eq, Ord, Show, Enum, Bounded)

data DescriptorType = Truthy | County deriving (Eq, Ord, Show, Enum, Bounded)

data DescriptorConsumeSpec = DescriptorConsumeSpec {
      _descriptorConsumerSpecKey :: Text --todo: add relation for key item type
    , _descriptorConsumerSpecLock :: Text
    } deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions{ fieldLabelModifier = drop (T.length "_descriptorConsumerSpec") . fmap toLower, rejectUnknownFields = True} ''DescriptorConsumeSpec)
$(deriveJSON defaultOptions{ constructorTagModifier = camelTo2 '-' } ''DescriptorType)
$(deriveJSON defaultOptions{ constructorTagModifier = camelTo2 '-' } ''Scoping)
$(deriveJSON defaultOptions{ constructorTagModifier = camelTo2 '-' . drop (T.length "DescriptorExport") } ''DescriptorExport)
$(deriveJSON defaultOptions{ fieldLabelModifier = drop (T.length "_descriptorDeclaration") . fmap toLower, omitNothingFields = True, rejectUnknownFields = True} ''DescriptorDeclaration)
$(deriveJSON defaultOptions{ fieldLabelModifier = drop (T.length "_moduleContent") . fmap toLower, omitNothingFields = True, rejectUnknownFields = True} ''ModuleContent)
$(makeLenses ''Module)
$(makeLenses ''ModuleContent)
$(makeLenses ''DescriptorDeclaration)
$(makeLenses ''DescriptorConsumeSpec)

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

$(deriveJSON defaultOptions{ fieldLabelModifier = drop (T.length "_module") . fmap toLower, omitNothingFields = True, rejectUnknownFields = True} ''Module)
