{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE CPP #-}
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
      Options(..) )
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
import Control.Lens (lens, iso, from, (&), (.~), (^.), Lens, Iso)
import TMCR.Logic.Logic (Forest, Sugar(..))
import TMCR.Logic.Data (LogicData')
import TMCR.Logic.Shuffle (ShuffleStatement)
import TMCR.Logic.Descriptor
import Data.Dependent.Map (DMap)

data Module a = Module {
      _moduleName :: Text
    , _moduleVersion :: Version
    , _moduleSyntaxVersion :: Version
    , _moduleDependencies :: [(Text, VersionSpec)]
    , _moduleSoftDependency :: [(Text, VersionSpec)]
    , _moduleProvides :: a
    } deriving (Eq, Ord, Show)

{-
data ModuleFull = ModuleFull {
      _moduleFullName :: Text
    , _moduleFullVersion :: Version
    , _moduleFullDependencies :: [(Text, VersionSpec)]
    , _moduleFullSoftDependency :: [(Text, VersionSpec)]
    , _moduleFullProvides :: ModuleFullContent
    }
-}

newtype Version = Version { getVersion :: [Int] } deriving (Eq, Ord, Show)

data VersionSpec = VersionSpecRange (Maybe Version) (Maybe Version) deriving (Eq, Ord, Show)

versionMatches :: VersionSpec -> Version -> Bool
versionMatches (VersionSpecRange minV maxV) v = maybe True (<= v) minV && maybe True (v <) maxV

data ModuleContent = ModuleContent
    { _moduleContentDescriptors :: Map DescriptorName DescriptorDeclaration
    , _moduleContentLogicSugar :: Map Text SugarDefinition
    , _moduleContentDescriptorDefinitions :: [ResourceSpecifier]
    , _moduleContentLogic :: [ResourceSpecifier]
    , _moduleContentPatches :: [ResourceSpecifier]
    , _moduleContentData :: [ResourceSpecifier]
    , _moduleContentShuffles :: [ResourceSpecifier]
    } deriving (Eq, Ord, Show)

data SugarDefinition = SugarDefinitionOperator { _sugarOperatorReplacement :: Text }
                     | SugarDefinitionMulti    { _sugarMultiExpandsTo :: [Text] }
                     deriving (Eq, Ord, Show)


data ModuleHeader = ModuleHeader
    { _moduleHeaderDescriptors :: Map DescriptorName DescriptorDeclaration
    , _moduleHeaderLogicSugar :: [Sugar]
    } deriving (Eq, Ord, Show)

data ModulePreparedContent = ModulePreparedContent {
      _modulePreparedContentDescriptorDefinitions :: [Text]
    , _modulePreparedContentLogic :: [Text]
    , _modulePreparedContentPatches :: [Text]
    , _modulePreparedContentData :: [Text]
    , _modulePreparedContentShuffles :: [Text]
    } deriving (Eq, Ord, Show)

data ModuleFullContent = ModuleFullContent {
      _moduleFullContentDescriptorDefinitions :: DMap DescriptorIdent Descriptors
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

#if MIN_VERSION_aeson(1,5,0)
$(deriveJSON defaultOptions{ sumEncoding = (TaggedObject "type" ""), constructorTagModifier = (camelTo2 '-' . drop (T.length "SugarDefinition")), fieldLabelModifier = (\s -> camelTo2 '-' $ head $ ["_sugarOperator", "_sugarMulti"] >>= (\p -> let l = length p in if p == take l s then [drop l s] else [])), omitNothingFields = True, rejectUnknownFields = True} ''SugarDefinition)
$(deriveJSON defaultOptions{ fieldLabelModifier = camelTo2 '-' . drop (T.length "_moduleContent"), omitNothingFields = True, rejectUnknownFields = True} ''ModuleContent)
$(deriveJSON defaultOptions{ fieldLabelModifier = camelTo2 '-' . drop (T.length "_module"), omitNothingFields = True, rejectUnknownFields = True} ''Module)
#else
$(deriveJSON defaultOptions{ sumEncoding = (TaggedObject "type" ""), constructorTagModifier = (camelTo2 '-' . drop (T.length "SugarDefinition")), fieldLabelModifier = (\s -> camelTo2 '-' $ head $ ["_sugarOperator", "_sugarMulti"] >>= (\p -> let l = length p in if p == take l s then [drop l s] else [])), omitNothingFields = True} ''SugarDefinition)
$(deriveJSON defaultOptions{ fieldLabelModifier = camelTo2 '-' . drop (T.length "_moduleContent"), omitNothingFields = True} ''ModuleContent)
$(deriveJSON defaultOptions{ fieldLabelModifier = camelTo2 '-' . drop (T.length "_module"), omitNothingFields = True} ''Module)
#endif
$(makeLenses ''Module)
$(makeLenses ''ModuleContent)
$(makeLenses ''ModuleHeader)
$(makeLenses ''ModuleFullContent)
$(makePrisms ''Version)

moduleContentHeader :: Lens ModuleContent ModuleContent ModuleHeader ModuleHeader
moduleContentHeader = lens get set where
    get m = ModuleHeader (m ^. moduleContentDescriptors) (m ^. moduleContentLogicSugar . sugars)
    set m (ModuleHeader descrs sugar) = m & moduleContentDescriptors .~ descrs & moduleContentLogicSugar . sugars .~ sugar

sugars :: Iso (Map Text SugarDefinition) (Map Text SugarDefinition) [Sugar] [Sugar]
sugars = iso f g where
    f = Map.foldlWithKey (\a k d -> f' k d : a) []
    f' t (SugarDefinitionOperator t') = SugarOpList t' t
    f' t (SugarDefinitionMulti t') = SugarMulti t' t
    g = Map.unions . fmap g'
    g' (SugarOpList v k) = Map.singleton k $ SugarDefinitionOperator v
    g' (SugarMulti v k) = Map.singleton k $ SugarDefinitionMulti v