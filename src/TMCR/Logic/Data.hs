{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
module TMCR.Logic.Data where

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

newtype LogicData = LogicData (Map Name (Either Text (IntMap LogicData))) deriving (Eq, Ord, Show)
newtype LogicData' = LogicData' (Map Name (Either Text (Mode, IntMap (Maybe LogicData')))) deriving (Eq, Ord, Show)

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

--type ScopedTraversal scope s t a b = forall f. (Applicative f) => (a -> scope -> f b) -> s -> scope -> f t
type ScopedTraversal scope s t a b = Traversal (scope, s) t (scope, a) b
type ScopedGetting scope r s a = LensLike (Const r) (scope, s) s (scope, a) a
--type Getting r s a = (a -> Const r a) -> s -> Const r s
scoped :: forall scope f s t a b. LensLike f s t a b -> LensLike f (scope, s) t (scope, a) b
scoped t f (scope, s) = t (\a -> f (scope, a)) s

--runScoped :: ScopedTraversal scope s t a b -> scope -> Traversal s t a b
--runScoped :: forall (c :: (Type -> Type) -> Constraint) scope s t a b f. c f => (forall f. c f => ((scope, a) -> f b) -> (scope, s) -> f t) -> scope -> (a -> f b) -> s -> f t
runScoped :: LensLike f (scope, s) t (scope, a) b -> scope -> LensLike f s t a b
runScoped sT scope f s = sT (\(_,a) -> f a) (scope, s)

evalDataLookup :: LogicData -> DataLookup -> [(Thingy, Nteger, Thingy)]
evalDataLookup input (DataLookup steps Nothing (steps', target)) =
  fmap (\x -> (Global "", Finite 1, x)) $ input ^.. runScoped (evalDataSteps steps . evalDataSteps steps' . evalDataTarget target) []
evalDataLookup input (DataLookup steps (Just (stepsL, targetL)) (stepsR, targetR)) =
  input ^.. runScoped (evalDataSteps steps . scopedTo (\scopes input' -> [(a, Finite 1, b) | a <- input' ^.. runScoped (evalDataSteps stepsL . evalDataTarget targetL) scopes, b <- input' ^.. runScoped (evalDataSteps stepsR . evalDataTarget targetR) scopes]) . scoped traverse) []

logicData :: Iso LogicData LogicData (Map Text (Either Text (IntMap LogicData))) (Map Text (Either Text (IntMap LogicData)))
logicData = coerced

evalDataStep :: DataStep -> ScopedTraversal [Text] LogicData LogicData LogicData LogicData
evalDataStep (DataTraverse (DataTraverseStep x Nothing)) = scoped $ logicData . at x . _Just . _Right . traverse
evalDataStep (DataTraverse (DataTraverseStep x (Just scopeKey))) = scoped (logicData . at x . _Just . _Right . traverse) . (\f (scopes, s) -> let
  scope' = s ^? logicData . at scopeKey . _Just . _Left
  scope = fromMaybe "" scope'
  in f (scopes <> [scope], s))
evalDataStep (DataFilter (DataFilterStep steps name cond)) = scoped $ filtered (\x -> any (matches cond) $ x ^.. runScoped (evalDataSteps steps . evalDataTarget name) [])

evalDataTarget :: Monoid r => DataTarget -> ScopedGetting [Text] r LogicData PossiblyScopedName
evalDataTarget (DataTarget name TargetGlobal) = scoped $ logicData . at name . _Just . _Left . to Global
evalDataTarget (DataTarget name TargetUnscoped) = scoped $ logicData . at name . _Just . _Left . to (ScopedName . (:[]))
evalDataTarget (DataTarget name TargetScoped) = scoped (logicData . at name . _Just . _Left) . scopedTo parseAndScopeName

parseAndScopeName :: [Text] -> Text -> PossiblyScopedName
parseAndScopeName scopes name = inScopes scopes $ either (const $ ScopedName (scopes <> [name])) id $ flip runReader () $ runParserT (parsePossiblyScopedName' <* eof) "" name

inScopes :: [Text] -> PossiblyScopedName -> PossiblyScopedName
inScopes _ g@(Global _) = g
inScopes scopes (ScopedName scopes') = ScopedName $ reverse (drop (length scopes' - 1) (reverse scopes)) <> scopes'

scopedTo :: (s -> a -> b) -> ScopedGetting s r a b
scopedTo g = (\f (scopes, a) -> (\(Const r) -> Const r) $ f (scopes, g scopes a))

matches :: FilterCondition -> PossiblyScopedName -> Bool
matches (FilterEQ name) x = name == x

evalDataSteps :: [DataStep] -> ScopedTraversal [Text] LogicData LogicData LogicData LogicData
evalDataSteps [] = id
evalDataSteps (step : steps) = evalDataStep step . evalDataSteps steps
