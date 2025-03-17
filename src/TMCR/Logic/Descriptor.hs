{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE PolyKinds #-}
module TMCR.Logic.Descriptor where

import TMCR.Logic.Common
import TMCR.Parser.Common

import Data.Char (toLower)

import Text.Megaparsec as MP
import Text.Megaparsec.Char as MP
import qualified Text.Megaparsec.Char.Lexer as MPL
import Control.Monad.Combinators.Expr

import Control.Monad

import Control.Monad.Reader

import Control.Lens
import Control.Lens.TH

import Data.Void (Void())

import Data.Text (Text())
import qualified Data.Text as T

import Data.Set (Set())
import qualified Data.Set as S

import Data.Map (Map())
import qualified Data.Map as Map

import qualified Data.Char as C

import Data.Either (either)

import Data.Dependent.Sum (DSum((:=>)))
import qualified Data.Dependent.Sum as DS

import Data.Dependent.Map (DMap())
import qualified Data.Dependent.Map as DM

import Data.GADT.Compare
import Data.Aeson (camelTo2, defaultOptions, Options(..))
import Data.Aeson.TH

import Data.Kind (Type)

import qualified Control.Monad.State as S

import GHC.Generics (Generic)
import Data.Hashable (Hashable(..))

data DescriptorDeclaration = DescriptorDeclaration {
      _descriptorDeclarationExport :: Maybe DescriptorExport
    , _descriptorDeclarationStateful :: Maybe Bool
    , _descriptorDeclarationArguments :: [Scoping]
    , _descriptorDeclarationType :: DescriptorType
    -- , _descriptorDeclarationConsumes :: Maybe DescriptorConsumeSpec
    } deriving (Eq, Ord, Show)

data DescriptorExport = DescriptorExportNone | DescriptorExportEdge | DescriptorExportSelfEdge | DescriptorExportEdgeFromBeyondTheVoid | DescriptorExportTarget deriving (Eq, Ord, Show, Enum, Bounded)

type DescriptorName = Text

data Scoping = Unscoped | Scoped deriving (Eq, Ord, Show, Enum, Bounded)

data DescriptorType = Truthy | County deriving (Eq, Ord, Show, Enum, Bounded)

-- data DescriptorConsumeSpec = DescriptorConsumeSpec {
--       _descriptorConsumerSpecKey :: Text --todo: add relation for key item type
--     , _descriptorConsumerSpecLock :: Text
--     } deriving (Eq, Ord, Show)

#if MIN_VERSION_aeson(1,5,0)
-- $(deriveJSON defaultOptions{ fieldLabelModifier = drop (T.length "_descriptorConsumerSpec") . fmap toLower, rejectUnknownFields = True} ''DescriptorConsumeSpec)
#else
-- $(deriveJSON defaultOptions{ fieldLabelModifier = drop (T.length "_descriptorConsumerSpec") . fmap toLower} ''DescriptorConsumeSpec)
#endif
$(deriveJSON defaultOptions{ constructorTagModifier = camelTo2 '-' } ''DescriptorType)
$(deriveJSON defaultOptions{ constructorTagModifier = camelTo2 '-' } ''Scoping)
$(deriveJSON defaultOptions{ constructorTagModifier = camelTo2 '-' . drop (T.length "DescriptorExport") } ''DescriptorExport)
#if MIN_VERSION_aeson(1,5,0)
$(deriveJSON defaultOptions{ fieldLabelModifier = drop (T.length "_descriptorDeclaration") . fmap toLower, omitNothingFields = True, rejectUnknownFields = True} ''DescriptorDeclaration)
#else
$(deriveJSON defaultOptions{ fieldLabelModifier = drop (T.length "_descriptorDeclaration") . fmap toLower, omitNothingFields = True} ''DescriptorDeclaration)
#endif
$(makeLenses ''DescriptorDeclaration)
-- $(makeLenses ''DescriptorConsumeSpec)

data DescriptorIdent t where
    TruthyDescriptorIdent :: DescriptorName -> DescriptorIdent Truthy
    CountyDescriptorIdent :: DescriptorName -> DescriptorIdent County

deriving instance Show (DescriptorIdent a)

instance Hashable (DescriptorIdent a) where
    hashWithSalt n (TruthyDescriptorIdent a) = hashWithSalt n a
    hashWithSalt n (CountyDescriptorIdent a) = hashWithSalt n a

instance GEq DescriptorIdent where
    TruthyDescriptorIdent _ `geq` TruthyDescriptorIdent _ = Just Refl
    CountyDescriptorIdent _ `geq` CountyDescriptorIdent _ = Just Refl
    _ `geq` _ = Nothing

instance GCompare DescriptorIdent where
    TruthyDescriptorIdent n `gcompare` TruthyDescriptorIdent n' = case compare n n' of
        LT -> GLT
        EQ -> GEQ
        GT -> GGT
    CountyDescriptorIdent n `gcompare` CountyDescriptorIdent n' = case compare n n' of
        LT -> GLT
        EQ -> GEQ
        GT -> GGT
    TruthyDescriptorIdent _ `gcompare` CountyDescriptorIdent _ = GLT
    CountyDescriptorIdent _ `gcompare` TruthyDescriptorIdent _ = GLT

deriving instance Eq (DescriptorIdent t)
deriving instance Ord (DescriptorIdent t)

newtype Descriptors t = Descriptors [Descriptor t]
deriving instance Show (Descriptors t)
deriving instance Eq (Descriptors t)
deriving instance Ord (Descriptors t)

data Descriptor (t :: DescriptorType) where
    Descriptor :: [Value] -> DescriptorRule t -> Descriptor t
deriving instance Show (Descriptor t)
deriving instance Eq (Descriptor t)
deriving instance Ord (Descriptor t)
type ConsumeUUID = Int

data SDescriptorType :: DescriptorType -> Type where
    STruthy :: SDescriptorType Truthy
    SCounty :: SDescriptorType County

deriving instance Show (SDescriptorType t)
deriving instance Eq (SDescriptorType t)
deriving instance Ord (SDescriptorType t)

type DescriptorRule t = DescriptorRule' t Value

data DescriptorRule' (t :: DescriptorType) v where
    Constant :: Literal t -> DescriptorRule' t v
    IsEqual :: v -> v -> DescriptorRule' Truthy v
    CallDescriptor :: SDescriptorType t -> Name -> [v] -> DescriptorRule' t v
    CanAccess :: SDescriptorType t -> Name -> [v] -> [StateBody v] -> DescriptorRule' t v
    Scale :: DescriptorRule' County v -> Nteger -> DescriptorRule' County v
    Sum :: [DescriptorRule' County v] -> DescriptorRule' County v
    AtLeast :: DescriptorRule' County v -> Nteger -> DescriptorRule' Truthy v
    Exist :: Relation -> v -> DescriptorRule' Truthy (Maybe v) -> DescriptorRule' Truthy v
    Count :: Relation -> v -> DescriptorRule' Truthy (Maybe v) -> DescriptorRule' County v
    Min :: SDescriptorType t -> [DescriptorRule' t v] -> DescriptorRule' t v
    Max :: SDescriptorType t -> [DescriptorRule' t v] -> DescriptorRule' t v
    Cast :: DescriptorRule' Truthy v -> DescriptorRule' County v -- truth -> infinity, false -> 0
    --PriorState :: (HasEff StateyEff effs) => [StateBody v] -> DescriptorRule' effs Truthy v
    --PostState :: (HasEff StateyEff effs) => [StateBody v] -> DescriptorRule' effs Truthy v
    Consume :: ConsumeUUID -> Name -> [v] -> DescriptorRule' t v -> DescriptorRule' t v

deriving instance (Show v) => Show (DescriptorRule' t v)
deriving instance (Eq v) => Eq (DescriptorRule' t v)
deriving instance (Ord v) => Ord (DescriptorRule' t v)
deriving instance Functor (DescriptorRule' t)

data Literal (t :: DescriptorType) where
    TruthyLiteral :: Oolean -> Literal Truthy
    CountyLiteral :: Nteger -> Literal County
    -- IntLiteral :: Int -> Literal County
    -- InfLiteral :: Literal County -- inf

deriving instance Show (Literal t)
deriving instance Eq (Literal t)
deriving instance Ord (Literal t)

data Oolean = OolFalse | OolOol | OolTrue deriving (Eq, Ord, Show, Enum, Bounded)

data Value = Variable VarName
           | ConstantValue PossiblyScopedName
                deriving (Eq, Ord, Show)

data StateBody v = IsSet v
                 | IsNotSet v
                deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data Relation = Forward RelName
              | Backward RelName
                deriving (Eq, Ord, Show, Generic)
instance Hashable Relation
relationName :: Relation -> RelName
relationName (Forward rel) = rel
relationName (Backward rel) = rel

data DescriptorRole = DefaultRole | Reachability deriving (Eq, Ord, Show, Enum, Bounded)

$(makePrisms ''Value)

type SomeDescriptorRule = Either (DescriptorRule Truthy) (DescriptorRule County)

type DescriptorDeclarations = Map (Name, DescriptorRole) ([Scoping], DescriptorType)
getDescriptorDeclarations :: Map DescriptorName DescriptorDeclaration -> DescriptorDeclarations
getDescriptorDeclarations = Map.fromList . fmap (\(name, decl) -> ((name, case decl ^. descriptorDeclarationExport of {Just DescriptorExportTarget -> Reachability; _ -> DefaultRole}), (decl ^. descriptorDeclarationArguments, decl ^. descriptorDeclarationType))) . Map.toList

castIfNeccessary :: SDescriptorType t -> DescriptorRule' Truthy v -> DescriptorRule' t v
castIfNeccessary STruthy = id
castIfNeccessary SCounty = Cast
