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

data DescriptorRuleEff = QuantifiedEff | StateyEff | ConsumeyEff | CallEff

type DescriptorRuleEffs = '[ DescriptorRuleEff ]

type DescriptorRule t = DescriptorRule' AllEffs t Value
type AllEffs = [QuantifiedEff, StateyEff, ConsumeyEff, CallEff]

data Witness (e :: k) (es :: [k]) where
  WitnessNow :: Witness e (e ': es)
  WitnessLater :: Witness e es -> Witness e (e' ': es)

class HasEff (e :: DescriptorRuleEff) (es :: [DescriptorRuleEff]) where
  witness :: Witness e es
instance HasEff e (e ': es) where
  witness = WitnessNow
instance {-# Overlappable #-} HasEff e es => HasEff e (e' ': es) where
  witness = WitnessLater witness

data DescriptorRule' (effs :: [DescriptorRuleEff]) (t :: DescriptorType) v where
    Constant :: Literal t -> DescriptorRule' effs t v
    IsEqual :: v -> v -> DescriptorRule' effs Truthy v
    CallDescriptor :: (HasEff CallEff effs) => SDescriptorType t -> Name -> [v] -> DescriptorRule' effs t v
    CanAccess :: (HasEff CallEff effs) => SDescriptorType t -> Name -> [v] -> [StateBody v] -> DescriptorRule' effs t v
    --Product :: DescriptorRule County -> DescriptorRule County -> DescriptorRule County  -- removed due to being buggy and no know use cases - we'll have scale instead
    Scale :: DescriptorRule' effs County v -> Nteger -> DescriptorRule' effs County v
    Sum :: [DescriptorRule' effs County v] -> DescriptorRule' effs County v
    AtLeast :: DescriptorRule' effs County v -> Nteger -> DescriptorRule' effs Truthy v
    Exist :: (HasEff QuantifiedEff effs) => Relation -> v -> DescriptorRule' effs Truthy (Maybe v) -> DescriptorRule' effs Truthy v
    Count :: (HasEff QuantifiedEff effs) => Relation -> v -> DescriptorRule' effs Truthy (Maybe v) -> DescriptorRule' effs County v
    Min :: SDescriptorType t -> [DescriptorRule' effs t v] -> DescriptorRule' effs t v
    Max :: SDescriptorType t -> [DescriptorRule' effs t v] -> DescriptorRule' effs t v
    Cast :: DescriptorRule' effs Truthy v -> DescriptorRule' effs County v -- truth -> infinity, false -> 0
    --PriorState :: (HasEff StateyEff effs) => [StateBody v] -> DescriptorRule' effs Truthy v
    --PostState :: (HasEff StateyEff effs) => [StateBody v] -> DescriptorRule' effs Truthy v
    Consume :: (HasEff ConsumeyEff effs) => ConsumeUUID -> Name -> [v] -> DescriptorRule' effs t v -> DescriptorRule' effs t v

data DescriptorRuleF (effs :: [DescriptorRuleEff]) (t :: DescriptorType) (v :: Type) (f :: DescriptorType -> Type -> Type) where
    ConstantF :: Literal t -> DescriptorRuleF effs t v f
    IsEqualF :: v -> v -> DescriptorRuleF effs Truthy v f
    CallDescriptorF :: (HasEff CallEff effs) => SDescriptorType t -> Name -> [v] -> DescriptorRuleF effs t v f
    CanAccessF :: (HasEff CallEff effs) => SDescriptorType t -> Name -> [v] -> [StateBody v] -> DescriptorRuleF effs t v f
    ScaleF :: f County v -> Nteger -> DescriptorRuleF effs County v f
    SumF :: [f County v] -> DescriptorRuleF effs County v f
    AtLeastF :: f County v -> Nteger -> DescriptorRuleF effs Truthy v f
    ExistF :: (HasEff QuantifiedEff effs) => Relation -> v -> f Truthy (Maybe v) -> DescriptorRuleF effs Truthy v f
    CountF :: (HasEff QuantifiedEff effs) => Relation -> v -> f Truthy (Maybe v) -> DescriptorRuleF effs County v f
    MinF :: SDescriptorType t -> [f t v] -> DescriptorRuleF effs t v f
    MaxF :: SDescriptorType t -> [f t v] -> DescriptorRuleF effs t v f
    CastF :: f Truthy v -> DescriptorRuleF effs County v f
    --PriorStateF :: (HasEff StateyEff effs) => [StateBody v] -> DescriptorRuleF effs Truthy v f
    --PostStateF :: (HasEff StateyEff effs) => [StateBody v] -> DescriptorRuleF effs Truthy v f
    ConsumeF :: (HasEff ConsumeyEff effs) => ConsumeUUID -> Name -> [v] -> f t v -> DescriptorRuleF effs t v f

deriving instance (Show v) => Show (DescriptorRule' effs t v)
deriving instance (Eq v) => Eq (DescriptorRule' effs t v)
deriving instance (Ord v) => Ord (DescriptorRule' effs t v)
deriving instance Functor (DescriptorRule' effs t)

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

embedDR :: DescriptorRuleF effs t v (DescriptorRule' effs) -> DescriptorRule' effs t v
embedDR (ConstantF l) = Constant l
embedDR (IsEqualF v v') = IsEqual v v'
embedDR (CallDescriptorF t d args) = CallDescriptor t d args
embedDR (CanAccessF t d args s) = CanAccess t d args s
embedDR (ScaleF r n) = Scale r n
embedDR (SumF rs) = Sum rs
embedDR (AtLeastF r n) = AtLeast r n
embedDR (ExistF rel v r) = Exist rel v r
embedDR (CountF rel v r) = Count rel v r
embedDR (MinF t rs) = Min t rs
embedDR (MaxF t rs) = Max t rs
embedDR (CastF r) = Cast r
--embedDR (PriorStateF s) = PriorState s
--embedDR (PostStateF s) = PostState s
embedDR (ConsumeF c n vs r) = Consume c n vs r
projectDR :: DescriptorRule' effs t v -> DescriptorRuleF effs t v (DescriptorRule' effs)
projectDR (Constant l) = ConstantF l
projectDR (IsEqual v v') = IsEqualF v v'
projectDR (CallDescriptor t d args) = CallDescriptorF t d args
projectDR (CanAccess t d args s) = CanAccessF t d args s
projectDR (Scale r n) = ScaleF r n
projectDR (Sum rs) = SumF rs
projectDR (AtLeast r n) = AtLeastF r n
projectDR (Exist rel v r) = ExistF rel v r
projectDR (Count rel v r) = CountF rel v r
projectDR (Min t rs) = MinF t rs
projectDR (Max t rs) = MaxF t rs
projectDR (Cast r) = CastF r
--projectDR (PriorState s) = PriorStateF s
--projectDR (PostState s) = PostStateF s
projectDR (Consume c n vs r) = ConsumeF c n vs r
{-
traverseDR :: (Monad m) => (forall t v. res t v -> m (res' t v)) -> DescriptorRuleF effs t v res -> m (DescriptorRuleF effs t v res')
traverseDR f (ConstantF l)              = pure $ ConstantF l
traverseDR f (SumF rs)                  = SumF <$> traverse f rs
traverseDR f (ExistF rel v r) = ExistF rel v <$> f r
traverseDR f (IsEqualF v v')            = IsEqual v v'
traverseDR f (CallDescriptorF t d args) = CallDescriptor t d args
traverseDR f (CanAccessF t d args s)    = CanAccess t d args s
traverseDR f (ScaleF r n)               = Scale r n
traverseDR f (AtLeastF r n) = AtLeast r n
traverseDR f (CountF rel v r) = Count rel v r
traverseDR f (MinF rs) = Min rs
traverseDR f (MaxF rs) = Max rs
traverseDR f (CastF r) = Cast r
traverseDR f (PriorStateF s) = PriorState s
traverseDR f (PostStateF s) = PostState s
traverseDR f (ConsumeF c n vs r) = Consume c n vs r
-}

type SomeDescriptorRule = Either (DescriptorRule Truthy) (DescriptorRule County)

type DescriptorDeclarations = Map (Name, DescriptorRole) ([Scoping], DescriptorType)
getDescriptorDeclarations :: Map DescriptorName DescriptorDeclaration -> DescriptorDeclarations
getDescriptorDeclarations = Map.fromList . fmap (\(name, decl) -> ((name, case decl ^. descriptorDeclarationExport of {Just DescriptorExportTarget -> Reachability; _ -> DefaultRole}), (decl ^. descriptorDeclarationArguments, decl ^. descriptorDeclarationType))) . Map.toList

castIfNeccessary :: SDescriptorType t -> DescriptorRule' effs Truthy v -> DescriptorRule' effs t v
castIfNeccessary STruthy = id
castIfNeccessary SCounty = Cast
