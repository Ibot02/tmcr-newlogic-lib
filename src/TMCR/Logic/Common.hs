{-# Language OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module TMCR.Logic.Common where

import qualified Data.Set as S

import Data.Text (Text())
import qualified Data.Text as T
import Data.Void
import Data.Kind (Type)

import Control.Monad.Reader
import Polysemy
import qualified Polysemy.Reader as PR
import Polysemy.Error
import Control.Monad.Identity
import GHC.Generics (Generic)
import Data.Hashable (Hashable)

type Name = Text

data PossiblyScopedName = Global Text
                        | ScopedName [Text]
                deriving (Eq, Ord, Show, Generic)

instance Hashable PossiblyScopedName where

type VarName = Text
data Nteger = Finite Int | Infinite deriving (Eq, Ord, Show)
type RelName = Text
type Thingy = PossiblyScopedName

newtype Lift (t :: (Type -> Type) -> Type -> Type) m a = Lift { unLift :: t m a }
        deriving newtype ( Functor
                         , Applicative
                         , Monad
                         , MonadTrans
                         )

