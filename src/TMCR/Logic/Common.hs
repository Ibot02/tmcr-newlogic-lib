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

import Data.Char (isUpper, isAlphaNum)

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

displayPossiblyScopedName :: PossiblyScopedName -> Text
displayPossiblyScopedName (Global n) = "g" <> displayPossiblyScopedNamePart n
displayPossiblyScopedName (ScopedName []) = error "Empty name"
displayPossiblyScopedName (ScopedName xs) = T.intercalate "." $ fmap displayPossiblyScopedNamePart xs

displayPossiblyScopedNamePart x = case T.uncons x of
        Nothing -> "\"\""
        Just (c, r) | isUpper c && T.all isAlphaNum r -> x
                    | otherwise -> T.pack $ show x

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

