{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveGeneric #-}
module TMCR.Logic.Logic where

import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer

import Control.Monad.Reader

import Control.Monad

import Control.Lens.TH

import Data.Char (isSeparator)

import Data.Hashable (Hashable)

import Data.Void
import Data.Text (Text())
import qualified Data.Text as T
import GHC.Generics (Generic)

data Sugar = SugarOpList Text Text
           | SugarMulti [Text] Text
         deriving (Eq, Ord, Show)

data Name = PlainName Text
          | QuotedName Text
          | Wildcard
          deriving (Eq, Ord, Show, Generic)

instance Hashable Name where

type ScopeName = Text

data Value = Anon Text
           | NamedScoped Text ScopedName
           | NamedScoping Text Name
           | Edge ScopedName ScopedName
           | EdgeUndirected ScopedName ScopedName
           deriving (Eq, Ord, Show)

type LogicNodeName = ScopedName
data ScopedName = Global Name
                | Scoped [Name]
                | FullWildcard
                deriving (Eq, Ord, Show, Generic)

instance Hashable ScopedName where

data Mode = ModeDefault --select or new
          | ModeAppend
          | ModeReplace
          | ModeAppendIfExists
          | ModeReplaceIfExists
          | ModeReplaceOrCreate
          deriving (Eq, Ord, Show)

$(makePrisms ''Mode)

newtype Scopes = Scopes { getScopes :: [ScopeName] } deriving (Eq, Ord, Show)

type Forest = [Tree]
data Tree = Node Value Mode Forest
            deriving (Eq, Ord, Show)
