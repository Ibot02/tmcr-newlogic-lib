{-# LANGUAGE OverloadedStrings #-}
module TMCR.TestData (testLogic, testDescriptors, testMergedLogic, testValue, testValueScopingArea) where

import Data.Map (Map())
import qualified Data.Map as M

import TMCR.Logic.Descriptor (DescriptorName(..), DescriptorDeclaration(..), DescriptorExport(..), DescriptorType(..))
import qualified TMCR.Logic.Descriptor as D
import qualified TMCR.Logic.Logic as L
import TMCR.Logic.Logic (Name(..), ScopedName(..), Mode(..), Value(..))
import TMCR.Logic.Merge (mergeLogic, MonadMerge(..), Forest'(..))

testLogic :: L.Forest
testLogic = [
      L.Node testValueScopingArea ModeDefault [
          L.Node (NamedScoping "room" (PlainName "Spawn")) ModeDefault [
              L.Node (NamedScoped "node" (L.Scoped [PlainName "Spawn"])) ModeDefault [
                  L.Node (Anon "spawn") ModeDefault []
                , L.Node (NamedScoped "set" (L.Scoped [PlainName "Test"])) ModeDefault []
                ]
            , L.Node (NamedScoped "node" (L.Scoped [PlainName "Extra1"])) ModeDefault []
            , L.Node (EdgeUndirected (L.Scoped [PlainName "Spawn"]) (L.Scoped [PlainName "Extra1"])) ModeDefault [
                  L.Node (NamedScoped "flag" (L.Scoped [PlainName "Test"])) ModeDefault []
                ]
            ]
        ]
    ]

testValue = (NamedScoped "set" (L.Scoped [PlainName "Test"]))

testValueScopingArea = NamedScoping "area" $ PlainName "Spawn"

testDescriptors :: Map DescriptorName DescriptorDeclaration
testDescriptors = M.fromList
    [ ("set", DescriptorDeclaration (Just DescriptorExportTarget) Nothing [D.Scoped] Truthy)
    , ("flag", DescriptorDeclaration (Just DescriptorExportEdge) Nothing [D.Scoped] Truthy)
    , ("spawn", DescriptorDeclaration (Just DescriptorExportEdgeFromBeyondTheVoid) Nothing [] Truthy)
    ]

testMergedLogic :: (MonadMerge m) => m (Forest' L.Value)
testMergedLogic = mergeLogic testDescriptors (M.singleton "test" [testLogic])
