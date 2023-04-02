{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Test.Hspec

import Test.QuickCheck
import Test.QuickCheck.Instances

import TMCR.Module
import Data.Yaml
import qualified Data.Map as M

import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import TMCR.Logic.Descriptor
import TMCR.IO (Directory (..))
import qualified TMCR.IO as TIO
import qualified Polysemy as PS
import qualified Polysemy.Error as PS

testModule1 = Module "test" (Version [1,0]) (Version [0,1]) [] [] $ ModuleContent (M.singleton "test" (DescriptorDeclaration Nothing (Just True) [Scoped] Truthy Nothing)) [] [] [] [] []
testModule1Enc :: BS.ByteString
testModule1Enc = "dependencies: []\nname: test\nprovides:\n  data: []\n  descriptordefinitions: []\n  descriptors:\n    test:\n      arguments:\n      - scoped\n      stateful: true\n      type: truthy\n  logic: []\n  patches: []\n  shuffles: []\nsoftdependency: []\nsyntaxversion: '0.1'\nversion: '1.0'\n"
testModuleInvalEnc :: BS.ByteString
testModuleInvalEnc = "dependencies: []\nname: test\nprovides:\n  data: []\n  descriptordefinitions: []\n  descriptors:\n    test:\n      arguments:\n      - scoped\n      stateful: true\n      type: nonexistent\n  logic: []\n  patches: []\n  shuffles: []\nsoftdependency: []\nversion: '1.0'\n"

testModule1Dir :: Directory
testModule1Dir = Directory $ M.singleton "module.yaml" (Right $ BL.fromStrict testModule1Enc)
testModule2Dir :: Directory
testModule2Dir = Directory {getDirectory = M.fromList [("testModule",Left (Directory {getDirectory = M.fromList [("data.json",Right "[]"),("descriptors.dscr",Right "flag Name:\n    [set Name].\n\nspawn: true."),("logic.logic",Right "area Spawn:\n    room Spawn:\n        node Spawn:\n            spawn\n            set \"Test\"\n        node Extra1\n        Spawn -> Extra1:\n            flag \"Test\""),("module.yaml",Right "\nname: testModule\nversion: '1.0'\nsyntax-version: '0.1'\ndependencies: []\nsoft-dependency: []\nprovides:\n  descriptors:\n    flag:\n      arguments:\n        - scoped\n      stateful: false\n      type: truthy\n      export: edge\n    set:\n      arguments:\n        - scoped\n      stateful: false\n      type: truthy\n      export: target\n    spawn:\n      arguments: []\n      stateful: false\n      type: truthy\n      export: edge-from-beyond-the-void\n  descriptor-definitions:\n    - descriptors.dscr\n  logic:\n    - logic.logic\n  shuffles:\n    - shuffles.shuff\n  data:\n    - data.json\n  patches: []"),("shuffles.shuf",Right "")]}))]}

main = hspec $ do
    -- describe "Module Yaml (de)serialization" $ do
    --     it "encodes a simple module" $ do
    --         encode testModule1 `shouldBe` testModule1Enc
    --     it "parses a simple module" $ do
    --         let r = decode testModule1Enc 
    --         r `shouldBe` Just testModule1
    --     it "rejects invalid encodings" $ do
    --         (decodeThrow testModuleInvalEnc :: _ Module) `shouldThrow` anyException
    --     it "en- and decodes arbitrary modules without changes" $ property $
    --         \(m :: Module) -> decodeEither (encode m) `shouldBe` Right m
    -- describe "Directory Stuff" $ do
    --     it "reads a single file correctly" $ do
    --         let Right x = PS.run $ PS.runError @ParseException $ PS.runError @() $ PS.mapError @Int (const ()) $ PS.runError @() $ TIO.runInMemoryDir testModule1Dir $ PS.mapError @() @Int (\() -> 1) $ TIO.withSingleFile "module.yaml" (const return)
    --         x `shouldBe` Right (Right $ BL.fromStrict testModule1Enc)
    -- describe "Module Parsing from Directories" $ do
    --     it "decodes a module from a pure Directory" $ do
    --         let (Right x) = PS.run $ PS.runError @ParseException $ PS.runError @() $ PS.mapError @Int (const ()) $ PS.runError @() $ TIO.runInMemoryDir testModule1Dir $ PS.mapError @() @Int (\() -> 1) $ TIO.readModule
    --         x `shouldBe` Right (Right testModule1)
    return ()

instance Arbitrary Version where
    arbitrary = fmap (Version . fmap abs) $ (:) <$> arbitrary <*> arbitrary

instance Arbitrary VersionSpec where
    arbitrary = do
        mi <- arbitrary
        ma <- arbitrary
        return $ VersionSpecRange mi ma

instance Arbitrary DescriptorExport where
    arbitrary = chooseEnum (minBound, maxBound)

instance Arbitrary Scoping where
    arbitrary = chooseEnum (minBound, maxBound)

instance Arbitrary DescriptorType where
    arbitrary = chooseEnum (minBound, maxBound)

instance Arbitrary DescriptorConsumeSpec where
    arbitrary = DescriptorConsumeSpec <$> arbitrary <*> arbitrary

instance Arbitrary DescriptorDeclaration where
    arbitrary = do
        e <- arbitrary
        s <- arbitrary
        a <- arbitrary
        t <- arbitrary
        c <- arbitrary
        return $ DescriptorDeclaration e s a t c

instance Arbitrary ModuleContent where
    arbitrary = do
        descriptors <- arbitrary
        return $ ModuleContent descriptors mempty mempty mempty mempty mempty --todo

instance Arbitrary Module where
    arbitrary = do
        name <- arbitrary
        version <- arbitrary
        syntaxVersion <- arbitrary
        dependencies <- arbitrary
        softDeps <- arbitrary
        content <- arbitrary
        return $ Module name syntaxVersion version dependencies softDeps content
