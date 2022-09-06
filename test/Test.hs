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

testModule1 = Module "test" (Version [1,0]) [] [] $ ModuleContent (M.singleton "test" (DescriptorDeclaration Nothing (Just True) [Scoped] Truthy Nothing)) [] [] [] [] []
testModule1Enc :: BS.ByteString
testModule1Enc = "dependencies: []\nname: test\nprovides:\n  data: []\n  descriptordefinitions: []\n  descriptors:\n    test:\n      arguments:\n      - scoped\n      stateful: true\n      type: truthy\n  logic: []\n  patches: []\n  shuffles: []\nsoftdependency: []\nversion: '1.0'\n"
testModuleInvalEnc :: BS.ByteString
testModuleInvalEnc = "dependencies: []\nname: test\nprovides:\n  data: []\n  descriptordefinitions: []\n  descriptors:\n    test:\n      arguments:\n      - scoped\n      stateful: true\n      type: nonexistent\n  logic: []\n  patches: []\n  shuffles: []\nsoftdependency: []\nversion: '1.0'\n"


main = hspec $ do
    describe "Module Yaml (de)serialization" $ do
        it "encodes a simple module" $ do
            encode testModule1 `shouldBe` testModule1Enc
        it "parses a simple module" $ do
            r <- decodeThrow testModule1Enc 
            r `shouldBe` testModule1
        it "rejects invalid encodings" $ do
            (decodeThrow testModuleInvalEnc :: _ Module) `shouldThrow` anyException
        it "en- and decodes arbitrary modules without changes" $ property $
            \(m :: Module) -> decodeEither (encode m) `shouldBe` Right m

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
        dependencies <- arbitrary
        softDeps <- arbitrary
        content <- arbitrary
        return $ Module name version dependencies softDeps content
