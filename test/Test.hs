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
import qualified Polysemy.Reader as PS

import TMCR.Logic.Logic (Scopes(..))
import TMCR.Logic.Merge (GameDef(..))

import Data.Text (Text(), unpack)
import Data.Either (isRight)
import Data.Maybe (isJust)

testModule1 = Module "test" (Version [1,0]) (Version [0,1]) [] [] $ ModuleContent (M.singleton "test" (DescriptorDeclaration Nothing (Just True) [Scoped] Truthy)) M.empty [] [] [] [] []
testModule1Enc :: BS.ByteString
testModule1Enc = "dependencies: []\nname: test\nprovides:\n  data: []\n  descriptordefinitions: []\n  descriptors:\n    test:\n      arguments:\n      - scoped\n      stateful: true\n      type: truthy\n  logic: []\n  patches: []\n  shuffles: []\nsoftdependency: []\nsyntaxversion: '0.1'\nversion: '1.0'\n"
testModuleInvalEnc :: BS.ByteString
testModuleInvalEnc = "dependencies: []\nname: test\nprovides:\n  data: []\n  descriptordefinitions: []\n  descriptors:\n    test:\n      arguments:\n      - scoped\n      stateful: true\n      type: nonexistent\n  logic: []\n  patches: []\n  shuffles: []\nsoftdependency: []\nversion: '1.0'\n"

testModule1Dir :: Directory
testModule1Dir = Directory $ M.singleton "module.yaml" (Left $ BL.fromStrict testModule1Enc)

testModule2Yaml :: BL.ByteString
testModule2Yaml =  "\nname: testModule\nversion: '1.0'\nsyntax-version: '0.1'\ndependencies: []\nsoft-dependency: []\nprovides:\n  descriptors:\n    flag:\n      arguments:\n        - scoped\n      stateful: false\n      type: truthy\n      export: edge\n    set:\n      arguments:\n        - scoped\n      stateful: false\n      type: truthy\n      export: target\n    spawn:\n      arguments: []\n      stateful: false\n      type: truthy\n      export: edge-from-beyond-the-void\n  descriptor-definitions:\n    - descriptors.dscr\n  logic:\n    - logic.logic\n  shuffles:\n    - shuffles.shuff\n  data:\n    - data.json\n  patches: []"
testModule2Dir :: Directory
testModule2Dir = Directory {getDirectory = M.fromList [("testModule",Right (Directory {getDirectory = M.fromList [("data.json",Left "[]"),("descriptors.dscr",Left "flag Name:\n    [set Name].\n\nspawn: true."),("logic.logic",Left "area Spawn:\n    room Spawn:\n        node Spawn:\n            spawn\n            set \"Test\"\n        node Extra1\n        Spawn -> Extra1:\n            flag \"Test\""),("module.yaml",Left testModule2Yaml),("shuffles.shuf",Left "")]}))]}

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
    describe "Directory Stuff" $ do
        it "reads a single file correctly" $ do
            let x = PS.run $ PS.runError @TIO.DirectoryErrorWithContext $ PS.runError @TIO.AssertionFailed $ TIO.runInMemoryDir testModule1Dir $ TIO.withSingleFile "module.yaml" (\_ x -> return x)
            x `shouldBe` Right (Right $ BL.fromStrict testModule1Enc)
        it "reads a single file correctly from a subdirectory" $ do
            let x = PS.run $ PS.runError @TIO.DirectoryErrorWithContext $ PS.runError @TIO.AssertionFailed $ TIO.runInMemoryDir testModule2Dir $ TIO.inSubdir "testModule" $  TIO.withSingleFile "module.yaml" (\_ x -> return x)
            x `shouldBe` Right (Right testModule2Yaml)
    describe "Module Parsing from Directories" $ do
        it "splits paths reasonably" $ do
            TIO.splitPath "nonexistent" `shouldBe` ["nonexistent"]
        it "reads a GameDef from a directory" $ do
            dir <- TIO.readDirectoryFull "testModules"
            print dir
            let xs = PS.run $ PS.runError @TIO.AssertionFailed $ PS.runError @TIO.DirectoryErrorWithContext $ TIO.runInMemoryDir dir $ TIO.inSubdirs "nonexistent" $ \path -> TIO.withSingleFile "module.yaml" $ \path' content -> return (path <> "/" <> path')
            xs `shouldBe` Right (Right [])
            let x = PS.run $ PS.runReader @Scopes (Scopes ["area", "room"]) $ PS.runError @Text $ PS.runError @TIO.DirectoryErrorWithContext $ TIO.runInMemoryDir dir $ TIO.readGameDefStrErr ["testModule"]
            case x of
                x@(Left text) -> fmap (const ()) x `shouldBe` Right ()
                Right x@(Left err) -> fmap (const ()) x `shouldBe` Right ()
                Right (Right x) -> do
                    putStrLn "Logic:"
                    print $ _defLogic x
                    _defLogic x `shouldNotSatisfy` null . snd
    -- describe "Module Export" $ do
    --     it "" $ do
    --         dir <- TIO.readDirectoryFull "modules"
    --         --dir `shouldBe` Directory {getDirectory = M.fromList [("basicDefinitions",Right (Directory {getDirectory = M.fromList [("descriptors.dscr",Left "flag vName:\n    [set vName].\n\nspawn: true.\n\ntarget vName:\n    [warp vName]."),("module.yaml",Left "name: basicDefinitions\nversion: '1.0'\nsyntax-version: '0.1'\ndependencies: []\nsoft-dependency: []\nprovides:\n  descriptors:\n    flag:\n      arguments:\n        - scoped\n      stateful: false\n      type: truthy\n      export: edge\n    set:\n      arguments:\n        - scoped\n      stateful: false\n      type: truthy\n      export: target\n    target:\n      arguments:\n        - scoped\n      stateful: false\n      type: truthy\n      export: edge-from-beyond-the-void\n    warp:\n      arguments:\n        - unscoped\n      stateful: false\n      type: truthy\n      export: target\n    item:\n      arguments:\n        - unscoped\n      stateful: false\n      type: truthy\n      export: edge\n    chest:\n      arguments:\n        - unscoped\n      stateful: false\n      type: truthy\n      export: target\n    kill:\n      arguments:\n        - scoped\n      stateful: false\n      type: truthy\n      export: edge\n    enemy:\n      arguments:\n        - unscoped\n      stateful: false\n      type: truthy\n      export: target\n    trick:\n      arguments:\n        - scoped\n      stateful: false\n      type: truthy\n      export: edge\n    spawn:\n      arguments: []\n      stateful: false\n      type: truthy\n      export: edge-from-beyond-the-void\n  logic-sugar:\n    door:\n      type: multi\n      expands-to:\n        - warp\n        - target\n    \"|\":\n      type: operator\n      replacement: or\n    \"||\":\n      type: operator\n      replacement: or\n    \"&\":\n      type: operator\n      replacement: and\n    \"&&\":\n      type: operator\n      replacement: and\n  descriptor-definitions:\n    - descriptors.dscr\n  shuffles:\n    - shuffles.shuff\n  logic: []\n  data: []\n  patches: []\n")]})),("tmc",Right (Directory {getDirectory = M.fromList [("descriptors.dscr",Left "trick Town.Main.GuardEastwards: ool.\ntrick Town.Main.GuardBootSkip: ool.\ntrick VeilFalls.Main.HPCapeJump: ool.\n\nitem CanSpin:\n  item Sword,\n  item SpinAttack.\n"),("logic",Right (Directory {getDirectory = M.fromList [("scratch.logic",Left "")]})),("module.yaml",Left "name: tmc\nversion: '1.0'\nsyntax-version: '0.1'\ndependencies:\n  - [basicDefinitions, \">= 1.0, < 2.0\"]\nsoft-dependency: []\nprovides:\n  descriptors:\n    npc:\n      arguments:\n        - scoped\n      stateful: false\n      type: truthy\n      export: target\n  logic-sugar:\n    entrance:\n      type: multi\n      expands-to:\n        - warp\n    exit:\n      type: multi\n      expands-to:\n        - target\n  descriptor-definitions:\n    - descriptors.dscr\n  logic:\n    - \"logic/*.logic\"\n  shuffles: []\n  data:\n    - \"logic/*.json\"\n  patches: []\n")]})),("tmcr",Right (Directory {getDirectory = M.fromList [("descriptors.dscr",Left "item CanGrow: true.\nitem CanTurnMinish: true.\n"),("module.yaml",Left "name: tmcr\nversion: '1.0'\nsyntax-version: '0.1'\ndependencies:\n  - [basicDefinitions, \">= 1.0, < 2.0\"]\n  - [tmc, \">= 1.0, < 2.0\"]\nsoft-dependency: []\nprovides:\n  descriptors: {}\n  logic-sugar: {}\n  descriptor-definitions:\n    - descriptors.dscr\n  logic:\n    - \"logic/*.logic\"\n  shuffles: []\n  data:\n    - \"logic/*.json\"\n  patches: []")]}))]}
    --         let compile :: Directory -> (Maybe GameDef, Text)
    --             compile dir = either (\x -> (Nothing, x)) (\y -> (Just y, "OK")) $ either (const (Left "Directory Error")) id $ PS.run $ PS.runError @TIO.DirectoryErrorWithContext $ PS.runReader @Scopes (Scopes ["area", "room"]) $ PS.runError @Text $ TIO.runInMemoryDir dir $ TIO.readGameDefStrErr (modules dir) where
    --                 modules (Directory m) = M.keys m --todo search for module.yaml
    --         let (res, msg) = compile dir
    --         putStrLn $ unpack msg
    --         isJust res `shouldBe` True
    --         _defLogic <$> res `shouldBe` Nothing


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

instance Arbitrary DescriptorDeclaration where
    arbitrary = do
        e <- arbitrary
        s <- arbitrary
        a <- arbitrary
        t <- arbitrary
        return $ DescriptorDeclaration e s a t

instance Arbitrary ModuleContent where
    arbitrary = do
        descriptors <- arbitrary
        return $ ModuleContent descriptors mempty mempty mempty mempty mempty mempty --todo

instance (Arbitrary c) => Arbitrary (Module c) where
    arbitrary = do
        name <- arbitrary
        version <- arbitrary
        syntaxVersion <- arbitrary
        dependencies <- arbitrary
        softDeps <- arbitrary
        content <- arbitrary
        return $ Module name syntaxVersion version dependencies softDeps content



{-
let testLogic = [
      Node (NamedScoping "area" (PlainName "Spawn")) ModeDefault [
          Node (NamedScoping "room" (PlainName "Spawn")) ModeDefault [
              Node (NamedScoped "node" (L.Scoped [PlainName "Spawn"])) ModeDefault [
                  Node (Anon "spawn") ModeDefault []
                , Node (NamedScoped "set" (L.Scoped [PlainName "Test"])) ModeDefault []
                ]
            , Node (NamedScoped "node" (L.Scoped [PlainName "Extra1"])) ModeDefault []
            , Node (Edge (L.Scoped [PlainName "Spawn"]) (L.Scoped [PlainName "Extra1"])) ModeDefault [
                  Node (NamedScoped "flag" (L.Scoped [PlainName "Test"])) ModeDefault []
                ]
            ]
        ]
    ]
let testLogic' = [
      Node (NamedScoping "area" (PlainName "Spawn")) [
          Node (NamedScoping "room" (PlainName "Spawn")) [
              Node (NamedScoped "node" (L.Scoped [PlainName "Spawn"])) [
                  Node (Anon "spawn") []
                , Node (NamedScoped "set" (L.Scoped [PlainName "Test"])) []
                ]
            , Node (NamedScoped "node" (L.Scoped [PlainName "Extra1"])) []
            , Node (Edge (L.Scoped [PlainName "Spawn"]) (L.Scoped [PlainName "Extra1"])) [
                  Node (NamedScoped "flag" (L.Scoped [PlainName "Test"])) []
                ]
            ]
        ]
    ]
-}

{-
[Node (NamedScoping "area" (PlainName "Test")) [Node (NamedScoping "room" (PlainName "Test"))
  [ Node (Edge (Scoped [PlainName "Test",PlainName "Test",PlainName "A"]) (Scoped [PlainName "Test",PlainName "Test",PlainName "B"]))
    [ Node (Anon "and") [Node (NamedScoped "item" (Scoped [PlainName "A"])) []],Node (Anon "and") [Node (NamedScoped "item" (Scoped [PlainName "C"])) []]]]]]
-}