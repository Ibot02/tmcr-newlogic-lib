{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
module TMCR.Tests where

import TMCR.Logic.Merge(GameDef(..))
import TMCR.IO
import TMCR.Logic.Logic (Scopes(..))
import TMCR.Logic.NewShuffle
import TMCR.Logic.DescriptorTranslation
import TMCR.IO.EvalDescriptor

import qualified Polysemy.Error as P
import qualified Polysemy.Reader as P
import qualified Polysemy as P

import Data.Void (Void())

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map as M
import TMCR.Logic.Common (displayPossiblyScopedName)

import Data.Set (Set())
import qualified Data.Set as S
import TMCR.Logic.Data (DataLookup(DataLookup))
import TMCR.Parser.Data (parseDataLookup)
import Text.Megaparsec (parseTest, ParseErrorBundle (ParseErrorBundle), errorBundlePretty)
import TMCR.Parser.Common (runParserC)

compile :: Directory -> (Maybe GameDef, Text)
compile dir = either (\x -> (Nothing, x)) (\y -> (Just y, "OK")) $ either (const (Left "Directory Error")) id $ P.run $ P.runError @DirectoryErrorWithContext $ P.runReader @Scopes (Scopes ["area", "room"]) $ P.runError @Text $ runInMemoryDir dir $ readGameDefStrErr (modules dir) where
                modules (Directory m) = filter (\f -> hasFile "module.yaml" $ m M.! f) $ M.keys m 
                hasFile _ (Left _) = False
                hasFile f (Right (Directory m)) = M.member f m


readTest :: FilePath -> IO GameDef
readTest f = do
    (x, e) <- fmap compile $ readDirectoryFull f
    case x of
        Nothing -> error $ T.unpack e
        Just g -> return g

testShuffle :: GameDef -> IO (PartialShuffle' String)
testShuffle g = PartialShuffle' [] <$> randomOrder (fmap (\x -> (x,True)) warps) <*> randomOrder warps where
    warps = ("ExtraWarp" :) $ S.toList $ foldMap (foldMap (uncurry getWarp)) $ snd $ _defLogic g
    getWarp "warp" [x] = S.singleton $ T.unpack $ displayPossiblyScopedName x
    getWarp _ _ = S.empty

testShuffle' :: GameDef -> IO (PartialShuffle' String)
testShuffle' g = do
    spec <- testShuffleSpec
    partial <- fromSpec'' randomOrder (return . evalDataLookup' (_defLogicData g)) (const $ return []) spec
    return $ fmap (T.unpack . displayPossiblyScopedName) partial

testShuffleSpec :: IO ShuffleSpec
testShuffleSpec = case P.run $ P.runError @(ParseErrorBundle Text Void) $ P.runReader @() () $ runParserC parseDataLookup "test input" "'areas' by 'name', 'rooms' by 'name', 'warps' foreach local 'name' collect local 'target'" of
    Left err -> do
        putStrLn $ errorBundlePretty err
        error ""
    Right d -> return $ DataBasedSpec d

testResult :: FilePath -> IO Result
testResult = fmap mkResult . readTest where

mkResult :: GameDef -> Result
mkResult = addGoal . fromGameDef where
    addGoal (Result r) = Result $ goalStatement : r

goalStatement :: Statement
goalStatement = Statement "goal" $ IntroVar $ DefinedBy $ Term $ Apply "reachableNode" [StringTerm "HouseInteriors2.LinkEntry.Main", VariableTerm Nothing]

doTest :: FilePath -> IO ()
doTest f = do
    putStrLn "Reading modules"
    g <- readTest f
    let r = mkResult g
    putStrLn "Read modules"
    s <- testShuffle' g
    r' <- initSolve s r
    putStrLn "Generated shuffle order, solving for placements"
    shuffle <- solveBatched s r'
    print shuffle