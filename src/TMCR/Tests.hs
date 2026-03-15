{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE RecordWildCards #-}
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
import qualified System.Random as R

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Data.Map as M
import qualified Data.IntMap as IM
import TMCR.Logic.Common (displayPossiblyScopedName, PossiblyScopedName (Global, ScopedName), Thingy)

import Data.Set (Set())
import qualified Data.Set as S
import TMCR.Logic.Data (DataLookup(DataLookup), LogicData (LogicData))
import TMCR.Parser.Data (parseDataLookup)
import Text.Megaparsec (parseTest, ParseErrorBundle (ParseErrorBundle), errorBundlePretty)
import TMCR.Parser.Common (runParserC)
import Control.Monad.Trans.Maybe (MaybeT(runMaybeT))
import TMCR.Logic.Descriptor (DescriptorName, Oolean (..))
import Control.Monad (forM_)
import Data.Aeson (encode)
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString as BS
import Data.Aeson.Encode.Pretty (encodePretty', Config(..), defConfig, keyOrder)
import System.IO (Handle(), stdout, IOMode (WriteMode), withFile, hPutStrLn)
import qualified TMCR.Logic.Eval as Eval
import TMCR.Logic.Eval (acyclicStatements)
import Control.Monad.State (evalStateT)
import Control.Monad.State.Lazy (evalState)
import Control.Monad.Trans.Writer.CPS (execWriterT)
import Control.Arrow (Arrow(second))
import Data.Foldable (toList)
import TMCR.Exec.Eval (EvalState(EvalState), makeEvalStateIO)
import qualified Data.Array as A

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

testShuffle :: GameDef -> IO (PartialShuffle' Thingy)
testShuffle g = PartialShuffle' [] <$> randomOrder (fmap (\x -> (x,True)) warps) <*> randomOrder warps where
    warps = (Global "ExtraWarp" :) $ S.toList $ foldMap (foldMap (uncurry getWarp)) $ snd $ _defLogic g
    getWarp "warp" [x] = S.singleton $ x
    getWarp _ _ = S.empty

getAll :: DescriptorName -> GameDef -> IO [Thingy]
getAll reachableName g = randomOrder $ S.toList $ foldMap (foldMap (uncurry get)) $ snd $ _defLogic g where
    get name [x] | name == reachableName = S.singleton x
    get _ _ = S.empty

testShuffles :: GameDef -> IO (PartialShuffles String)
testShuffles g = do
    spec <- testShuffleSpec
    warps <- {-testShuffle g-}fromSpec'' randomOrder (return . evalDataLookup' (_defLogicData g)) (const $ return []) spec
    let warps' = fmap (T.unpack . displayPossiblyScopedName) $ warps
    itemSpec <- testItemShuffleSpec
    {-
    chests <- getAll "chest" g
    traverse (putStrLn . T.unpack . displayPossiblyScopedName) chests
    items <- return $ reverse $ fmap (ScopedName . (:[])) $ take (length chests) $ ["BombBag"] <> fmap (\n -> T.pack $ "Junk" <> show n) [1..]
    let itemShuffle = fmap (T.unpack . displayPossiblyScopedName) $ PartialShuffle' [] (fmap (\x -> (x, False)) chests) items
    -}
    itemShuffle <- fromSpec'' randomOrder (return . evalDataLookup' (_defLogicData g)) (const $ return []) itemSpec >>= rerandomize
    let itemShuffle' = fmap (T.unpack . displayPossiblyScopedName) $ itemShuffle
    return $ PartialShuffles mempty [("Warps", warps'), ("Items", itemShuffle')]

testShuffles' :: GameDef -> IO (PartialShuffles Thingy)
testShuffles' g = do
    spec <- testShuffleSpec
    warps <- testShuffle g --fromSpec'' randomOrder (return . evalDataLookup' (_defLogicData g)) (const $ return []) spec
    itemSpec <- testItemShuffleSpec
    {-
    chests <- getAll "chest" g
    traverse (putStrLn . T.unpack . displayPossiblyScopedName) chests
    items <- return $ reverse $ fmap (ScopedName . (:[])) $ take (length chests) $ ["BombBag"] <> fmap (\n -> T.pack $ "Junk" <> show n) [1..]
    let itemShuffle = fmap (T.unpack . displayPossiblyScopedName) $ PartialShuffle' [] (fmap (\x -> (x, False)) chests) items
    -}
    itemShuffle <- fromSpec'' randomOrder (return . evalDataLookup' (_defLogicData g)) (const $ return []) itemSpec >>= rerandomize
    return $ PartialShuffles mempty [("Warps", warps), ("Items", itemShuffle)]

testShuffleSpec :: IO ShuffleSpec
testShuffleSpec = case P.run $ P.runError @(ParseErrorBundle Text Void) $ P.runReader @() () $ runParserC parseDataLookup "test input" "'areas' by 'name', 'rooms' by 'name', 'warps' foreach local 'name' collect local 'target'" of
    Left err -> do
        putStrLn $ errorBundlePretty err
        error ""
    Right d -> return $ DataBasedSpec d

rerandomize :: PartialShuffle' a -> IO (PartialShuffle' a)
rerandomize (PartialShuffle' k l r) = go k l r where
    go [] l r = do
        l' <- randomOrder l
        r' <- randomOrder r
        return $ PartialShuffle' [] l' r'
    go (OrderedPair l' r' : k) l r = go k ((l', False):l) (r':r)
    go (UnorderedPair l' r' : k) l r = go k ((l', True):(r',True):l) (r':l':r)

testItemShuffleSpec :: IO ShuffleSpec
testItemShuffleSpec = case P.run $ P.runError @(ParseErrorBundle Text Void) $ P.runReader @() () $ runParserC parseDataLookup "test input" "'areas' by 'name', 'rooms' by 'name', 'chests' foreach local 'name' collect unscoped 'item'" of
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
goalStatement = Statement "goal" $ IntroVar $ IntroVar $ DefinedBy $ getItems where
    getItem i = Term $ Apply "descriptor" [Apply "item" [], StringTerm i, VariableTerm Nothing, VariableTerm (Just Nothing)]
    items = ["EarthElement", "FireElement", "WaterElement", "WindElement", "GustJar", "Cane", "Cape", "Lantern"]
    getItems = foldl1 Conj $ fmap getItem items
    findallReachable = IntroVarExpr $ (Term (Apply "findall" [VariableTerm Nothing, Apply "reachableNode" [VariableTerm Nothing, Apply "_" []], Apply "_" []]))

doTest :: FilePath -> IO ()
doTest f = do
    putStrLn "Reading modules"
    g <- readTest f
    let r = mkResult g
    putStrLn "Read modules"
    s <- testShuffles g
    putStrLn "Generated shuffle order, solving for placements"
    shuffle <- runMaybeT $ solveAll s r
    print shuffle
    --print $ shuffle >>= M.lookup "Items"

randomOrder :: [a] -> IO [a]
randomOrder [] = return []
randomOrder inputs = do
    let takeOut 0 (a:as) = (a,as)
        takeOut (pred -> n) (a:as) = let (a', as') = takeOut n as in (a', a:as')
    let l = length inputs
    i <- R.randomRIO (0, l-1)
    let (x,xs) = takeOut i inputs
    fmap (x:) $ randomOrder xs


writeChests :: Maybe FilePath -> GameDef -> IO ()
writeChests f g = withFileOrStdout f $ \h -> do
    traverse (hPutStrLn h . T.unpack . displayPossiblyScopedName) $ getChests g
    return ()

withFileOrStdout :: Maybe FilePath -> (Handle -> IO ()) -> IO ()
withFileOrStdout Nothing a = a stdout
withFileOrStdout (Just f) a = System.IO.withFile f WriteMode a

getChests :: GameDef -> [Thingy]
getChests g = foldMap getChests' $ snd (_defLogic g) where
    getChests' :: [(DescriptorName, [Thingy])] -> [Thingy]
    getChests' = foldMap (uncurry getChest)
    getChest "chest" [t] = [t]
    getChest _ _ = []

getChestsWithIDs :: GameDef -> ([(Thingy, Int, Int)], M.Map Text (Int, M.Map Text Int))
getChestsWithIDs g = (fmap annotateWithIndex chests, indexMap) where
    chests = getChests g
    annotateWithIndex t@(findIndex -> Just (a,b))= (t,a,b)
    annotateWithIndex t = error $ "Failed to find index for: " <> T.unpack (displayPossiblyScopedName t)
    findIndex (ScopedName [a,b,c]) = do
        (outer, innerMap) <- M.lookup a indexMap
        inner <- M.lookup b innerMap
        return (outer,inner)
    findIndex _ = Nothing
    (LogicData d) = _defLogicData g
    (Just (Right areas)) = M.lookup "areas" d
    indexMap :: M.Map Text (Int, M.Map Text Int)
    indexMap = IM.foldMapWithKey areaIndices areas
    areaIndices :: Int -> LogicData -> M.Map Text (Int, M.Map Text Int)
    areaIndices key (LogicData value) = maybe mempty (uncurry M.singleton) $ do
        (Left name) <- M.lookup "name" value
        (Right rooms) <- M.lookup "rooms" value
        return (name,(key, roomIndices rooms))
    roomIndices :: IM.IntMap LogicData -> M.Map Text Int
    roomIndices = IM.foldMapWithKey roomIndex
    roomIndex :: Int -> LogicData -> M.Map Text Int
    roomIndex key (LogicData value) = maybe mempty (uncurry M.singleton) $ do
        (Left name) <- M.lookup "name" value
        return (name, key)

writeChestsWithIDs :: GameDef -> IO ()
writeChestsWithIDs g = forM_ (fst $ getChestsWithIDs g) $ \(t,a,r) -> do
    putStr $ show a
    putStr ", "
    putStr $ show r
    putStr ", "
    putStrLn $ T.unpack $ displayPossiblyScopedName t

writeAreasWithIDs :: GameDef -> IO ()
writeAreasWithIDs g = forM_ (M.toList $ snd $ getChestsWithIDs g) $ \(k,v) -> do
    putStr $ T.unpack k
    putStr ", "
    print $ fst v

writeLogicDataTo :: Handle -> GameDef -> IO ()
writeLogicDataTo h g = do
    let config = defConfig {confCompare = keyOrder ["name", "chests", "warps", "areas", "items", "item", "flag", "target", "value", "subvalue"], confTrailingNewline = True }
    BL.hPutStr h $ encodePretty' config $ _defLogicData g

writeLogicData = writeLogicDataTo stdout

writeDefinitionsTo :: (Maybe FilePath) -> GameDef -> IO ()
writeDefinitionsTo f g = withFileOrStdout f $ \h ->
    BS.hPutStr h $ T.encodeUtf8 $ Eval.displayDefinitions $ Eval.compile g


testAcyclics :: IO ()
testAcyclics = do
    let stmts = snd $ flip Eval.runWithIDPool [0..] $ fmap IM.fromList $ execWriterT $ do
            rec i <- Eval.makeStatement 0 $ Eval.ProjectStatement i []
            c <- Eval.makeStatement 0 $ Eval.ConstantStatement []
            j <- Eval.makeStatement 0 $ Eval.JoinStatement i c []
            rec l <- do
                    j' <- Eval.makeStatement 0 $ Eval.JoinStatement l i []
                    Eval.makeStatement 0 $ Eval.UnionStatement [j', c]
            return ()
    
    traverse (print . uncurry Eval.displayStatement . (second  fst) ) $ IM.toList stmts
    traverse (print . second (toList . fst)) $ IM.toList stmts
    print $ (\(a,_,_) -> a) $ evalState Eval.dependencyGraph stmts
    print $ evalState acyclicStatements stmts


testEval :: IO (Maybe [Pair Thingy])
testEval = do
    let stmts = A.listArray (0, 6) [
              Eval.JoinStatement 1 2 [(0,0)]
            , Eval.ConstantStatement [(OolTrue, [Global "A"])]
            , Eval.UnionStatement [3, 4]
            , Eval.ProjectStatement 5 [Eval.Match 1]
            , Eval.ConstantStatement [(OolTrue, [Global "C"])]
            , Eval.JoinStatement 2 6 [(0,0)]
            , Eval.ShuffleStatement "Test"
            ]
    s <- makeEvalStateIO stmts 0 2
    lefts <- randomOrder ["A", "B", "C", "D"]
    rights <- randomOrder ["A", "B", "C", "D"]
    solve' "Test" (PartialShuffle' [] [(Global x, False) | x <- lefts] [Global y | y <- rights]) s

testEval' :: GameDef -> IO (Maybe (M.Map String [Pair Thingy]))
testEval' game = do
    let x = Eval.compile game
    s <- makeEvalStateIO (fmap fst $ Eval.statements x) (Eval.definitionsGoalStatement x) 1
    shuf <- testShuffles' game
    runMaybeT $ solveAll shuf s