{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
module TMCR.Exec.Eval where

import TMCR.Logic.Eval (Definitions(..), StatementF(..), Pattern(..), StatementID)
import TMCR.Logic.NewShuffle (NewShuffleProgress(..), ShuffleIdent, Pair(..), NewShuffleProgress' (..))
import Data.Array (Ix, Array, listArray, (!))
import qualified Data.Array as A
import Data.Kind (Type)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import Data.Data (Proxy (..))
import Control.Monad.Trans.Free (Free, iter, iterM, foldFreeT, transFreeT, retract, FreeF (..), FreeT (..), liftF)
import Control.Lens.TH (makeLenses)
import Control.Lens
import Control.Monad.ST
import Control.Concurrent.STM
import Control.Monad (forM_, when, join)
import Control.Concurrent.Async (forConcurrently_)
import Control.Applicative ((<|>))
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import TMCR.Logic.Common (Thingy)
import TMCR.Logic.Descriptor (Oolean(..))
import Data.List (sort, sortBy)
import Control.Arrow (Arrow(..))
import Data.Foldable (Foldable(..))
import Data.Ord (comparing)
import Data.Maybe (mapMaybe, catMaybes)
import Debug.Trace (traceShowId, trace)


data Value x = Concrete x | OneOf (Set x) | AnyValue deriving (Eq, Ord, Show)

type Statement = Free StatementF StatementID

data EvalState (m :: Type -> Type) = EvalState {
      _statementDefinitions :: Array StatementID Statement
    , _statementDependencies :: IntMap [StatementID]
    , _statementValues :: Array StatementID (Set [Value Thingy])
    , _goalStatement :: StatementID
    , _shuffleState :: Map ShuffleIdent [(Value Thingy, Value Thingy)]
    , _shuffleStatements :: Map ShuffleIdent StatementID
    , _mType :: Proxy m
    , _numThreads :: Int
}

$(makeLenses 'EvalState)

class (Monad m) => MonadEval m where
  markDirty :: [StatementID] -> EvalState m -> m (EvalState m)

instance (MonadEval m) => NewShuffleProgress (EvalState m) m Thingy where
  inform s addedShuffleValues e = trace ("Inform: " <> s <> " with " <> show (length addedShuffleValues) <> " entries") $ e & shuffleState . at s %~ addShuffleValues & markDirty (e ^.. shuffleStatements . ix s) where
    addShuffleValues v = Just $ S.toList $ S.union (maybe mempty S.fromList v) $ S.unions $ fmap (\case (OrderedPair a b) -> S.singleton (Concrete a, Concrete b); (UnorderedPair a b) -> S.singleton (Concrete a, Concrete b) <> S.singleton (Concrete b, Concrete a)) addedShuffleValues
  check e = return $ traceShowId $ not $ null $ e ^. statementValues . to (! (e ^. goalStatement))

instance (MonadEval m) => NewShuffleProgress' (EvalState m) m Thingy where
  informOpen s lefts rights e = trace ("Inform Open: " <> s <> " with " <> show (length lefts, length rights) <> " entries") $ e & shuffleState . at s %~ addOpens & markDirty (e ^.. shuffleStatements . ix s) where
    addOpens Nothing = Just newEntries
    addOpens (Just xs) = Just $ newEntries <> xs
    newEntries = [(OneOf $ S.fromList lefts, OneOf $ S.fromList rights)]
    --newEntries = [(Concrete x, Concrete y) | x <- lefts, y <- rights]

instance MonadEval IO where
  markDirty :: [StatementID] -> EvalState IO -> IO (EvalState IO)
  markDirty stmts EvalState{..} = do
    mutValues <- atomically $ thaw _statementValues
    worklist <- newTQueueIO
    atomically $ forM_ stmts $ writeTQueue worklist
    workingState <- traverse newTVarIO $ listArray (1, _numThreads) $ replicate _numThreads False
    let dependents :: StatementID -> [StatementID]
        dependents i = IM.findWithDefault [] i _statementDependencies
        processSingle :: StatementID -> IO Bool
        processSingle i = do
          stmt <- traverse (\i' -> readTVarIO (mutValues ! i')) $ _statementDefinitions ! i
          v' <- iterM (fmap (computeSingle _shuffleState) . sequenceA) stmt
          atomically $ do
            let var = mutValues ! i
            v <- readTVar var
            let v'' = S.union v v'
            writeTVar var v''
            return $ v /= v''
        runner ownWorkingState = do
          work <- atomically $ (Just <$> (writeTVar ownWorkingState True >> readTQueue worklist)) <|> (Nothing <$ ((&&) <$> isEmptyTQueue worklist <*> fmap and (traverse readTVar workingState)))
          case work of
            Nothing -> return ()
            Just work -> do
              hasChanged <- processSingle work
              atomically $ do
                when hasChanged $ forM_ (dependents work) $ writeTQueue worklist
                writeTVar ownWorkingState False
              runner ownWorkingState
    putStrLn $ "Fanning out to runners: " <> show stmts
    forConcurrently_ workingState runner
    values <- atomically $ freeze mutValues
    putStrLn $ "Computed stable state"
    return $ EvalState {_statementValues = values, ..}

thaw :: (Ix i) => Array i e -> STM (Array i (TVar e))
thaw = traverse newTVar
freeze :: (Ix i) => Array i (TVar e) -> STM (Array i e)
freeze = traverse readTVar

computeSingle :: Map ShuffleIdent [(Value Thingy, Value Thingy)] -> StatementF (Set [Value Thingy]) -> Set [Value Thingy]
computeSingle _ (ConstantStatement c) = S.fromList $ fmap (fmap Concrete . snd) $ filter ((== OolTrue) . fst) c
computeSingle _ (ProjectStatement p m) = S.map (\row -> fmap (chooseCol row) m) p where
  chooseCol row Any = AnyValue
  chooseCol row (Match i) = row !! i
computeSingle _ (JoinStatement s s' on) | null s || null s' = S.empty
computeSingle _ (JoinStatement s s' on) = S.fromList $ fmap resultProj $ doJoin (S.toList $ S.map leftPerm s) (S.toList $ S.map rightPerm s') where
  leftSize = length $ S.findMin s
  rightSize = length $ S.findMin s'
  leftJoined = S.fromList $ fmap fst on
  rightJoined = S.fromList $ fmap snd on
  leftIndexPerm i | i `S.member` leftJoined = S.size $ S.filter (< i) leftJoined
                  | otherwise = i + S.size leftJoined - S.size ( S.filter (< i) leftJoined)
  rightIndexPerm = (sortBy (comparing rightIndexPerm') [0..rightSize - 1] !!)
  leftIndexPerm' i | i < S.size leftJoined = S.elemAt i leftJoined
                   | otherwise = S.elemAt (i - S.size leftJoined) (S.fromList [0..leftSize - 1] S.\\ leftJoined)
  rightIndexPerm' = ((sortBy (comparing (\j -> let corresponding = filter ((== j) . snd) on in (null corresponding, sort corresponding))) [0..rightSize - 1])  !!)
  resultProj xs = fmap ((xs !!) . leftIndexPerm) [0..leftSize - 1] <> fmap ((xs !!) . (+ leftSize)) (filter (>= S.size rightJoined) (fmap rightIndexPerm [0 .. rightSize - 1]))
  doJoin = makeJoinFrom $  fmap (\(i,j) -> (leftIndexPerm i, rightIndexPerm j)) on
  leftPerm xs = fmap ((xs !!) . leftIndexPerm') [0..leftSize - 1]
  rightPerm xs = fmap ((xs !!) . rightIndexPerm') [0..rightSize - 1]
computeSingle _ (UnionStatement s) = S.unions s
computeSingle s (ShuffleStatement i) = S.fromList $ fmap (\(x,y) -> [x,y]) $ M.findWithDefault [] i s
computeSingle _ (AtLeastStatement _ _) = S.empty --todo

makeJoinFrom :: (Ord a) => [(Int, Int)] -> [[Value a]] -> [[Value a]] -> [[Value a]]
makeJoinFrom (sortBy (\a b -> comparing (uncurry min) a b <> compare a b) -> on) xs ys = finalize $ makeJoinFrom' on xs ys where
  finalize = fmap (\(xs, ys) -> xs <> ys)
  makeJoinFrom' [] = \xs ys -> [(x, y) | x <- xs, y <- ys]
  makeJoinFrom' ((0,0):(0,0):on) = makeJoinFrom' ((0,0):on)
  makeJoinFrom' ((0,0):(0,n):on) = \xs ys -> fmap (second (dupFirstToNth n)) $ makeJoinFrom' ((0,0):fmap (second (skipNthIndex n)) on) xs (joinFirstAndNth n ys)
  makeJoinFrom' ((0,0):(n,0):on) = \xs ys -> fmap (first (dupFirstToNth n)) $ makeJoinFrom' ((0,0):fmap (first (skipNthIndex n)) on) (joinFirstAndNth n xs) ys
  makeJoinFrom' ((0,0):on) = doJoin (makeJoinFrom' (fmap (skipFirstIndex *** skipFirstIndex) on))
  makeJoinFrom' ((a,b):on) = error $ "Reached index " <> show (a,b) <> " unexpectedly"
  dupFirstToNth n (x:xs) = x:insert (n-1) x xs
  dupFirstToNth _ [] = []
  insert 0 x xs = x : xs
  insert n x (x':xs) = x' : insert (n-1) x xs
  insert n _ [] = error "too short to insert at offset"
  skipNthIndex n i | i < n = i
                   | otherwise = i - 1
  extractNth 0 (x:xs) = (x,xs)
  extractNth n (x:xs) = let (x', xs') = extractNth (n-1) xs in (x', x:xs')
  extractNth _ [] = error "too short to extract nth"
  skipFirstIndex = skipNthIndex 1
  joinFirstAndNth n = mapMaybe (\(x:xs) -> let (x', xs') = extractNth (n-1) xs in fmap (: xs') (simpleJoin x x'))
  simpleJoin AnyValue AnyValue = Just AnyValue
  simpleJoin x AnyValue = Just x
  simpleJoin AnyValue x = Just x
  simpleJoin (OneOf xs) (OneOf ys) = OneOf <$> nonEmptySet (S.intersection xs ys)
  simpleJoin (Concrete x) (OneOf ys) | x `S.member` ys = Just $ Concrete x
                                     | otherwise = Nothing
  simpleJoin (OneOf xs) (Concrete y) | y `S.member` xs = Just $ Concrete y
                                     | otherwise = Nothing
  simpleJoin (Concrete x) (Concrete y) | x == y = Just $ Concrete x
                                       | otherwise = Nothing
  nonEmptySet xs | null xs = Nothing
                 | otherwise = Just xs
  doJoin r (splitByParts -> (concreteXs, multiXs)) (splitByParts -> (concreteYs, multiYs)) = doJoin' r concreteXs concreteYs <> doJoin'' r (toMultis concreteXs) multiYs <> doJoin'' r multiXs (toMultis concreteYs) <> doJoin'' r multiXs multiYs
  doJoin' r [] _ = []
  doJoin' r _ [] = []
  doJoin' r xss'@((x:xs):xss) yss'@((y:ys):yss) = case compare x y of
    LT -> doJoin' r (dropWhile (\(x:xs) -> x < y) xss) yss'
    GT -> doJoin' r xss' (dropWhile (\(y:ys) -> x > y) yss)
    EQ -> fmap (\(xs, ys) -> (x:xs, y:ys)) (r matchingX matchingY) <> doJoin' r laterX laterY where
      (matchingX', laterX) = span (\(x':xs') -> x == x') xss'
      (matchingY', laterY) = span (\(y':ys') -> y == y') yss'
      matchingX = fmap tail matchingX'
      matchingY = fmap tail matchingY'
  doJoin' _ _ _ = error "Malformed arguments to join: too few columns"
  doJoin'' r xss yss = join $ catMaybes $ [doSimpleJoin r x y xs ys | (x:xs) <- xss, (y:ys) <- yss]
  doSimpleJoin r x y xs ys = do
    x' <- simpleJoin x y
    let rs' = r [xs] [ys]
    return (fmap ((x':) *** (x':)) rs')
  toMultis :: (Ord x) => [[Value x]] -> [[Value x]]
  toMultis [] = []
  toMultis toBeCombined = (:[]) $ foldr1 (zipWith combine) toBeCombined
  combine AnyValue _ = AnyValue
  combine _ AnyValue = AnyValue
  combine (Concrete x) (Concrete y) = OneOf $ S.fromList [x,y]
  combine (Concrete x) (OneOf y) = OneOf $ S.insert x y
  combine (OneOf x) (Concrete y) = OneOf $ S.insert y x
  combine (OneOf x) (OneOf y) = OneOf $ S.union x y
  splitByParts xs = splitByParts' xs [] []
  splitByParts' [] as bs = (reverse as, reverse $ toMultis bs)
  splitByParts' (xs@(Concrete x:_):ys) as bs = splitByParts' ys (xs:as) bs
  splitByParts' (xs@(OneOf x:_):ys) as bs = splitByParts' ys as (xs:bs)
  splitByParts' (xs@(AnyValue:_):ys) as bs = splitByParts' ys as (xs:bs)
  splitByParts' ([]:_) _ _ = error "too few columns to split"


makeJoinFrom'' :: (Ord a) => [(Int, Int)] -> [[a]] -> [[a]] -> [[a]]
makeJoinFrom'' (sortBy (\a b -> comparing (uncurry min) a b <> compare a b) -> on) xs ys = finalize $ makeJoinFrom' on xs ys where
  finalize = fmap (\(xs, ys) -> xs <> ys)
  makeJoinFrom' [] = \xs ys -> [(x, y) | x <- xs, y <- ys]
  makeJoinFrom' ((0,0):(0,0):on) = makeJoinFrom' ((0,0):on)
  makeJoinFrom' ((0,0):(0,n):on) = \xs ys -> fmap (second (dupFirstToNth n)) $ makeJoinFrom' ((0,0):fmap (second (skipNthIndex n)) on) xs (joinFirstAndNth n ys)
  makeJoinFrom' ((0,0):(n,0):on) = \xs ys -> fmap (first (dupFirstToNth n)) $ makeJoinFrom' ((0,0):fmap (first (skipNthIndex n)) on) (joinFirstAndNth n xs) ys
  makeJoinFrom' ((0,0):on) = doJoin (makeJoinFrom' (fmap (skipFirstIndex *** skipFirstIndex) on))
  makeJoinFrom' _ = undefined
  dupFirstToNth n (x:xs) = x:insert (n-1) x xs
  dupFirstToNth _ [] = []
  insert 0 x xs = x : xs
  insert n x (x':xs) = x' : insert (n-1) x xs
  insert n _ [] = error "too short to insert at offset"
  skipNthIndex n i | i < n = i
                   | otherwise = i - 1
  doJoin r [] _ = []
  doJoin r _ [] = []
  doJoin r xss'@((x:xs):xss) yss'@((y:ys):yss) = case compare x y of
    LT -> doJoin r (dropWhile (\(x:xs) -> x < y) xss) yss'
    GT -> doJoin r xss' (dropWhile (\(y:ys) -> x > y) yss)
    EQ -> fmap (\(xs, ys) -> (x:xs, y:ys)) (r matchingX matchingY) <> doJoin r laterX laterY where
      (matchingX', laterX) = span (\(x':xs') -> x == x') xss'
      (matchingY', laterY) = span (\(y':ys') -> y == y') yss'
      matchingX = fmap tail matchingX'
      matchingY = fmap tail matchingY'
  doJoin _ _ _ = error "Malformed arguments to join: too few columns"
  joinFirstAndNth n = mapMaybe (\(x:xs) -> let (x', xs') = extractNth (n-1) xs in fmap (: xs) (maybeEq x x'))
  maybeEq x y | x == y = Just x
              | otherwise = Nothing
  extractNth 0 (x:xs) = (x,xs)
  extractNth n (x:xs) = let (x', xs') = extractNth (n-1) xs in (x', x:xs')
  extractNth _ [] = error "too short to extract nth"
  skipFirstIndex = skipNthIndex 1


makeEvalStateIO :: Array StatementID (StatementF StatementID) -> StatementID -> Int -> IO (EvalState IO)
makeEvalStateIO stmts goal numThreads = markDirty stmtIndices $ EvalState stmts' deps vals goal mempty shuffleStmts Proxy numThreads where
  stmts' = fmap liftF stmts
  stmtIndices = A.indices stmts
  deps = IM.map S.toList $ IM.fromListWith (<>) $ concatMap (\(i, stmt) -> [(j, S.singleton i) | j <- toList stmt]) $ A.assocs stmts
  vals = fmap (const mempty) stmts
  shuffleStmts = M.fromList $ concatMap (\(i, stmt) -> case stmt of (ShuffleStatement ident) -> [(ident, i)]; _ -> []) $ A.assocs stmts