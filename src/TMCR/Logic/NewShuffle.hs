{-# Language MultiParamTypeClasses #-}
{-# Language FlexibleInstances #-}
{-# Language UndecidableInstances #-}
{-# Language FunctionalDependencies #-}
{-# Language DeriveFunctor #-}
{-# Language ViewPatterns #-}
{-# Language RankNTypes #-}
module TMCR.Logic.NewShuffle where


import Data.List (sortOn)
import Data.Bool (bool)
import Data.Maybe (catMaybes)
import Data.Functor.Identity (Identity(..))

import Data.Set (Set())
import qualified Data.Set as S
import Data.Map (Map())
import qualified Data.Map as M


import qualified System.Random as R
import Debug.Trace (trace)
import TMCR.Logic.Data (DataLookup, LogicData, evalDataLookup)
import TMCR.Logic.Common (Thingy)
import Control.Monad.Trans.Maybe (MaybeT(runMaybeT, MaybeT))
import Control.Monad.Trans (MonadTrans(lift))

type ShuffleIdent = String

data PoolSpec = FinitePoolSpec | ArbitraryPoolSpec --todo: both data-based

data ShuffleSpec =
      DataBasedSpec DataLookup
    | BipartiteSpec PoolSpec PoolSpec
    | CommonSpec PoolSpec
    | AndThen ShuffleSpec ShuffleSpec

data ShuffleDef =
    ShuffleDef NewShuffleName ShuffleSpec
    --todo: conditional based on other shuffles
    --todo: specify shuffle order
type NewShuffleName = String

data Pair a = OrderedPair a a | UnorderedPair a a deriving (Functor, Show)

data PartialShuffle' a = PartialShuffle'
  {
    known :: [Pair a]
  , remainingLeft :: [(a, Bool)]
  , remainingRight :: [a]
  } deriving (Eq, Show, Functor)

data PartialShuffles a = PartialShuffles {
      doneShuffles :: Map ShuffleIdent [Pair a]
    , openShuffles :: [(ShuffleIdent, PartialShuffle' a)]
    } deriving (Eq, Show, Functor)

fromSpec'' :: (Monad m, Ord a) => (forall a. [a] -> m [a]) -> (DataLookup -> m [Pair a]) -> (PoolSpec -> m [a]) -> ShuffleSpec -> m (PartialShuffle' a)
fromSpec'' shuf f g spec = fromSpec' shuf f g spec mempty mempty
fromSpec' :: (Monad m, Ord a) => (forall a. [a] -> m [a]) -> (DataLookup -> m [Pair a]) -> (PoolSpec -> m [a]) -> ShuffleSpec -> Set a -> Set a -> m (PartialShuffle' a)
fromSpec' shuf f g (DataBasedSpec lookup) ls rs = do
    pairs <- f lookup
    let pairs' = filter (\pair -> S.fromList (getLefts pair) `S.disjoint` ls) $ filter (\pair -> S.fromList (getRights pair) `S.disjoint` rs) pairs
    return $ PartialShuffle' pairs' [] []
fromSpec' shuf f g (BipartiteSpec p p') ls rs = do
    as <- g p
    bs <- g p'
    let as' = filter (`notElem` ls) as
        bs' = filter (`notElem` rs) bs
    PartialShuffle' [] <$> shuf (fmap (\a -> (a,False)) as') <*> shuf bs'
fromSpec' shuf f g (CommonSpec p) ls rs = do
    as <- g p
    let as' = filter (\a -> a `notElem` ls && a `notElem` rs) as
    PartialShuffle' [] <$> shuf (fmap (\a -> (a, True)) as') <*> shuf as'
fromSpec' shuf f g (AndThen s s') ls rs = do
    PartialShuffle' res as bs <- fromSpec' shuf f g s ls rs
    let ls' = ls <> S.fromList (fmap fst as) <> foldMap (S.fromList . getLefts) res
        rs' = rs <> S.fromList (fmap fst (filter snd as)) <> S.fromList bs <> foldMap (S.fromList . getRights) res
    PartialShuffle' res' as' bs' <- fromSpec' shuf f g s' ls' rs'
    return $ PartialShuffle' (res <> res') (as <> as') (bs <> bs')

getLefts :: Pair a -> [a]
getLefts (OrderedPair a _) = [a]
getLefts (UnorderedPair a b) = [a,b]
getRights :: Pair a -> [a]
getRights (OrderedPair _ a) = [a]
getRights (UnorderedPair a b) = [a,b]

instance (Eq a) => Eq (Pair a) where
    OrderedPair a b == OrderedPair a' b' = a == a' && b == b'
    UnorderedPair a b == UnorderedPair a' b' = a == a' && b == b' || a == b' && b == a'
    _ == _ = False

conflictsWith :: (Eq a) => Pair a -> Pair a -> Bool
conflictsWith (OrderedPair a b) (OrderedPair a' b') = a == a' || b == b'
conflictsWith (OrderedPair a b) (UnorderedPair a' b') = a == a' || a == b' || b == a' || b == b'
conflictsWith (UnorderedPair a b) (OrderedPair a' b') = a == a' || a == b' || b == a' || b == b'
conflictsWith (UnorderedPair a b) (UnorderedPair a' b') = a == a' || a == b' || b == a' || b == b'

class (Monad m) => NewShuffleProgress x m a | x -> m a where
    inform :: ShuffleIdent -> [Pair a] -> x -> m x
    check :: x -> m Bool

newtype DedupedShuffleProgress x b = DedupedShuffleProgress { getDedupedShuffleProgress :: x }

instance (NewShuffleProgress x m a) => NewShuffleProgress (DedupedShuffleProgress x b) m (a,b) where
    inform s as (DedupedShuffleProgress x) = DedupedShuffleProgress <$> inform s (fmap (fmap fst) as) x
    check (DedupedShuffleProgress x) = check x

class (NewShuffleProgress x m a) => NewShuffleProgress' x m a where
    informOpen :: ShuffleIdent -> [a] -> [a] -> x -> m x

instance (NewShuffleProgress' x m a) => NewShuffleProgress' (DedupedShuffleProgress x b) m (a,b) where
    informOpen s ls rs (DedupedShuffleProgress x) = DedupedShuffleProgress <$> informOpen s (fmap fst ls) (fmap fst rs) x

solveStep :: (MonadFail m, NewShuffleProgress' x m a, Eq a) => (ShuffleIdent -> PartialShuffle' a -> x -> m (Maybe [Pair a])) -> ShuffleIdent -> PartialShuffle' a -> x -> m (Maybe [Pair a])
solveStep _ shuffleName (PartialShuffle' rs [] _) x = bool Nothing (Just rs) <$> check x
solveStep rec shuffleName (PartialShuffle' rs ((a, True):as) bs) x = do
    (x', b, bs') <- findMatchUnordered shuffleName a (fmap fst as) (filter (/= a) bs) x
    let as' = filter ((/= b) . fst) as
    rec shuffleName (PartialShuffle' (UnorderedPair a b : rs) as' bs') x'
solveStep rec shuffleName (PartialShuffle' rs ((a, False):as) bs) x = do
    (x', b, bs') <- findMatchOrdered shuffleName a (fmap fst as) bs x
    let as' = filter (\(a', isUnordered) -> not isUnordered || a' /= b) as
    rec shuffleName (PartialShuffle' (OrderedPair a b : rs) as' bs') x'

solve' :: (MonadFail m, NewShuffleProgress' x m a, Eq a) => ShuffleIdent -> PartialShuffle' a -> x -> m (Maybe [Pair a])
solve' = solveStep solve'
{-
solve' (PartialShuffle' rs [] _) x = bool Nothing (Just rs) <$> check x
solve' (PartialShuffle' rs ((a, True):as) bs) x = do
    (x', b, bs') <- findMatchUnordered a (fmap fst as) (filter (/= a) bs) x
    let as' = filter ((/= b) . fst) as
    solve' (PartialShuffle' (UnorderedPair a b : rs) as' bs') x'
solve' (PartialShuffle' rs ((a, False):as) bs) x = do
    (x', b, bs') <- findMatchOrdered a (fmap fst as) bs x
    let as' = filter (\(a', isUnordered) -> not isUnordered || a' /= b) as
    solve' (PartialShuffle' (OrderedPair a b : rs) as' bs') x'
-}

findMatchUnordered :: (MonadFail m, NewShuffleProgress' x m a, Eq a) => ShuffleIdent -> a -> [a] -> [a] -> x -> m (x, a, [a])
findMatchUnordered s a as bs x = findMatchUnordered' a as bs x [] where
    findMatchUnordered' a as [] x cs = fail "No match available"
    findMatchUnordered' a as (b:bs) x cs | a == b = findMatchUnordered' a as bs x cs
    findMatchUnordered' a as (b:bs) x cs = do
        x' <- inform s [UnorderedPair a b] x
        let as' = filter (/= b) as
        let bs' = filter (/= a) bs
        let cs' = filter (/= a) cs
        y <- informOpen s as' (cs' <> bs') x'
        c <- check y
        if c then return (x', b, reverse cs' <> bs')
        else findMatchUnordered' a as bs x (b:cs)

findMatchOrdered :: (MonadFail m, NewShuffleProgress' x m a, Eq a) => ShuffleIdent -> a -> [a] -> [a] -> x -> m (x, a, [a])
findMatchOrdered s a as bs x = findMatchOrdered' a as bs x [] where
    findMatchOrdered' a as [] x cs = fail "No match available"
    findMatchOrdered' a as (b:bs) x cs = do
        x' <- inform s [OrderedPair a b] x
        y <- informOpen s as (cs <> bs) x'
        c <- check y
        if c then return (x', b, reverse cs <> bs)
        else findMatchOrdered' a as bs x (b:cs)

solveBatched :: (MonadFail m, NewShuffleProgress' x m a, Eq a) => ShuffleIdent -> PartialShuffle' a -> x -> m (Maybe [Pair a])
solveBatched shuffleIdent s@(PartialShuffle' rs as bs) x | length as <= 2 = solve' shuffleIdent s x
solveBatched shuffleIdent s@(PartialShuffle' rs as bs) x = solveBatch shuffleIdent (length as, length as `div` 2) s x

solveBatched' :: (MonadFail m, NewShuffleProgress' x m a, Eq a) => ShuffleIdent -> PartialShuffle' a -> x -> m (Maybe [Pair a])
solveBatched' shuffleIdent s@(PartialShuffle' rs as bs) x | length as <= 2 = solve' shuffleIdent s x
solveBatched' shuffleIdent s@(PartialShuffle' rs as bs) x = solveBatch' shuffleIdent (length as, length as, 0) s x

solveBatch' :: (MonadFail m, NewShuffleProgress' x m a, Eq a) => ShuffleIdent -> (Int, Int, Int) -> PartialShuffle' a -> x -> m (Maybe [Pair a])
solveBatch' shuffleIdent (total, n, offset) s@(PartialShuffle' rs as bs) x = trace ("solveBatch' " <> show (total, n, offset)) $ do
    let (rs', as', bs') = findBatch n as (drop offset bs <> take offset bs)
    x' <- inform shuffleIdent rs' x
    y <- informOpen shuffleIdent (fmap fst as') bs' x'
    c <- check y
    if c
    then solveBatched' shuffleIdent (PartialShuffle' (rs <> rs') as' bs') x'
    else if offset + n < total
        then solveBatch' shuffleIdent (total, n, offset + n) s x
        else if n > 1 then solveBatch' shuffleIdent (total, n `div` 2, 0) s x else return Nothing


solveBatch :: (MonadFail m, NewShuffleProgress' x m a, Eq a) => ShuffleIdent -> (Int, Int) -> PartialShuffle' a -> x -> m (Maybe [Pair a])
solveBatch shuffleIdent (total, n) s x | total `div` 2 > n = solveBatched shuffleIdent s x
solveBatch shuffleIdent (total, n) s@(PartialShuffle' rs as bs) x | length as - 1 <= n = solveStep (\shuffleIdent -> solveBatch shuffleIdent (total, total - ((total - n) * 2))) shuffleIdent s x
solveBatch shuffleIdent (total, n) s@(PartialShuffle' rs as bs) x = do
    let (rs', as', bs') = findBatch n as bs
    x' <- inform shuffleIdent rs' x
    y <- informOpen shuffleIdent (fmap fst as') bs' x'
    c <- check y
    if c then solveBatch shuffleIdent (total, total - ((total - n) * 2)) (PartialShuffle' (rs <> rs') as' bs') x' --todo: don't go to full half of new size in success case
    else solveBatch shuffleIdent (total, ((total - n) `div` 2) + n) s x

findBatch :: (Eq a) => Int -> [(a, Bool)] -> [a] -> ([Pair a], [(a, Bool)], [a])
findBatch n as bs = findBatch' [] n as bs where
    findBatch' rs n [] bs' = (rs, [], bs')
    findBatch' rs 0 as' bs' = (rs, as', bs')
    --findBatch' rs n as' bs' | length as' <= n = (rs, as', bs')
    findBatch' rs n as@((a, True):_) (b:bs) | a == b = findBatch' rs n as bs
    findBatch' rs n ((a, isUnordered):as) (b:bs) = let
        as' | isUnordered = filter ((/= b) . fst) as
            | otherwise = filter (\(a', isUnordered) -> not isUnordered || a' /= b) as
        bs' | isUnordered = filter (/= a) bs
            | otherwise = bs
        r | isUnordered = UnorderedPair a b
          | otherwise = OrderedPair a b
        in findBatch' (r:rs) (n-1) as' bs'
    findBatch' rs n _ _ = error "failed to find match"

evalDataLookup' :: LogicData -> DataLookup -> [Pair Thingy]
evalDataLookup' logicData lookup = (\(l,_,r) -> OrderedPair l r) <$> evalDataLookup logicData lookup


solveAll :: (MonadFail m, NewShuffleProgress' x m a, Eq a) => PartialShuffles a -> x -> MaybeT m (Map String [Pair a])
solveAll (PartialShuffles done []) _ = return done
solveAll (PartialShuffles done ((name, s@(PartialShuffle' known ls rs)):todo)) x = do
    x' <- lift $ inform name known x
    x'' <- lift $ informOpenAll todo x'
    pairs <- MaybeT $ solveBatched' name s x''
    y <- lift $ inform name pairs x
    solveAll (PartialShuffles (M.insert name pairs done) todo) y

informOpenAll :: (NewShuffleProgress' x m a) => [(ShuffleIdent, PartialShuffle' a)] -> x -> m x
informOpenAll [] x = return x
informOpenAll ((name, PartialShuffle' known ls rs) : partialShuffles) x = do
    x' <- inform name known x
    x'' <- informOpen name (fmap fst ls) rs x'
    informOpenAll partialShuffles x''