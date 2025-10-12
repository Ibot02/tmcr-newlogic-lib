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

newtype PartialShuffle a = PartialShuffle
  { remaining :: [Pair a]
  }

data PartialShuffle' a = PartialShuffle'
  {
    known :: [Pair a]
  , remainingLeft :: [(a, Bool)]
  , remainingRight :: [a]
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

fromSpec :: (Monad m, Ord a) => (forall a. [a] -> m [a]) -> (PoolSpec -> m [a]) -> ShuffleSpec -> m (PartialShuffle a)
fromSpec shuf f (DataBasedSpec _) = return $ PartialShuffle [] --todo
fromSpec shuf f (BipartiteSpec p p') = do
    as <- f p
    bs <- f p'
    PartialShuffle <$> shuf [(OrderedPair a b) | a <- as, b <- bs]
fromSpec shuf f (CommonSpec p) = do
    as <- f p
    PartialShuffle <$> shuf [(UnorderedPair a b) | a <- as, b <- as, a < b]
fromSpec shuf f (AndThen s s') = do
    PartialShuffle ps <- fromSpec shuf f s
    PartialShuffle ps' <- fromSpec shuf f s'
    return $ PartialShuffle $ ps <> ps'


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
    inform :: [Pair a] -> x -> m x
    check :: x -> m Bool

newtype DedupedShuffleProgress x b = DedupedShuffleProgress { getDedupedShuffleProgress :: x }

instance (NewShuffleProgress x m a) => NewShuffleProgress (DedupedShuffleProgress x b) m (a,b) where
    inform as (DedupedShuffleProgress x) = DedupedShuffleProgress <$> inform (fmap (fmap fst) as) x
    check (DedupedShuffleProgress x) = check x

class (NewShuffleProgress x m a) => NewShuffleProgress' x m a where
    informOpen :: [a] -> [a] -> x -> m x

solve :: (NewShuffleProgress x m a, Eq a) => PartialShuffle a -> x -> m (Maybe [Pair a])
solve (PartialShuffle []) x = bool Nothing (Just []) <$> check x
solve (PartialShuffle (a:as)) x = do
    x' <- inform [a] x
    let as' = filter (not . conflictsWith a) as
    y <- inform as' x'
    b <- check y
    if b then
        fmap (a:) <$> solve (PartialShuffle as') x'
    else
        solve (PartialShuffle as) x

solveStep :: (MonadFail m, NewShuffleProgress' x m a, Eq a) => (PartialShuffle' a -> x -> m (Maybe [Pair a])) -> PartialShuffle' a -> x -> m (Maybe [Pair a])
solveStep _ (PartialShuffle' rs [] _) x = bool Nothing (Just rs) <$> check x
solveStep rec (PartialShuffle' rs ((a, True):as) bs) x = do
    (x', b, bs') <- findMatchUnordered a (fmap fst as) (filter (/= a) bs) x
    let as' = filter ((/= b) . fst) as
    rec (PartialShuffle' (UnorderedPair a b : rs) as' bs') x'
solveStep rec (PartialShuffle' rs ((a, False):as) bs) x = do
    (x', b, bs') <- findMatchOrdered a (fmap fst as) bs x
    let as' = filter (\(a', isUnordered) -> not isUnordered || a' /= b) as
    rec (PartialShuffle' (OrderedPair a b : rs) as' bs') x'

solve' :: (MonadFail m, NewShuffleProgress' x m a, Eq a) => PartialShuffle' a -> x -> m (Maybe [Pair a])
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

findMatchUnordered :: (MonadFail m, NewShuffleProgress' x m a, Eq a) => a -> [a] -> [a] -> x -> m (x, a, [a])
findMatchUnordered a as bs x = findMatchUnordered' a as bs x [] where
    findMatchUnordered' a as [] x cs = fail "No match available"
    findMatchUnordered' a as (b:bs) x cs | a == b = findMatchUnordered' a as bs x cs
    findMatchUnordered' a as (b:bs) x cs = do
        x' <- inform [UnorderedPair a b] x
        let as' = filter (/= b) as
        let bs' = filter (/= a) bs
        let cs' = filter (/= a) cs
        y <- informOpen as' (cs' <> bs') x'
        c <- check y
        if c then return (x', b, reverse cs' <> bs')
        else findMatchUnordered' a as bs x (b:cs)

findMatchOrdered :: (MonadFail m, NewShuffleProgress' x m a, Eq a) => a -> [a] -> [a] -> x -> m (x, a, [a])
findMatchOrdered a as [] x = fail "No match available"
findMatchOrdered a as (b:bs) x = do
    x' <- inform [OrderedPair a b] x
    y <- informOpen as bs x'
    c <- check y
    if c then return (x', b, bs)
    else (\(x'', b', bs') -> (x'', b', b:bs')) <$> findMatchOrdered a as bs x

solveBatched :: (MonadFail m, NewShuffleProgress' x m a, Eq a, Show a) => PartialShuffle' a -> x -> m (Maybe [Pair a])
solveBatched s@(PartialShuffle' rs as bs) x | length as <= 5 = trace ("solve' (" <> show s <> ") x") $ solve' s x
solveBatched s@(PartialShuffle' rs as bs) x = trace ("solveBatched, lengths as, bs: " <> show (length as) <> " " <> show (length bs)) $ solveBatch (length as, length as `div` 2) s x

solveBatch :: (MonadFail m, NewShuffleProgress' x m a, Eq a, Show a) => (Int, Int) -> PartialShuffle' a -> x -> m (Maybe [Pair a])
solveBatch (total, n) s x | total `div` 2 > n = solveBatched s x
solveBatch (total, n) s@(PartialShuffle' rs as bs) x | length as - 1 <= n = solveStep (solveBatch (total, total - ((total - n) * 2)))  s x
solveBatch (total, n) s@(PartialShuffle' rs as bs) x = do
    let (rs', as', bs') = findBatch n as bs
    x' <- inform rs' x
    y <- informOpen (fmap fst as') bs' x'
    c <- check y
    if c then solveBatch (total, total - ((total - n) * 2)) (PartialShuffle' (rs <> rs') as' bs') x' --todo: don't go to full half of new size in success case
    else solveBatch (total, ((total - n) `div` 2) + n) s x

findBatch :: (Eq a) => Int -> [(a, Bool)] -> [a] -> ([Pair a], [(a, Bool)], [a])
findBatch n as bs = findBatch' [] n as bs where
    findBatch' rs n as' bs' | length as' <= n = (rs, as', bs')
    findBatch' rs n as@((a, True):_) (b:bs) | a == b = findBatch' rs n as bs
    findBatch' rs n ((a, isUnordered):as) (b:bs) = let
        as' | isUnordered = filter ((/= b) . fst) as
            | otherwise = filter (\(a', isUnordered) -> not isUnordered || a' /= b) as
        bs' | isUnordered = filter (/= a) bs
            | otherwise = bs
        r | isUnordered = UnorderedPair a b
          | otherwise = OrderedPair a b
        in findBatch' (r:rs) n as' bs'
    findBatch' rs n _ _ = error "failed to find match"

initSolve :: (NewShuffleProgress x m a) => PartialShuffle' a -> x -> m x
initSolve (PartialShuffle' known ls rs) = inform known


evalDataLookup' :: LogicData -> DataLookup -> [Pair Thingy]
evalDataLookup' logicData lookup = (\(l,_,r) -> OrderedPair l r) <$> evalDataLookup logicData lookup


--test stuff

data KNFLiteral a = Positive a | Negative a deriving (Eq, Show)

newtype KNF a = KNF [[KNFLiteral a]] deriving (Show)

instance (Eq a) => NewShuffleProgress (KNF a) Identity (Either a Bool) where
    check (KNF clauses) = return $ null clauses
    inform [] x = return x
    inform ((toLit -> (Just a)) : as) (KNF clauses) = inform as $ KNF $ filter (a `notElem`) clauses
    inform (_:as) x = inform as x

toLit (OrderedPair (Left a) (Right b)) = Just $ bool Negative Positive b a
toLit _ = Nothing

start :: (Ord a) => KNF a -> IO (PartialShuffle ((Either a Bool), a))
start (KNF clauses) = fmap PartialShuffle $ randomOrder $ concatMap (\a -> [OrderedPair (Left a, a) (Right True, a), OrderedPair (Left a, a) (Right False, a)]) $ S.toList $ S.fromList $ [a | c <- clauses, Positive a <- c] <> [a | c <- clauses, Negative a <- c]

randomOrder :: [a] -> IO [a]
randomOrder [] = return []
randomOrder inputs = do
    let l = length inputs
    i <- R.randomRIO (0, l-1)
    let (x,xs) = takeOut i inputs
    fmap (x:) $ randomOrder xs

takeOut 0 (a:as) = (a,as)
takeOut (pred -> n) (a:as) = let (a', as') = takeOut n as in (a', a:as')


solveKNF :: (Ord a) => KNF a -> IO (Maybe [KNFLiteral a])
solveKNF k = do
    p <- start k
    let Identity xs = solve p $ DedupedShuffleProgress k
    return $ (catMaybes . fmap (toLit . fmap fst)) <$> xs

exampleInput :: KNF Char
exampleInput = KNF [[Positive 'a'], [Negative 'b'], [Negative 'a', Positive 'b', Negative 'c', Negative 'd', Positive 'e'], [Positive 'c']]

{-

for each shuffle:
  assume all future shuffles in full
  find a solution for the current shuffle
  check the solution against constraints

-}