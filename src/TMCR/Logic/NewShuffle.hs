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


import qualified System.Random as R


data PoolSpec = Finite | Arbitrary --todo: both data-based

data ShuffleSpec =
      DataBasedSpec
    | BipartiteSpec PoolSpec PoolSpec
    | CommonSpec PoolSpec
    | AndThen ShuffleSpec ShuffleSpec

data ShuffleDef =
    ShuffleDef ShuffleName ShuffleSpec
    --todo: conditional based on other shuffles
    --todo: specify shuffle order
type ShuffleName = String

data Pair a = OrderedPair a a | UnorderedPair a a deriving Functor

newtype PartialShuffle a = PartialShuffle
  { remaining :: [Pair a]
  }


fromSpec :: (Monad m, Ord a) => (forall a. [a] -> m [a]) -> (PoolSpec -> m [a]) -> ShuffleSpec -> m (PartialShuffle a)
fromSpec shuf f DataBasedSpec = return $ PartialShuffle [] --todo
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

class (Monad m) => ShuffleProgress x m a | x -> m a where
    inform :: [Pair a] -> x -> m x
    check :: x -> m Bool

newtype DedupedShuffleProgress x b = DedupedShuffleProgress { getDedupedShuffleProgress :: x }

instance (ShuffleProgress x m a) => ShuffleProgress (DedupedShuffleProgress x b) m (a,b) where
    inform as (DedupedShuffleProgress x) = DedupedShuffleProgress <$> inform (fmap (fmap fst) as) x
    check (DedupedShuffleProgress x) = check x

solve :: (ShuffleProgress x m a, Eq a) => PartialShuffle a -> x -> m (Maybe [Pair a])
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



--test stuff

data Literal a = Positive a | Negative a deriving (Eq, Show)

newtype KNF a = KNF [[Literal a]] deriving (Show)

instance (Eq a) => ShuffleProgress (KNF a) Identity (Either a Bool) where
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


solveKNF :: (Ord a) => KNF a -> IO (Maybe [Literal a])
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