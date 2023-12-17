{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
module TMCR.Logic.Algebra (OolAble(), liftOolAble, outOfLogic, getInLogic, getOutOfLogic, Count(), liftCount, finitePart, infiniteExtension, Lattice(..), EqLattice(..), Canonical(..), CountyLattice(..), CompLattice(..), StatefulLattice(..), LogicValues(..), LogicValue(..), latticeFromMaybe, Meet(..), Join(..), DNF(..), singleToDNF) where


import TMCR.Logic.Descriptor
import TMCR.Logic.Common

import Data.Set (Set)
import qualified Data.Set as S

{-
(meet, top) and (join, bottom) are monoids, and there's distributive laws
-}
class Lattice a where
    meet :: a -> a -> a
    join :: a -> a -> a
    bottom :: a
    top :: a

instance Lattice Bool where
    meet = (&&)
    join = (||)
    bottom = False
    top = True

newtype Meet a = Meet { getMeet :: a } deriving (Eq, Ord, Show)
newtype Join a = Join { getJoin :: a } deriving (Eq, Ord, Show)

instance (Lattice a) => Semigroup (Meet a) where
    Meet a <> Meet b = Meet $ meet a b
instance (Lattice a) => Monoid (Meet a) where
    mempty = Meet top

instance (Lattice a) => Semigroup (Join a) where
    Join a <> Join b = Join $ join a b
instance (Lattice a) => Monoid (Join a) where
    mempty = Join bottom

newtype DNF a = DNF { getDisjunctions :: Set (Set a) } deriving (Eq, Ord, Show)

singleToDNF :: (Ord a) => a -> DNF a
singleToDNF = DNF . S.singleton . S.singleton

instance (Ord a) => Lattice (DNF a) where
    meet (DNF x) (DNF y) = DNF $ S.map (uncurry S.union) $ S.cartesianProduct x y
    join (DNF x) (DNF y) = DNF $ S.union x y
    bottom = DNF $ S.empty
    top = DNF $ S.singleton S.empty

data OolAble t = OolAble t t deriving (Eq, Ord, Show)

liftOolAble :: t -> OolAble t
liftOolAble x = OolAble x x

outOfLogic :: (Lattice t) => OolAble t
outOfLogic = OolAble bottom top

getInLogic (OolAble a _) = a
getOutOfLogic (OolAble _ a) = a

instance (Lattice t) => Lattice (OolAble t) where
    bottom = OolAble bottom bottom
    top = OolAble top top
    meet (OolAble x1 x2) (OolAble y1 y2) = OolAble (meet x1 y1) (meet x1 y2 `join` meet x2 y1 `join` meet x2 y2)
    join (OolAble x1 x2) (OolAble y1 y2) = OolAble (join x1 y1) $ x1 `join` x2 `join` y1 `join` y2

class Lattice a => EqLattice a where
    equiv :: a -> a -> Bool
    default equiv :: (Canonical a, Eq a)  => a -> a -> Bool
    a `equiv` b = canonicalize a == canonicalize b
    implies :: a -> a -> Bool
    a `implies` b = (a `join` b) `equiv` b

class EqLattice a => Canonical a where
    canonicalize :: a -> a

instance EqLattice Bool
instance Canonical Bool where
    canonicalize = id

instance (EqLattice t) => EqLattice (OolAble t) where
    (OolAble x1 y1) `equiv` (OolAble x2 y2) = x1 `equiv` x2 && y1 `equiv` y2

instance Canonical t => Canonical (OolAble t) where
    canonicalize = id

--monotonically decreasing
data Count t = CountyValue [t] t
    deriving (Eq, Ord, Show)

finitePart (CountyValue ts _) = ts
infiniteExtension (CountyValue _ t) = t

instance (EqLattice t) => EqLattice (Count t) where
    equiv (CountyValue [] t) (CountyValue [] t') = equiv t t'
    equiv (CountyValue as t) (CountyValue [] t') = all (`equiv` t') as && equiv t t'
    equiv (CountyValue [] t) (CountyValue bs t') = all (equiv t) bs && equiv t t'
    equiv (CountyValue (a:as) t) (CountyValue (b:bs) t') = equiv a b && equiv (CountyValue as t) (CountyValue bs t')

instance (Canonical t) => Canonical (Count t) where
    canonicalize (CountyValue ts t) = CountyValue (takeWhile (\t' -> not $ t `implies` t') ts) t

liftCount :: t -> Count t
liftCount t = CountyValue [] t


instance (Lattice t) => Lattice (Count t) where
    bottom = CountyValue [] bottom
    top = CountyValue [] top
    meet (CountyValue [] x) (CountyValue [] y) = CountyValue [] $ meet x y
    meet (CountyValue (a:as) x) y'@(CountyValue [] y) = (a `meet` y) `andThen` (CountyValue as x `meet` y')
    meet x'@(CountyValue [] x) (CountyValue (b:bs) y) = (x `meet` b) `andThen` (x' `meet` CountyValue bs y)
    meet (CountyValue (a:as) x) (CountyValue (b:bs) y) = (a `meet` b) `andThen` (CountyValue as x `meet` CountyValue bs y)
    join (CountyValue [] x) (CountyValue [] y) = CountyValue [] $ join x y
    join (CountyValue (a:as) x) y'@(CountyValue [] y) = (a `join` y) `andThen` (CountyValue as x `join` y')
    join x'@(CountyValue [] x) (CountyValue (b:bs) y) = (x `join` b) `andThen` (x' `join` CountyValue bs y)
    join (CountyValue (a:as) x) (CountyValue (b:bs) y) = (a `join` b) `andThen` (CountyValue as x `join` CountyValue bs y)

andThen :: t -> (Count t) -> (Count t)
andThen a (CountyValue b c) = CountyValue (a:b) c

class (Lattice a) => CountyLattice a where
    fromNumber :: Int -> a
    addCounty :: a -> a -> a
    multiplyCounty :: a -> a -> a

instance (Lattice t) => CountyLattice (Count t) where
    fromNumber n = CountyValue (replicate n top) bottom
    --addCounty :: CountyValue -> CountyValue -> CountyValue
    addCounty (CountyValue [] x) (CountyValue [] y) = CountyValue [] $ x `join` y
    addCounty x'@(CountyValue [] x) (CountyValue (b:bs) y) = (x `join` b) `andThen` addCounty x' (CountyValue bs y)
    addCounty (CountyValue (a:as) x) y'@(CountyValue [] y) = (a `join` y) `andThen` addCounty (CountyValue as x) y'
    addCounty x'@(CountyValue (a:as) x) y'@(CountyValue (b:bs) y) = (a `join` b) `andThen` meet (addCounty (CountyValue as x) y') (addCounty x' (CountyValue bs y))
    multiplyCounty (CountyValue [] x) y = scale x y
    multiplyCounty (CountyValue (a:as) x) y = scale a y `addCounty` multiplyCounty (CountyValue as x) y

class (Lattice t, CountyLattice c) => LogicValues t c where
    scale :: t -> c -> c
    atLeast :: Nteger -> c -> t

instance (Lattice t) => LogicValues t (Count t) where
    --scale :: TruthyValue -> CountyValue -> CountyValue
    scale x (CountyValue bs y) = CountyValue (fmap (meet x) bs) $ meet x y
    atLeast Infinite (CountyValue _ x) = x
    atLeast (Finite n) _ | n <= 0 = top
    atLeast (Finite _) (CountyValue [] x) = x
    atLeast (Finite 1) (CountyValue (a:_ ) _) = a
    atLeast (Finite n) (CountyValue (_:as) x) = atLeast (Finite $ n-1) (CountyValue as x)

data LogicValue t :: DescriptorType -> * where
    LogicTruthyValue :: t -> LogicValue t Truthy
    LogicCountyValue :: (Count t) -> LogicValue t County

deriving instance (Eq t) => Eq (LogicValue t Truthy)
deriving instance (Eq t) => Eq (LogicValue t County)
deriving instance (Ord t) => Ord (LogicValue t Truthy)
deriving instance (Ord t) => Ord (LogicValue t County)
deriving instance (Show t) => Show (LogicValue t Truthy)
deriving instance (Show t) => Show (LogicValue t County)

instance (EqLattice t) => EqLattice (LogicValue t Truthy) where
    equiv (LogicTruthyValue t) (LogicTruthyValue t') = equiv t t'
instance (Canonical t) => Canonical (LogicValue t Truthy) where
    canonicalize (LogicTruthyValue t) = LogicTruthyValue $ canonicalize t
instance (EqLattice t) => EqLattice (LogicValue t County) where
    equiv (LogicCountyValue t) (LogicCountyValue t') = equiv t t'
instance (Canonical t) => Canonical (LogicValue t County) where
    canonicalize (LogicCountyValue t) = LogicCountyValue $ canonicalize t

instance (Lattice t) => Lattice (LogicValue t Truthy) where
    top = LogicTruthyValue top
    bottom = LogicTruthyValue bottom
    LogicTruthyValue x `meet` LogicTruthyValue y = LogicTruthyValue $ x `meet` y
    LogicTruthyValue x `join` LogicTruthyValue y = LogicTruthyValue $ x `join` y

instance (Lattice t) => Lattice (LogicValue t County) where
    top = LogicCountyValue top
    bottom = LogicCountyValue bottom
    LogicCountyValue x `meet` LogicCountyValue y = LogicCountyValue $ x `meet` y
    LogicCountyValue x `join` LogicCountyValue y = LogicCountyValue $ x `join` y

instance (Lattice t) => CountyLattice (LogicValue t County) where
    fromNumber n = LogicCountyValue $ fromNumber n
    LogicCountyValue x `addCounty` LogicCountyValue y = LogicCountyValue $ x `addCounty` y
    LogicCountyValue x `multiplyCounty` LogicCountyValue y = LogicCountyValue $ x `multiplyCounty` y

instance (Lattice t) => LogicValues (LogicValue t Truthy) (LogicValue t County) where
    scale (LogicTruthyValue x) (LogicCountyValue y) = LogicCountyValue $ scale x y
    atLeast n (LogicCountyValue x) = LogicTruthyValue $ atLeast n x

latticeFromMaybe Nothing = bottom
latticeFromMaybe (Just x) = x

class (Lattice t) => CompLattice t where
    composeL :: t -> t -> t

instance (CompLattice t) => CompLattice (LogicValue t Truthy) where
    composeL (LogicTruthyValue a) (LogicTruthyValue b) = LogicTruthyValue $ a `composeL` b

instance (CompLattice t) => CompLattice (Count t) where
    composeL (CountyValue [] xs) (CountyValue [] ys) = CountyValue [] (xs `composeL` ys)
    composeL (CountyValue xss xs) y@(CountyValue yss ys) = foldr addCounty (foldr addCounty (CountyValue [] (xs `composeL` ys)) $ fmap (\y -> CountyValue [] (xs `composeL` y)) yss) $ fmap (\x -> CountyValue (fmap (composeL x) yss) (composeL x ys)) xss

instance (CompLattice t) => CompLattice (LogicValue t County) where
    composeL (LogicCountyValue a) (LogicCountyValue b) = LogicCountyValue $ a `composeL` b

instance (CompLattice t) => CompLattice (OolAble t) where
    composeL (OolAble x1 x2) (OolAble y1 y2) = OolAble (composeL x1 y1) (composeL x1 y2 `join` composeL x2 y1 `join` composeL x2 y2)

newtype ComposeByMeet a = ComposeByMeet a deriving newtype Lattice

instance (Lattice a) => CompLattice (ComposeByMeet a) where
    composeL = meet

deriving via (ComposeByMeet Bool) instance (CompLattice Bool)
deriving via (ComposeByMeet (DNF a)) instance (Ord a) => (CompLattice (DNF a))

class (CompLattice a) => StatefulLattice s a | a -> s where
    preState :: s -> a
    postState :: s -> a
    atState :: s -> a -> a

instance (StatefulLattice s a) => StatefulLattice s (Count a) where
    preState s = CountyValue [] $ preState s
    postState s = CountyValue [] $ postState s
    atState s (CountyValue xs x) = CountyValue (fmap (atState s) xs) (atState s x)

instance (StatefulLattice s t) => StatefulLattice s (LogicValue t Truthy) where
    preState s = LogicTruthyValue $ preState s
    postState s = LogicTruthyValue $ postState s
    atState s (LogicTruthyValue t) = LogicTruthyValue $ atState s t

instance (StatefulLattice s t) => StatefulLattice s (LogicValue t County) where
    preState s = LogicCountyValue $ preState s
    postState s = LogicCountyValue $ postState s
    atState s (LogicCountyValue t) = LogicCountyValue $ atState s t