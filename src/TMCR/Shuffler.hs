{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
module TMCR.Shuffler where

import TMCR.Logic.Descriptor
import TMCR.Logic.Shuffle
import TMCR.Logic.Common
import TMCR.Logic.Logic (ScopedName, LogicNodeName)
import TMCR.Module
import TMCR.Logic.Graphs

import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M

import Data.Set (Set)
import qualified Data.Set as S

import Data.Functor.Const (Const(..))
import Data.Functor.Identity (Identity(..))

import Control.Monad hiding (join)

import Data.Kind (Type)

import Control.Lens
    ( Identity(runIdentity),
      Traversal',
      _Just,
      makeLenses,
      At(at),
      Ixed(ix),
      Field1(_1),
      Field2(_2),
      (^?!),
      (^.),
      to,
      use,
      view,
      (<<.=),
      (%=),
      (%~),
      (.=),
      (<>=), Getter )
import Control.Lens.TH
import Control.Monad.Trans
import Control.Monad.RWS (RWST(..), MonadState(..), MonadWriter(..), execRWST, gets)
import Control.Monad.Reader (MonadReader(..), ReaderT(..), asks, local)
import TMCR.Logic.Algebra
import TMCR.Logic.Merge

import Data.Coerce (coerce)
import Data.List (subsequences, (\\))
import Data.Maybe (catMaybes, fromMaybe)
import Control.Monad.Trans.Writer (WriterT, execWriterT)
import GHC.Generics (Generic)
import Data.Hashable (Hashable)

--descriptors, with all parameters specified, with reachability (and maybe sphere) values (truthy descriptors) or reachable counts (county descriptors)
--shuffles, hierarchical multi relations
--logic nodes, with reachability values

data ShuffleProgress t c = ShuffleProgress {
      _shuffles :: ShufflesProgress
    , _truthyDescriptors :: Map (DescriptorIdent Truthy, [Thingy]) t
    , _countyDescriptors :: Map (DescriptorIdent County, [Thingy]) c
    , _logicNodes :: Map LogicNodeName t
    , _cachedAccess :: Map (DescriptorName, [Thingy]) (Set LogicNodeName)
    , _cachedDependencies :: Bipartite ShuffleDependency ShuffleDependent
    } deriving (Eq, Show)

initialShufflesProgress :: GameDef -> RandomSeed -> ShufflesProgress
initialShufflesProgress def seed = (def ^. defShuffles . to (convertShuffles (def ^. defLogicData) seed) )

initialShuffleProgress :: GameDef -> RandomSeed -> ShuffleProgress t c
initialShuffleProgress def seed = ShuffleProgress (initialShufflesProgress def seed) M.empty M.empty M.empty (computeAccess def) mempty

computeAccess :: GameDef -> Map (DescriptorName, [Thingy]) (Set LogicNodeName)
computeAccess def = def ^. defLogic . _2 . to M.toList . to (\xs -> [(d, S.singleton n) | (n, ds) <- xs, d <- ds]) . to (M.fromListWith (<>))

data ShuffleDependent =
      DescriptorDependent (DescriptorName, [Thingy])
    | LogicNodeDependent LogicNodeName
    | ShuffleDependent ShuffleStepIdent
    deriving (Eq, Ord, Show, Generic)

instance Hashable ShuffleDependent where

data ShuffleDependency =
      DescriptorDependency (DescriptorName, [Thingy])
    | ShuffleDependency Relation Thingy
    | AccessDependency DescriptorType (DescriptorName, [Thingy])
    | LogicNodeDependency LogicNodeName
    deriving (Eq, Ord, Show)

data ShuffleDependencyWithValue v where
      DescriptorDependencyWithValue :: (DescriptorIdent t, [Thingy]) -> v t -> ShuffleDependencyWithValue v
      ShuffleDependencyWithValue :: Relation -> Thingy -> [(Thingy, Nteger)] -> ShuffleDependencyWithValue v
      AccessDependencyWithValue :: SDescriptorType t -> (DescriptorIdent t, [Thingy]) -> v t -> ShuffleDependencyWithValue v
      LogicNodeDependencyWithValue :: LogicNodeName -> v Truthy -> ShuffleDependencyWithValue v

forgetValue :: ShuffleDependencyWithValue v -> ShuffleDependency
forgetValue (DescriptorDependencyWithValue (TruthyDescriptorIdent name, params) _) = DescriptorDependency (name, params)
forgetValue (DescriptorDependencyWithValue (CountyDescriptorIdent name, params) _) = DescriptorDependency (name, params)
forgetValue (ShuffleDependencyWithValue rel x _) = ShuffleDependency rel x
forgetValue (AccessDependencyWithValue STruthy (TruthyDescriptorIdent name, params) _) = AccessDependency Truthy (name, params)
forgetValue (AccessDependencyWithValue SCounty (CountyDescriptorIdent name, params) _) = AccessDependency County (name, params)
forgetValue (LogicNodeDependencyWithValue name _) = LogicNodeDependency name

$(makeLenses ''ShuffleProgress)

class (Monad m) => MonadEval t c m | m -> t c where
    askDefinitions :: m Definitions
    askTruthyDescriptor :: DescriptorIdent Truthy -> [Thingy] -> m t
    askCountyDescriptor :: DescriptorIdent County -> [Thingy] -> m c
    askAccessTruthy :: DescriptorName -> [Thingy] -> m t
    askAccessCounty :: DescriptorName -> [Thingy] -> m c
    askLogicNodeAccess :: LogicNodeName -> m t
    askShuffle :: Relation -> Thingy -> m [(Thingy, Nteger)]

askDescriptor :: (MonadEval (v Truthy) (v County) m) => DescriptorIdent t -> [Thingy] -> m (v t)
askDescriptor ident@(TruthyDescriptorIdent _) args = askTruthyDescriptor ident args
askDescriptor ident@(CountyDescriptorIdent _) args = askCountyDescriptor ident args
askAccess :: forall (v :: DescriptorType -> Type) t m. (MonadEval (v Truthy) (v County) m) => DescriptorIdent t -> [Thingy] -> m (v t)
askAccess (TruthyDescriptorIdent name) = askAccessTruthy name
askAccess (CountyDescriptorIdent name) = askAccessCounty name


type Eval m v = forall t. DescriptorRule' t Thingy -> m (v t)

data Eval' m v f x = Eval' {
    evalIsEq :: x -> x -> m (v Truthy)
  , evalCall :: forall t'. DescriptorIdent t' -> [Thingy] -> m (v t')
  , evalCanAccess :: forall t'. DescriptorIdent t' -> [Thingy] -> [StateBody Thingy] -> m (v t')
  , evalQuantify :: Relation -> Thingy -> m (f Thingy)
  , evalExists :: f (v Truthy) -> m (v Truthy)
  , evalCount :: f (v Truthy) -> m (v County)
  , evalConsume :: forall t'. ConsumeUUID -> DescriptorName -> [Thingy] -> DescriptorRule' t' Thingy -> m (v t') -- this is probably wrong, but let's put off consuming until later
  }


basicEval' :: forall m f v. (Monad m, Traversable f, LogicValues (v Truthy) (v County), OoLattice (v Truthy)) => Eval' m v f Thingy -> Eval m v
basicEval' Eval' {..} = eval where
  eval :: forall t'. DescriptorRule' t' Thingy -> m (v t')
  eval (Constant (TruthyLiteral OolTrue)) = return $ top
  eval (Constant (TruthyLiteral OolOol)) = return $ ool
  eval (Constant (TruthyLiteral OolFalse)) = return $ bottom
  eval (Constant (CountyLiteral n)) = return $ fromNteger n
  eval (IsEqual a b) = evalIsEq a b
  eval (CallDescriptor STruthy name args) = evalCall (TruthyDescriptorIdent name) args
  eval (CallDescriptor SCounty name args) = evalCall (CountyDescriptorIdent name) args
  eval (CanAccess STruthy name args state) = evalCanAccess (TruthyDescriptorIdent name) args state
  eval (CanAccess SCounty name args state) = evalCanAccess (CountyDescriptorIdent name) args state
  eval (Scale a n) = fmap ((`scaleC` n)) $ eval $ a
  eval (Sum as) = fmap (foldr addCounty bottom) $ traverse eval as
  eval (AtLeast a n) = fmap (atLeast n) $ eval a
  eval (Exist rel var rule') = do
    c <- evalQuantify rel var
    ts <- forM c $ \c' -> eval $ fmap (fromMaybe c') rule'
    evalExists ts
  eval (Count rel var rule') = do
    c <- evalQuantify rel var
    ts <- forM c $ \c' -> eval $ fmap (fromMaybe c') rule'
    evalCount ts
  eval (Min STruthy x) = fmap (getMeet . foldMap Meet) $ traverse eval x
  eval (Min SCounty x) = fmap (getMeet . foldMap Meet) $ traverse eval x
  eval (Max STruthy x) = fmap (getJoin . foldMap Join) $ traverse eval x
  eval (Max SCounty x) = fmap (getJoin . foldMap Join) $ traverse eval x
  eval (Cast a) = fmap cast $ eval a
  --eval (PriorState s) = priorState s
  --eval (PostState s) = postState s
  eval (Consume uid name args rule') = evalConsume uid name args rule'

fromNteger :: (CountyLattice a) => Nteger -> a
fromNteger Infinite = top
fromNteger (Finite n) = fromNumber n

data Definitions = Definitions {
                     _definedEdges :: TaggedGraph (Join (DNF (DescriptorName, [Thingy]))) (Maybe LogicNodeName)
                   , _definedLogicNodes :: Map LogicNodeName [(DescriptorName, [Thingy])]
                   , _descriptorDeclarations :: Map DescriptorName DescriptorDeclaration
                   , _truthyDescriptorDefinitions :: Map (DescriptorIdent Truthy) [Descriptor Truthy]
                   , _countyDescriptorDefinitions :: Map (DescriptorIdent County) [Descriptor County]
                   , _definedShuffles :: Map ShuffleName (ShuffleInstruction, [ShuffleInstruction])
                   } deriving (Eq, Ord, Show)

$(makeLenses ''Definitions)

getDefinitions :: GameDef -> Definitions
getDefinitions def = Definitions (def ^. defLogic . _1) (def ^. defLogic . _2) (def ^. defDescriptors) (def ^. defDescriptorDefinitionsTruthy) (def ^. defDescriptorDefinitionsCounty) (def ^. defShuffles)

--definedEdgesTo :: LogicNodeName -> Traversal' Definitions [(LogicNodeName, Descriptor Truthy)]
definedEdgesTo name = definedEdges . to (taggedGetEdgesTo name)
--definedEdgesFrom :: LogicNodeName -> Traversal' Definitions [(Descriptor Truthy, LogicNodeName)]
definedEdgesFrom name = definedEdges . to (taggedGetEdgesFrom name)
--definedLogicNodeAccess :: LogicNodeName -> Traversal' Definitions [(DescriptorName, [Thingy])]
definedLogicNodeAccess name = definedLogicNodes . ix name
definedDescriptorType  :: DescriptorName -> Traversal' Definitions DescriptorType
definedDescriptorType name = descriptorDeclarations . ix name . descriptorDeclarationType
-- definedDescriptorConsumesSpec  :: DescriptorName -> Traversal' Definitions DescriptorConsumeSpec
-- definedDescriptorConsumesSpec name = descriptorDeclarations . ix name . descriptorDeclarationConsumes . _Just
definedDescriptor :: DescriptorIdent t -> Traversal' Definitions [Descriptor t]
definedDescriptor name@(TruthyDescriptorIdent _) = truthyDescriptorDefinitions . ix name
definedDescriptor name@(CountyDescriptorIdent _) = countyDescriptorDefinitions . ix name


updateLocal :: (Eq (v Truthy), Eq (v County), LogicValues (v Truthy) (v County)) => Definitions -> Eval (UpdateT v (ReadEval v Identity)) v -> ShuffleDependent -> ShuffleProgress (v Truthy) (v County) -> ([Update v], [ShuffleDependencyWithValue v])
updateLocal defs eval object progress = runUpdate defs progress $ updateLocal' eval object

updateLocal' :: (Eq (v Truthy), Eq (v County), Monad m, MonadEval (v Truthy) (v County) m, LogicValues (v Truthy) (v County)) => Eval (UpdateT v m) v -> ShuffleDependent -> UpdateT v m ()
updateLocal' eval object = case object of
    LogicNodeDependent name -> do
        updateLogicNode eval name
    DescriptorDependent (name, params) -> do
        defs <- askDefinitions
        let descType = defs ^?! definedDescriptorType name
        -- spec <- asks (^? definedDescriptorConsumesSpec name)
        case descType of
            Truthy -> do
                updateTruthyDescriptor eval (name, params)
            County -> do
                updateCountyDescriptor eval (name, params)
            -- (Truthy, Just (DescriptorConsumeSpec key lock)) -> deferConsumer eval (TruthyDescriptorIdent lock, params) >>= updateTruthyDescriptor (name, params)
            -- (County, Just (DescriptorConsumeSpec key lock)) -> deferConsumer eval (CountyDescriptorIdent lock, params) >>= updateCountyDescriptor (name, params)
    ShuffleDependent ident -> do
        {-
        currentShuffles <- use $ _1 . shuffles
        let (ShuffleStepResult shuffles' deps didUpdate) = stepShuffle currentShuffles ident
        _1 . shuffles .= shuffles'
        tell $ ShuffleDependent <$> deps
        let shuffleName = associatedShuffle ident
        _1 . cachedDependencies %= bipSetEdgesTo (ShuffleDependent ident) (ShuffleDependency . associatedShuffle <$> deps)
        when didUpdate $ do
            xs <- use $ _1 . cachedDependencies . to (bipGetEdgesFrom  $ ShuffleDependency shuffleName)
            tell xs
            -}
            return () --todo


type UpdateContext v = (Definitions, ShuffleProgress (v Truthy) (v County))

newtype UpdateT v m a = UpdateT { extractUpdate :: WriterT ([Update v], [ShuffleDependencyWithValue v]) m a }
                      deriving newtype ( MonadWriter ([Update v], [ShuffleDependencyWithValue v]))
                      deriving newtype Functor
                      deriving newtype Applicative
                      deriving newtype Monad

updateContextDefinitions :: Getter (UpdateContext v) Definitions
updateContextDefinitions = _1
tellUpdate u = (u, mempty)
tellDependency d = (mempty, d)

data Update v = UpdateDependency [ShuffleDependencyWithValue v] ShuffleDependent
              | UpdateLogicNode LogicNodeName (v Truthy)
              | UpdateTruthyDescriptor (DescriptorName, [Thingy]) (v Truthy)
              | UpdateCountyDescriptor (DescriptorName, [Thingy]) (v County)

runUpdateT :: (Eq (v Truthy), Eq (v County), Monad m) => Definitions -> ShuffleProgress (v Truthy) (v County) -> UpdateT v (ReadEval v m) () -> m ([Update v], [ShuffleDependencyWithValue v])
runUpdateT defs progress action = runReaderT (runReadEval $ execWriterT $ extractUpdate action) (defs, progress)

runUpdate :: (Eq (v Truthy), Eq (v County)) => Definitions -> ShuffleProgress (v Truthy) (v County) -> UpdateT v (ReadEval v Identity) () -> ([Update v], [ShuffleDependencyWithValue v])
runUpdate defs progress = runIdentity . runUpdateT defs progress

--viewDefinitions :: (MonadEval (v Truthy) (v County) m) => Getter Definitions a -> m a
viewDefinitions g = fmap (^. g) askDefinitions

updateLogicNode :: (MonadEval (v Truthy) (v County) m, Eq (v Truthy), LogicValues (v Truthy) (v County)) => Eval (UpdateT v m) v -> LogicNodeName -> UpdateT v m ()
updateLogicNode eval name = do
        (t, (_, deps)) <- listen $ do
          incomingEdges <- viewDefinitions $ definedEdgesTo (Just name)
          ts <- forM incomingEdges $ \(source, edge) -> do
            t <- case source of
                Just source -> askLogicNodeAccess source
                Nothing -> return $ top
            t' <- fmap (getJoin . foldMap Join) $ forM (S.toList $ getDisjunctions $ getJoin edge) $ \clause ->
                    fmap (getMeet . foldMap Meet) $ forM (S.toList clause) $ \(descName, args) ->
                        askTruthyDescriptor (TruthyDescriptorIdent descName) args
            return $ meet t t'
          return $ getJoin $ foldMap Join ts
        updateLogicNode' name deps t

updateLogicNode' :: (Monad m, Eq (v Truthy)) => LogicNodeName -> [ShuffleDependencyWithValue v] -> v Truthy -> UpdateT v m ()
updateLogicNode' name deps value = tell $ tellUpdate $ [UpdateLogicNode name value, UpdateDependency deps (LogicNodeDependent name)]

tryBind :: Value -> Thingy -> DescriptorRule t -> Maybe (DescriptorRule t)
tryBind (ConstantValue v) v' | v == v' = Just
                             | otherwise = const Nothing
tryBind (Variable var) val = Just . fmap (bind var val) where
  bind var val (Variable var') | var == var' = ConstantValue val
  bind _ _ x = x

updateCountyDescriptor :: (MonadEval (v Truthy) (v County) m, Eq (v County), LogicValues (v Truthy) (v County)) => Eval (UpdateT v m) v -> (DescriptorName, [Thingy]) -> UpdateT v m ()
updateCountyDescriptor eval (name, params) = do
    (t, (_, deps)) <- listen $ do
                ds <- viewDefinitions $ definedDescriptor (CountyDescriptorIdent name)
                ts <- forM ds $ \(Descriptor patterns rule) ->
                    fromMaybe (return bottom) $ do
                      rule' <- foldr (>=>) return (zipWith tryBind patterns params) rule
                      return $ eval $ fmap (assertNotFree name) rule'
                return $  getJoin $ foldMap Join ts
    updateCountyDescriptor' (name, params) t deps

assertNotFree :: DescriptorName -> Value -> Thingy
assertNotFree _ (ConstantValue v) = v
assertNotFree name (Variable var) = error $ "Unbound variable " <> show var <> " in definition of " <> show name -- this *should* be validated with proper error handling earlier, but just in case we have a sensible message here

updateCountyDescriptor' :: (Monad m, Eq (v County)) => (DescriptorName, [Thingy]) -> v County -> [ShuffleDependencyWithValue v] -> UpdateT v m ()
updateCountyDescriptor' desc value deps = tell $ tellUpdate [UpdateCountyDescriptor desc value, UpdateDependency deps $ DescriptorDependent desc]

updateTruthyDescriptor :: (MonadEval (v Truthy) (v County) m, Eq (v Truthy), LogicValues (v Truthy) (v County)) => Eval (UpdateT v m) v -> (DescriptorName, [Thingy]) -> UpdateT v m ()
updateTruthyDescriptor eval (name, params) = do
    (t, (_, deps)) <- listen $ do
                ds <- viewDefinitions $ definedDescriptor (TruthyDescriptorIdent name)
                ts <- forM ds $ \(Descriptor patterns rule) ->
                    fromMaybe (return bottom) $ do
                      rule' <- foldr (>=>) return (zipWith tryBind patterns params) rule
                      return $ eval $ fmap (assertNotFree name) rule'
                return $ getJoin $ foldMap Join ts
    updateTruthyDescriptor' (name, params) t deps

updateTruthyDescriptor' :: (Monad m, Eq (v Truthy)) => (DescriptorName, [Thingy]) -> v Truthy -> [ShuffleDependencyWithValue v] -> UpdateT v m ()
updateTruthyDescriptor' desc value deps = tell $ tellUpdate [UpdateTruthyDescriptor desc value, UpdateDependency deps $ DescriptorDependent desc]

instance (MonadEval (v Truthy) (v County) m, LogicValues (v Truthy) (v County)) => MonadEval (v Truthy) (v County) (UpdateT v m) where
    askDefinitions = UpdateT $ askDefinitions
    askTruthyDescriptor name@(TruthyDescriptorIdent _) params = do
        value <- UpdateT $ askTruthyDescriptor name params
        tell $ tellDependency [DescriptorDependencyWithValue (name, params) value]
        return value
    askCountyDescriptor name@(CountyDescriptorIdent name') params = do
        value <- UpdateT $ askCountyDescriptor name params
        tell $ tellDependency [DescriptorDependencyWithValue (name, params) value]
        return value
    askAccessTruthy name params = do
      value <- UpdateT $ askAccessTruthy name params
      tell $ tellDependency [AccessDependencyWithValue STruthy (TruthyDescriptorIdent name, params) value]
      return value
    askAccessCounty name params = do
      value <- UpdateT $ askAccessCounty name params
      tell $ tellDependency [AccessDependencyWithValue SCounty (CountyDescriptorIdent name, params) value]
      return value
    askShuffle rel x = do
      value <- UpdateT $ askShuffle rel x
      tell $ tellDependency [ShuffleDependencyWithValue rel x value]
      return value
    askLogicNodeAccess name = do
      value <- UpdateT $ askLogicNodeAccess name
      tell $ tellDependency [LogicNodeDependencyWithValue name value]
      return value

newtype ReadEval v m a = ReadEval { runReadEval :: ReaderT (UpdateContext v) m a } deriving newtype (Functor, Applicative, Monad, MonadReader (UpdateContext v))

instance (Monad m, LogicValues (v Truthy) (v County)) => MonadEval (v Truthy) (v County) (ReadEval v m) where
    askDefinitions = view $ _1
    askTruthyDescriptor name@(TruthyDescriptorIdent name') params = do
        val <- view $ _2 . truthyDescriptors . at (name, params)
        case val of
            Nothing -> return bottom
            Just x -> return x
    askCountyDescriptor name@(CountyDescriptorIdent name') params = do
        val <- view $ _2 . countyDescriptors . at (name, params)
        case val of
            Nothing -> return bottom
            Just x -> return x
    askAccessTruthy name params = do
      n <- view $ _2 . cachedAccess . at (name, params)
      case n of
          Nothing -> return bottom
          Just (S.toList -> n) -> fmap (getJoin . foldMap Join) $ traverse askLogicNodeAccess n
    askAccessCounty name params = do
      n <- view $ _2 . cachedAccess . at (name, params)
      case n of
          Nothing -> return bottom
          Just (S.toList -> n) -> fmap (foldr (\x a -> addCounty a $ cast x) bottom) $ traverse askLogicNodeAccess n
    askLogicNodeAccess name = do
        val <- view $ _2 . logicNodes . at name
        case val of
            Nothing -> return bottom
            Just x -> return x
    askShuffle rel x = do
        let (name, condition) = case rel of
                Forward name -> (name, MappedTo x)
                Backward name -> (name, MappedFrom x)
        view $ _2 . shuffles . to (\x -> getByCondition x name condition)

instance (MonadEval t c m, MonadTrans t', Monad (t' m)) => MonadEval t c (Lift t' m) where
    askDefinitions = lift $ askDefinitions
    askTruthyDescriptor name params = lift $ askTruthyDescriptor name params
    askCountyDescriptor name params = lift $ askCountyDescriptor name params
    askAccessTruthy name params = lift $ askAccessTruthy name params
    askAccessCounty name params = lift $ askAccessCounty name params
    askLogicNodeAccess name = lift $ askLogicNodeAccess name
    askShuffle name param = lift $ askShuffle name param

deriving via Lift (ReaderT r) m instance (MonadEval t c m) => MonadEval t c (ReaderT r m)
deriving via Lift (WriterT w) m instance (Monoid w, MonadEval t c m) => MonadEval t c (WriterT w m)

data LockIdent = LockIdent {
      lockIdentOpenUUID :: Int
    , lockIdentOpenContext :: Map VarName Thingy
    , lockIdentKeyDesc :: DescriptorName
    , lockIdentKeyNames :: [Thingy]
    } deriving (Eq, Ord, Show)

data Consuming a t = Consuming { getConsuming :: (Map (Set a) t) } deriving (Eq, Ord, Show)

data StateBodies a = StateBodies
        { isSets :: Set a
        , isNotSets :: Set a
        , othersUnlimited :: Bool
        } deriving (Eq, Ord, Show)

instance (Ord a) => Semigroup (StateBodies a) where
    StateBodies x y b <> StateBodies x' y' b' = StateBodies (x <> x') (y <> y') (b || b')

instance (Ord a) => Monoid (StateBodies a) where
    mempty = StateBodies mempty mempty False

sbFromList :: (Ord a) => [StateBody a] -> StateBodies a
sbFromList xs = StateBodies (S.fromList [v | IsSet v <- xs]) (S.fromList [v | IsNotSet v <- xs]) False

newtype Stateful t = Stateful (Map (StateBodies Thingy, StateBodies Thingy) t) -- invariant: for all keys, the concerned states in the pre- and post-conditions are the same (union of isSet and isNotSet)
    deriving Eq
    deriving Ord
    deriving Show

instance (Lattice t) => Lattice (Stateful t) where
    meet (Stateful a) (Stateful b) = Stateful $ M.fromListWith join $ do
            ((StateBodies preT preF preB, StateBodies postT postF postB), val) <- M.toList a
            ((StateBodies preT' preF' preB', StateBodies postT' postF' postB'), val') <- M.toList b
            let concerned = preT `S.union` preF
                concerned' = preT' `S.union` preF'
                concernedBoth = concerned `S.intersection` concerned'
                concernedEither = concerned `S.union` concerned'
                rBoth = S.intersection concernedBoth
                rLeft = S.intersection (concerned S.\\ concerned')
                rRight = S.intersection (concerned' S.\\ concerned)
            guard $ (rBoth <$> [preT, preF, postT, postF]) == (rBoth <$> [preT', preF', postT', postF'])
            guard $ case (preB, postB) of
                (True, True) -> null $ rRight preF' -- allow high and falling connections only
                (True, False) -> null $ rRight $ preF' `S.union` postF' -- allow high connections only
                (False, False) -> null $ rRight $ S.intersection preF' postT' `S.union` S.intersection preT' postF' -- allow same connections only
                (False, True) -> True -- no restrictions
            guard $ case (preB', postB') of
                (True, True) -> null $ rLeft preF -- allow high and falling connections only
                (True, False) -> null $ rLeft $ preF `S.union` postF -- allow high connections only
                (False, False) -> null $ rLeft $ S.intersection preF postT `S.union` S.intersection preT postF -- allow same connections only
                (False, True) -> True -- no restrictions
            let presT = preT <> preT'
                presF = preF <> preF'
                presB = preB || preB'
                postsT = postT <> postT'
                postsF = postF <> postF'
                postsB = postB && postB'
            return ((StateBodies presT presF presB, StateBodies postsT postsF postsB),val `meet` val')
    join (Stateful a) (Stateful b) = Stateful $ M.unionWith join a b
    top = Stateful (M.singleton (StateBodies mempty mempty False, StateBodies mempty mempty True) top)
    bottom = Stateful mempty

liftStateful :: t -> Stateful t
liftStateful = Stateful . M.singleton (mempty,mempty)

liftConsuming = Consuming . uncurry M.singleton . ((,) S.empty)

instance (Lattice t, Ord a) => Lattice (Consuming a t) where
    meet (Consuming x) (Consuming y) = Consuming $ M.fromList $ [(S.union k1 k2, v1 `meet` v2) | (k1, v1) <- M.toList x, (k2, v2) <- M.toList y]
    join (Consuming x) (Consuming y) = Consuming $ M.unionWith join x y
    top = liftConsuming top
    bottom = liftConsuming bottom

canonicalizeConsuming :: (Ord a, EqLattice t) => Consuming a t -> Consuming a t
canonicalizeConsuming = Consuming . M.foldlWithKey' f mempty . getConsuming where
        f acc key (!value) = if | supplanted acc key value -> acc
                                                | otherwise -> M.insert key value $ M.mapMaybeWithKey (g key value) acc
        supplanted acc key value = any (\(key', value') -> S.isSubsetOf key' key && value `implies` value') $ M.toList acc
        g key1 v1 key2 v2 | key1 `S.isSubsetOf` key2 = let !vnew = v1 `join` v2 in if | vnew `equiv` v1 -> Nothing
                                                                                      | otherwise -> Just vnew
                          | otherwise = Just v2

instance (EqLattice t, Ord a) => EqLattice (Consuming a t) where
    (canonicalizeConsuming -> Consuming x1) `equiv` (canonicalizeConsuming -> Consuming x2) = case M.mergeA (M.traverseMissing $ \_ _ -> Nothing) (M.traverseMissing $ \_ _ -> Nothing) (M.zipWithAMatched $ \_ a b -> if equiv a b then Just () else Nothing) x1 x2 of
        Just _ -> True
        Nothing -> False

instance (Canonical t, Ord a) => Canonical (Consuming a t) where
    canonicalize (Consuming a) = canonicalizeConsuming $ Consuming $ fmap canonicalize a

instance (EqLattice t) => EqLattice (Stateful t) where
    (Stateful a) `equiv` (Stateful b) = case M.mergeA (M.traverseMissing $ \_ _ -> Nothing) (M.traverseMissing $ \_ _ -> Nothing) (M.zipWithAMatched $ \_ a b -> if equiv a b then Just () else Nothing) a b of
        Just _ -> True
        Nothing -> False

defaultEval :: (v ~ (LogicValue (Consuming LockIdent (OolAble t))), Monad m, LogicValues (v Truthy) (v County), OoLattice (v Truthy), MonadEval (v Truthy) (v County) m) => Eval m v
defaultEval = basicEval' $ Eval' isEq askDescriptor (\ident args _state -> askAccess ident args) quantify exists count consume where
  isEq a b = return $ if a == b then top else bottom
  quantify rel x = fmap CountedList $ askShuffle rel x
  exists ts = return $ getJoin $ foldMap Join ts
  count ts = return $ getLatticeSum $ foldMap (\(a,n) -> LatticeSum $ meet (fromNteger n) $ cast a) $ getCountedList ts
  consume = undefined

newtype CountedList a = CountedList { getCountedList :: [(a, Nteger)] } deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)

{-
    evalDeferConsumer :: forall t'. (Int, Map VarName Thingy, DescriptorIdent t', [Thingy]) -> m (LogicValue t t')
    evalDeferConsumer (uuid, bindings, TruthyDescriptorIdent name, args) = return $ LogicTruthyValue $ Consuming $ uncurry M.singleton $ (S.singleton (LockIdent uuid bindings name args), top)
    evalDeferConsumer (uuid, bindings, CountyDescriptorIdent name, args) = return $ LogicCountyValue $ liftCount $ Consuming $ uncurry M.singleton $ (S.singleton (LockIdent uuid bindings name args), top)
-}
