{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}
module TMCR.Exec where


import Control.Concurrent.STM.Map (Map())
import qualified Control.Concurrent.STM.Map as TM
import Control.Concurrent.STM
import Control.Lens.TH
import Control.Lens

import TMCR.Logic.Descriptor (DescriptorType(..), DescriptorIdent (..), DescriptorName, Relation (..))
import TMCR.Logic.Common (Thingy)
import TMCR.Logic.Logic (LogicNodeName)
import Data.Set (Set)
import TMCR.Shuffler (ShuffleDependency (..), ShuffleDependent, ShuffleProgress (..), updateLocal, Definitions, defaultEval, MonadEval (..), Eval, Update (..), definedLogicNodes, definedDescriptorType, truthyDescriptors, countyDescriptors, UpdateContext, ReadEval (runReadEval))
import TMCR.Logic.Graphs (Bipartite, bipSetEdgesTo, bipGetEdgesFrom)
import TMCR.Logic.Shuffle (ShufflesProgress, Condition (..), getByCondition)
import TMCR.Logic.Algebra (Lattice (..), CompLattice, LogicValues, CountyLattice (..), cast, Join (..))
import Control.Monad
import Data.Foldable (Foldable(..))
import Data.Bool (bool)
import TMCR.Logic.Merge (defLogic)
import Data.Hashable (Hashable)
import Control.Applicative (Alternative(..))
import Data.Maybe (isNothing, catMaybes)
import Control.Monad.Reader (ReaderT(..), MonadReader, MonadTrans (lift))
import Control.Monad.Trans.Class (MonadTrans)
import qualified Data.Set as S
import qualified Data.Map as M
import Control.Exception (bracket, finally)
import Control.Concurrent.Async (replicateConcurrently_)

data TransactionalShuffleProgress t c = TransactionalShuffleProgress {
      _tShuffles :: TransactionalShufflesProgress
    , _tTruthyDescriptors :: Map (DescriptorIdent Truthy, [Thingy]) t
    , _tKnownTruthyDescriptors :: TVar (Set (DescriptorIdent Truthy, [Thingy]))
    , _tCountyDescriptors :: Map (DescriptorIdent County, [Thingy]) c
    , _tKnownCountyDescriptors :: TVar (Set (DescriptorIdent County, [Thingy]))
    , _tLogicNodes :: Map LogicNodeName t
    , _tCachedAccess :: M.Map (DescriptorName, [Thingy]) (Set LogicNodeName)
    , _tCachedDependencies :: TVar (Bipartite ShuffleDependency ShuffleDependent)
    , _tQueue :: TQueue ShuffleDependent
    , _tInQueue :: Map ShuffleDependent ()
    }

type TransactionalShufflesProgress = TVar ShufflesProgress

$(makeLenses 'TransactionalShuffleProgress)

runAsyncs ::  (Eq (v Truthy), Eq (v County), Lattice (v Truthy), Lattice (v County), LogicValues (v Truthy) (v County)) => Int -> Definitions -> (forall m. MonadEval (v Truthy) (v County) m => Eval m v) -> TransactionalShuffleProgress (v Truthy) (v County) -> IO ()
runAsyncs threadCount defs eval progress = do
  v <- newTVarIO 0
  replicateConcurrently_ threadCount $ runAsync v defs eval progress

runAsync :: (Eq (v Truthy), Eq (v County), Lattice (v Truthy), Lattice (v County), LogicValues (v Truthy) (v County)) => TVar Int -> Definitions -> (forall m. MonadEval (v Truthy) (v County) m => Eval m v) -> TransactionalShuffleProgress (v Truthy) (v County) -> IO ()
runAsync counter defs eval progress = do
  x <- atomically $ (do
    w <- readTQueue $ progress ^. tQueue
    modifyTVar' counter (+1)
    p <- getShuffleProgress defs progress
    return $ Just (w, p)) <|> (do
    readTVar counter >>= (check . (==0))
    isEmptyTQueue (progress ^. tQueue) >>= check
    return Nothing)
  case x of
    Nothing -> return ()
    Just (workItem, shuffleProgress) -> do
      finally (step defs eval progress workItem shuffleProgress) (atomically $ modifyTVar' counter $ (+ (-1)))
      runAsync counter defs eval progress


getShuffleProgress :: Definitions -> TransactionalShuffleProgress t c -> STM (ShuffleProgress t c)
getShuffleProgress defs TransactionalShuffleProgress{..} = do
  _shuffles <- readTVar _tShuffles
  knowTruthyDescriptors <- readTVar $ _tKnownTruthyDescriptors
  _truthyDescriptors <- fmap (M.fromList . catMaybes) $ forM (toList knowTruthyDescriptors) $ \key -> do
    v <- TM.lookup key _tTruthyDescriptors
    return $ fmap ((,) key) v
  knowCountyDescriptors <- readTVar $ _tKnownCountyDescriptors
  _countyDescriptors <- fmap (M.fromList . catMaybes) $ forM (toList knowCountyDescriptors) $ \key -> do
    v <- TM.lookup key _tCountyDescriptors
    return $ fmap ((,) key) v
  let _cachedAccess = _tCachedAccess
  _cachedDependencies <- readTVar _tCachedDependencies
  let allLogicNodes = defs ^.. definedLogicNodes . to M.toList . traverse . _1
  _logicNodes <- fmap (M.fromList . catMaybes) $ forM (toList allLogicNodes) $ \key -> do
    v <- TM.lookup key _tLogicNodes
    return $ fmap ((,) key) v
  return ShuffleProgress{..}

step :: (Eq (v Truthy), Eq (v County), Lattice (v Truthy), Lattice (v County), LogicValues (v Truthy) (v County)) => Definitions -> (forall m. MonadEval (v Truthy) (v County) m => Eval m v) -> TransactionalShuffleProgress (v Truthy) (v County) -> ShuffleDependent -> ShuffleProgress (v Truthy) (v County) -> IO ()
step defs eval progress workItem shuffleProgress = do
  let (updates, reqs) = updateLocal defs eval workItem shuffleProgress
  forM_ updates $ \case
      UpdateTruthyDescriptor (name, args) access -> addKnownTruthyDescriptor progress (TruthyDescriptorIdent name, args)
      UpdateCountyDescriptor (name, args) access -> addKnownCountyDescriptor progress (CountyDescriptorIdent name, args)
  atomically $ do
    changes <- fmap concat $ forM updates $ \case
      UpdateDependency dependencies dependent -> setDependencies progress dependencies dependent >> return []
      UpdateLogicNode name access -> setLogicNodeAccess defs progress name access
      UpdateTruthyDescriptor (name, args) access -> setTruthyDescriptor progress (TruthyDescriptorIdent name, args) access
      UpdateCountyDescriptor (name, args) access -> setCountyDescriptor progress (CountyDescriptorIdent name, args) access
    toUpdate <- do
      g <- readTVar $ progress ^. tCachedDependencies
      return $ concatMap (\x -> bipGetEdgesFrom x g) changes
    forM_ toUpdate $ \u -> queueUpdate progress u
    (checkDependenciesUnchanged defs progress shuffleProgress reqs >> TM.delete workItem (progress ^. tInQueue)) <|> writeTQueue (progress ^. tQueue) workItem
    return ()

addKnownTruthyDescriptor :: TransactionalShuffleProgress (v Truthy) (v County) -> (DescriptorIdent Truthy, [Thingy]) -> IO ()
addKnownTruthyDescriptor progress key = atomically $
  modifyTVar (progress ^. tKnownTruthyDescriptors) $ \s -> if S.member key s then s else S.insert key s
addKnownCountyDescriptor :: TransactionalShuffleProgress (v Truthy) (v County) -> (DescriptorIdent County, [Thingy]) -> IO ()
addKnownCountyDescriptor progress key = atomically $
  modifyTVar (progress ^. tKnownCountyDescriptors) $ \s -> if S.member key s then s else S.insert key s

setTruthyDescriptor :: (Eq (v Truthy)) => TransactionalShuffleProgress (v Truthy) (v County) -> (DescriptorIdent Truthy, [Thingy]) -> v Truthy -> STM [ShuffleDependency]
setTruthyDescriptor progress key@(TruthyDescriptorIdent name, args) access = do
  fmap (bool [] [DescriptorDependency (name, args)]) $ replace' key access $ progress ^. tTruthyDescriptors
setCountyDescriptor :: (Eq (v County)) => TransactionalShuffleProgress (v Truthy) (v County) -> (DescriptorIdent County, [Thingy]) -> v County -> STM [ShuffleDependency]
setCountyDescriptor progress key@(CountyDescriptorIdent name, args) access = do
  fmap (bool [] [DescriptorDependency (name, args)]) $ replace' key access $ progress ^. tCountyDescriptors

checkDependenciesUnchanged :: (Eq (v Truthy), Eq (v County), LogicValues (v Truthy) (v County)) => Definitions -> TransactionalShuffleProgress (v Truthy) (v County) -> ShuffleProgress (v Truthy) (v County) -> Set ShuffleDependency -> STM ()
checkDependenciesUnchanged defs progress oldProgress reqs = forM_ reqs $ \req -> checkDependencyUnchanged defs progress oldProgress req

checkDependencyUnchanged :: (Eq (v Truthy), Eq (v County), LogicValues (v Truthy) (v County)) => Definitions -> TransactionalShuffleProgress (v Truthy) (v County) -> ShuffleProgress (v Truthy) (v County) -> ShuffleDependency -> STM ()
checkDependencyUnchanged defs progress oldProgress (DescriptorDependency (name, args)) = case
  defs ^? definedDescriptorType name of
    Nothing -> return ()
    Just Truthy -> do
      let key = (TruthyDescriptorIdent name, args)
      v <- TM.lookup key (progress ^. tTruthyDescriptors)
      let v' = oldProgress ^. truthyDescriptors . at key
      check $ v == v'
    Just County -> do
      let key = (CountyDescriptorIdent name, args)
      v <- TM.lookup key (progress ^. tCountyDescriptors)
      let v' = oldProgress ^. countyDescriptors . at key
      check $ v == v'
checkDependencyUnchanged defs progress oldProgress (ShuffleDependency rel x) = do
  old <- runReaderT (runReadEval (askShuffle rel x)) (defs, oldProgress)
  new <- runReaderT (runTReadEval (askShuffle rel x)) progress
  check $ old == new
checkDependencyUnchanged defs progress oldProgress (AccessDependency Truthy (name, args)) = do
  old <- runReaderT (runReadEval (askAccessTruthy name args)) (defs, oldProgress)
  new <- runReaderT (runTReadEval (askAccessTruthy name args)) progress
  check $ old == new
checkDependencyUnchanged defs progress oldProgress (AccessDependency County (name, args)) = do
  old <- runReaderT (runReadEval (askAccessCounty name args)) (defs, oldProgress)
  new <- runReaderT (runTReadEval (askAccessCounty name args)) progress
  check $ old == new
checkDependencyUnchanged defs progress oldProgress (LogicNodeDependency name) = do
  old <- runReaderT (runReadEval (askLogicNodeAccess name)) (defs, oldProgress)
  new <- runReaderT (runTReadEval (askLogicNodeAccess name)) progress
  check $ old == new

newtype TReadEval v m a = TReadEval { runTReadEval :: ReaderT (TransactionalShuffleProgress (v Truthy) (v County)) m a } deriving newtype (Functor, Applicative, Monad, MonadReader (TransactionalShuffleProgress (v Truthy) (v County)), MonadTrans)

instance (LogicValues (v Truthy) (v County)) => MonadEval (v Truthy) (v County) (TReadEval v STM) where
  askTruthyDescriptor name params = do
    m <- view tTruthyDescriptors
    v <- TReadEval $ ReaderT $ const $ TM.lookup (name, params) m
    case v of
      Just v' -> return v'
      Nothing -> return bottom
  askCountyDescriptor name params = do
    m <- view tCountyDescriptors
    v <- lift $ TM.lookup (name, params) m
    case v of
      Just v' -> return v'
      Nothing -> return bottom
  askAccessTruthy name params = do
    n <- view $ tCachedAccess . at (name, params)
    case n of
        Nothing -> return bottom
        Just (toList -> n) -> getJoin . foldMap Join <$> traverse askLogicNodeAccess n
  askAccessCounty name params = do
    n <- view $ tCachedAccess . at (name, params)
    case n of
      Nothing -> return bottom
      Just (toList -> n) -> foldr (\x a -> addCounty a $ cast x) bottom <$> traverse askLogicNodeAccess n
  askLogicNodeAccess name = do
    m <- view $ tLogicNodes
    n <- lift $ TM.lookup name m
    case n of
      Nothing -> return bottom
      Just x -> return x
  askShuffle rel x = do
        let (name, condition) = case rel of
                Forward name -> (name, MappedTo x)
                Backward name -> (name, MappedFrom x)
        v <- view tShuffles
        x <- lift $ readTVar v
        return $ getByCondition x name condition


queueUpdate :: TransactionalShuffleProgress (v Truthy) (v County) -> ShuffleDependent -> STM ()
queueUpdate progress v = (<|> return ()) $ do
  v' <- replace v () $ progress ^. tInQueue
  check $ isNothing v'
  writeTQueue (progress ^. tQueue) v

setLogicNodeAccess :: (Eq (v Truthy)) => Definitions -> TransactionalShuffleProgress (v Truthy) (v County) -> LogicNodeName -> v Truthy -> STM [ShuffleDependency]
setLogicNodeAccess defs progress name access = bool [] (defs ^.. definedLogicNodes . at name . _Just . traverse . to (\name -> [AccessDependency Truthy name, AccessDependency County name]) . traverse) <$> replace' name access (progress ^. tLogicNodes)

setDependencies :: TransactionalShuffleProgress (v Truthy) (v County) -> Set ShuffleDependency -> ShuffleDependent -> STM ()
setDependencies progress dependencies dependent = modifyTVar (progress ^. tCachedDependencies) $ bipSetEdgesTo dependent $ toList dependencies


replace :: (Hashable k) => k -> v -> Map k v -> STM (Maybe v)
replace key val m = do
  val' <- TM.lookup key m
  TM.insert key val m
  return val'

replace' :: (Hashable k, Eq v) => k -> v -> Map k v -> STM Bool
replace' key val = fmap (== Just val) . replace key val