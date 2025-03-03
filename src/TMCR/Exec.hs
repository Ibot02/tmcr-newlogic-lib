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
{-# LANGUAGE BangPatterns #-}
module TMCR.Exec where


import qualified StmContainers.Set as TS
import Control.Concurrent.STM.Map (Map())
import qualified Control.Concurrent.STM.Map as TM
import Control.Concurrent.STM
import Control.Lens.TH
import Control.Lens

import TMCR.Logic.Descriptor (DescriptorType(..), DescriptorIdent (..), DescriptorName, Relation (..), SDescriptorType(..), relationName)
import TMCR.Logic.Common (Thingy)
import TMCR.Logic.Logic (LogicNodeName)
import Data.Set (Set)
import TMCR.Shuffler (ShuffleDependency (..), ShuffleDependencyWithValue(..), ShuffleDependent(..), ShuffleProgress (..), updateLocal', Definitions, defaultEval, MonadEval (..), Eval, Update (..), definedLogicNodes, definedDescriptorType, truthyDescriptors, countyDescriptors, UpdateContext, ReadEval (runReadEval), forgetValue, UpdateT(..), getDefinitions, initialShufflesProgress, computeAccess)
import TMCR.Logic.Graphs (Bipartite, bipSetEdgesTo, bipGetEdgesFrom, taggedGetNodes)
import TMCR.Logic.Shuffle (ShufflesProgress(..), Condition (..), getByCondition'', RandomSeed(), ShuffleKey(..), ShuffleStepIdent, ShuffleValue'', ShuffleName, MonadEvalShuffle(..), stepShuffle', shuffleKeyName)
import TMCR.Logic.Algebra (Lattice (..), CompLattice, LogicValues, CountyLattice (..), cast, Join (..))
import Control.Monad
import Data.Foldable (Foldable(..))
import Data.Bool (bool)
import TMCR.Logic.Merge (GameDef(), defLogic)
import Data.Hashable (Hashable)
import Control.Applicative (Alternative(..))
import Data.Maybe (isNothing, catMaybes)
import Control.Monad.Reader (ReaderT(..), MonadReader, MonadTrans (lift), mapReaderT)
import Control.Monad.Trans.Class (MonadTrans)
import qualified Data.Set as S
import qualified Data.Map as M
import Control.Exception (bracket, finally)
import Control.Concurrent.Async (replicateConcurrently_)
import Control.Monad.Trans.Writer (WriterT, execWriterT)

import qualified DeferredFolds.UnfoldlM as DF

data TransactionalShuffleProgress t c = TransactionalShuffleProgress {
      _tShuffles :: TransactionalShufflesProgress
    , _tTruthyDescriptors :: Map (DescriptorIdent Truthy, [Thingy]) t
    , _tCountyDescriptors :: Map (DescriptorIdent County, [Thingy]) c
    , _tLogicNodes :: Map LogicNodeName t
    , _tCachedAccess :: M.Map (DescriptorName, [Thingy]) (Set LogicNodeName)
    , _tCachedDependencies :: TVar (Bipartite ShuffleDependency ShuffleDependent)
    , _tQueue :: TQueue ShuffleDependent
    , _tInQueue :: Map ShuffleDependent ()
    , _tDefinitions :: Definitions
    , _tShufflesToForce :: TS.Set ShuffleName
    , _tChangedDepsAfterShuffleForce :: TS.Set (Relation, Thingy)
    , _tShuffleQueue :: TQueue ShuffleStepIdent
    , _tInShuffleQueue :: Map ShuffleStepIdent ()
    }

data TransactionalShufflesProgress = TransactionalShufflesProgress {
    _tCurrentLatest :: Map ShuffleKey Int
  , _tCurrent :: Map ShuffleStepIdent ShuffleValue''
  }

$(makeLenses 'TransactionalShuffleProgress)
$(makeLenses 'TransactionalShufflesProgress)

runAsyncs ::  (Eq (v Truthy), Eq (v County), Lattice (v Truthy), Lattice (v County), LogicValues (v Truthy) (v County)) => Int -> (forall m. MonadEval (v Truthy) (v County) m => Eval m v) -> TransactionalShuffleProgress (v Truthy) (v County) -> IO ()
runAsyncs threadCount eval progress = do
  v <- newTVarIO 0
  replicateConcurrently_ threadCount $ runAsync v eval progress
  initializeShuffleQueue progress
  replicateConcurrently_ threadCount $ runShufflesAsync v progress
  markShufflesDirty progress
  replicateConcurrently_ threadCount $ runAsync v eval progress

runAsyncsLogicOnly ::  (Eq (v Truthy), Eq (v County), Lattice (v Truthy), Lattice (v County), LogicValues (v Truthy) (v County)) => Int -> (forall m. MonadEval (v Truthy) (v County) m => Eval m v) -> TransactionalShuffleProgress (v Truthy) (v County) -> IO ()
runAsyncsLogicOnly threadCount eval progress = do
  v <- newTVarIO 0
  replicateConcurrently_ threadCount $ runAsync v eval progress

runAsyncsShufflesOnly ::  (Eq (v Truthy), Eq (v County), Lattice (v Truthy), Lattice (v County), LogicValues (v Truthy) (v County)) => Int -> (forall m. MonadEval (v Truthy) (v County) m => Eval m v) -> TransactionalShuffleProgress (v Truthy) (v County) -> IO ()
runAsyncsShufflesOnly threadCount eval progress = do
  v <- newTVarIO 0
  replicateConcurrently_ threadCount $ runShufflesAsync v progress

stepsAsyncs :: (Eq (v Truthy), Eq (v County), Lattice (v Truthy), Lattice (v County), LogicValues (v Truthy) (v County)) => Int -> Int -> (forall m. MonadEval (v Truthy) (v County) m => Eval m v) -> TransactionalShuffleProgress (v Truthy) (v County) -> IO Int
stepsAsyncs threadCount stepCount eval progress = do
  v <- newTVarIO 0
  v' <- newTVarIO stepCount
  replicateConcurrently_ threadCount $ stepsAsync v' v eval progress
  remaining' <- atomically $ readTVar v'
  putStrLn $ "done first pass, remaining steps: " <> show remaining'
  when (remaining' > 0) $ initializeShuffleQueue progress
  replicateConcurrently_ threadCount $ stepsShufflesAsync v' v progress
  remaining'' <- atomically $ readTVar v'
  putStrLn $ "done shuffles, remaining steps: " <> show remaining''
  when (remaining'' > 0) $ markShufflesDirty progress
  replicateConcurrently_ threadCount $ stepsAsync v' v eval progress
  fmap (\remaining -> stepCount - remaining) $ atomically $ readTVar v'

runAsync :: (Eq (v Truthy), Eq (v County), Lattice (v Truthy), Lattice (v County), LogicValues (v Truthy) (v County)) => TVar Int -> (forall m. MonadEval (v Truthy) (v County) m => Eval m v) -> TransactionalShuffleProgress (v Truthy) (v County) -> IO ()
runAsync counter = runAsync' 
  (\progress -> (Just <$> takeWorkItem progress counter) <|> stopWhenAllDone progress counter)
  (modifyTVar' counter $ (+ (-1)))

runShufflesAsync counter = runAsync''
  (\progress -> (Just <$> takeWorkItem' (progress ^. tShuffleQueue) counter) <|> stopWhenAllDone' (progress ^. tShuffleQueue) counter)
  (modifyTVar' counter $ (+ (-1)))
  stepShuffleAsync

stepsAsync :: (Eq (v Truthy), Eq (v County), Lattice (v Truthy), Lattice (v County), LogicValues (v Truthy) (v County)) => TVar Int -> TVar Int -> (forall m. MonadEval (v Truthy) (v County) m => Eval m v) -> TransactionalShuffleProgress (v Truthy) (v County) -> IO ()
stepsAsync stepLimit counter = runAsync'
  (\progress -> (Just <$> (countStep stepLimit >> takeWorkItem progress counter)) <|> stopWhenAllDone progress counter <|> noStepsLeft stepLimit)
  (modifyTVar' counter $ (+ (-1)))

stepsShufflesAsync stepLimit counter = runAsync''
  (\progress -> (Just <$> (countStep stepLimit >> takeWorkItem' (progress ^. tShuffleQueue) counter)) <|> stopWhenAllDone' (progress ^. tShuffleQueue) counter <|> noStepsLeft stepLimit)
  (modifyTVar' counter $ (+ (-1)))
  stepShuffleAsync

runAsync' :: (Eq (v Truthy), Eq (v County), Lattice (v Truthy), Lattice (v County), LogicValues (v Truthy) (v County)) => (TransactionalShuffleProgress (v Truthy) (v County) -> STM (Maybe ShuffleDependent)) -> STM () -> (forall m. MonadEval (v Truthy) (v County) m => Eval m v) -> TransactionalShuffleProgress (v Truthy) (v County) -> IO ()
runAsync' getWork afterWork eval = runAsync'' getWork afterWork (step eval)

runAsync'' :: (TransactionalShuffleProgress (v Truthy) (v County) -> STM (Maybe a)) -> STM () -> (TransactionalShuffleProgress (v Truthy) (v County) -> a -> IO ()) -> TransactionalShuffleProgress (v Truthy) (v County) -> IO ()
runAsync'' getWork afterWork doWork progress = do
  x <- atomically $ getWork progress
  case x of
    Nothing -> return ()
    Just workItem -> do
      finally (doWork progress workItem) (atomically afterWork)
      runAsync'' getWork afterWork doWork progress

takeWorkItem progress = takeWorkItem' (progress ^. tQueue)
takeWorkItem' queue counter = do
    w <- readTQueue queue
    modifyTVar' counter (+1)
    return w

stopWhenAllDone progress = stopWhenAllDone' $ progress ^. tQueue
stopWhenAllDone' queue counter = do
    readTVar counter >>= (check . (==0))
    isEmptyTQueue queue >>= check
    return Nothing

countStep :: TVar Int -> STM ()
countStep counter = do
  v <- readTVar counter
  check $ v > 0
  writeTVar counter $ v - 1

noStepsLeft :: TVar Int -> STM (Maybe a)
noStepsLeft counter = readTVar counter >>= (check . (==0)) >> return Nothing

step :: (Eq (v Truthy), Eq (v County), Lattice (v Truthy), Lattice (v County), LogicValues (v Truthy) (v County)) => (forall m. MonadEval (v Truthy) (v County) m => Eval m v) -> TransactionalShuffleProgress (v Truthy) (v County) -> ShuffleDependent -> IO ()
step eval progress workItem = do
  (updates, reqs) <- flip runReaderT progress $ runTReadEval $ execWriterT $ extractUpdate $ updateLocal' eval workItem
  atomically $ do
    changes <- fmap concat $ forM updates $ \case
      UpdateDependency dependencies dependent -> setDependencies progress dependencies dependent >> return []
      UpdateLogicNode name access -> setLogicNodeAccess progress name access
      UpdateTruthyDescriptor (name, args) access -> setTruthyDescriptor progress (TruthyDescriptorIdent name, args) access
      UpdateCountyDescriptor (name, args) access -> setCountyDescriptor progress (CountyDescriptorIdent name, args) access
    markDirty progress changes
    (checkDependenciesUnchanged progress reqs >> TM.delete workItem (progress ^. tInQueue)) <|> writeTQueue (progress ^. tQueue) workItem
    return ()

markDirty :: TransactionalShuffleProgress (v Truthy) (v County) -> [ShuffleDependency] -> STM ()
markDirty progress changes = do
    toUpdate <- do
      g <- readTVar $ progress ^. tCachedDependencies
      return $ concatMap (\x -> bipGetEdgesFrom x g) changes
    forM_ toUpdate $ \u -> queueUpdate progress u

setTruthyDescriptor :: (Eq (v Truthy)) => TransactionalShuffleProgress (v Truthy) (v County) -> (DescriptorIdent Truthy, [Thingy]) -> v Truthy -> STM [ShuffleDependency]
setTruthyDescriptor progress key@(TruthyDescriptorIdent name, args) access = do
  fmap (bool [] [DescriptorDependency (name, args)]) $ replace' key access $ progress ^. tTruthyDescriptors
setCountyDescriptor :: (Eq (v County)) => TransactionalShuffleProgress (v Truthy) (v County) -> (DescriptorIdent County, [Thingy]) -> v County -> STM [ShuffleDependency]
setCountyDescriptor progress key@(CountyDescriptorIdent name, args) access = do
  fmap (bool [] [DescriptorDependency (name, args)]) $ replace' key access $ progress ^. tCountyDescriptors

checkDependenciesUnchanged :: (Eq (v Truthy), Eq (v County), LogicValues (v Truthy) (v County)) => TransactionalShuffleProgress (v Truthy) (v County) -> [ShuffleDependencyWithValue v] -> STM ()
checkDependenciesUnchanged progress reqs = forM_ reqs $ \req -> checkDependencyUnchanged progress req

checkDependencyUnchanged :: (Eq (v Truthy), Eq (v County), LogicValues (v Truthy) (v County)) => TransactionalShuffleProgress (v Truthy) (v County) -> ShuffleDependencyWithValue v -> STM ()
checkDependencyUnchanged progress (DescriptorDependencyWithValue (name@(TruthyDescriptorIdent _), args) old) = do
  new <- runReaderT (runTReadEval (askTruthyDescriptor name args)) progress
  check $ old == new
checkDependencyUnchanged progress (DescriptorDependencyWithValue (name@(CountyDescriptorIdent _), args) old) = do
  new <- runReaderT (runTReadEval (askCountyDescriptor name args)) progress
  check $ old == new
checkDependencyUnchanged progress (ShuffleDependencyWithValue rel x old) = do
  new <- runReaderT (runTReadEval (askShuffle rel x)) progress
  check $ old == new
checkDependencyUnchanged progress (AccessDependencyWithValue STruthy (TruthyDescriptorIdent name, args) old) = do
  new <- runReaderT (runTReadEval (askAccessTruthy name args)) progress
  check $ old == new
checkDependencyUnchanged progress (AccessDependencyWithValue SCounty (CountyDescriptorIdent name, args) old) = do
  new <- runReaderT (runTReadEval (askAccessCounty name args)) progress
  check $ old == new
checkDependencyUnchanged progress (LogicNodeDependencyWithValue name old) = do
  new <- runReaderT (runTReadEval (askLogicNodeAccess name)) progress
  check $ old == new

newtype TReadEval v m a = TReadEval { runTReadEval :: ReaderT (TransactionalShuffleProgress (v Truthy) (v County)) m a } deriving newtype (Functor, Applicative, Monad, MonadReader (TransactionalShuffleProgress (v Truthy) (v County)), MonadTrans)

instance (LogicValues (v Truthy) (v County)) => MonadEval (v Truthy) (v County) (TReadEval v STM) where
  askDefinitions = view tDefinitions
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
        v <- view $ tShuffles . tCurrent
        res <- getByCondition'' (\ident -> lift $ TM.lookup ident v) name condition
        s <- view tShufflesToForce
        lift $ TS.insert (relationName rel) s
        s' <- view tChangedDepsAfterShuffleForce
        lift $ TS.insert (rel, x) s'
        return res

instance (LogicValues (v Truthy) (v County)) => MonadEval (v Truthy) (v County) (TReadEval v IO) where
  askDefinitions = view tDefinitions
  askTruthyDescriptor name params = TReadEval $ mapReaderT atomically $ runTReadEval $ askTruthyDescriptor name params
  askCountyDescriptor name params = TReadEval $ mapReaderT atomically $ runTReadEval $ askCountyDescriptor name params
  askAccessTruthy name params = TReadEval $ mapReaderT atomically $ runTReadEval $ askAccessTruthy name params
  askAccessCounty name params = TReadEval $ mapReaderT atomically $ runTReadEval $ askAccessCounty name params
  askShuffle name params = TReadEval $ mapReaderT atomically $ runTReadEval $ askShuffle name params
  askLogicNodeAccess name = TReadEval $ mapReaderT atomically $ runTReadEval $ askLogicNodeAccess name


queueUpdate :: TransactionalShuffleProgress (v Truthy) (v County) -> ShuffleDependent -> STM ()
queueUpdate progress = queueUpdate' (progress ^. tQueue) (progress ^. tInQueue)
queueUpdate' queue inQueue v = (<|> return ()) $ do
  v' <- replace v () inQueue
  check $ isNothing v'
  writeTQueue queue v

setLogicNodeAccess :: (Eq (v Truthy)) => TransactionalShuffleProgress (v Truthy) (v County) -> LogicNodeName -> v Truthy -> STM [ShuffleDependency]
setLogicNodeAccess progress name access = do
  let defs = progress ^. tDefinitions
  bool [] (defs ^.. definedLogicNodes . at name . _Just . traverse . to (\name -> [AccessDependency Truthy name, AccessDependency County name]) . traverse) <$> replace' name access (progress ^. tLogicNodes)

setDependencies :: (Lattice (v Truthy)) => TransactionalShuffleProgress (v Truthy) (v County) -> [ShuffleDependencyWithValue v] -> ShuffleDependent -> STM ()
setDependencies progress dependencies dependent = do
  modifyTVar (progress ^. tCachedDependencies) $ bipSetEdgesTo dependent $ fmap forgetValue $ dependencies
  forM_ dependencies $ \dep -> (checkNotDefined progress dep >>= traverse (queueUpdate progress) >> return ()) <|> return ()

checkNotDefined :: (Lattice (v Truthy)) => TransactionalShuffleProgress (v Truthy) (v County) -> ShuffleDependencyWithValue v -> STM [ShuffleDependent]
checkNotDefined progress (DescriptorDependencyWithValue k@(TruthyDescriptorIdent name, args) _) =
  TM.lookup k (progress ^. tTruthyDescriptors) >>= (check . isNothing) >> return [DescriptorDependent (name, args)]
checkNotDefined progress (DescriptorDependencyWithValue k@(CountyDescriptorIdent name, args) _) =
  TM.lookup k (progress ^. tCountyDescriptors) >>= (check . isNothing) >> return [DescriptorDependent (name, args)]
checkNotDefined progress (ShuffleDependencyWithValue _ _ _) = empty
checkNotDefined progress (AccessDependencyWithValue _ (getDescriptorName -> name, args) _) = do
  fmap concat $ traverse (checkNotDefined progress . flip LogicNodeDependencyWithValue bottom) $ progress ^.. tCachedAccess . at (name, args) . _Just . to S.toList . traverse
checkNotDefined progress (LogicNodeDependencyWithValue name _) =
  TM.lookup name (progress ^. tLogicNodes) >>= (check . isNothing) >> return [LogicNodeDependent name]

getDescriptorName :: DescriptorIdent t -> DescriptorName
getDescriptorName (TruthyDescriptorIdent name) = name
getDescriptorName (CountyDescriptorIdent name) = name

replace :: (Hashable k) => k -> v -> Map k v -> STM (Maybe v)
replace key val m = do
  val' <- TM.lookup key m
  TM.insert key val m
  return val'

replace' :: (Hashable k, Eq v) => k -> v -> Map k v -> STM Bool
replace' key val = fmap (/= Just val) . replace key val

initialTShuffleProgress :: GameDef -> RandomSeed -> IO (TransactionalShuffleProgress (v Truthy) (v County))
initialTShuffleProgress def seed = do
  _tShuffles <- toTShufflesProgress $ initialShufflesProgress def seed
  _tTruthyDescriptors <- atomically TM.empty
  _tCountyDescriptors <- atomically TM.empty
  _tLogicNodes <- atomically TM.empty
  _tCachedDependencies <- newTVarIO mempty
  _tQueue <- newTQueueIO
  _tInQueue <- atomically TM.empty
  _tShuffleQueue <- newTQueueIO
  _tInShuffleQueue <- atomically TM.empty
  _tShufflesToForce <- atomically TS.new
  _tChangedDepsAfterShuffleForce <- atomically TS.new
  let _tCachedAccess = computeAccess def
  let _tDefinitions = getDefinitions def
  let progress = TransactionalShuffleProgress {..}
  initializeQueue progress
  return progress

initializeQueue progress =
  forM_ (progress ^.. tDefinitions . definedLogicNodes . to M.toList . traverse . _1) $ \node -> atomically $
    queueUpdate progress $ LogicNodeDependent node

toTShufflesProgress :: ShufflesProgress -> IO TransactionalShufflesProgress
toTShufflesProgress (ShufflesProgress x y) = TransactionalShufflesProgress
  <$> (TM.fromList $ fmap (\(a,(_,b)) -> (a,b)) $ M.toList x)
  <*> (TM.fromList $ M.toList y)

instance MonadEvalShuffle (TReadEval v STM) where
  getValue key = TReadEval $ do
    s <- view $ tShuffles . tCurrent
    lift $ TM.lookup key s
  putValue key value = TReadEval $ do
    s <- view $ tShuffles . tCurrent
    lift $ TM.insert key value s
  allocIdent key = TReadEval $ do
    s <- view $ tShuffles . tCurrentLatest
    n <- fmap (maybe 0 id) $ lift $ TM.lookup key s
    let !n' = n + 1
    lift $ TM.insert key n' s
    return $ (key, n)

stepShuffleAsync progress ident = atomically $ flip runReaderT progress $ runTReadEval $ do
  (firstDo, moreWork) <- stepShuffle' ident
  lift $ forM_ firstDo $ queueUpdate' (progress ^. tShuffleQueue) (progress ^. tInShuffleQueue)
  isImportant <- do
    toForce <- view $ tShufflesToForce
    lift $ TS.lookup (shuffleKeyName $ fst ident) toForce
  lift $ if moreWork && isImportant then writeTQueue (progress ^. tShuffleQueue) ident
  else TM.delete ident (progress ^. tInShuffleQueue)

initializeShuffleQueue :: TransactionalShuffleProgress (v Truthy) (v County) -> IO ()
initializeShuffleQueue progress = atomically $ do
  DF.forM_ (TS.unfoldlM $ progress ^. tShufflesToForce) $ queueUpdate' (progress ^. tShuffleQueue) (progress ^. tInShuffleQueue) . (flip (,) 0) . ShuffleKeyMain

markShufflesDirty :: TransactionalShuffleProgress (v Truthy) (v County) -> IO ()
markShufflesDirty progress = atomically $ do
  DF.forM_ (TS.unfoldlM $ progress ^. tChangedDepsAfterShuffleForce) $ markDirty progress . (:[]) . uncurry ShuffleDependency
