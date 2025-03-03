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
import Data.Maybe (catMaybes)
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

data Eval m (v :: DescriptorType -> Type) = Eval {
      evalConstant :: forall t. Literal t -> m (v t)
    --, evalProduct :: v County -> v County -> m (v County)
    , evalScale :: v County -> Nteger -> m (v County)
    , evalSum :: [v County] -> m (v County)
    , evalAtLeast :: v County -> Nteger -> m (v Truthy)
    , evalExists :: Relation -> Thingy -> (Thingy -> m (v Truthy)) -> m (v Truthy)
    , evalCount :: Relation -> Thingy -> (Thingy -> m (v Truthy)) -> m (v County)
    , evalMin :: forall t. SDescriptorType t -> [v t] -> m (v t)
    , evalMax :: forall t. SDescriptorType t -> [v t] -> m (v t)
    , evalCast :: v Truthy -> m (v County)
    , evalPriorState :: [StateBody Thingy] -> m (v Truthy)
    , evalPostState :: [StateBody Thingy] -> m (v Truthy)
    , evalSequence :: forall t. SDescriptorType t -> v t -> v t -> m (v t)
    , evalDeferConsumer :: forall t. (Int, Map VarName Thingy, DescriptorIdent t, [Thingy]) -> m (v t)
    , evalValueAtState :: forall t. SDescriptorType t -> [StateBody Thingy] -> v t -> m (v t)
    }

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


updateLocal :: (Eq (v Truthy), Eq (v County), Lattice (v Truthy), Lattice (v County), LogicValues (v Truthy) (v County)) => Definitions -> (forall m. MonadEval (v Truthy) (v County) m => Eval m v) -> ShuffleDependent -> ShuffleProgress (v Truthy) (v County) -> ([Update v], [ShuffleDependencyWithValue v])
updateLocal defs eval object progress = runUpdate defs progress $ updateLocal' eval object

updateLocal' :: (MonadEval (v Truthy) (v County) m, LogicValues (v Truthy) (v County), Eq (v Truthy), Eq (v County)) => (forall m. MonadEval (v Truthy) (v County) m => Eval m v) -> ShuffleDependent -> UpdateT v m ()
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

-- runUpdate :: (Eq (v Truthy), Eq (v County)) => Definitions -> ShuffleProgress (v Truthy) (v County) -> UpdateT v Identity () -> (ShuffleProgress (v Truthy) (v County), [ShuffleDependent])
-- runUpdate defs progress update = _1 %~ fst $ runIdentity $ execRWST (extractUpdate update) defs (progress, [])

--viewDefinitions :: (MonadEval (v Truthy) (v County) m) => Getter Definitions a -> m a
viewDefinitions g = fmap (^. g) askDefinitions

updateLogicNode :: (MonadEval (v Truthy) (v County) m, Eq (v Truthy), LogicValues (v Truthy) (v County)) => (forall m. MonadEval (v Truthy) (v County) m => Eval m v) -> LogicNodeName -> UpdateT v m ()
updateLogicNode eval name = do
        (t, (_, deps)) <- listen $ do
          incomingEdges <- viewDefinitions $ definedEdgesTo (Just name)
          ts <- forM incomingEdges $ \(source, edge) -> do
            t <- case source of
                Just source -> askLogicNodeAccess source
                Nothing -> evalConstant eval $ TruthyLiteral OolTrue
            t' <- fmap (getJoin . foldMap Join) $ forM (S.toList $ getDisjunctions $ getJoin edge) $ \clause ->
                    fmap (getMeet . foldMap Meet) $ forM (S.toList clause) $ \(descName, args) ->
                        askTruthyDescriptor (TruthyDescriptorIdent descName) args
            evalSequence eval STruthy t t'
          return $ getJoin $ foldMap Join ts
        updateLogicNode' name deps t

updateLogicNode' :: (Monad m, Eq (v Truthy)) => LogicNodeName -> [ShuffleDependencyWithValue v] -> v Truthy -> UpdateT v m ()
updateLogicNode' name deps value = tell $ tellUpdate $ [UpdateLogicNode name value, UpdateDependency deps (LogicNodeDependent name)]

updateCountyDescriptor :: (MonadEval (v Truthy) (v County) m, Eq (v County), LogicValues (v Truthy) (v County)) => (forall m. MonadEval (v Truthy) (v County) m => Eval m v) -> (DescriptorName, [Thingy]) -> UpdateT v m ()
updateCountyDescriptor eval (name, params) = do
    (t, (_, deps)) <- listen $ do
                ds <- viewDefinitions $ definedDescriptor (CountyDescriptorIdent name)
                ts <- forM ds $ \d ->
                    evalDescriptor eval SCounty name d params
                return $  getJoin $ foldMap Join ts
    updateCountyDescriptor' (name, params) t deps

updateCountyDescriptor' :: (Monad m, Eq (v County)) => (DescriptorName, [Thingy]) -> v County -> [ShuffleDependencyWithValue v] -> UpdateT v m ()
updateCountyDescriptor' desc value deps = tell $ tellUpdate [UpdateCountyDescriptor desc value, UpdateDependency deps $ DescriptorDependent desc]

updateTruthyDescriptor :: (MonadEval (v Truthy) (v County) m, Eq (v Truthy), LogicValues (v Truthy) (v County)) => (forall m. MonadEval (v Truthy) (v County) m => Eval m v) -> (DescriptorName, [Thingy]) -> UpdateT v m ()
updateTruthyDescriptor eval (name, params) = do
    (t, (_, deps)) <- listen $ do
                ds <- viewDefinitions $ definedDescriptor (TruthyDescriptorIdent name)
                ts <- forM ds $ \d ->
                    evalDescriptor eval STruthy name d params
                return $ getJoin $ foldMap Join ts
    updateTruthyDescriptor' (name, params) t deps

updateTruthyDescriptor' :: (Monad m, Eq (v Truthy)) => (DescriptorName, [Thingy]) -> v Truthy -> [ShuffleDependencyWithValue v] -> UpdateT v m ()
updateTruthyDescriptor' desc value deps = tell $ tellUpdate [UpdateTruthyDescriptor desc value, UpdateDependency deps $ DescriptorDependent desc]

updateShuffle :: ShuffleStepIdent -> UpdateT v m ()
updateShuffle = undefined

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

askDescriptor :: (MonadEval (v Truthy) (v County) m) => SDescriptorType t -> DescriptorName -> [Thingy] -> m (v t)
askDescriptor STruthy = askTruthyDescriptor . TruthyDescriptorIdent
askDescriptor SCounty = askCountyDescriptor . CountyDescriptorIdent

deriving via Lift (ReaderT r) m instance (MonadEval t c m) => MonadEval t c (ReaderT r m)
deriving via Lift (WriterT w) m instance (Monoid w, MonadEval t c m) => MonadEval t c (WriterT w m)

askAccess :: forall (v :: DescriptorType -> Type) t m. (MonadEval (v Truthy) (v County) m) => SDescriptorType t -> DescriptorName -> [Thingy] -> m (v t)
askAccess STruthy = askAccessTruthy
askAccess SCounty = askAccessCounty

evalDescriptor :: forall m (v :: DescriptorType -> Type) t. (MonadEval (v Truthy) (v County) m) => Eval (ReaderT (Map VarName Thingy) m) v -> SDescriptorType t -> DescriptorName -> Descriptor t -> [Thingy] -> m (v t)
evalDescriptor eval dt name (Descriptor paramSpec rule) params = maybe (runReaderT (evalConstant eval (bottomLiteral dt)) mempty) (runReaderT (go dt rule)) (tryBinds paramSpec params) where
    bottomLiteral :: forall t. SDescriptorType t -> Literal t
    bottomLiteral STruthy = TruthyLiteral OolFalse
    bottomLiteral SCounty = CountyLiteral (Finite 0)
    tryBinds xs ys = tryBind xs ys mempty
    tryBind :: [Value] -> [PossiblyScopedName] -> Map VarName PossiblyScopedName -> Maybe (Map VarName PossiblyScopedName)
    tryBind [] [] m = Just m
    tryBind (Variable name : xs) (value : ys) m = case M.lookup name m of
        Nothing -> tryBind xs ys (M.insert name value m)
        Just value' | value == value' -> tryBind xs ys m
                    | otherwise -> Nothing
    tryBind (ConstantValue x : xs) (value : ys) m | x == value = tryBind xs ys m
                                                  | otherwise = Nothing
    tryBind _ _ _ = Nothing
    goT :: DescriptorRule Truthy -> ReaderT (Map VarName Thingy) m (v Truthy)
    goT = go STruthy
    goC :: DescriptorRule County -> ReaderT (Map VarName Thingy) m (v County)
    goC = go SCounty
    go :: forall t. SDescriptorType t -> DescriptorRule t -> ReaderT (Map VarName Thingy) m (v t)
    go _ (IsEqual val val') = do
        x <- valToThingy val
        y <- valToThingy val'
        if x == y then evalConstant eval (TruthyLiteral OolTrue) else evalConstant eval (TruthyLiteral OolFalse)
    go t (CallDescriptor t' name values) = do
        params <- traverse valToThingy values
        askDescriptor t name params
    go t (CanAccess t' name values sb) = do
        params <- traverse valToThingy values
        sb' <- traverse (\case
                IsSet v -> IsSet <$> valToThingy v
                IsNotSet v -> IsNotSet <$> valToThingy v) sb
        v <- askAccess t' name params
        evalValueAtState eval t sb' v
    go _ (Constant x) = evalConstant eval x
    -- go _ (Product a b) = do
    --     x <- goC a
    --     y <- goC b
    --     evalProduct eval x y
    go _ (Scale x y) = do
        x' <- goC x
        evalScale eval x' y
    go _ (Sum as) = traverse goC as >>= evalSum eval
    go _ (AtLeast a n) = do
        x <- goC a
        evalAtLeast eval x n
    go _ (Exist var rel val rule) = do
        val <- valToThingy val
        evalExists eval rel val $ \val' -> local (M.insert var val') $ goT rule
    go _ (Count var rel val rule) = do
        val <- valToThingy val
        evalCount eval rel val $ \val' -> local (M.insert var val') $ goT rule
    go t (Min rules) = traverse (go t) rules >>= evalMin eval t
    go t (Max rules) = traverse (go t) rules >>= evalMax eval t
    go _ (Cast rule) = goT rule >>= evalCast eval
    go _ (PriorState sb) = do
        sb' <- traverse (\case
                IsSet v -> IsSet <$> valToThingy v
                IsNotSet v -> IsNotSet <$> valToThingy v) sb
        evalPriorState eval sb'
    go _ (PostState sb) = do
        sb' <- traverse (\case
                IsSet v -> IsSet <$> valToThingy v
                IsNotSet v -> IsNotSet <$> valToThingy v) sb
        evalPostState eval sb'
    go _ (Consume uuid name' args' rule') = do
        args <- traverse valToThingy args'
        evalDeferConsumer eval (uuid, undefined, undefined, undefined)
    valToThingy (Variable var) = asks (^?! ix var)
    valToThingy (ConstantValue t) = return t

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

{-

-}

instance (EqLattice t) => EqLattice (Stateful t) where
    (Stateful a) `equiv` (Stateful b) = case M.mergeA (M.traverseMissing $ \_ _ -> Nothing) (M.traverseMissing $ \_ _ -> Nothing) (M.zipWithAMatched $ \_ a b -> if equiv a b then Just () else Nothing) a b of
        Just _ -> True
        Nothing -> False


instance (CompLattice t) => CompLattice (Stateful t) where
    composeL (Stateful a) (Stateful b) = Stateful $ M.fromListWith join $ do --todo: invariant
        ((StateBodies preT preF preB, StateBodies postT postF postB),v) <- M.toList a
        ((StateBodies preT' preF' preB', StateBodies postT' postF' postB'), v') <- M.toList b
        guard $ null $ S.intersection preT' postF
        guard $ null $ S.intersection preF' postT
        guard $ not preB' || S.isSubsetOf postF preF'
        let posts = StateBodies postsT postsF postsB
            postsT = postT' <> (postT S.\\ postF')
            postsF = postF' <> (postF S.\\ postT')
            postsB = (postB && not preB') || postB'
            pres = StateBodies presT presF presB
            presT = preT <> (preT' S.\\ postT)
            presF = preF <> (preF' S.\\ postF)
            presB = preB || (preB' && not postB)
        guard $ null $ S.intersection presT presF
        pure ((pres, posts), composeL v v')

instance (CompLattice t) => StatefulLattice [StateBody Thingy] (Stateful t) where
    -- preState sb = Stateful $ M.fromList $
    --     let pre@(StateBodies preT preF False) = sbFromList sb in
    --     [((pre, StateBodies mempty (S.fromList postF) False), top) | postF <- subsequences (S.toList preT)]
    preState sb = getMeet $ foldMap (\case
        IsSet s -> let opts = [(S.singleton s, mempty), (mempty, S.singleton s)] in
            Meet $ Stateful $ M.fromList $ [((StateBodies (S.singleton s) mempty False, StateBodies a b False), top) | (a,b) <- opts]
        IsNotSet s -> Meet $ Stateful $ M.fromList $ [((StateBodies mempty (S.singleton s) False, StateBodies mempty (S.singleton s) False), top)]
        ) sb
    -- postState sb = Stateful $ M.fromList $ 
    --     let (StateBodies postT postF False) = sbFromList sb in
    --     [((mempty, StateBodies (S.fromList postT') postF False), top) | postT' <- subsequences (S.toList postT)]
    postState sb = getMeet $ foldMap (\case
        IsSet s -> let opts = [(S.singleton s, mempty), (mempty, S.singleton s)] in
            Meet $ Stateful $ M.fromList $ [((StateBodies a b False, StateBodies c d False), top) | (a,b) <- opts, (c,d) <- opts]
        IsNotSet s -> let opts = [(S.singleton s, mempty), (mempty, S.singleton s)] in
            Meet $ Stateful $ M.fromList $ [((StateBodies a b False, StateBodies mempty (S.singleton s) False), top) | (a,b) <- opts]
        ) sb
    atState sb (Stateful x) = Stateful $
        M.singleton mempty $
        getJoin $
        foldMap Join $
        -- foldMap (Join . snd) $
        -- foldMap (Join . snd) $
        -- foldMap (Join . snd) $
        -- foldMap (Join . snd) $
        -- M.toList $
        -- M.toList $
        -- M.toList $
        -- M.toList $
        M.filterWithKey (
            \(StateBodies preP _ preB,StateBodies postP postF postB) _ ->
                null preP && not preB && --no pre-state requirements, we assume we're coming from no state --no pre-state requirements, we assume we're coming from no state
                (  (not postB && all (\case IsSet s -> s `elem` postP; IsNotSet s -> s `notElem` postP) sb)
                || (postB && all (\case IsSet s -> s `notElem` postF; IsNotSet s -> s `elem` postF) sb)
            ))
        x

instance (CompLattice t, Ord a) => CompLattice (Consuming a t) where
    composeL (Consuming x) (Consuming y) = Consuming $ M.fromList $ [(S.union k1 k2, v1 `composeL` v2) | (k1, v1) <- M.toList x, (k2, v2) <- M.toList y]

instance (StatefulLattice s t, Ord a) => StatefulLattice s (Consuming a t) where
    preState s = liftConsuming $ preState s
    postState s = liftConsuming $ postState s
    atState s (Consuming xs) = Consuming $ fmap (atState s) xs

defaultEval :: forall m t t'. (CompLattice t', Ord t', t ~ (Consuming LockIdent (Stateful (OolAble t'))), MonadEval (LogicValue t Truthy) (LogicValue t County) m) => Eval m (LogicValue t)
defaultEval = Eval {..} where
    evalConstant :: forall t'. Literal t' -> m (LogicValue t t')
    evalConstant (TruthyLiteral OolTrue) = return $ LogicTruthyValue $ liftConsuming $ liftStateful top
    evalConstant (TruthyLiteral OolOol) = return $ LogicTruthyValue $ liftConsuming $ liftStateful outOfLogic
    evalConstant (TruthyLiteral OolFalse) = return $ LogicTruthyValue $ liftConsuming $ liftStateful bottom
    evalConstant (CountyLiteral n) = do
        t <- evalConstant (TruthyLiteral OolTrue)
        return $ cast t `scaleC` n
    -- evalConstant (CountyLiteral Infinite) = return $ top
    -- evalConstant (CountyLiteral (Finite n)) = return $ LogicCountyValue $ fromNumber n
    -- evalProduct :: LogicValue t County -> LogicValue t County -> m (LogicValue t County)
    -- evalProduct x y = return $ multiplyCounty x y
    evalScale :: LogicValue t County -> Nteger -> m (LogicValue t County)
    evalScale x n = return $ x `scaleC` n
    evalSum :: [LogicValue t County] -> m (LogicValue t County)
    evalSum = return . foldr addCounty bottom
    evalAtLeast :: LogicValue t County -> Nteger -> m (LogicValue t Truthy)
    evalAtLeast x n = return $ atLeast n x
    evalExists :: Relation -> Thingy -> (Thingy -> m (LogicValue t Truthy)) -> m (LogicValue t Truthy)
    evalExists rel t p = do
        xs <- askShuffle rel t
        ys <- traverse (\(a,n) -> if n > Finite 0 then p a else return bottom) xs
        evalMax STruthy ys
    evalCount :: Relation -> Thingy -> (Thingy -> m (LogicValue t Truthy)) -> m (LogicValue t County)
    evalCount rel t p = do
        xs <- askShuffle rel t
        ys <- forM xs $ \(a,n) -> do
--            n' <- evalConstant @'County (CountyLiteral n)
            a' <- p a
            return $ scaleC (cast a') n
        evalSum ys
    evalMin :: forall t'. SDescriptorType t' -> [LogicValue t t'] -> m (LogicValue t t')
    evalMin STruthy = return . foldr meet top
    evalMin SCounty = return . foldr meet top
    evalMax :: forall t'. SDescriptorType t' -> [LogicValue t t'] -> m (LogicValue t t')
    evalMax STruthy = return . foldr join bottom
    evalMax SCounty = return . foldr join bottom
    evalCast :: LogicValue t Truthy -> m (LogicValue t County)
    evalCast = return . cast
    evalPriorState :: [StateBody Thingy] -> m (LogicValue t Truthy)
    evalPriorState sb = return $ preState sb
    evalPostState :: [StateBody Thingy] -> m (LogicValue t Truthy)
    evalPostState sb = return $ postState sb
    evalSequence :: forall t'. SDescriptorType t' -> LogicValue t t' -> LogicValue t t' -> m (LogicValue t t')
    evalSequence STruthy a b = return (a `composeL` b)
    evalSequence SCounty a b = return (a `composeL` b)
    evalDeferConsumer :: forall t'. (Int, Map VarName Thingy, DescriptorIdent t', [Thingy]) -> m (LogicValue t t')
    evalDeferConsumer (uuid, bindings, TruthyDescriptorIdent name, args) = return $ LogicTruthyValue $ Consuming $ uncurry M.singleton $ (S.singleton (LockIdent uuid bindings name args), top)
    evalDeferConsumer (uuid, bindings, CountyDescriptorIdent name, args) = return $ LogicCountyValue $ liftCount $ Consuming $ uncurry M.singleton $ (S.singleton (LockIdent uuid bindings name args), top)
    evalValueAtState :: forall t'. SDescriptorType t' -> [StateBody Thingy] -> LogicValue t t' -> m (LogicValue t t')
    evalValueAtState STruthy sb x = return $ atState sb x
    evalValueAtState SCounty sb x = return $ atState sb x

