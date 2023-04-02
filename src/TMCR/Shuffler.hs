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
module TMCR.Shuffler where

import TMCR.Logic.Descriptor
import TMCR.Logic.Shuffle
import TMCR.Logic.Common
import TMCR.Logic.Logic (ScopedName)
import TMCR.Module
import TMCR.Logic.Graphs

import Data.Map (Map)
import qualified Data.Map as M

import Control.Monad

import Control.Lens
import Control.Lens.TH
import Control.Monad.Trans
import Control.Monad.RWS (RWST(..), MonadState(..), MonadWriter(..), execRWST, gets)
import Control.Monad.Reader (MonadReader(..), ReaderT(..), asks, local)

type Thingy = PossiblyScopedName
type LogicNodeName = ScopedName

--descriptors, with all parameters specified, with reachability (and maybe sphere) values (truthy descriptors) or reachable counts (county descriptors)
--shuffles, hierarchical multi relations
--logic nodes, with reachability values


type ShuffleValue = () --todo

data ShuffleProgress t c = ShuffleProgress {
      _shuffles :: Map ShuffleName ShuffleValue
    , _truthyDescriptors :: Map (DescriptorIdent Truthy, [Thingy]) t
    , _countyDescriptors :: Map (DescriptorIdent County, [Thingy]) c
    , _logicNodes :: Map LogicNodeName t
    , _cachedAccess :: Map (DescriptorName, [Thingy]) LogicNodeName
    , _cachedDependencies :: Bipartite ShuffleDependency ShuffleDependend
    }

data ShuffleDependend =
      DescriptorDependend (DescriptorName, [Thingy])
    | LogicNodeDependent LogicNodeName
    deriving (Eq, Ord, Show)

data ShuffleDependency =
      DescriptorDependency (DescriptorName, [Thingy])
    | ShuffleDependency ShuffleName
    | AccessDependency (DescriptorName, [Thingy])
    deriving (Eq, Ord, Show)

$(makeLenses ''ShuffleProgress)

class (Monad m) => MonadEval t c m | m -> t c where
    askTruthyDescriptor :: DescriptorIdent Truthy -> [Thingy] -> m (Maybe t)
    askCountyDescriptor :: DescriptorIdent County -> [Thingy] -> m (Maybe c)
    askAccess :: DescriptorName -> [Thingy] -> m (Maybe t)
    askLogicNodeAccess :: LogicNodeName -> m (Maybe t)
    askShuffle :: ShuffleName -> Thingy -> m [(Thingy, Nteger)]

{-
data Eval t c = Eval {
      evalTruthyDescriptor :: forall m. (MonadEval t c m) => Descriptor Truthy -> m t
    , evalCountyDescriptor :: forall m. (MonadEval t c m) => Descriptor County -> m c
    , evalLogicNodesIncomingEdges :: forall m. (MonadEval t c m) => LogicNodeName -> m t
    }

-}

data Eval m (v :: DescriptorType -> *) = Eval {
      evalConstant :: forall t. Literal t -> m (v t)
    , evalProduct :: v County -> v County -> m (v County)
    , evalSum :: [v County] -> m (v County)
    , evalAtLeast :: v County -> Nteger -> m (v Truthy)
    , evalExists :: Relation -> Thingy -> (Thingy -> m (v Truthy)) -> m (v Truthy)
    , evalCount :: Relation -> Thingy -> (Thingy -> m (v Truthy)) -> m (v County)
    , evalMin :: forall t. SDescriptorType t -> [v t] -> m (v t)
    , evalMax :: forall t. SDescriptorType t -> [v t] -> m (v t)
    , evalCast :: v Truthy -> m (v County)
    , evalPriorState :: [StateBody] -> m (v Truthy)
    , evalPostState :: [StateBody] -> m (v Truthy)
    , evalSequence :: v Truthy -> v Truthy -> m (v Truthy)
    , deferConsumer :: forall t. (DescriptorIdent t, [Thingy]) -> m (v t)
    }

data Definitions = Definitions {
                     _definedEdges :: TaggedGraph (Descriptor Truthy) (Maybe LogicNodeName)
                   , _definedLogicNodes :: Map LogicNodeName [(DescriptorName, [Thingy])]
                   , _descriptorDeclarations :: Map DescriptorName (DescriptorType, Maybe DescriptorConsumeSpec)
                   , _truthyDescriptorDefinitions :: Map (DescriptorIdent Truthy) [Descriptor Truthy]
                   , _countyDescriptorDefinitions :: Map (DescriptorIdent County) [Descriptor County]
                   }

$(makeLenses ''Definitions)

--definedEdgesTo :: LogicNodeName -> Traversal' Definitions [(LogicNodeName, Descriptor Truthy)]
definedEdgesTo name = definedEdges . to (taggedGetEdgesTo name)
--definedEdgesFrom :: LogicNodeName -> Traversal' Definitions [(Descriptor Truthy, LogicNodeName)]
definedEdgesFrom name = definedEdges . to (taggedGetEdgesFrom name)
--definedLogicNodeAccess :: LogicNodeName -> Traversal' Definitions [(DescriptorName, [Thingy])]
definedLogicNodeAccess name = definedLogicNodes . ix name
--definedDescriptorType  :: DescriptorName -> Traversal' Definitions (DescriptorType, Maybe DescriptorConsumeSpec)
definedDescriptorType name = descriptorDeclarations . ix name
definedDescriptor :: DescriptorIdent t -> Traversal' Definitions [Descriptor t]
definedDescriptor name@(TruthyDescriptorIdent _) = truthyDescriptorDefinitions . ix name
definedDescriptor name@(CountyDescriptorIdent _) = countyDescriptorDefinitions . ix name

updateLocal :: (Eq (v Truthy), Eq (v County)) => Definitions -> (forall m. MonadEval (v Truthy) (v County) m => Eval m v) -> ShuffleDependend -> ShuffleProgress (v Truthy) (v County) -> (ShuffleProgress (v Truthy) (v County), [ShuffleDependend])
updateLocal defs eval object progress = runUpdate defs progress $ case object of
    -- DescriptorDependend (i@(TruthyDescriptorIdent name), params) -> evalMax eval STruthy $ fmap (goT . applyParams params) $ lookupDescriptors i defs
    -- DescriptorDependend (i@(CountyDescriptorIdent name), params) -> evalMax eval SCounty $ fmap (goC . applyParams params) $ lookupDescriptors i defs
    LogicNodeDependent name -> do
        incomingEdges <- view $ definedEdgesTo (Just name)
        ts <- forM incomingEdges $ \(source, edge) -> do
            t <- case source of 
                Just source -> askLogicNodeAccess source
                Nothing -> fmap Just $ evalConstant eval $ TruthyLiteral OolTrue
            t' <- case t of
                Nothing -> evalConstant eval $ TruthyLiteral OolFalse
            t'' <- evalDescriptor eval STruthy edge []
            evalSequence eval t' t''
        t <- evalMax eval STruthy ts
        updateLogicNode name t
    DescriptorDependend (name, params) -> do
        (descType, spec) <- asks (^?! definedDescriptorType name)
        case (descType, spec) of
            (Truthy, Nothing) -> do
                ds <- view $ definedDescriptor (TruthyDescriptorIdent name)
                ts <- forM ds $ \d ->
                    evalDescriptor eval STruthy d params
                t <- evalMax eval STruthy ts
                updateTruthyDescriptor (name, params) t
            (County, Nothing) -> do
                ds <- view $ definedDescriptor (CountyDescriptorIdent name)
                ts <- forM ds $ \d ->
                    evalDescriptor eval SCounty d params
                t <- evalMax eval SCounty ts
                updateCountyDescriptor (name, params) t
            (Truthy, Just (DescriptorConsumeSpec key lock)) -> deferConsumer eval (TruthyDescriptorIdent lock, params) >>= updateTruthyDescriptor (name, params)
            (County, Just (DescriptorConsumeSpec key lock)) -> deferConsumer eval (CountyDescriptorIdent lock, params) >>= updateCountyDescriptor (name, params)

newtype UpdateT v m a = UpdateT { extractUpdate :: RWST Definitions [ShuffleDependend] (ShuffleProgress (v Truthy) (v County), [ShuffleDependency]) m a }
                      deriving newtype ( MonadReader Definitions )
                      deriving newtype ( MonadState (ShuffleProgress (v Truthy) (v County), [ShuffleDependency]))
                      deriving newtype ( MonadWriter [ShuffleDependend])
                      deriving newtype Functor
                      deriving newtype Applicative
                      deriving newtype Monad

runUpdate :: (Eq (v Truthy), Eq (v County)) => Definitions -> ShuffleProgress (v Truthy) (v County) -> UpdateT v Identity () -> (ShuffleProgress (v Truthy) (v County), [ShuffleDependend])
runUpdate defs progress update = _1 %~ fst $ runIdentity $ execRWST (extractUpdate update) defs (progress, [])

updateLogicNode :: (Monad m, Eq (v Truthy)) => LogicNodeName -> v Truthy -> UpdateT v m ()
updateLogicNode name value = do
    deps <- _2 <<.= []
    value' <- _1 . logicNodes . at name <<.= Just value
    _1 . cachedDependencies %= bipSetEdgesTo (LogicNodeDependent name) deps
    when (value' /= Just value) $ do
        accs <- view $ definedLogicNodeAccess name . to (fmap AccessDependency)
        forM_ accs $ \acc -> do
            w <- gets (^. _1 . cachedDependencies . to (bipGetEdgesFrom acc))
            tell w
        w <- view $ definedEdgesFrom (Just name) . traverse . _2 . _Just . to ((:[]) . LogicNodeDependent)
        tell w

updateCountyDescriptor :: (Monad m, Eq (v County)) => (DescriptorName, [Thingy]) -> v County -> UpdateT v m ()
updateCountyDescriptor desc@(name, params) value = do
    deps <- _2 <<.= []
    value' <- _1 . countyDescriptors . at (CountyDescriptorIdent name, params) <<.= Just value
    _1 . cachedDependencies %= bipSetEdgesTo (DescriptorDependend desc) deps
    when (value' /= Just value) $ do
        w <- gets (^. _1 . cachedDependencies . to (bipGetEdgesFrom (DescriptorDependency desc)))
        tell w

updateTruthyDescriptor :: (Monad m, Eq (v Truthy)) => (DescriptorName, [Thingy]) -> v Truthy -> UpdateT v m ()
updateTruthyDescriptor desc@(name, params) value = do
    deps <- _2 <<.= []
    value' <- _1 . truthyDescriptors . at (TruthyDescriptorIdent name, params) <<.= Just value
    _1 . cachedDependencies %= bipSetEdgesTo (DescriptorDependend desc) deps
    when (value' /= Just value) $ do
        w <- gets (^. _1 . cachedDependencies . to (bipGetEdgesFrom (DescriptorDependency desc)))
        tell w

instance (Monad m) => MonadEval (v Truthy) (v County) (UpdateT v m) where
    askTruthyDescriptor name params = use $ _1 . truthyDescriptors . at (name, params)
    askCountyDescriptor name params = use $ _1 . countyDescriptors . at (name, params)
    askAccess name params = do
      n <- use $ _1 . cachedAccess . at (name, params)
      case n of
          Nothing -> return Nothing
          Just n -> askLogicNodeAccess n
    askLogicNodeAccess name = use $ _1 . logicNodes . at name
    --askShuffle = --TODO

newtype Lift (t :: (* -> *) -> * -> *) m a = Lift { unLift :: t m a }
        deriving newtype ( Functor
                         , Applicative
                         , Monad
                         , MonadTrans
                         )

instance (MonadEval t c m, MonadTrans t', Monad (t' m)) => MonadEval t c (Lift t' m) where
    askTruthyDescriptor name params = lift $ askTruthyDescriptor name params
    askCountyDescriptor name params = lift $ askCountyDescriptor name params
    askAccess name params = lift $ askAccess name params
    askLogicNodeAccess name = lift $ askLogicNodeAccess name
    askShuffle name param = lift $ askShuffle name param

askDescriptor :: (MonadEval (v Truthy) (v County) m) => SDescriptorType t -> DescriptorName -> [Thingy] -> m (Maybe (v t))
askDescriptor STruthy = askTruthyDescriptor . TruthyDescriptorIdent
askDescriptor SCounty = askCountyDescriptor . CountyDescriptorIdent

deriving via Lift (ReaderT r) m instance (MonadEval t c m) => MonadEval t c (ReaderT r m)


evalDescriptor :: forall m (v :: DescriptorType -> *) t. (MonadEval (v Truthy) (v County) m) => Eval (ReaderT (Map VarName Thingy) m) v -> SDescriptorType t -> Descriptor t -> [Thingy] -> m (v t)
evalDescriptor eval dt (Descriptor paramSpec rule) params = maybe (runReaderT (evalConstant eval (bottomLiteral dt)) mempty) (runReaderT (go dt rule)) (tryBinds paramSpec params) where
    bottomLiteral :: forall t. SDescriptorType t -> Literal t
    bottomLiteral STruthy = TruthyLiteral OolFalse
    bottomLiteral SCounty = IntLiteral 0
    tryBinds xs ys = tryBind xs ys mempty
    tryBind [] [] m = Just m
    tryBind (Variable name : xs) (value : ys) m = case M.lookup name m of
        Nothing -> tryBind xs ys (M.insert name value m)
        Just value' | value == value' -> tryBind xs ys m
                    | otherwise -> Nothing
    goT :: DescriptorRule Truthy -> ReaderT (Map VarName Thingy) m (v Truthy)
    goT = go STruthy
    goC :: DescriptorRule County -> ReaderT (Map VarName Thingy) m (v County)
    goC = go SCounty
    go :: forall t. SDescriptorType t -> DescriptorRule t -> ReaderT (Map VarName Thingy) m (v t)
    go _ (IsEqual val val') = do
        x <- valToThingy val
        y <- valToThingy val'
        if x == y then evalConstant eval (TruthyLiteral OolTrue) else evalConstant eval (TruthyLiteral OolFalse)
    go t (CallDescriptor name values) = do
        params <- traverse valToThingy values
        v <- askDescriptor t name params
        resOrBottom t v
    go t (CanAccess name values sb) = do
        params <- traverse valToThingy values
        v <- askAccess name params
        v' <- resOrBottom t v
        s <- evalPriorState eval sb
        evalSequence eval v' s
    go _ (Constant x) = evalConstant eval x
    go _ (Product a b) = do
        x <- goC a
        y <- goC b
        evalProduct eval x y
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
    go _ (PriorState sb) = evalPriorState eval sb
    go _ (PostState sb) = evalPostState eval sb
    resOrBottom :: forall t. SDescriptorType t -> Maybe (v t) -> ReaderT (Map VarName Thingy) m (v t)
    resOrBottom t Nothing = evalConstant eval (bottomLiteral t)
    resOrBottom _ (Just v) = return v
    valToThingy (Variable var) = asks (^?! ix var)
    valToThingy (ConstantValue t) = return t
