{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
module TMCR.Logic.Merge where

import TMCR.Module
import TMCR.Logic.Descriptor

import Data.Map (Map())
import qualified Data.Map as M

import Data.Set (Set())
import qualified Data.Set as S

import Data.Dependent.Map (DMap())
import qualified Data.Dependent.Map as DM

import Data.Dependent.Sum (DSum())
import qualified Data.Dependent.Sum as DS

import Data.Foldable

import Data.GADT.Compare

import Data.Coerce (coerce)

type ModuleIdentifier = ()

class Monad m => MonadMergeError m where
    mergeDescDeclError :: DescriptorName -> [[ModuleIdentifier]] -> m a
    --

-- Descriptor declarations have to be identical when defined in multiple modules

mergeDescriptorDeclarations :: forall m. (MonadMergeError m) => Map ModuleIdentifier (Map DescriptorName DescriptorDeclaration) -> m (Map DescriptorName DescriptorDeclaration)
mergeDescriptorDeclarations defs = M.traverseWithKey merge $ fmap M.toList $ transpose defs where
    merge :: DescriptorName -> [(ModuleIdentifier, DescriptorDeclaration)] -> m DescriptorDeclaration
    merge name xs = case M.toList $ M.fromListWith (<>) $ fmap (\(x,y) -> (y,[x])) xs of
        [] -> error "unreachable" --from the definition of transpose
        xs@(_:_:_) -> mergeDescDeclError name $ fmap snd $ toList xs
        [(x,_)] -> return x



transpose :: forall k k' v. (Ord k, Ord k') => Map k (Map k' v) -> Map k' (Map k v)
transpose = buildUp . flatten where
    buildUp :: [(k,(k',v))] -> Map k' (Map k v)
    buildUp = M.fromListWith M.union . fmap (\(x,(y,z)) -> (y,M.singleton x z))
    flatten :: Map k (Map k' v) -> [(k,(k',v))]
    flatten = concatMap (\(x,xs) -> fmap ((,) x) xs) . M.toList . fmap M.toList

-- Descriptor definitions can extend (default) or overwrite

newtype Compose (a :: k -> *) (b :: k' -> k) (c :: k') = Compose (a (b c))

dtranspose :: forall k k' f. (GCompare k', Ord k) => Map k (DMap k' f) -> DMap k' (Compose (Map k) f)
dtranspose = buildUp . flatten where
    buildUp :: [(k, DSum k' f)] -> DMap k' (Compose (Map k) f)
    buildUp = DM.fromListWithKey (\_ (Compose m) (Compose m') -> Compose (m <> m')) . fmap (\(x,(y DS.:=> z)) -> (y DS.:=> Compose (M.singleton x z)))
    flatten :: Map k (DMap k' f) -> [(k, DSum k' f)]
    flatten = concatMap (\(x,xs) -> fmap ((,) x) xs) . M.toList . fmap DM.toList

type OverwritingInfo = ()
type ModuleDependencyInfo = (ModuleIdentifier -> ModuleIdentifier -> Bool)

mergeDescriptorDefinitions :: (MonadMergeError m) => ModuleDependencyInfo -> OverwritingInfo -> Map ModuleIdentifier (DMap DescriptorIdent Descriptors) -> m (DMap DescriptorIdent Descriptors)
mergeDescriptorDefinitions dependencies overwriting = DM.traverseWithKey (merge dependencies overwriting) . DM.map (\(Compose m) -> Compose (fmap Compose (M.toList m)) ) . dtranspose where
    merge :: (MonadMergeError m) => ModuleDependencyInfo -> OverwritingInfo -> DescriptorIdent t -> Compose [] (Compose ((,) ModuleIdentifier) Descriptors) t -> m (Descriptors t)
    merge depends overwriting ident (coerce -> blah :: [(ModuleIdentifier, [Descriptor t])]) = return $ coerce $ concatMap snd blah
    -- coerce :: Compose [] (Compose ((,) ModuleIdentifier) Descriptors) t -> [(ModuleIdentifier, Descriptors t)]

--todo: data, logic

--for logic, remember to extract key info from locks