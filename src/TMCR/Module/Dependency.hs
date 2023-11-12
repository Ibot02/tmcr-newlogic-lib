{-# LANGUAGE ViewPatterns #-}
module TMCR.Module.Dependency (ModuleIdentifier(), ModuleDependencyInfo(), DependencyError(..), dependsOn, dependencyOrder, makeModuleDependencyInfo, singleModuleDependencies) where
import TMCR.Module
import Data.Text (Text)
import qualified Algebra.Graph.AdjacencyMap as AM
import qualified Algebra.Graph.NonEmpty.AdjacencyMap as NAM
import qualified Algebra.Graph.Acyclic.AdjacencyMap as AAM
import Data.Foldable (Foldable(toList))
import qualified Data.Map as M

type ModuleIdentifier = Text
newtype ModuleDependencyInfo = ModuleDependencyInfo { getModuleDependencyInfo :: AAM.AdjacencyMap ModuleIdentifier }
                             deriving (Eq, Ord, Show)
type SingleModuleDependencies = ((ModuleIdentifier, Version), [(ModuleIdentifier, VersionSpec)], [(ModuleIdentifier, VersionSpec)])

data DependencyError = DependencyUnmet ModuleIdentifier ModuleIdentifier
                     | DependencyVersionMismatch ModuleIdentifier ModuleIdentifier VersionSpec Version
                     | CircularDependencies [ModuleIdentifier]
                     deriving (Eq, Ord, Show)

dependsOn :: ModuleDependencyInfo -> ModuleIdentifier -> ModuleIdentifier -> Bool
dependsOn info a b = AAM.hasEdge a b $ getModuleDependencyInfo info

dependencyOrder :: ModuleDependencyInfo -> [(ModuleIdentifier, a)] -> [(ModuleIdentifier, a)]
dependencyOrder g vx = reverse $ fmap (\x -> let (x':_) = filter ((==x) . fst) vx in x') $ AAM.topSort $ AAM.induce (\x -> x `elem` fmap fst vx) $ getModuleDependencyInfo g

makeModuleDependencyInfo :: [SingleModuleDependencies] -> Either [DependencyError] ModuleDependencyInfo
makeModuleDependencyInfo deps = let
    moduleVersions = M.fromList $ fmap (\((moduleId, version), deps, optionalDeps) -> (moduleId, version)) deps
    relevantDeps = concatMap (\((m,_), deps, optionalDeps) -> fmap ((,) m) $ deps <> filter (\(x, _) -> M.member x moduleVersions) optionalDeps) deps
    resolvedDeps = fmap (\(m', (m,vs)) -> (((m, m'),vs), M.lookup m moduleVersions)) relevantDeps
    versionMismatch = concatMap (\(((m, m'), vs),v) -> helper v vs m m') resolvedDeps
    helper Nothing _ m m' = [DependencyUnmet m' m]
    helper (Just v) vs m m' | versionMatches vs v = []
                            | otherwise = [DependencyVersionMismatch m' m vs v]
    cycles = fmap (CircularDependencies . toList . NAM.vertexList1) $ filter (not . null . NAM.edgeList) $ AAM.vertexList $ AAM.scc graph --no strongly connected components may have internal edges
    graph = AM.overlays $ fmap (\((v,_),d1s, d2s) -> AM.star v (map fst d1s <> map fst d2s)) deps
    errors = versionMismatch <> cycles
    in case errors of 
        [] -> fmap (ModuleDependencyInfo . AAM.transitiveClosure) $ maybe (Left [] {- should not happen -}) Right $ AAM.toAcyclic $ graph
        xs -> Left xs
--todo: better errors, check version requirements

singleModuleDependencies :: Module a -> SingleModuleDependencies
singleModuleDependencies (Module name version _ deps softdeps _) = ((name, version), deps, softdeps)