{-# LANGUAGE ViewPatterns #-}
module TMCR.Module.Dependency (ModuleIdentifier(), ModuleDependencyInfo(), DependencyError(..), dependsOn, dependencyOrder, makeModuleDependencyInfo, singleModuleDependencies) where
import TMCR.Module
import Data.Text (Text)
import qualified Algebra.Graph.AdjacencyMap as AM
import qualified Algebra.Graph.Acyclic.AdjacencyMap as AAM

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
makeModuleDependencyInfo deps = fmap (ModuleDependencyInfo . AAM.transitiveClosure) $ maybe (Left $ (:[]) $ CircularDependencies $ [] {-todo-}) Right $ AAM.toAcyclic $ AM.overlays $ fmap (\((v,_),d1s, d2s) -> AM.star v (map fst d1s <> map fst d2s)) deps
--todo: better errors, check version requirements

singleModuleDependencies :: Module a -> SingleModuleDependencies
singleModuleDependencies (Module name version _ deps softdeps _) = ((name, version), deps, softdeps)