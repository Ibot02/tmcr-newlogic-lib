module TMCR.Module.Dependency (ModuleIdentifier(), ModuleDependencyInfo(), dependsOn, dependencyOrder, makeModuleDependencyInfo) where
import TMCR.Module
import Data.Text (Text)

type ModuleIdentifier = Text
type ModuleDependencyInfo = ()

data DependencyError = DependencyUnmet ModuleIdentifier ModuleIdentifier
                     | DependencyVersionMismatch ModuleIdentifier ModuleIdentifier VersionSpec Version
                     | CircularDependencies [ModuleIdentifier]

dependsOn :: ModuleDependencyInfo -> ModuleIdentifier -> ModuleIdentifier -> Bool
dependsOn _ _ _ = False --todo

dependencyOrder :: ModuleDependencyInfo -> [(ModuleIdentifier, a)] -> [(ModuleIdentifier, a)]
dependencyOrder _ = id --todo

makeModuleDependencyInfo :: [((ModuleIdentifier, Version), [(ModuleIdentifier, VersionSpec)], [(ModuleIdentifier, VersionSpec)])] -> Either [DependencyError] ModuleDependencyInfo
makeModuleDependencyInfo _ = Right () --todo
