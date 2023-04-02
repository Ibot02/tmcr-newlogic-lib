{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
module TMCR.Logic.Merge where

import TMCR.Module
import TMCR.Logic.Descriptor
import TMCR.Logic.Logic (Forest)
import qualified TMCR.Logic.Logic as L

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
import TMCR.Logic.Graphs (TaggedGraph, taggedEdge)
import TMCR.Shuffler (LogicNodeName, Thingy)
import Control.Lens
import Data.Functor.Foldable
import Data.Functor.Foldable.TH
import Control.Lens.Extras
import Data.List (sortBy)
import Data.Maybe (catMaybes, maybeToList, mapMaybe)
import Control.Monad (unless)
import TMCR.Logic.Common (PossiblyScopedName (..), Name)
import Data.Function (fix)
import TMCR.Logic.Data
import Data.Functor.Compose (Compose (..))
import Data.Void (absurd)
import Data.Text (Text)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Control.Arrow (first)
import TMCR.Logic.Shuffle (ShuffleStatement (..), ShuffleInstruction, ShuffleName)
import TMCR.Module.Dependency
import qualified Data.Text as T

class Monad m => MonadMerge m where
    mergeDescDeclError :: DescriptorName -> [[ModuleIdentifier]] -> m a
    errorDescriptorNotDeclared :: DescriptorName -> m a
    errorDescriptorArgsMismatch :: DescriptorName -> [Scoping] -> Int -> m a
    errorDescriptorTypeMismatch :: DescriptorName -> DescriptorType -> DescriptorType -> m a
    errorOverspecifiedScope :: [L.Name] -> m a
    mergeErrorAppendToUndefined :: ShuffleName -> m a
    warningIgnoredLogicSubtree :: Forest' L.Value -> m ()
    mergeErrorUnresolvedOrderingOverwrite :: ModuleIdentifier -> ModuleIdentifier -> m a
    errorUnexpectedLogicStructure :: m a
    errorLogicDataMergeConflict :: [([(Text, Int)],Text)] -> m a
    dependencies :: m ModuleDependencyInfo
    --

-- Descriptor declarations have to be identical when defined in multiple modules

mergeDescriptorDeclarations :: forall m. (MonadMerge m) => Map ModuleIdentifier (Map DescriptorName DescriptorDeclaration) -> m (Map DescriptorName DescriptorDeclaration)
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

dtranspose :: forall k k' f. (GCompare k', Ord k) => Map k (DMap k' f) -> DMap k' (Compose (Map k) f)
dtranspose = buildUp . flatten where
    buildUp :: [(k, DSum k' f)] -> DMap k' (Compose (Map k) f)
    buildUp = DM.fromListWithKey (\_ (Compose m) (Compose m') -> Compose (m <> m')) . fmap (\(x,(y DS.:=> z)) -> (y DS.:=> Compose (M.singleton x z)))
    flatten :: Map k (DMap k' f) -> [(k, DSum k' f)]
    flatten = concatMap (\(x,xs) -> fmap ((,) x) xs) . M.toList . fmap DM.toList

type OverwritingInfo = ()

mergeDescriptorDefinitions :: (MonadMerge m) => OverwritingInfo -> Map DescriptorName DescriptorDeclaration -> Map ModuleIdentifier (DMap DescriptorIdent Descriptors) -> m (DMap DescriptorIdent Descriptors)
mergeDescriptorDefinitions overwriting declarations x = do
    r <- mergeDescriptorDefinitions' overwriting x
    verifyDescriptorDefinitions declarations r
    return r

mergeDescriptorDefinitions' :: (MonadMerge m) => OverwritingInfo -> Map ModuleIdentifier (DMap DescriptorIdent Descriptors) -> m (DMap DescriptorIdent Descriptors)
mergeDescriptorDefinitions' overwriting = DM.traverseWithKey (merge overwriting) . DM.map (\(Compose m) -> Compose (fmap Compose (M.toList m)) ) . dtranspose where
    merge :: (MonadMerge m) => OverwritingInfo -> DescriptorIdent t -> Compose [] (Compose ((,) ModuleIdentifier) Descriptors) t -> m (Descriptors t)
    merge overwriting ident (coerce -> blah :: [(ModuleIdentifier, [Descriptor t])]) = return $ coerce $ concatMap snd blah
    -- coerce :: Compose [] (Compose ((,) ModuleIdentifier) Descriptors) t -> [(ModuleIdentifier, Descriptors t)]

verifyDescriptorDefinitions :: (MonadMerge m) => Map DescriptorName DescriptorDeclaration -> DMap DescriptorIdent Descriptors -> m ()
verifyDescriptorDefinitions _ _ = return () --todo: check if all defined descriptors are declared, check that all variables are bound

type Forest' a = [Tree' a]
data Tree' a = Node a (Forest' a)
    deriving (Eq, Ord, Show, Functor)

$(makeBaseFunctor ''Tree')

generalizeForest :: Forest -> Forest' (L.Value, L.Mode)
generalizeForest = fmap generalizeTree where
    generalizeTree (L.Node a b f) = Node (a,b) $ generalizeForest f

topDown :: ((a,b) -> (c,b)) -> b -> Tree' a -> Tree' c
topDown f b a = runIdentity $ topDownM (Identity . f) b a

topDownM :: (Monad m) => ((a,b) -> m (c,b)) -> b -> Tree' a -> m (Tree' c)
topDownM f = go where
    go b (Node a as) = do
        (c, b') <- f (a,b)
        as' <- traverse (go b') as
        return $ Node c as'

{-

Module A:

area A:
  room A:
    node A
    node B
    A -> B : blah


Module B <- A, (C):

area A:
  room A:
    node A +:
      something

Module C <- A

area * !:
  room A:
    node A

Module D <- C:
area A +:

---

area A
  [ (Module A, default, ...)
  , (Module B, default, ...)
  , (Module C, overwrite, ...)
  ]

area A:
  Module C: ...
  Module B: ...

---

area A:
  room A:
    node A.A.A:
      something

-}

findLast :: (MonadMerge m) => [(ModuleIdentifier, a)] -> m (ModuleIdentifier, a)
findLast overwrites = do
    dependencies <- dependencies
    let ((candidate, value):_) = reverse $ dependencyOrder dependencies overwrites
    case filter (\(c', _) -> candidate /= c' && not (dependsOn dependencies candidate c')) overwrites of
        [] -> return (candidate, value)
        ((x,_):_) -> mergeErrorUnresolvedOrderingOverwrite x candidate
restrictLaterThan :: (MonadMerge m) => ModuleIdentifier -> [(ModuleIdentifier, a, b)] -> m [(ModuleIdentifier, b)]
restrictLaterThan o = fmap catMaybes . traverse (\(m,_,v) -> do
    dependencies <- dependencies
    if
        | o == m -> return $ Nothing
        | dependsOn dependencies m o -> return $ Just (m,v)
        | dependsOn dependencies o m -> return $ Nothing
        | otherwise -> mergeErrorUnresolvedOrderingOverwrite o m
        )
extractOverwrites :: [(a, L.Mode, b)] -> [(a, b)]
extractOverwrites = fmap (\(a,_,b) -> (a,b)) . filter (\x -> is L._ModeReplace (x ^. _2))

resolveConflicts :: (MonadMerge m) => (Map ModuleIdentifier [a] -> m b) -> [(ModuleIdentifier, L.Mode, a)] -> m b
resolveConflicts f possiblyConflictingDefinitions = do
    let overwrites = extractOverwrites possiblyConflictingDefinitions
    if null overwrites
    then --todo: verify no module is appending to nothing
        f $ M.fromListWith (<>) $ fmap (\(a,_,b) -> (a,[b])) possiblyConflictingDefinitions
    else do
        dependencies <- dependencies
        (o,v) <- findLast overwrites
        later <- restrictLaterThan o possiblyConflictingDefinitions
        let same = reverse $ foldl' (\acc (_, mode, val) -> if is L._ModeReplace mode then [(o, val)] else (o,val) : acc) [] $ filter ((== o) . (^. _1)) possiblyConflictingDefinitions
        f $ M.fromListWith (<>) $ fmap (\(a,b) -> (a,[b])) $ same <> later

mergeRecursively :: (MonadMerge m, Ord i) => (a -> [(L.Mode, Either i j, a)]) -> (i -> j -> Bool) -> (Map i b -> b) -> Map ModuleIdentifier [a] -> m b
mergeRecursively destruct wildcards reconstruct = f where
    f i = fmap reconstruct $ traverse (resolveConflicts f) $ g $ concatMap (\(moduleIdent, xs) -> fmap (\(mode, ident, val) -> (moduleIdent, mode, ident, val)) xs) $ M.toList $ fmap (concatMap destruct) i
    --g :: [(ModuleIdentifier, L.Mode, Either i j, a)] -> Map i [(ModuleIdentifier, L.Mode, a)]
    g = fmap reverse . fst . foldl (\(m,w) (moduleIdent, mode, ident, val) -> case ident of
        Left ident ->
            let newVal = (moduleIdent, mode, val)
                wildcarded = mapMaybe (\(moduleIdent, mode, wildcardIdent, val) -> if wildcards ident wildcardIdent then Just (moduleIdent, mode, val) else Nothing) w
            in (M.alter (Just . maybe (newVal : wildcarded) (newVal :) ) ident m,w)
        Right wildcard -> (M.mapWithKey (\ident xs -> if wildcards ident wildcard then (moduleIdent, mode, val) : xs else xs) m, (moduleIdent, mode, wildcard, val) : w)
        ) (M.empty, [])

mergeLogic :: (MonadMerge m) => Map DescriptorName DescriptorDeclaration -> Map ModuleIdentifier Forest -> m (Forest' L.Value)
mergeLogic descriptors sources = traverse (fullyScopeNames . generalizeForest) sources >>= f where
    f :: (MonadMerge m) => Map ModuleIdentifier (Forest' (L.Value, L.Mode)) -> m (Forest' L.Value)
    f = mergeRecursively (\(project -> NodeF (val,mode) xs) -> fmap (\x -> (mode, (if hasWildcard val then Right else Left) val, x)) xs) (flip wildcardMatches) (fmap (embed . uncurry NodeF) . M.toList)
    hasWildcard (L.Anon _) = False
    hasWildcard (L.NamedScoped _ name) = hasWildcard' name
    hasWildcard (L.NamedScoping _ name) = hasWildcard'' name
    hasWildcard (L.Edge name name2) = hasWildcard' name || hasWildcard' name2
    hasWildcard (L.EdgeUndirected name name2) = hasWildcard' name || hasWildcard' name2
    hasWildcard' L.FullWildcard = True
    hasWildcard' (L.Global name) = hasWildcard'' name
    hasWildcard' (L.Scoped names) = any hasWildcard'' names
    hasWildcard'' L.Wildcard = True
    hasWildcard'' _ = False
    wildcardMatches (L.NamedScoped x name) (L.NamedScoped x' name') = x == x' && wildcardMatches' name name'
    wildcardMatches (L.NamedScoping x name) (L.NamedScoping x' name') =  x == x' && wildcardMatches'' name name'
    wildcardMatches (L.Edge name name2) (L.Edge name' name2') = wildcardMatches' name name' && wildcardMatches' name2 name2'
    wildcardMatches (L.EdgeUndirected name name2) (L.EdgeUndirected name' name2') = wildcardMatches' name name' && wildcardMatches' name2 name2'
    wildcardMatches _ _ = False
    wildcardMatches' L.FullWildcard _ = True
    wildcardMatches' (L.Global name) (L.Global name') = wildcardMatches'' name name'
    wildcardMatches' (L.Scoped names) (L.Scoped names') = all (uncurry wildcardMatches'') $ zip names names' --note the assumption that lists are of the same length, this should always be the case here since we fully scoped names earlier
    wildcardMatches' _ _ = False
    wildcardMatches'' L.Wildcard _ = True
    wildcardMatches'' x y = x == y
    fullyScopeNames :: (MonadMerge m) => Forest' (L.Value, L.Mode) -> m (Forest' (L.Value, L.Mode))
    fullyScopeNames = traverse (topDownM (\((value, mode), scope) -> fmap (\(value', scope') -> ((value', mode), scope)) (scopeStep value scope )) [])
    scopeStep :: (MonadMerge m) => L.Value -> [L.Name] -> m (L.Value, [L.Name])
    scopeStep value scope = case value of
        L.NamedScoping _ s -> return (value, s:scope)
        L.NamedScoped "node" x -> do
            x' <- applyScope scope x
            return $ (L.NamedScoped "node" x', scope)
        L.NamedScoped desc val -> case M.lookup desc descriptors of
            Nothing -> errorDescriptorNotDeclared desc
            Just ((^. descriptorDeclarationArguments) -> [scoping]) -> case scoping of
                Scoped -> do
                    val' <- applyScope scope val
                    return $ (L.NamedScoped desc val', scope)
                Unscoped -> return (value, scope)
            Just ((^. descriptorDeclarationArguments) -> xs) -> errorDescriptorArgsMismatch desc xs 1
        L.Edge x y -> do
            x' <- applyScope scope x
            y' <- applyScope scope y
            return $ (L.Edge x' y', scope)
        L.EdgeUndirected x y -> do
            x' <- applyScope scope x
            y' <- applyScope scope y
            return $ (L.EdgeUndirected x y, scope)
        L.Anon _ -> return $ (value, scope)
    applyScope _ x@(L.Global _) = return x
    applyScope _ x@L.FullWildcard = return x
    applyScope scope (L.Scoped names) | length names > length scope + 1 = errorOverspecifiedScope names
                                      | otherwise = return $ L.Scoped $ prependRev (drop (length names - 1) scope) names
    prependRev [] x = x
    prependRev (x:xs) y = prependRev xs $ x:y


transformLogic :: (MonadMerge m) => Map DescriptorName DescriptorDeclaration -> Forest' L.Value -> m (TaggedGraph (DescriptorRule Truthy) (Maybe LogicNodeName), Map LogicNodeName [(DescriptorName, [Thingy])])
transformLogic descriptors forest = Data.Foldable.fold <$> traverse f forest where
    f (Node (L.NamedScoping _ _) forest) = Data.Foldable.fold <$> traverse f forest
    f (Node (L.NamedScoped "node" logicNodeName) forest) = Data.Foldable.fold <$> traverse (nodeDescr logicNodeName) forest
    f (Node (L.Edge source target) desc) = ((,)) . (\e -> taggedEdge e (Just source) (Just target)) <$> (Min <$> traverse descrRule desc) <*> pure M.empty
    f (Node (L.EdgeUndirected source target) desc) = ((,)) . (\e -> taggedEdge e (Just source) (Just target) <> taggedEdge e (Just target) (Just source)) <$> (Min <$> traverse descrRule desc) <*> pure M.empty
    nodeDescr name (Node (L.Anon descr) xs) = case M.lookup descr descriptors of
        Nothing -> errorDescriptorNotDeclared descr
        Just def -> do
            unless (def ^. descriptorDeclarationArguments . to null) $ errorDescriptorArgsMismatch descr (def ^. descriptorDeclarationArguments) 0
            unless ((def ^. descriptorDeclarationType) == Truthy) $ errorDescriptorTypeMismatch descr County Truthy
            unless (null xs) $ warningIgnoredLogicSubtree xs
            case def ^. descriptorDeclarationExport of
                Nothing -> errorDescriptorNotDeclared descr --todo, make this go away while parsing the module or merging
                Just DescriptorExportNone -> errorDescriptorNotDeclared descr
                Just DescriptorExportEdge -> errorDescriptorNotDeclared descr
                Just DescriptorExportSelfEdge -> return (taggedEdge (CallDescriptor descr []) (Just name) (Just name), mempty)
                Just DescriptorExportEdgeFromBeyondTheVoid -> return (taggedEdge (CallDescriptor descr []) Nothing (Just name), mempty)
                Just DescriptorExportTarget -> return (mempty, M.singleton name [(descr,[])])
    nodeDescr name (Node (L.NamedScoped descr arg) xs) = case M.lookup descr descriptors of
        Nothing -> errorDescriptorNotDeclared descr
        Just def -> do
            unless ((def ^. descriptorDeclarationArguments . to length)  == 1) $ errorDescriptorArgsMismatch descr (def ^. descriptorDeclarationArguments) 1
            unless ((def ^. descriptorDeclarationType) == Truthy) $ errorDescriptorTypeMismatch descr County Truthy
            unless (null xs) $ warningIgnoredLogicSubtree xs
            case def ^. descriptorDeclarationExport of
                Nothing -> errorDescriptorNotDeclared descr --todo, make this go away while parsing the module or merging
                Just DescriptorExportNone -> errorDescriptorNotDeclared descr
                Just DescriptorExportEdge -> errorDescriptorNotDeclared descr
                Just DescriptorExportSelfEdge -> return (taggedEdge (CallDescriptor descr [ConstantValue $ nonWildcardScopedName arg]) (Just name) (Just name), mempty)
                Just DescriptorExportEdgeFromBeyondTheVoid -> return (taggedEdge (CallDescriptor descr [ConstantValue $ nonWildcardScopedName arg]) Nothing (Just name), mempty)
                Just DescriptorExportTarget -> return (mempty, M.singleton name [(descr,[nonWildcardScopedName arg])])
    nodeDescr _ _ = errorUnexpectedLogicStructure
    descrRule :: (MonadMerge m) => Tree' L.Value -> m (DescriptorRule Truthy)
    descrRule (Node (L.Anon "and") xs) = Min <$> traverse descrRule xs --todo: forbid reserved names "and" and "or" to be declared as descriptors
    descrRule (Node (L.Anon "or") xs)  = Max <$> traverse descrRule xs
    descrRule (Node (L.Anon descr) xs) = case M.lookup descr descriptors of
        Nothing -> errorDescriptorNotDeclared descr
        Just def -> do
            unless (def ^. descriptorDeclarationArguments . to null) $ errorDescriptorArgsMismatch descr (def ^. descriptorDeclarationArguments) 0
            unless ((def ^. descriptorDeclarationType) == Truthy) $ errorDescriptorTypeMismatch descr County Truthy
            unless (null xs) $ warningIgnoredLogicSubtree xs
            case def ^. descriptorDeclarationExport of
                Just DescriptorExportEdge -> return $ CallDescriptor descr []
                _ -> errorDescriptorNotDeclared descr
    descrRule (Node (L.NamedScoped descr arg) xs) = case M.lookup descr descriptors of
        Nothing -> errorDescriptorNotDeclared descr
        Just def -> do
            unless ((def ^. descriptorDeclarationArguments . to length)  == 1) $ errorDescriptorArgsMismatch descr (def ^. descriptorDeclarationArguments) 1
            unless ((def ^. descriptorDeclarationType) == Truthy) $ errorDescriptorTypeMismatch descr County Truthy
            unless (null xs) $ warningIgnoredLogicSubtree xs
            case def ^. descriptorDeclarationExport of
                Just DescriptorExportEdge -> return $ CallDescriptor descr [ConstantValue $ nonWildcardScopedName arg]
                _ -> errorDescriptorNotDeclared descr
    descrRule _ = errorUnexpectedLogicStructure

nonWildcardScopedName :: L.ScopedName -> PossiblyScopedName
nonWildcardScopedName (L.Global n) = Global $ nonWildcardName n
nonWildcardScopedName (L.Scoped n) = ScopedName $ fmap nonWildcardName n

nonWildcardName :: L.Name -> Name
nonWildcardName (L.PlainName t) = t
nonWildcardName (L.QuotedName t) = t

-- ~~for logic, remember to extract key info from locks~~ move to be a relation

$(makeBaseFunctor ''LogicData)

data DataMergeKey = TextValue Text Text
                  | MapValue Text Int
                  deriving (Eq, Ord)

mergeData :: (MonadMerge m) => Map ModuleIdentifier [LogicData'] -> m LogicData
mergeData xs = (mergeRecursively f (const absurd) g . fmap (fmap Just)) xs >>= either errorLogicDataMergeConflict return where
    f (Just (LogicData' m)) = concatMap (\(t, e) -> case e of
        Left t' -> [(L.ModeReplace, Left (TextValue t t'), Nothing)]
        Right (mode, intMap) -> fmap (\(i,maybeLogicData) -> (mode, (Left (MapValue t i)), maybeLogicData)) $ IM.toList intMap
        ) $ M.toList m
    f Nothing = []
    g :: Map DataMergeKey (Either [([(Text, Int)],Text)] LogicData) -> Either [([(Text, Int)],Text)] LogicData
    g = (\(m, c, s) -> let conflicts = S.toList s <> c in case conflicts of
        [] -> Right $ LogicData m
        _ -> Left conflicts
        ) . foldl (\(m, cs, s) n -> case n of
                (MapValue t i, Left c) -> (m,conflictContext t i c <> cs,s)
                (MapValue t i, Right l) -> case M.lookup t m of
                    Nothing -> (M.insert t (Right $ IM.singleton i l) m, cs, s)
                    Just (Left _) -> (m, cs, S.insert ([],t) s)
                    Just (Right im) -> (M.insert t (Right $ IM.insert i l im) m, cs, s)
                (TextValue t t', _) -> (M.insert t (Left t') m, cs, case M.lookup t m of
                    Nothing -> s
                    Just _ -> S.insert ([],t) s
                    )
                ) (M.empty, [], S.empty) . M.toList
    conflictContext :: a -> b -> [([(a, b)],c)] -> [([(a, b)],c)]
    conflictContext t i = fmap (first ((t,i):))

mergeShuffle :: (MonadMerge m) => Map ModuleIdentifier [ShuffleStatement] -> m [ShuffleStatement]
mergeShuffle = resolveConflicts (return . concat . toList) . concat . fmap (\(ident,xs) -> fmap (tag ident) xs) . M.toList where
    tag ident x@(DefineShuffle _ _) = (ident, L.ModeReplace, x)
    tag ident x@(ExpandShuffle _ _) = (ident, L.ModeAppend, x)

groupShuffle :: (MonadMerge m) => [ShuffleStatement] -> m (Map ShuffleName (ShuffleInstruction, [ShuffleInstruction]))
groupShuffle shuffles = M.traverseWithKey verifySingleDefine $ M.unionsWith (<>) $ fmap convert shuffles where
    convert (DefineShuffle n v) = M.singleton n ([v],[])
    convert (ExpandShuffle n v) = M.singleton n ([],[v])
    verifySingleDefine _ ([x],xs) = return (x,xs)
    verifySingleDefine n ([],_) = mergeErrorAppendToUndefined n
    verifySingleDefine n _ = error $ "multiple definitions of shuffle " <> T.unpack n --should be unreachable in mergeShuffle >>= groupShuffle case

--resolveConflicts :: (MonadMerge m) => (Map ModuleIdentifier [a] -> m b) -> [(ModuleIdentifier, L.Mode, a)] -> m b

data GameDef = GameDef {
      _defDescriptors :: Map DescriptorName DescriptorDeclaration
    , _defDescriptorDefinitionsTruthy :: Map (DescriptorIdent Truthy) [Descriptor Truthy]
    , _defDescriptorDefinitionsCounty :: Map (DescriptorIdent County) [Descriptor County]
    , _defLogic :: (TaggedGraph (DescriptorRule Truthy) (Maybe LogicNodeName), Map LogicNodeName [(DescriptorName, [Thingy])]) 
    , _defPatches :: Map ModuleIdentifier (FilePath, [ResourceSpecifier])
    , _defLogicData :: LogicData
    , _defShuffles :: Map ShuffleName (ShuffleInstruction, [ShuffleInstruction])
    } deriving (Eq, Ord)

mergeContent :: (MonadMerge m) => Map ModuleIdentifier (FilePath, ModuleFullContent) -> m GameDef
mergeContent modules = do
    descriptors <- mergeDescriptorDeclarations $ fmap (^. _2 . moduleFullContentDescriptors) modules
    descriptorDefs <- mergeDescriptorDefinitions () descriptors $ fmap (^. _2 . moduleFullContentDescriptorDefinitions) modules
    logic <- do
        l <- mergeLogic descriptors $ fmap (^. _2 . moduleFullContentLogic) modules
        transformLogic descriptors l
    let patches = fmap (fmap (^. moduleFullContentPatches)) modules
    logicData <- mergeData $ fmap (^. _2 . moduleFullContentData) modules
    shuffles <- (mergeShuffle $ fmap (^. _2 . moduleFullContentShuffles) modules) >>= groupShuffle
    let (descriptorDefsTruthy, descriptorDefsCounty) = DM.foldrWithKey mergeContentHelper (mempty, mempty) descriptorDefs
    return $ GameDef descriptors descriptorDefsTruthy descriptorDefsCounty logic patches logicData shuffles

mergeContentHelper :: (DescriptorIdent v) -> Descriptors v -> (Map (DescriptorIdent Truthy) [Descriptor Truthy], Map (DescriptorIdent County) [Descriptor County]) -> (Map (DescriptorIdent Truthy) [Descriptor Truthy], Map (DescriptorIdent County) [Descriptor County])
mergeContentHelper x@(TruthyDescriptorIdent _) (Descriptors v) (t,c) = (M.insert x v t, c)
mergeContentHelper x@(CountyDescriptorIdent _) (Descriptors v) (t,c) = (t, M.insert x v c)