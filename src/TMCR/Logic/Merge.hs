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
import Control.Lens
import Control.Comonad.Cofree (Cofree())
import qualified Control.Comonad.Cofree as CF
import qualified Control.Comonad.Trans.Cofree as CFT
import Data.Functor.Foldable
import Data.Functor.Foldable.TH
import Control.Lens.Extras
import Data.List (sortBy)
import Data.Maybe (catMaybes, maybeToList, mapMaybe)
import Control.Monad (unless)
import TMCR.Logic.Common (PossiblyScopedName (..), Name, Thingy)
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
import TMCR.Logic.Algebra (DNF(..), singleToDNF, Meet(..), Join(..))
import Data.Either (partitionEithers)

class Monad m => MonadMerge m where
    mergeDescDeclError :: DescriptorName -> [[ModuleIdentifier]] -> m a
    mergeSugarConflictError :: Text -> [[ModuleIdentifier]] -> m a
    errorDescriptorNotDeclared :: DescriptorName -> m a
    errorDescriptorArgsMismatch :: DescriptorName -> [Scoping] -> Int -> m a
    errorDescriptorTypeMismatch :: DescriptorName -> DescriptorType -> DescriptorType -> m a
    errorOverspecifiedScope :: [L.Name] -> m a
    mergeErrorAppendToUndefined :: ShuffleName -> m a
    warningIgnoredLogicSubtree :: Forest' L.Value -> m ()
    mergeErrorUnresolvedOrderingOverwrite :: ModuleIdentifier -> ModuleIdentifier -> m a
    errorUnexpectedLogicStructure :: m a
    errorLogicDataMergeConflict :: [([(Text, Int)],Text)] -> m a
    errorGenericMergeError :: Int -> m a
    dependencies :: m ModuleDependencyInfo
    errorContext :: Text -> m a -> m a
    --

-- Descriptor declarations have to be identical when defined in multiple modules


mergeDescriptorDeclarations :: forall m. (MonadMerge m) => Map ModuleIdentifier (Map DescriptorName DescriptorDeclaration) -> m (Map DescriptorName DescriptorDeclaration)
mergeDescriptorDeclarations = mergeMap mergeDescDeclError

mergeSugar :: forall m. (MonadMerge m) => Map ModuleIdentifier (Map Text SugarDefinition) -> m (Map Text SugarDefinition)
mergeSugar = mergeMap mergeSugarConflictError

mergeMap :: forall m k v. (MonadMerge m, Ord k, Ord v) => (forall a. k -> [[ModuleIdentifier]] -> m a) -> Map ModuleIdentifier (Map k v) -> m (Map k v)
mergeMap createError defs = M.traverseWithKey merge $ fmap M.toList $ transpose defs where
    merge :: k -> [(ModuleIdentifier, v)] -> m v
    merge name xs = case M.toList $ M.fromListWith (<>) $ fmap (\(x,y) -> (y,[x])) xs of
        [] -> error "unreachable" --from the definition of transpose
        xs@(_:_:_) -> createError name $ fmap snd $ toList xs --todo error messages
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

--broken
-- topDown :: ((a,b) -> (c,b)) -> b -> Tree' a -> Tree' c
-- topDown f b a = runIdentity $ topDownM (Identity . f) b a

-- topDownM :: (Monad m) => ((a,b) -> m (c,b)) -> b -> Tree' a -> m (Tree' c)
-- topDownM f = go where
--     go b (Node a as) = do
--         (c, b') <- f (a,b)
--         as' <- traverse (go b') as
--         return $ Node c as'

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
findLast overwrites = errorContext "findLast" $ do
    dependencies <- dependencies
    let ((candidate, value):_) = reverse $ dependencyOrder dependencies overwrites
    case filter (\(c', _) -> candidate /= c' && not (dependsOn dependencies candidate c')) overwrites of
        [] -> return (candidate, value)
        ((x,_):_) -> mergeErrorUnresolvedOrderingOverwrite x candidate
restrictLaterThan :: (MonadMerge m) => ModuleIdentifier -> [(ModuleIdentifier, a, b)] -> m [(ModuleIdentifier, b)]
restrictLaterThan o = fmap catMaybes . traverse (\(m,_,v) -> errorContext "restrictLaterThan" $ do
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
    f i = fmap reconstruct $
            traverse (resolveConflicts f) $
            groupAndWildcards wildcards $
            concatMap (\(moduleIdent, xs) -> fmap (\(mode, ident, val) -> (moduleIdent, mode, ident, val)) xs) $
            M.toList $
            fmap (concatMap destruct)
            i

groupAndWildcards :: (Ord i, Ord m) => (i -> j -> Bool) -> [(ModuleIdentifier, m, Either i j, a)] -> Map i [(ModuleIdentifier, m, a)]
groupAndWildcards wildcards = fmap reverse . fst . foldl (\(m,w) (moduleIdent, mode, ident, val) -> case ident of
    Left ident ->
        let newVal = (moduleIdent, mode, val)
            wildcarded = mapMaybe (\(moduleIdent, mode, wildcardIdent, val) -> if wildcards ident wildcardIdent then Just (moduleIdent, mode, val) else Nothing) w
        in (M.alter (Just . maybe (newVal : wildcarded) (newVal :) ) ident m,w)
    Right wildcard -> (M.mapWithKey (\ident xs -> if wildcards ident wildcard then (moduleIdent, mode, val) : xs else xs) m, (moduleIdent, mode, wildcard, val) : w)
    ) (M.empty, [])

resolveConflicts' :: (MonadMerge m) => (Map ModuleIdentifier [a] -> m (b, Bool)) -> [(ModuleIdentifier, L.Mode, a)] -> m (b, Bool)
resolveConflicts' = undefined

-- mergeRecursively' :: forall m a i j b. (MonadMerge m) => (a -> [(L.Mode, Either i j, a)]) -> (i -> Bool) -> (i -> j -> Bool) -> ([(i,b)] -> b) -> Map ModuleIdentifier [a] -> m b
-- mergeRecursively' deconstruct mayMultiDefine wildcards reconstruct = f where
--     f i = fmap reconstruct $
--             traverse (resolveConflicts' f) $ b i --todo
--     b :: Map ModuleIdentifier [a] -> Map i [(ModuleIdentifier, L.Mode, a)] -- Compose (Map ModuleIdentifier) [] ~> Compose (Map i) (Compose [] (ModuleIdentifier, L.Mode, ))
--     b i = groupAndWildcards' wildcards $
--             M.toList $
--             fmap (concatMap destruct) i

data CreationRole = NewDecl | Modify | ModifyIfExists | Append | Override | OverrideOrCreate | AppendIfExists | OverrideIfExists

remainEmpty NewDecl = False
remainEmpty Modify = False
remainEmpty ModifyIfExists = True
remainEmpty Append = False
remainEmpty Override = False
remainEmpty OverrideOrCreate = False
remainEmpty AppendIfExists = True
remainEmpty OverrideIfExists = True

createsStuff NewDecl = True
createsStuff Modify = False
createsStuff ModifyIfExists = False
createsStuff Append = False
createsStuff Override = False
createsStuff OverrideOrCreate = True
createsStuff AppendIfExists = False
createsStuff OverrideIfExists = False

isOverride NewDecl = True
isOverride Modify = False
isOverride ModifyIfExists = False
isOverride Append = False
isOverride Override = True
isOverride OverrideOrCreate = True
isOverride AppendIfExists = False
isOverride OverrideIfExists = True

isModify NewDecl = False
isModify Modify = True
isModify ModifyIfExists = True
isModify Append = False
isModify Override = False
isModify OverrideOrCreate = False
isModify AppendIfExists = False
isModify OverrideIfExists = False

isNewDecl NewDecl = True
isNewDecl Modify = False
isNewDecl ModifyIfExists = False
isNewDecl Append = False
isNewDecl Override = False
isNewDecl OverrideOrCreate = False
isNewDecl AppendIfExists = False
isNewDecl OverrideIfExists = False

resolveOverrides :: (MonadMerge m) => [(ModuleIdentifier, Bool, a)] -> m [(ModuleIdentifier, a)]
resolveOverrides xs = do
    (x, y) <- findLast $ fmap (\(a,b,c) -> (a,c)) $ filter (^. _2) xs
    ((x,y):) <$> restrictLaterThan x xs

resolveNewdecls :: (MonadMerge m) => [(ModuleIdentifier, Bool, a)] -> m [(ModuleIdentifier, a)]
resolveNewdecls xs = errorContext "resolveNewdecls" $
    case (filter (^. _2) xs) of
        [] -> errorGenericMergeError 1
        [(x,_,y)] -> do
            dependencies <- dependencies
            if all (\(x',b,_) -> b || dependsOn dependencies x' x) xs then return [(x,y) | (x,_,y) <- xs]
            else errorGenericMergeError 2
        _ -> errorGenericMergeError 3

merge1 :: (MonadMerge m) => [(ModuleIdentifier, CreationRole, r)] -> m [(ModuleIdentifier, r)] --allow one newdecl, appends, modifys and overrides
merge1 stuff = errorContext "merge1" $
    if | all (^. _2 . to remainEmpty) stuff -> return []
       | any (^. _2 . to createsStuff) stuff -> do
            resolveOverrides $ [(moduleId, isOverride role, payload) | (moduleId, role, payload) <- stuff]
            -- let x = M.fromListWith (<>) [(key, [(moduleId, isAppendy, payload')]) | (moduleId, (isAppendy, payload)) <- remainingStuff, (key, payload') <- payload]
            -- traverse resolveNewdecls x
       | otherwise -> errorGenericMergeError 4

merge2 :: (MonadMerge m) => [(ModuleIdentifier, CreationRole, r)] -> m [r] --allow multiple newdecls, no appends, no modifys but overrides. Overrides conflict with newdecls when unordered
merge2 stuff = errorContext "merge2" $
    if | any (^. _2 . to (not . isOverride)) stuff -> errorGenericMergeError 5
       | all (^. _2 . to isNewDecl) stuff -> return $ stuff ^.. traverse . _3
       | otherwise -> map snd <$> resolveOverrides [(moduleId, not (isNewDecl role), payload) | (moduleId, role, payload) <- stuff]

determineCreationRole :: Tree'F L.Mode CreationRole -> CreationRole
determineCreationRole (NodeF L.ModeDefault []) = NewDecl
determineCreationRole (NodeF L.ModeDefault xs) | any isNewDecl xs = NewDecl
                                               | all remainEmpty xs = ModifyIfExists
                                               | otherwise = Modify
determineCreationRole (NodeF L.ModeAppend _) = Append
determineCreationRole (NodeF L.ModeReplace _) = Override
determineCreationRole (NodeF L.ModeAppendIfExists _) = AppendIfExists
determineCreationRole (NodeF L.ModeReplaceIfExists _) = OverrideIfExists
determineCreationRole (NodeF L.ModeReplaceOrCreate _) = OverrideOrCreate

determineCreationRoles :: Tree' (L.Value, L.Mode) -> Cofree (Tree'F (L.Value, L.Mode)) CreationRole
determineCreationRoles = zygo f g where
    f = determineCreationRole . (\(NodeF (_,a) b) -> NodeF a b)
    g x = f (fmap fst x) CF.:< fmap snd x

split :: (ModuleIdentifier, Cofree (Tree'F (L.Value, L.Mode)) CreationRole) -> (L.Value, Either (ModuleIdentifier, CreationRole, [Cofree (Tree'F (L.Value, L.Mode)) CreationRole]) (ModuleIdentifier, CreationRole, Forest' L.Value))
split (moduleId, role CF.:< (NodeF (val, _) r)) = (val, b) where
    b = case val of
        L.Edge _ _ -> Right c
        L.EdgeUndirected _ _ -> Right c
        _ -> Left (moduleId, role, r)
    c :: (ModuleIdentifier, CreationRole, Forest' L.Value)
    c = (moduleId, role, fmap (fmap fst . hoist (\(_ CFT.:< t') -> t')) r)

mergeLogic' :: (MonadMerge m) => Map ModuleIdentifier [Forest' (L.Value, L.Mode)] -> m (Forest' L.Value)
mergeLogic' = errorContext "mergeLogic'" . helper . fmap (fmap determineCreationRoles . concat) where
    helper :: (MonadMerge m) => Map ModuleIdentifier [Cofree (Tree'F (L.Value, L.Mode)) CreationRole] -> m (Forest' L.Value)
    helper = fmap (concatMap snd . M.toList) . M.traverseWithKey (\k v -> errorContext ("helper1 on " <> (T.pack $ show k)) $ helper1 k v) . M.fromListWith (<>) . fmap ((\(a,b) -> (a,[b])) . split) . concatMap (\(a,b) -> (,) a <$> b) . M.toList
    helper1 :: (MonadMerge m) => L.Value -> [Either (ModuleIdentifier, CreationRole, [Cofree (Tree'F (L.Value, L.Mode)) CreationRole]) (ModuleIdentifier, CreationRole, Forest' L.Value)] -> m (Forest' L.Value)
    helper1 v xs = case partitionEithers xs of
        ([], rs) -> fmap (fmap (Node v)) $ merge2 $ rs
        (rs, []) -> do
            xs <- merge1 $ rs
            fmap ((:[]) . Node v) $ helper $ M.fromListWith (<>) xs

--_ :: [(ModuleIdentifier, CreationRole, a)] -> m [(CreationRole, a)]

-- thing :: (Base f CreationRole -> CreationRole) -> ([(ModuleIdentifier, Base f (Cofree (Base f) CreationRole))] -> Base g (_)) -> Map ModuleIdentifier [f] -> g
-- thing = undefined

-- groupAndWildcards' :: (Ord b) => (i -> j -> Bool) -> [(ModuleIdentifier, b, Either i j, a)] -> Map i (Map (ModuleIdentifier, b) [a])
-- groupAndWildcards' wildcards = conv . groupAndWildcards wildcards where
--     conv :: (Ord a, Ord b, Ord c) => Map a [(b,c,d)] -> Map a (Map (b,c) [d])
--     conv = fmap (\xs -> M.fromListWith (<>) [((a,b),[c]) | (a,b,c) <- xs])
    --conv = fmap (M.fromListWith (<>)) . M.fromListWith (<>) . (\x -> [(a,[((c, b),[d])]) | (a,bcds) <- x, (b,c,d) <- bcds]) . M.toList

--todo: appends to nothing don't error, multiple newdecls don't error (where not permitted)
mergeLogic :: (MonadMerge m) => Map DescriptorName DescriptorDeclaration -> Map ModuleIdentifier [Forest] -> m (Forest' L.Value)
mergeLogic descriptors sources = errorContext "mergeLogic" $ traverse (traverse $ fullyScopeNames descriptors . directEdges . generalizeForest) sources >>= mergeLogic' where
    f :: (MonadMerge m) => Map ModuleIdentifier [Forest' (L.Value, L.Mode)] -> m (Forest' L.Value)
    f = mergeRecursively
            destruct
            (flip wildcardMatches)
            reconstruct
    destruct :: Forest' (L.Value, L.Mode) -> [(L.Mode, Either L.Value L.Value, Forest' (L.Value, L.Mode))]
    --destruct (project -> NodeF (val,mode) xs) = fmap (\x -> (mode, (if hasWildcard val then Right else Left) val, x)) xs
    destruct = fmap $ \(project -> NodeF (val, mode) xs) -> (mode, (if hasWildcard val then Right else Left) val, xs)
    reconstruct :: Map i (Forest' i) -> Forest' i
    reconstruct = fmap (embed . uncurry NodeF) . M.toList
    hasWildcard (L.Anon _) = False
    hasWildcard (L.NamedScoped _ name) = hasWildcard' name
    hasWildcard (L.NamedScoping _ name) = hasWildcard'' name
    hasWildcard (L.Edge name name2) = hasWildcard' name || hasWildcard' name2
    --hasWildcard (L.EdgeUndirected name name2) = hasWildcard' name || hasWildcard' name2
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
    directEdges :: Forest' (L.Value, a) -> Forest' (L.Value, a)
    directEdges = fmap (embed . (\(NodeF x ys) -> NodeF x $ directEdges ys) . project). concatMap (\case 
        Node (L.EdgeUndirected x y, mode) children -> [Node (L.Edge x y, mode) children, Node (L.Edge y x, mode) children]
        x -> [x])

fullyScopeNames :: (MonadMerge m) => Map DescriptorName DescriptorDeclaration -> Forest' (L.Value, L.Mode) -> m (Forest' (L.Value, L.Mode))
--fullyScopeNames = traverse (topDownM (\((value, mode), scope) -> fmap (\(value', scope') -> ((value', mode), scope)) (scopeStep value scope )) [])
fullyScopeNames descriptors = errorContext "fullyScopeNames" . fullyScopeNames' [] where
    fullyScopeNames' :: (MonadMerge m) => [L.Name] -> Forest' (L.Value, L.Mode) -> m (Forest' (L.Value, L.Mode))
    fullyScopeNames' scope = traverse (fmap embed . (\(NodeF (val, mode) ys) -> do
            (val', scope') <- scopeStep descriptors val scope
            ys' <- fullyScopeNames' scope' ys
            return $ NodeF (val', mode) ys'
        ) . project)

scopeStep :: (MonadMerge m) => Map DescriptorName DescriptorDeclaration -> L.Value -> [L.Name] -> m (L.Value, [L.Name])
scopeStep descriptors value scope = errorContext "scopeStep" $ case value of
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


transformLogic :: forall m. (MonadMerge m) => Map DescriptorName DescriptorDeclaration -> Forest' L.Value -> m (TaggedGraph (Join (DNF (DescriptorName, [Thingy]))) (Maybe L.LogicNodeName), Map L.LogicNodeName [(DescriptorName, [Thingy])])
transformLogic descriptors forest = errorContext "transformLogic" $ g <$> traverse f forest where
    g = (foldr (\(g, m) (g', m') -> (g <> g', M.unionWith (<>) m m')) (mempty, mempty))
    f :: Tree' L.Value -> m (TaggedGraph (Join (DNF (DescriptorName, [Thingy]))) (Maybe L.LogicNodeName), Map L.LogicNodeName [(DescriptorName, [Thingy])])
    f (Node (L.NamedScoping _ _) forest) = g <$> traverse f forest
    f (Node (L.NamedScoped "node" logicNodeName) forest) = g <$> traverse (nodeDescr logicNodeName) forest
    f (Node (L.Edge source target) desc) = ((,)) . (\e -> taggedEdge (Join e) (Just source) (Just target)) <$> ((getMeet . foldMap Meet) <$> traverse descrRule desc) <*> pure M.empty
    --f (Node (L.EdgeUndirected source target) desc) = ((,)) . (\e -> taggedEdge e (Just source) (Just target) <> taggedEdge e (Just target) (Just source)) <$> ((getJoin . foldMap Join) <$> traverse descrRule desc) <*> pure M.empty --cleared out in mergeLogic
    nodeDescr :: L.LogicNodeName -> Tree' L.Value -> m (TaggedGraph (Join (DNF (DescriptorName, [Thingy]))) (Maybe L.LogicNodeName), Map L.LogicNodeName [(DescriptorName, [Thingy])])
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
                Just DescriptorExportSelfEdge -> return (taggedEdge (Join $ singleToDNF (descr, [])) (Just name) (Just name), mempty)
                Just DescriptorExportEdgeFromBeyondTheVoid -> return (taggedEdge (Join $ singleToDNF (descr, [])) Nothing (Just name), mempty)
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
                Just DescriptorExportSelfEdge -> return (taggedEdge (Join $ singleToDNF (descr, [nonWildcardScopedName arg])) (Just name) (Just name), mempty)
                Just DescriptorExportEdgeFromBeyondTheVoid -> return (taggedEdge (Join $ singleToDNF (descr, [nonWildcardScopedName arg])) Nothing (Just name), mempty)
                Just DescriptorExportTarget -> return (mempty, M.singleton name [(descr,[nonWildcardScopedName arg])])
    nodeDescr _ _ = errorGenericMergeError 6
    descrRule :: (MonadMerge m) => Tree' L.Value -> m (DNF (DescriptorName, [Thingy]))
    descrRule (Node (L.Anon "and") xs) = (getMeet . foldMap Meet) <$> traverse descrRule xs --todo: forbid reserved names "and" and "or" to be declared as descriptors
    descrRule (Node (L.Anon "or") xs)  = (getJoin . foldMap Join) <$> traverse descrRule xs
    descrRule (Node (L.Anon descr) xs) = case M.lookup descr descriptors of
        Nothing -> errorDescriptorNotDeclared descr
        Just def -> do
            unless (def ^. descriptorDeclarationArguments . to null) $ errorDescriptorArgsMismatch descr (def ^. descriptorDeclarationArguments) 0
            unless ((def ^. descriptorDeclarationType) == Truthy) $ errorDescriptorTypeMismatch descr County Truthy
            unless (null xs) $ warningIgnoredLogicSubtree xs
            case def ^. descriptorDeclarationExport of
                Just DescriptorExportEdge -> return $ singleToDNF $ (descr, [])
                _ -> errorDescriptorNotDeclared descr
    descrRule (Node (L.NamedScoped descr arg) xs) = case M.lookup descr descriptors of
        Nothing -> errorDescriptorNotDeclared descr
        Just def -> do
            unless ((def ^. descriptorDeclarationArguments . to length)  == 1) $ errorDescriptorArgsMismatch descr (def ^. descriptorDeclarationArguments) 1
            unless ((def ^. descriptorDeclarationType) == Truthy) $ errorDescriptorTypeMismatch descr County Truthy
            unless (null xs) $ warningIgnoredLogicSubtree xs
            case def ^. descriptorDeclarationExport of
                Just DescriptorExportEdge -> return $ singleToDNF $ (descr, [nonWildcardScopedName arg])
                _ -> errorDescriptorNotDeclared descr
    descrRule _ = errorGenericMergeError 7

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
    , _defLogic :: (TaggedGraph (Join (DNF (DescriptorName, [Thingy]))) (Maybe L.LogicNodeName), Map L.LogicNodeName [(DescriptorName, [Thingy])])
    , _defPatches :: Map ModuleIdentifier (FilePath, [ResourceSpecifier])
    , _defLogicData :: LogicData
    , _defShuffles :: Map ShuffleName (ShuffleInstruction, [ShuffleInstruction])
    } deriving (Eq, Ord)

$(makeLenses ''GameDef)

mergeHeader :: (MonadMerge m) => Map ModuleIdentifier ModuleHeader -> m ModuleHeader
mergeHeader headers = do
    descrs <- mergeDescriptorDeclarations $ fmap (^. moduleHeaderDescriptors) headers
    sugar <- mergeSugar $ fmap (^. moduleHeaderLogicSugar . from sugars) headers
    return $ ModuleHeader descrs (sugar ^. sugars)


mergeContent :: (MonadMerge m) => ModuleHeader -> Map ModuleIdentifier (FilePath, ModuleFullContent) -> m GameDef
mergeContent header modules = do
    let descriptors = header ^. moduleHeaderDescriptors
    --mergeDescriptorDeclarations $ fmap (^. _2 . moduleFullContentDescriptors) modules
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