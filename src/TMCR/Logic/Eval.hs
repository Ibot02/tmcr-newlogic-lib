{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeApplications #-}
module TMCR.Logic.Eval where

import TMCR.Logic.Common
import TMCR.Logic.Descriptor (Oolean (..), DescriptorName, DescriptorIdent (..), Descriptor (..), Literal (..), DescriptorRule' (..), DescriptorType(..), DescriptorRule, Value (..), SDescriptorType (..), Value' (..), Relation (..))
import TMCR.Logic.Shuffle (ShuffleName)
import TMCR.Logic.Merge (GameDef(..), defLogic, defDescriptorDefinitionsCounty, defDescriptors)
import TMCR.Logic.Descriptor (DescriptorDeclaration(..), DescriptorExport(..), descriptorDeclarationArguments)

import Data.Array (Array)
import qualified Data.Array as A
import Data.Set (Set())
import qualified Data.Set as S
import Data.Map (Map())
import qualified Data.Map as M
import Data.IntMap (IntMap())
import qualified Data.IntMap as IM
import Data.IntSet (IntSet())
import qualified Data.IntSet as IS
import Data.Map.Monoidal (MonoidalMap)
import qualified Data.Map.Monoidal as MM
import qualified Data.Graph as G
import Data.Maybe (mapMaybe, isNothing, catMaybes, isJust, fromJust)
import Control.Monad (forM, forM_, MonadPlus (..), when)
import Control.Monad.Fix (MonadFix (..))
import Control.Arrow (second, Arrow (..), ArrowApply (app))
import Control.Monad.Writer.CPS (MonadTrans(..), MonadWriter (..), WriterT(..))
import Control.Monad.Reader (ReaderT(..), MonadReader, asks)
import Control.Monad.Trans.Writer.CPS (runWriterT, execWriterT)
import Control.Comonad.Trans.Env (EnvT(..), lowerEnvT)

import Data.Text (Text)
import qualified Data.Text as T
import TMCR.Logic.Logic (LogicNodeName)
import qualified TMCR.Logic.Logic as L

import qualified TMCR.Logic.Graphs as G
import TMCR.Logic.Algebra (Join(..), DNF (..), Lattice (join), singleToDNF)
import Control.Monad.State (StateT (runStateT), execStateT, MonadState (..), evalState, gets)
import qualified Control.Monad.State.Strict as S

import Control.Lens
import Control.Lens.TH
import Control.Monad.Trans.Maybe (MaybeT(..))
import Data.Foldable (Foldable(..))
import qualified Data.Monoid as Mon
import Debug.Trace (traceShowM)
import Control.Monad.Trans.Free
import Control.Comonad (Comonad(..))
import qualified Algebra.Graph.Labelled as LG
import Text.Read (readMaybe)
import TMCR.Logic.NewShuffle (ShuffleIdent)
import Data.Functor.Classes (Show1 (..))

type StatementID = Int
type CountyStatementID = Int
type Statement = StatementF StatementID

data Definitions = Definitions {
      statements :: Array StatementID (Statement, Int) -- statement, together with the number of columns its evaluation has
    , statementNames :: Map (Role, DescriptorName) StatementID
    , definitionsGoalStatement :: StatementID
    , countyStatments :: () --todo
}

data StatementF a =
      UnionStatement [a]
    | ProjectStatement a [Pattern Int]
    | JoinStatement a a [(Int, Int)]
    | ShuffleStatement ShuffleIdent
    | ConstantStatement [(Oolean, [Thingy])]
    | AtLeastStatement CountyStatementID Nteger
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Show1 StatementF where
    liftShowsPrec showsPrec' showList' prec s = showParen (prec > 10) $ case s of
        UnionStatement xs -> showString "UnionStatement " . showList' xs
        ProjectStatement x patt -> showString "ProjectStatement " . showsPrec' 11 x . showString " " . showList patt
        JoinStatement x y on -> showString "JoinStatement " . showsPrec' 11 x . showString " " . showsPrec' 11 y . showString " " . showList on
        ShuffleStatement ident -> showString "ShuffleStatement " . showsPrec 11 ident
        ConstantStatement c -> showString "ConstantStatement " . showList c
        AtLeastStatement c n -> showString "AtLeastStatement " . showsPrec 11 c . showString " " . showsPrec 11 n

data Pattern a = Any | Match a deriving (Eq, Ord, Show)

data WithIDPool i a = WithIDPool { runWithIDPool :: [i] -> (Int, a) } deriving (Functor)

instance Applicative (WithIDPool i) where
    pure x = WithIDPool $ \_ -> (0, x)
    WithIDPool f <*> WithIDPool g = WithIDPool $ \ids -> let (n, x) = f ids; (n', y) = g (drop n ids) in (n + n', x y)

instance Monad (WithIDPool i) where
    return = pure
    (>>=) :: WithIDPool i a -> (a -> WithIDPool i b) -> WithIDPool i b
    WithIDPool f >>= g = WithIDPool $ \ids -> let (n, x) = f ids; (n', y) = runWithIDPool (g x) (drop n ids) in (n + n', y)

instance MonadFix (WithIDPool i) where
    mfix f = WithIDPool $ \ids -> let x = runWithIDPool (f $ snd x) ids in x

class (Monad m) => MonadWithIDPool i m | m -> i where
    getID :: m i

instance MonadWithIDPool i (WithIDPool i) where
    getID = WithIDPool $ \(i:_) -> (1, i)

instance (Monoid w, MonadWithIDPool i m) => MonadWithIDPool i (WriterT w m) where
    getID = lift getID

instance (MonadWithIDPool i m) => MonadWithIDPool i (ReaderT r m) where
    getID = lift getID

instance (MonadWithIDPool i m) => MonadWithIDPool i (StateT s m) where
    getID = lift getID

instance (MonadWithIDPool i m) => MonadWithIDPool i (S.StateT s m) where
    getID = lift getID

evalWithIDPool m = snd . runWithIDPool m

data Role = Defined | Exported deriving (Eq, Ord, Show)

$(makePrisms ''StatementF)
$(makePrisms ''Pattern)

compile :: GameDef -> Definitions
compile gameDef = f' a where
    logicGraph' = simplifyLogic $ gameDef ^. defLogic . _1
    f' x = flip evalWithIDPool [0..] $ do
        (names, stmts) <- x
        (names', (stmts', _)) <- flip runStateT (stmts, IM.empty) $ do
            optimize names
            names' <- zoom _2 $ applyTranslations names
            zoom _1 $ restrictUsed' names'
            issues <- zoom _1 findIssues
            case issues of
                [] -> return ()
                _ -> error $ "Issues after restrict used"--unlines ("After restrict used:" : issues)
            removeGaps
            issues <- zoom _1 findIssues
            case issues of
                [] -> return ()
                _ -> error $ unlines ("After remove gaps:" : issues)
            zoom _2 $ applyTranslations names
        return $ definitionsFromStatements stmts' names'
    a :: WithIDPool StatementID (Map (Role, DescriptorName) StatementID, IntMap (Statement, Int))
    a = fmap (second IM.fromList) $ runWriterT $ do
        rec (descriptorNames, reachableNodesStmt) <- do
                descriptorNames' <- runReaderT (descriptorStatements reachableNodesStmt) descriptorNames
                reachableNodesStmt' <- logicStatements descriptorNames reachableNodesStmt
                return (descriptorNames', reachableNodesStmt')
        return descriptorNames
    logicTargets :: Map DescriptorName [(LogicNodeName, [Thingy])]
    logicTargets = M.fromListWith (<>) $ [(d, [(n, args)]) | (n, ds) <- M.toList $ snd $ _defLogic gameDef, (d, args) <- ds]
    descriptorStatements :: (MonadWriter [(StatementID, (Statement, Int))] m, MonadReader (Map (Role, DescriptorName) StatementID) m, MonadWithIDPool StatementID m) => StatementID -> m (Map (Role, DescriptorName) StatementID)
    descriptorStatements reachableNodes = do
        truthies <- flip M.traverseWithKey (_defDescriptorDefinitionsTruthy gameDef) $ \name defs -> forM defs $ \def -> do
            mkDescriptorStatement def
        fmap M.fromList $ forM (M.toList $ _defDescriptors gameDef) $ \(name, decl) -> do
            let numArgs = length $ _descriptorDeclarationArguments decl
            if (_descriptorDeclarationExport decl == Just DescriptorExportTarget)
            then do
                let nodesWithArgs = M.findWithDefault [] name logicTargets
                i <- makeStatement (numArgs + 1) $ ConstantStatement $ fmap (\(n, args) -> (OolTrue, asThingy n : args)) nodesWithArgs
                j <- makeStatement (numArgs + 1) $ JoinStatement reachableNodes i [(0,0)]
                p <- makeStatement numArgs $ ProjectStatement j $ take numArgs $ fmap Match [1..]
                return ((Exported, name), p)
            else do
                let ids = M.findWithDefault [] (TruthyDescriptorIdent name) truthies
                i <- case ids of
                    [i] -> return i
                    us -> makeStatement numArgs $ UnionStatement us
                return ((Defined, name), i)
    asThingy :: LogicNodeName -> Thingy
    asThingy (L.Global n) = Global $ asText n
    asThingy (L.Scoped ns) = ScopedName $ fmap asText ns
    asThingy L.FullWildcard = error "unexpected wildcard"
    asText :: L.Name -> Text
    asText (L.PlainName t) = t
    asText (L.QuotedName t) = t
    asText L.Wildcard = error "unexpected wildcard"
    logicStatements :: (MonadWithIDPool StatementID m, MonadWriter [(StatementID, (Statement, Int))] m) => Map (Role, DescriptorName) StatementID -> StatementID -> m StatementID
    logicStatements names reachable = do
        let edges = LG.edgeSet logicGraph'
            edgesFromBeyondTheVoid = M.fromListWith (<>) [(e, [(args, n)]) | (es, Nothing, Just n) <- S.toList edges, (ConditionalEdge (e, args)) <- es]
            unconditionalReachable = S.fromList [n | (es, Nothing, Just n) <- S.toList edges, UnconditionalEdge <- es]
            innerUnconditionalEdges = S.fromList [(s,t) | (es, Just s, Just t) <- S.toList edges, UnconditionalEdge <- es]
            innerEdges = M.fromListWith (<>) [(e, [(source, args, target)]) | (es, Just source, Just target) <- S.toList edges, (ConditionalEdge (e, args)) <- es]
        initialReachable' <- forM (M.toList edgesFromBeyondTheVoid) $ \(descriptorName, rows) -> do
            let x = names M.! (Defined, descriptorName)
                [d] = gameDef ^.. defDescriptors . at descriptorName . _Just . descriptorDeclarationArguments . to length
            c <- makeStatement (d + 1) $ ConstantStatement $ fmap (\(args, target) -> (OolTrue, args <> [asThingy target])) rows
            j <- makeStatement (d + 1) $ JoinStatement x c $ [(i, i) | i <- [0..(d-1)]]
            if (d == 0) then return j else makeStatement 1 $ ProjectStatement j [Match d]
        initialReachable <- if null unconditionalReachable then return initialReachable' else do
            s <- makeStatement 1 $ ConstantStatement $ fmap (\n -> (OolTrue, [asThingy n])) $ S.toList unconditionalReachable
            return $ s : initialReachable'
        reachableByEdge' <- forM (M.toList innerEdges) $ \(descriptorName, rows) -> do
            let x = names M.! (Defined, descriptorName)
                [d] = gameDef ^.. defDescriptors . at descriptorName . _Just . descriptorDeclarationArguments . to length
            c <- makeStatement (d + 2) $ ConstantStatement $ fmap (\(source, args, target) -> (OolTrue, args <> [asThingy source, asThingy target])) rows
            j <- makeStatement (d + 2) $ JoinStatement x c $ [(i,i) | i <- [0.. d-1]]
            p <- makeStatement 2 $ ProjectStatement j [Match d, Match (d+1)]
            j' <- makeStatement 2 $ JoinStatement reachable p [(0,0)] 
            makeStatement 1 $ ProjectStatement j' [Match 1]
        reachableByEdge <- if null innerUnconditionalEdges then return reachableByEdge' else do
            c <- makeStatement 2 $ ConstantStatement $ fmap (\(s,t) -> (OolTrue, [asThingy s, asThingy t])) $ S.toList innerUnconditionalEdges
            j <- makeStatement 2 $ JoinStatement reachable c [(0,0)]
            s <- makeStatement 1 $ ProjectStatement j [Match 1]
            return $ s : reachableByEdge'
        makeStatement 1 $ UnionStatement $ initialReachable <> reachableByEdge
    logicStatements' :: (MonadWithIDPool StatementID m, MonadWriter [(StatementID, (Statement, Int))] m) => Map (Role, DescriptorName) StatementID -> StatementID -> m StatementID
    logicStatements' names reachable = do
        us <- forM (G.taggedGetEdges $ fst $ _defLogic gameDef) $ \(fromNode, rules, toNode) -> forM (S.toList $ getDisjunctions $ getJoin rules) $ \d -> do
            let conj (name, args) acc = do
                    let x = names M.! (Defined, name)
                    c <- makeStatement (length args) $ ConstantStatement [(OolTrue, args)]
                    s <- makeStatement (length args) $ JoinStatement c x $ take (length args) $ fmap (\i -> (i, i)) [0..]
                    p <- makeStatement 0 $ ProjectStatement s []
                    a <- acc
                    makeStatement 0 $ JoinStatement p a []
            r <- S.foldr conj (makeStatement 0 $ ConstantStatement [(OolTrue, [])]) d --todo: use fromNode, toNode and reachable
            case (fromNode, toNode) of
                (Just fromNode', Just toNode') -> do
                    c <- makeStatement 2 $ ConstantStatement [(OolTrue, [asThingy fromNode', asThingy toNode'])]
                    j <- makeStatement 2 $ JoinStatement reachable c [(0,0)]
                    j' <- makeStatement 2 $ JoinStatement j r []
                    makeStatement 1 $ ProjectStatement j' [Match 1]
                (Nothing, Just toNode') -> do
                    c <- makeStatement 1 $ ConstantStatement [(OolTrue, [asThingy toNode'])]
                    makeStatement 1 $ JoinStatement c r []
                (_, Nothing) -> error "logic edge to the void"
        makeStatement 1 $ UnionStatement $ concat us
    mkDescriptorStatement :: (MonadWriter [(StatementID, (Statement, Int))] m, MonadReader (Map (Role, DescriptorName) StatementID) m, MonadWithIDPool StatementID m) => Descriptor Truthy -> m StatementID
    mkDescriptorStatement (Descriptor args rule) = do
        (s, vars) <- fromRule rule
        let constantArgs = zip args [0.. ]>>= \case
                (Variable v, _) -> []
                (ConstantValue c, i) -> [(c,i)]
            variableArgs = zip args [0..] >>= \case
                (Variable v, i) -> [(v, i)]
                (ConstantValue c, _) -> []
            toProj (Variable v) _ = case filter ((== v) . fst) (zip vars [length constantArgs..]) of
                    [] -> Any
                    (_,i):_ -> Match i
            toProj (ConstantValue _) i = Match $ snd $ head $ filter ((== i) . fst) $ zip (fmap snd constantArgs) [0..]
        c <- makeStatement (length constantArgs) $ ConstantStatement [(OolTrue, fmap fst constantArgs)]
        j <- makeStatement (length constantArgs + length vars) $ JoinStatement c s []
        makeStatement (length args) $ ProjectStatement j $ fmap (uncurry toProj) $ zip args [0..]
    fromRule :: (MonadWriter [(StatementID, (Statement, Int))] m, MonadReader (Map (Role, DescriptorName) StatementID) m, MonadWithIDPool StatementID m, Ord v) => DescriptorRule' Truthy v -> m (StatementID, [v])
    fromRule (Constant (TruthyLiteral t)) = do
        i <- makeStatement 0 $ ConstantStatement [(t, [])]
        return (i, [])
    fromRule (IsEqual (Variable v) (Variable v')) | v == v' = do
        t <- makeStatement 0 $ ConstantStatement [(OolTrue, [])]
        refl <- makeStatement 1 $ ProjectStatement t [Any]
        return (refl, [v])
    fromRule (IsEqual (Variable v) (Variable v')) = do
        t <- makeStatement 0 $ ConstantStatement [(OolTrue, [])]
        refl <- makeStatement 1 $ ProjectStatement t [Any]
        eq <- makeStatement 2 $ ProjectStatement refl [Match 0, Match 0]
        return (eq, [v, v'])
    fromRule (IsEqual (Variable v) (ConstantValue t)) = fmap (\x -> (x, [v])) $ makeStatement 1 $ ConstantStatement [(OolTrue, [t])]
    fromRule (IsEqual a@(ConstantValue t) b@(Variable v)) = fromRule (IsEqual b a)
    fromRule (IsEqual (ConstantValue t) (ConstantValue t')) | t == t' = fmap (\x -> (x, [])) $ makeStatement 0 $ ConstantStatement [(OolTrue, [])]
                                                            | otherwise = fmap (\x -> (x, [])) $ makeStatement 0 $ ConstantStatement []
    fromRule (CallDescriptor STruthy name args) = call (Defined, name) args
    fromRule (CanAccess STruthy name args _) = call (Exported, name) args
    fromRule (AtLeast r n) = do
        (c, vars) <- fromCountyRule r
        s <- makeStatement (length vars) $ AtLeastStatement c n
        return (s, vars)
    fromRule (Exist rel (Variable v) r) = do
        (c, vars) <- fromRule r
        (s, a, b) <- fromRel rel
        let vars' = catMaybes vars
        j <- makeStatement (length vars' + 2) $ JoinStatement s c $ fmap ((,) b . snd) $ filter (isNothing . fst) $ zip vars [0..]
        p <- makeStatement (length vars' + 1) $ ProjectStatement j (Match a: fmap Match [2..length vars' + 1])
        if v `elem` vars'
        then do
            t <- makeStatement 0 $ ConstantStatement [(OolTrue, [])]
            p' <- makeStatement 1 $ ProjectStatement t [Any]
            j' <- makeStatement (length vars') $ JoinStatement p p' $ ((0,0):) $ fmap ((,) 0 . snd) $ filter ((==v) . fst) $ zip vars' [0..] --todo: check semantics
            return (j', v : filter (/= v) vars')
        else return (p, v:vars')
    fromRule (Exist rel (ConstantValue t) r) = do
        (c, vars) <- fromRule r
        (s, a, b) <- fromRel rel
        c' <- makeStatement 1 $ ConstantStatement [(OolTrue, [t])]
        s' <- makeStatement 2 $ JoinStatement s c' [(a, 0)]
        let vars' = catMaybes vars
        j <- makeStatement (length vars' + 2) $ JoinStatement s c $ fmap ((,) b . snd) $ filter (isNothing . fst) $ zip vars [0..]
        p <- makeStatement (length vars') $ ProjectStatement j (fmap Match [2..length vars' + 1])
        return (p, vars')
    fromRule (Min STruthy rs) = foldr fromConj (fmap (\s -> (s,[])) $ makeStatement 0 $ ConstantStatement [(OolTrue, [])]) rs
    fromRule (Max STruthy rs) = do
        xs <- traverse fromRule rs
        let vars = S.toList $ foldMap (S.fromList . snd) xs
            varIndices = M.fromList $ zip vars [0..]
        ps <- forM xs $ \(s, vs) ->
            let vsWithIndices = M.fromList $ zip vs [Match n | n <- [0..]] in
            makeStatement (length vars) $ ProjectStatement s $ fmap (\v -> M.findWithDefault Any v vsWithIndices) vars
        u <- makeStatement (length vars) $ UnionStatement ps
        return (u, vars)
    fromRule (Consume i n vs rs) = error "todo consume"
    fromCountyRule :: (MonadWriter [(StatementID, (Statement, Int))] m, MonadReader (Map (Role, DescriptorName) StatementID) m, MonadWithIDPool StatementID m) => DescriptorRule' County v -> m (StatementID, [v])
    fromCountyRule r = do --todo
        return (0, [])
    fromRel :: (MonadWriter [(StatementID, (Statement, Int))] m, MonadReader (Map (Role, DescriptorName) StatementID) m, MonadWithIDPool StatementID m) => Relation -> m (StatementID, Int, Int)
    fromRel (Forward s) = do
        i <- makeStatement 2 $ ShuffleStatement $ T.unpack s
        return (i, 0, 1)
    fromRel (Backward s) = do
        i <- makeStatement 2 $ ShuffleStatement $ T.unpack s
        return (i, 1, 0)
    fromConj r a = do
        (s, vars) <- fromRule r
        (s', vars') <- a
        let newVars = vars <> filter (not . (`elem` vars)) vars'
        j <- makeStatement (length newVars) $ JoinStatement s s' [(i,j) | (v,i) <- zip vars [0..], (v',j) <- zip vars' [0..], v == v']
        return (j, newVars)

    call r args = do
        let args' = zip args [0..]
            constants = mapMaybe (\case (Variable _, _) -> Nothing; (ConstantValue t, i) -> Just (t, i)) args'
            variables = mapMaybe (\case (Variable v, i) -> Just (v, i); (ConstantValue t, i) -> Nothing) args'
        c <- makeStatement (length constants) $ ConstantStatement [(OolTrue, fmap fst constants)]
        d <- asks (M.findWithDefault (error $ show (fst r) <> " " <> T.unpack (snd r) <> " not in the map") r)
        j <- makeStatement (length args) $ JoinStatement d c $ zip (fmap snd constants) [0..]
        p <- makeStatement (length variables) $ ProjectStatement j $ fmap (Match . snd) variables
        return (p, fmap fst variables)

data EdgeCondition e = ConditionalEdge e | UnconditionalEdge deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

simplifyLogic :: G.TaggedGraph (Join (DNF e)) (Maybe LogicNodeName) -> G.TaggedGraph [EdgeCondition e] (Maybe LogicNodeName)
simplifyLogic logicGraph = allocateNewNames . splitEdges $ logicGraph where
    splitEdges :: G.TaggedGraph (Join (DNF e)) v -> G.TaggedGraph [EdgeCondition e] (Either Int v)
    splitEdges = flip evalWithIDPool [0..] . LG.foldg (return LG.empty) (return . LG.Vertex . Right) splitEdge
    splitEdge :: Join (DNF e) -> WithIDPool i (G.TaggedGraph [EdgeCondition e] (Either i v)) -> WithIDPool i (G.TaggedGraph [EdgeCondition e] (Either i v)) -> WithIDPool i (G.TaggedGraph [EdgeCondition e] (Either i v))
    splitEdge (Join (DNF e)) | null e = liftA2 $ LG.Connect []
                             | otherwise = foldl1 (\f f' g g' -> liftA2 (LG.Connect []) (f g g') (f' g g')) $ fmap (splitConjunction . S.toList) $ S.toList e
    splitConjunction :: [e] -> WithIDPool i (G.TaggedGraph [EdgeCondition e] (Either i v)) -> WithIDPool i (G.TaggedGraph [EdgeCondition e] (Either i v)) -> WithIDPool i (G.TaggedGraph [EdgeCondition e] (Either i v))
    splitConjunction [] = liftA2 $ LG.Connect [UnconditionalEdge]
    splitConjunction [e] = liftA2 $ LG.Connect [ConditionalEdge e]
    splitConjunction (e:es) = \getSource getTarget -> do
        source <- getSource
        target <- getTarget
        v <- getID
        let intermediate = LG.Vertex $ Left v
        later <- splitConjunction es (pure intermediate) (pure target)
        return $ LG.Connect [] (LG.Connect [ConditionalEdge e] source intermediate) later
    allocateNewNames :: (Functor f) => f (Either Int (Maybe LogicNodeName)) -> f (Maybe LogicNodeName)
    allocateNewNames = fmap $ either (Just . newNames) id
    newNames :: Int -> LogicNodeName
    newNames i = L.Global . L.QuotedName . T.pack . show . (i +) $ maybe 0 succ highestPossibleConflict
    usedNames :: [LogicNodeName]
    usedNames = logicGraph ^.. to LG.vertexList . traverse . traverse
    highestPossibleConflict :: Maybe Int
    highestPossibleConflict = S.lookupMax @Int $ S.fromList $ mapMaybe (\case L.QuotedName n -> readMaybe (T.unpack n); _ -> Nothing) $ mapMaybe (\case L.Global a -> Just a; _ -> Nothing) usedNames


removeGaps :: (MonadWithIDPool StatementID m, MonadState (IntMap (Statement, Int), IntMap StatementID) m) => m ()
removeGaps = do
    stmts <- use _1
    stmts' <- forM stmts $ \s -> do
        i <- getID
        return (i, s)
    let idMapping = fmap fst stmts'
        newStatements = IM.fromList $ fmap (\(oldId, (newId, (oldStmt, numCols))) -> (newId, (fmap (idMapping IM.!) oldStmt, numCols))) $ IM.toList stmts'
    _2 %= composeIdMapping idMapping
    _1 .= newStatements

-- given applyIdMap m i = lookupWithDefault i i m,
-- apppyIdMap (composeIdMapping m2 m1) i = applyIdMap m2 (applyIdMap m1 i)
composeIdMapping :: IntMap StatementID -> IntMap StatementID -> IntMap StatementID
composeIdMapping mapping2 mapping1 = IM.compose mapping2 mapping1' where
    mapping1' = IM.union mapping1 $ IM.fromList [(i, i) | i <- IM.keys mapping2, i `IM.notMember` mapping1, i `IS.notMember` mapping1Values]
    mapping1Values = IS.fromList $ toList mapping1

restrictUsed' :: (Traversable t, Foldable f, MonadState (IntMap (t StatementID, Int)) m) => f StatementID -> m ()
restrictUsed' used = do
    (g, fromVertex, toVertex) <- dependencyGraph
    let reachable = foldMap (IS.fromList . fmap ((^. _1) . fromVertex) . maybe [] (G.reachable g) . toVertex) used
    id %= (`IM.restrictKeys` reachable)

restrictUsed :: Foldable t => IntMap (Statement, Int) -> t StatementID -> WithIDPool StatementID (IntMap (Statement, Int))
restrictUsed stmts used = do
    let (g, fromVertex, toVertex) = evalState dependencyGraph stmts
        reachable = foldMap (IS.fromList . fmap ((^. _1) . fromVertex) . maybe [] (G.reachable g) . toVertex) used
    return $ IM.restrictKeys stmts reachable


definitionsFromStatmentsWithGaps :: IntMap (Statement, Int) -> Map (Role, DescriptorName) StatementID -> Definitions
definitionsFromStatmentsWithGaps stmts names = runIdentity $ do
        let stmts' = zip (IM.toList stmts) [0..]
            oldToNewIDs = IM.fromList $ fmap (first fst) stmts'
            minID = 0
            maxID = length stmts' - 1
            stmtArray = A.array (minID, maxID) $ fmap (snd &&& (snd . fst)) stmts'
            names' = case traverse (`IM.lookup` oldToNewIDs) names of
                Just x -> x
                Nothing -> error "name of not defined statment"
            goalStmt = names M.! (Exported, "goal")
        return $ Definitions stmtArray names' goalStmt ()

definitionsFromStatements :: IntMap (Statement, Int) -> Map (Role, DescriptorName) StatementID -> Definitions
definitionsFromStatements stmts names =
    let minBound = fst $ IM.findMin stmts
        maxBound = fst $ IM.findMax stmts
        bounds = (minBound, maxBound)
        stmtArray = A.array bounds $ IM.toList stmts
        goalStmt = names M.! (Exported, "goal")
    in Definitions stmtArray names goalStmt ()

makeStatement :: (MonadWithIDPool i m, MonadWriter [(i, (a, b2))] m) => b2 -> a -> m i
makeStatement n s = do
    i <- getID
    tell [(i, (s, n))]
    return i

applyTranslations :: (MonadState (IntMap Int) m, Traversable t) => t Int -> m (t Int)
applyTranslations ids = forM ids $ \i -> do
    i' <- use $ at i
    case i' of
        Just i'' -> return i''
        Nothing -> return i

optimize :: (Traversable f) => f StatementID -> StateT (IntMap (Statement, Int), IntMap StatementID) (WithIDPool StatementID) ()
optimize keep = do
    issues <- zoom _1 findIssues
    case issues of
        [] -> return ()
        _ -> error $ unlines issues
    zoom _1 propagateConstants
    zoom _1 propagateBottoms
    zoom _2 (applyTranslations keep) >>= (zoom _1 . restrictUsed')
    deduplicate
    zoom _2 (applyTranslations keep) >>= (zoom _1 . restrictUsed')
    eliminateAny
    zoom _2 (applyTranslations keep) >>= (zoom _1 . restrictUsed')
    deduplicate
    where
        propagateConstants :: (MonadState (IntMap (Statement, Int)) m, MonadFix m) => m ()
        propagateConstants = onAcyclics (const Nothing) (fmap ConstantStatement) $ \case
                    ConstantStatement x -> return x
                    UnionStatement us -> do
                        vs <- traverse snd us
                        return (concat vs)
                    ProjectStatement p cols -> do
                        cols' <- forM cols $ \case
                            Any -> mzero
                            Match n -> return n
                        fmap (\(oolean, thingies) -> (oolean, [thingies !! c | c <- cols'])) <$> snd p
                    JoinStatement s1 s2 on -> do
                        v1 <- snd s1
                        v2 <- snd s2
                        return $ evalJoin v1 v2 on
                    _ -> mzero
        propagateBottoms = onAcyclics ((,) False) (Just . snd) $ \s -> let s' = fmap fst s; simplifyBottoms (False, s) = (False, s); simplifyBottoms (True, _) = (True, ConstantStatement []) in simplifyBottoms $ case s of
                    ConstantStatement [] -> (True, s')
                    ProjectStatement (_, (True, _)) _ -> (True, s')
                    JoinStatement (_, (b, _)) (_, (b', _)) _ -> (b || b', s')
                    UnionStatement xs -> (all (fst . snd) xs, UnionStatement (fst <$> filter (fst . snd) xs))
                    _ -> (False, s')
        deduplicate :: (MonadWithIDPool StatementID m, MonadState (IntMap (Statement, Int), IntMap StatementID) m, MonadFix m) => m ()
        deduplicate = do
            oldState <- use _1
            (newState, idMapping) <- deduplicate' oldState
            _2 %= composeIdMapping idMapping
            _1 .= newState
        deduplicate' :: (MonadWithIDPool StatementID m, MonadFix m) => IntMap (Statement, Int) -> m (IntMap (Statement, Int), IntMap StatementID)
        deduplicate' stmts = do
            let lowerBound = fst $ IM.findMin stmts
                upperBound = fst $ IM.findMax stmts
                bounds = (lowerBound, upperBound)
                indices = A.listArray bounds $ A.range bounds
            ((oldToNewIDs, _), newStatements) <- fmap (^. lazy) $ flip S.execStateT (((IM.empty, IS.empty), M.empty) ^. strict) $ forM_ indices $ \oldIndex -> case IM.lookup oldIndex stmts of
                    Nothing -> return oldIndex
                    Just (oldStatement, numCols) -> do
                        oldToNewIDs <- use $ _1 . _1
                        translatedStatement <- forM oldStatement $ \oldID' -> return $ IM.findWithDefault oldID' oldID' oldToNewIDs
                        s <- use $ _2 . at (translatedStatement, numCols)
                        newIndex <- case s of
                            Just newIndex -> return newIndex
                            Nothing -> do
                                let newIndex = oldIndex
                                _2 . at (translatedStatement, numCols) .= Just newIndex
                                forM_ translatedStatement $ \usedIndex ->
                                    _1 . _2 . at usedIndex .= Just ()
                                return newIndex
                        when (oldIndex /= newIndex) $ do
                            oldIndexUsed <- use $ _1 ._2 . at oldIndex
                            when (isJust oldIndexUsed) $ _2 %= M.mapKeys (_1 . traverse %~ \oldId' -> if oldId' == oldIndex then newIndex else oldId')
                        _1 . _1 . at oldIndex .= Just newIndex
                        return newIndex
            let newStmts = IM.fromList $ fmap (snd &&& fst) $ M.toList newStatements
            return (newStmts, oldToNewIDs)
        eliminateAny = do
            onGroupedJoinsAndProjections keep $ \stmt ->
                let usedStatments = iter (IS.unions . lowerEnvT) $ fmap (IS.singleton . fst) stmt
                    evalStep :: (MonadWithIDPool Int m) => StatementF ([(Maybe StatementID, Int)], [((Maybe StatementID, Int), (Maybe StatementID, Int))]) -> m ([(Maybe StatementID, Int)], [((Maybe StatementID, Int), (Maybe StatementID, Int))])
                    evalStep (JoinStatement (cols, constraints) (cols', constraints') joinOn) = do
                        newConstraints <- forM joinOn $ \(i, i') -> return (cols !! i, cols' !! i')
                        let cols'' = fmap fst $ filter ((`notElem` fmap snd joinOn) . snd) $ zip cols' [0..]
                        return (cols <> cols'', constraints <> constraints' <> newConstraints)
                    evalStep (ProjectStatement (cols, constraints) p) = do
                        cols' <- forM p $ \case
                            Match i -> return $ cols !! i
                            Any -> fmap ((,) Nothing) getID
                        return (cols', constraints)
                    evalStep _ = error "Unexpected statment"
                    (nextFree, (cols, constraints)) = flip runWithIDPool [0..] $ iterM ((>>= evalStep) . sequence . lowerEnvT) $ fmap (\(i, n) -> (fmap ((,) (Just i)) [0..(n-1)], [])) stmt
                    findBy constraints t = [l | (l, r) <- constraints, t r] <> [r | (l, r) <- constraints, t l]
                    elim i (cols, constraints) = case findBy constraints (== (Nothing, i)) of
                        [] -> (cols, constraints)
                        (e:_) -> let replace x | x == (Nothing, i) = e; replace x = x in (cols & traverse %~ replace, constraints & traverse . both %~ replace)
                    (cols', constraints') = foldr elim (cols, constraints) [0..(nextFree - 1)]
                    usedCols = cols' <> constraints' ^.. traverse . both
                    usedCols' = IM.fromList $ fmap (\i -> (i, usedCols ^. traverse . filtered ((== Just i) . fst) . _2 . to IS.singleton)) $ IS.toList usedStatments
                    projectAndJoin :: (StatementID, IntSet) -> Maybe (Free (EnvT Int StatementF) StatementID, [[(Maybe StatementID, Int)]]) ->
                        (Free (EnvT Int StatementF) StatementID, [[(Maybe StatementID, IS.Key)]])
                    projectAndJoin (i, cols) Nothing = (wrap $ EnvT (IS.size cols) $ ProjectStatement (pure i) (Match <$> IS.toList cols), [[(Just i, c)] | c <- IS.toList cols])
                    projectAndJoin (i, cols) (Just (stmt, cols')) = (wrap $ EnvT n $ JoinStatement project stmt joinOn, cols'') where
                        project :: Free (EnvT Int StatementF) StatementID
                        project = wrap $ EnvT (IS.size cols) $ ProjectStatement (pure i) $ Match <$> IS.toList cols
                        n = IS.size cols + length cols' - IS.size (IS.fromList $ fmap snd joinOn)
                        leftIndices = M.fromList $ zip [(Just i, c) | c <- IS.toList cols] [0..]
                        rightIndices = M.fromList $ [(c', i) | (c, i) <- zip cols' [0..], c' <- c]
                        lookupIndices (a,b) = (,) <$> M.lookup a leftIndices <*> M.lookup b rightIndices
                        joinOn = mapMaybe lookupIndices (constraints' <> fmap (\(a,b) -> (b,a)) constraints')
                        cols'' = fmap (\i' -> [(Just i, i')] <> [c | l <- catMaybes [M.lookup (Just i, i') leftIndices], (l',r) <- joinOn, l == l', c <- cols' !! r]) (IS.toList cols)
                            <> fmap fst (filter ((`notElem` fmap snd joinOn) . snd) $ zip cols' [0..])
                    Just joinStmt = foldr (\new accum -> Just $ projectAndJoin new accum) Nothing (IM.assocs usedCols')
                    reusedAnys = M.keys $ M.filter (> 1) $ fmap Mon.getSum $ M.fromListWith (<>) [(c, Mon.Sum 1) | c <- cols', fst c == Nothing]
                    withReusedAnys | null reusedAnys = joinStmt
                                   | otherwise = (project, cols <> fmap (:[]) reusedAnys) where
                                        project = wrap $ EnvT n $ ProjectStatement (fst joinStmt) $ (Match <$> [0..length cols]) <> replicate (length reusedAnys) Any
                                        cols = snd joinStmt
                                        n = length cols + length reusedAnys
                    projection = wrap $ EnvT (length cols') $ ProjectStatement (fst withReusedAnys) cols'' where
                        cols'' = fmap (\col -> case M.lookup col colIndices of
                            Nothing -> if isNothing (fst col) then Any else error "failed to find column"
                            Just i -> Match i) cols'
                        colIndices = M.fromList [(c,i) | (cs, i) <- zip (snd withReusedAnys) [0..], c <- cs]
                in projection

onAcyclics :: (MonadState (IntMap (Statement, Int)) m, MonadFix m) => (Statement -> a) -> (a -> Maybe Statement) -> (StatementF (StatementID, a) ->  a) -> m ()
onAcyclics initializer finalizer localComputation = do
    acyclic <- acyclicStatements
    rec vals <- do
            lowerBound <- use $ to IM.findMin . _1
            upperBound <- use $ to IM.findMax . _1
            let bounds = (lowerBound, upperBound)
                indices = A.listArray bounds $ A.range bounds
                possibleConstants = S.fromList $ toList acyclic
            forM indices $ \i -> use $ at i . to fromJust . _1 . to (if S.notMember i possibleConstants then initializer else localComputation . fmap (\i -> (i, vals A.! i)))
    forM_ (A.assocs vals) $ \(i, v) -> forM_ (finalizer v) ((at i . _Just . _1) .=)

onGroupedJoinsAndProjections :: (Traversable f, MonadState (IntMap (Statement, Int), IntMap StatementID) m, MonadWithIDPool StatementID m, Zoom m1 m (IntMap (Statement, Int)) (IntMap (Statement, Int), IntMap StatementID), Functor (Zoomed m1 ()), Zoom m0 m (IntMap StatementID) (IntMap (Statement, Int), IntMap StatementID), Functor (Zoomed m0 (f Int))) => f StatementID -> (Free (EnvT (StatementID, Int) StatementF) (StatementID, Int) -> Free (EnvT Int StatementF) StatementID) -> m ()
onGroupedJoinsAndProjections keep f = do
    let isJoinOrProject = (\case (_, (JoinStatement _ _ _, _)) -> True; (_, (ProjectStatement _ _, _)) -> True; _ -> False)
    stmts <- use $ _1 . to IM.assocs . traverse . filtered isJoinOrProject . to (:[])
    stmts' <- forM stmts $ \(i, stmt) -> ((,) i) <$> inlining (IS.singleton i) isJoinOrProject (i, stmt)
    zoom _2 (applyTranslations keep) >>= (zoom _1 . restrictUsed')
    forM_ stmts' $ \(i, stmt) -> do
        let newStmt = f stmt
        case runFree newStmt of
            Pure i' -> error "expected at least one layer of statments"
            Free s -> do
                (EnvT n s') <- forM s $ \inner -> flip iterM inner $ \(EnvT n' inner') -> do
                    inner'' <- sequence inner'
                    i'' <- getID
                    _1 . at i'' .= Just (inner'', n')
                    return i''
                _1 . at i .= Just (s', n)

inlining :: (MonadState (IntMap (Statement, Int), IntMap StatementID) m) => IntSet -> ((StatementID, (Statement, Int)) -> Bool) -> (StatementID, (Statement, Int)) -> m (Free (EnvT (StatementID, Int) StatementF) (StatementID, Int))
inlining dontInline doInline stmt = joinFreeT $ inlining' dontInline doInline stmt where
    inlining' :: (MonadState (IntMap (Statement, Int), IntMap StatementID) m) => IntSet -> ((StatementID, (Statement, Int)) -> Bool) -> (StatementID, (Statement, Int)) -> FreeT (EnvT (StatementID, Int) StatementF) m (StatementID, Int)
    inlining' dontInline doInline (i, (stmt, n)) = liftF (EnvT (i,n) stmt) >>= \innerStmtID -> do
            innerStmt <- use $ _1 . at innerStmtID
            case innerStmt of
                Nothing -> error "unknown statement referred"
                Just innerStmt | (innerStmtID `IS.notMember` dontInline) && doInline (innerStmtID, innerStmt) -> inlining' (IS.insert innerStmtID dontInline) doInline (innerStmtID, innerStmt)
                               | otherwise -> return (innerStmtID, snd innerStmt)

findIssues :: (MonadState (IntMap (Statement, Int)) m) => m [String]
findIssues = execWriterT $ do
    allStatements <- use $ to IM.toList
    forM_ allStatements $ \(i, (stmt, n)) -> do
        case stmt of
            UnionStatement us -> forM_ us $ \i' -> do
                s <- use $ at i'
                case s of
                    Just (stmt', n') -> when (n /= n') $ tell ["Union " <> show i <> " with " <> show n <> " columns contains statement " <> show i' <> " with " <> show n' <> " columns"]
                    Nothing -> tell ["Union " <> show i <> " contains statement " <> show i' <> " which is not defined"]
            ProjectStatement p args -> do
                when (n /= length args) $ tell ["Projection " <> show i <> " is declared to have " <> show n <> " columns, but defines " <> show (length args)]
                s <- use $ at p
                case s of
                    Just (stmt', n') -> forM_ args $ \case
                            Any -> return ()
                            Match n -> when (n > n') $ tell ["Projection " <> show i <> " of statement " <> show p <> " refers to column " <> show n <> " out of " <> show n']
                    Nothing -> tell ["Projection " <> show i <> " of statement " <> show p <> " which is not defined"]
            JoinStatement s1 s2 joins -> do
                s1' <- use $ at s1
                when (isNothing s1') $ tell ["Join " <> show i <> " uses statement " <> show s1 <> " which is not defined"]
                s2' <- use $ at s2
                when (isNothing s2') $ tell ["Join " <> show i <> " uses statement " <> show s2 <> " which is not defined"]
                case (s1', s2') of
                    (Just (stmt1, n1), Just (stmt2, n2)) -> do
                        forM_ joins $ \(x1, x2) -> do
                            when (x1 > n1) $ tell ["Join " <> show i <> " refers to column " <> show x1 <> " of statement " <> show s1 <> ", but it only has " <> show n1 <> " columns"]
                            when (x2 > n2) $ tell ["Join " <> show i <> " refers to column " <> show x2 <> " of statement " <> show s2 <> ", but it only has " <> show n2 <> " columns"]
                        --todo: check output num of columns properly
                        when (n > n1 + n2) $ tell ["Join " <> show i <> " of statement " <> show s1 <> " with " <> show n1 <> " columns and statement " <> show s2 <> " with " <> show n2 <> " columns claims to have " <> show n <> " columns"]
                        when (n < n1 + n2 - length joins) $ tell ["Join " <> show i <> " of statement " <> show s1 <> " with " <> show n1 <> " columns and statement " <> show s2 <> " with " <> show n2 <> " columns but only " <> show (length joins) <> " relations claims to have " <> show n <> " columns"]
                    _ -> return ()
            ConstantStatement cs -> forM_ cs $ \(_, values) -> when (length values /= n) $ tell ["Constant statement " <> show i <> " has term " <> show values <> " but claims " <> show n <> " columns"]
            ShuffleStatement _ -> when (n /= 2) $ tell ["Shuffle " <> show i <> " claims " <> show n <> " columns"]
            AtLeastStatement _ _ -> return () --todo: once counties are implemented

acyclicStatements :: (MonadState (IntMap (Statement, Int)) m) => m [StatementID]
acyclicStatements = do
    (g, fromVertex, getVertex) <- dependencyGraph
    let comps = toList <$> G.scc g
        loneVertecies = comps >>= \case
            [v] -> let (_, i, js) = fromVertex v in [i | i `notElem` js]
            _ -> []
    return loneVertecies

dependencyGraph :: (Traversable t, MonadState (IntMap (t StatementID, Int)) m) => m   (G.Graph, G.Vertex -> (IM.Key, IM.Key, [IM.Key]), IM.Key -> Maybe G.Vertex)
dependencyGraph = do
    x <- use $ to IM.toList
    return $ G.graphFromEdges [(i, i, toList s) | (i, (s, _)) <- x]

evalJoin :: [(Oolean, [Thingy])] -> [(Oolean, [Thingy])] -> [(Int, Int)] -> [(Oolean, [Thingy])]
evalJoin [] _ _ = []
evalJoin _ [] _ = []
evalJoin v1 v2 on = [(join oolean1 oolean2, combine cols1 cols2) | (oolean1, cols1) <- v1, (oolean2, cols2) <- v2, check cols1 cols2] where
    check cols1 cols2 = all (\(i,j) -> cols1 !! i == cols2 !! j) on
    combine cols1 cols2 = onlyFirstFromEqGroup $ cols1 <> cols2
    onlyFirstFromEqGroup xs = fmap fst $ filter ((\i -> eqGroup i == i) . snd) $ zip xs [0..]
    col1len = length $ snd $ head v1
    col2len = length $ snd $ head v2
    eqGroup i = eqGroups !! i
    eqGroups = findEqGroup <$> take (col1len + col2len) [0..] --todo: there's a bug here if two columns from v1 are joined to one column from v2
    findEqGroup i = let rs = filter ((==i) . snd) on' in
        if null rs then i else eqGroup $ fst $ head rs
    on' = fmap (second (+ col1len)) on

displayDefinitions :: Definitions -> Text
displayDefinitions defs = displayStatements defs <> displayNames defs where

displayPattern Any = "_"
displayPattern (Match n) = T.pack $ show n
displayRef n = "#" <> T.pack (show n)
displayConstant OolTrue cols = "[" <> T.intercalate ", " (fmap displayPossiblyScopedName cols) <> "]"
displayConstant OolOol cols = "ool" <> displayConstant OolTrue cols
displayConstant OolFalse cols = "false" <> displayConstant OolTrue cols
displayNames defs = M.foldMapWithKey (\k v -> displayName k v <> "\n") $ statementNames defs
displayName (Defined, d) i = d <> ": " <> T.pack (show i)
displayName (Exported, d) i = "[" <> d <> "]: " <> T.pack (show i)

displayStatements defs = foldMap ((<> "\n") . uncurry displayStatement . second fst) $ A.assocs $ statements defs
displayStatement i s = T.pack (show i) <> " <- " <> case s of
    UnionStatement [] -> "false"
    UnionStatement us -> T.intercalate " | " $ fmap displayRef us
    ProjectStatement p patterns -> displayRef p <> "!(" <> T.intercalate "," (fmap displayPattern patterns) <> ")"
    JoinStatement s s' [] -> displayRef s <> " x " <> displayRef s'
    JoinStatement s s' vs -> displayRef s <> " x " <> displayRef s' <> "!(" <> T.intercalate ", " (fmap (\(v1, v2) -> T.pack $ show v1 <> "=" <> show v2) vs)<> ")"
    ShuffleStatement shuf -> "\"" <> T.pack shuf <> "\""
    ConstantStatement [] -> "false"
    ConstantStatement s -> T.intercalate " | " $ fmap (uncurry displayConstant) s
    AtLeastStatement s Infinite -> displayRef s <> " == inf"
    AtLeastStatement s (Finite n) -> displayRef s <> " >= " <> T.pack (show n)
{-

descriptor(item, "CanTurnMinish", X1, X0) :- ool.

item <- ConstantStatement [(OolOol, ["CanTurnMinish"])]
Join (ConstantStatment [(OolTrue, ["CanTurnMinish"])]) (ConstantStatment [(OolOol, [])]) [])



descriptor(target, X0, X2, X1) :- (shuffle("Warps",X3,X0), (node(X4,[warp,X3]), reachableNode(X4,state))).

warp <- _
target <- Project (Join (Shuffle "Warps") warp [(0, 0)])) [1]

-}