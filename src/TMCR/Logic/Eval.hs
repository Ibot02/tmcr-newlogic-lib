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
module TMCR.Logic.Eval where

import TMCR.Logic.Common
import TMCR.Logic.Descriptor (Oolean (..), DescriptorName, DescriptorIdent (..), Descriptor (..), Literal (..), DescriptorRule' (..), DescriptorType(..), DescriptorRule, Value (..), SDescriptorType (..), Value' (..), Relation (..))
import TMCR.Logic.Shuffle (ShuffleName)
import TMCR.Logic.Merge (GameDef(..))
import TMCR.Logic.Descriptor (DescriptorDeclaration(..), DescriptorExport(..))

import Data.Array (Array)
import qualified Data.Array as A
import Data.Set (Set())
import qualified Data.Set as S
import Data.Map (Map())
import qualified Data.Map as M
import Data.IntMap (IntMap())
import qualified Data.IntMap as IM
import Data.Map.Monoidal (MonoidalMap)
import qualified Data.Map.Monoidal as MM
import qualified Data.Graph as G
import Data.Maybe (mapMaybe, isNothing, catMaybes)
import Control.Monad (forM, forM_, MonadPlus (..))
import Control.Monad.Fix (MonadFix (..))
import Control.Arrow (second)
import Control.Monad.Writer.CPS (MonadTrans(..), MonadWriter (..), WriterT(..))
import Control.Monad.Reader (ReaderT(..), MonadReader, asks)
import Control.Monad.Trans.Writer.CPS (runWriterT)

import Data.Text (Text)
import qualified Data.Text as T
import TMCR.Logic.Logic (LogicNodeName)
import qualified TMCR.Logic.Logic as L

import qualified TMCR.Logic.Graphs as G
import TMCR.Logic.Algebra (Join(getJoin), DNF (getDisjunctions), Lattice (join))
import Control.Monad.State (StateT, execStateT, MonadState)

import Control.Lens
import Control.Monad.Trans.Maybe (MaybeT(..))
import Data.Foldable (Foldable(..))

type StatementID = Int
type CountyStatementID = Int
type Statement = StatementF StatementID

data Definitions = Definitions {
      statements :: Array StatementID Statement
    , statementNames :: Map (Role, DescriptorName) StatementID
    , countyStatments :: () --todo
}

data StatementF a =
      UnionStatement [a]
    | ProjectStatement a [Pattern Int]
    | JoinStatement a a [(Int, Int)]
    | ShuffleStatement ShuffleName
    | ConstantStatement [(Oolean, [Thingy])]
    | AtLeastStatment CountyStatementID Nteger
    deriving (Eq, Functor, Foldable, Traversable)

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

evalWithIDPool m = snd . runWithIDPool m

data Role = Defined | Exported deriving (Eq, Ord, Show)

compile :: GameDef -> Definitions
compile gameDef = f' a where
    f' x = flip evalWithIDPool [0..] $ do
        (names, stmts) <- x
        stmts' <- execStateT optimize stmts
        stmts'' <- restrictUsed stmts' names
        --let stmts'' = stmts
        let minID = fst $ IM.findMin stmts''
            maxID = fst $ IM.findMax stmts''
            stmtArray = A.array (minID, maxID) $ IM.toList stmts''
        return $ Definitions stmtArray names ()
    a :: WithIDPool StatementID (Map (Role, DescriptorName) StatementID, IntMap Statement)
    a = fmap (second IM.fromList) $ runWriterT $ do
        rec (descriptorNames, reachableNodesStmt) <- do
                descriptorNames' <- runReaderT (descriptorStatements reachableNodesStmt) descriptorNames
                reachableNodesStmt' <- logicStatements descriptorNames reachableNodesStmt
                return (descriptorNames', reachableNodesStmt')
        return descriptorNames
    logicTargets :: Map DescriptorName [(LogicNodeName, [Thingy])]
    logicTargets = M.fromListWith (<>) $ [(d, [(n, args)]) | (n, ds) <- M.toList $ snd $ _defLogic gameDef, (d, args) <- ds]
    descriptorStatements :: (MonadWriter [(StatementID, Statement)] m, MonadReader (Map (Role, DescriptorName) StatementID) m, MonadWithIDPool StatementID m) => StatementID -> m (Map (Role, DescriptorName) StatementID)
    descriptorStatements reachableNodes = do
        truthies <- flip M.traverseWithKey (_defDescriptorDefinitionsTruthy gameDef) $ \name defs -> forM defs $ \def -> do
            mkDescriptorStatement def
        fmap M.fromList $ forM (M.toList $ _defDescriptors gameDef) $ \(name, decl) ->
            if (_descriptorDeclarationExport decl == Just DescriptorExportTarget)
            then do
                let nodesWithArgs = M.findWithDefault [] name logicTargets
                i <- makeStatement $ ConstantStatement $ fmap (\(n, args) -> (OolTrue, asThingy n : args)) nodesWithArgs
                j <- makeStatement $ JoinStatement reachableNodes i [(0,0)]
                p <- makeStatement $ ProjectStatement j $ take (length $ _descriptorDeclarationArguments decl) $ fmap Match [1..]
                return ((Exported, name), j)
            else do
                let ids = M.findWithDefault [] (TruthyDescriptorIdent name) truthies
                i <- case ids of
                    [i] -> return i
                    us -> makeStatement $ UnionStatement us
                return ((Defined, name), i)
    asThingy :: LogicNodeName -> Thingy
    asThingy (L.Global n) = Global $ asText n
    asThingy (L.Scoped ns) = ScopedName $ fmap asText ns
    asThingy L.FullWildcard = error "unexpected wildcard"
    asText :: L.Name -> Text
    asText (L.PlainName t) = t
    asText (L.QuotedName t) = t
    asText L.Wildcard = error "unexpected wildcard"
    logicStatements names reachable = do
        us <- forM (G.taggedGetEdges $ fst $ _defLogic gameDef) $ \(fromNode, rules, toNode) -> forM (S.toList $ getDisjunctions $ getJoin rules) $ \d ->
            let conj (name, args) acc = do
                    let x = names M.! (Defined, name)
                    c <- makeStatement $ ConstantStatement [(OolTrue, args)]
                    s <- makeStatement $ JoinStatement c x $ take (length args) $ fmap (\i -> (i, i)) [0..]
                    p <- makeStatement $ ProjectStatement s []
                    a <- acc
                    makeStatement $ JoinStatement p a []
            in S.foldr conj (makeStatement $ ConstantStatement [(OolTrue, [])]) d
        makeStatement $ UnionStatement $ concat us
    mkDescriptorStatement :: (MonadWriter [(StatementID, Statement)] m, MonadReader (Map (Role, DescriptorName) StatementID) m, MonadWithIDPool StatementID m) => Descriptor Truthy -> m StatementID
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
        c <- makeStatement $ ConstantStatement [(OolTrue, fmap fst constantArgs)]
        j <- makeStatement $ JoinStatement c s []
        makeStatement $ ProjectStatement c $ fmap (uncurry toProj) $ zip args [0..]
    fromRule :: (MonadWriter [(StatementID, Statement)] m, MonadReader (Map (Role, DescriptorName) StatementID) m, MonadWithIDPool StatementID m, Ord v) => DescriptorRule' Truthy v -> m (StatementID, [v])
    fromRule (Constant (TruthyLiteral t)) = do
        i <- makeStatement $ ConstantStatement [(t, [])]
        return (i, [])
    fromRule (IsEqual (Variable v) (Variable v')) | v == v' = do
        t <- makeStatement $ ConstantStatement [(OolTrue, [])]
        refl <- makeStatement $ ProjectStatement t [Any]
        return (refl, [v])
    fromRule (IsEqual (Variable v) (Variable v')) = do
        t <- makeStatement $ ConstantStatement [(OolTrue, [])]
        refl <- makeStatement $ ProjectStatement t [Any]
        eq <- makeStatement $ ProjectStatement refl [Match 0, Match 0]
        return (eq, [v, v'])
    fromRule (IsEqual (Variable v) (ConstantValue t)) = fmap (\x -> (x, [v])) $ makeStatement $ ConstantStatement [(OolTrue, [t])]
    fromRule (IsEqual a@(ConstantValue t) b@(Variable v)) = fromRule (IsEqual b a)
    fromRule (IsEqual (ConstantValue t) (ConstantValue t')) | t == t' = fmap (\x -> (x, [])) $ makeStatement $ ConstantStatement [(OolTrue, [])]
                                                            | otherwise = fmap (\x -> (x, [])) $ makeStatement $ ConstantStatement []
    fromRule (CallDescriptor STruthy name args) = call (Defined, name) args
    fromRule (CanAccess STruthy name args _) = call (Exported, name) args
    fromRule (AtLeast r n) = do
        (c, vars) <- fromCountyRule r
        s <- makeStatement $ AtLeastStatment c n
        return (s, vars)
    fromRule (Exist rel (Variable v) r) = do
        (c, vars) <- fromRule r
        (s, a, b) <- fromRel rel
        j <- makeStatement $ JoinStatement s c $ fmap ((,) b . snd) $ filter (isNothing . fst) $ zip vars [0..]
        let vars' = catMaybes vars
        p <- makeStatement $ ProjectStatement j (Match a: fmap Match [2..length vars' + 1])
        if v `elem` vars'
        then do
            t <- makeStatement $ ConstantStatement [(OolTrue, [])]
            p' <- makeStatement $ ProjectStatement t [Any]
            j' <- makeStatement $ JoinStatement p p' $ ((0,0):) $ fmap ((,) 0 . snd) $ filter ((==v) . fst) $ zip vars' [0..]
            return (j', v : filter (/= v) vars')
        else return (p, v:vars')
    fromRule (Exist rel (ConstantValue t) r) = do
        (c, vars) <- fromRule r
        (s, a, b) <- fromRel rel
        c' <- makeStatement $ ConstantStatement [(OolTrue, [t])]
        s' <- makeStatement $ JoinStatement s c' [(a, 0)]
        j <- makeStatement $ JoinStatement s c $ fmap ((,) b . snd) $ filter (isNothing . fst) $ zip vars [0..]
        let vars' = catMaybes vars
        p <- makeStatement $ ProjectStatement j (fmap Match [2..length vars' + 1])
        return (p, vars')
    fromRule (Min STruthy rs) = foldr fromConj (fmap (\s -> (s,[])) $ makeStatement $ ConstantStatement [(OolTrue, [])]) rs
    fromRule (Max STruthy rs) = do
        xs <- traverse fromRule rs
        let vars = S.toList $ foldMap (S.fromList . snd) xs
            varIndices = M.fromList $ zip vars [0..]
        ps <- forM xs $ \(s, vs) ->
            let vsWithIndices = M.fromList $ zip vs [Match n | n <- [0..]] in
            makeStatement $ ProjectStatement s $ fmap (\v -> M.findWithDefault Any v vsWithIndices) vars
        u <- makeStatement $ UnionStatement ps
        return (u, vars)
    fromRule (Consume i n vs rs) = error "todo consume"
    fromCountyRule :: (MonadWriter [(StatementID, Statement)] m, MonadReader (Map (Role, DescriptorName) StatementID) m, MonadWithIDPool StatementID m) => DescriptorRule' County v -> m (StatementID, [v])
    fromCountyRule r = do --todo
        return (0, [])
    fromRel :: (MonadWriter [(StatementID, Statement)] m, MonadReader (Map (Role, DescriptorName) StatementID) m, MonadWithIDPool StatementID m) => Relation -> m (StatementID, Int, Int)
    fromRel (Forward s) = do
        i <- makeStatement $ ShuffleStatement s
        return (i, 0, 1)
    fromRel (Backward s) = do
        i <- makeStatement $ ShuffleStatement s
        return (i, 1, 0)
    makeStatement s = do
        i <- getID
        tell [(i, s)]
        return i
    fromConj r a = do
        (s, vars) <- fromRule r
        (s', vars') <- a
        j <- makeStatement $ JoinStatement s s' [(i,j) | (v,i) <- zip vars [0..], (v',j) <- zip vars' [0..], v == v']
        return (j, vars <> filter (not . (`elem` vars)) vars')

    call r args = do
        let args' = zip args [0..]
            constants = mapMaybe (\case (Variable _, _) -> Nothing; (ConstantValue t, i) -> Just (t, i)) args'
            variables = mapMaybe (\case (Variable v, i) -> Just (v, i); (ConstantValue t, i) -> Nothing) args'
        c <- makeStatement $ ConstantStatement [(OolTrue, fmap fst constants)]
        d <- asks (M.findWithDefault (error $ show (fst r) <> " " <> T.unpack (snd r) <> " not in the map") r)
        j <- makeStatement $ JoinStatement d c $ zip (fmap snd constants) [0..]
        p <- makeStatement $ ProjectStatement j $ fmap (Match . snd) variables
        return (p, fmap fst variables)

optimize :: StateT (IntMap Statement) (WithIDPool StatementID) ()
optimize = do
    propagateConstants
    where
        propagateConstants :: (MonadState (IntMap Statement) m, MonadFix m) => m ()
        propagateConstants = do
            acyclic <- acyclicStatements
            rec constantValues <- findConstantValues acyclic constantValues
            forM_ (A.assocs constantValues) $ \case
                (_, Nothing) -> return ()
                (i, Just v) -> at i .= Just (ConstantStatement v)
        findConstantValues :: (MonadState (IntMap Statement) m, Foldable t) => t StatementID -> Array StatementID (Maybe [(Oolean, [Thingy])]) -> m (Array StatementID (Maybe [(Oolean, [Thingy])]))
        findConstantValues s vals = do
            lowerBound <- use $ to IM.findMin . _1
            upperBound <- use $ to IM.findMax . _1
            let bounds = (lowerBound, upperBound)
                indices = A.listArray bounds $ A.range bounds
                possibleConstants = S.fromList $ toList s
            forM indices $ \i -> if S.notMember i possibleConstants then return Nothing else runMaybeT $ do
                Just statement <- use $ at i
                case statement of
                    ConstantStatement x -> return x
                    UnionStatement us -> do
                        Just vs <- return $ traverse (vals A.!) us
                        return (concat vs)
                    ProjectStatement p cols -> do
                        cols' <- forM cols $ \case
                            Any -> mzero
                            Match n -> return n
                        Just v <- return $ vals A.! p
                        return $ fmap (\(oolean, thingies) -> (oolean, [thingies !! c | c <- cols'])) v
                    {-
                    JoinStatement s1 s2 on -> do
                        Just v1 <- return $ vals A.! s1
                        Just v2 <- return $ vals A.! s2
                        let v = evalJoin v1 v2 on
                        return v
                        -}
                    _ -> mzero

acyclicStatements :: (MonadState (IntMap Statement) m) => m [StatementID]
acyclicStatements = do
    x <- use $ to IM.toList
    let (g, fromVertex, getVertex) = G.graphFromEdges [(i, i, toList s) | (i, s) <- x]
        comps = toList <$> G.scc g
        loneVertecies = comps >>= \case
            [v] -> let (_, i, js) = fromVertex v in [i | i `notElem` js]
            _ -> []
    return loneVertecies

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
    eqGroups = findEqGroup <$> take (col1len + col2len) [0..]
    findEqGroup i = let rs = filter ((==i) . snd) on' in
        if null rs then i else eqGroup $ fst $ head rs
    on' = fmap (second (+ col1len)) on

restrictUsed :: Foldable t => IntMap Statement -> t StatementID -> WithIDPool StatementID (IntMap Statement)
restrictUsed s _ = return s --todo

displayDefinitions :: Definitions -> Text
displayDefinitions defs = displayStatements <> displayNames where
    displayStatements = foldMap ((<> "\n") . uncurry displayStatement) $ A.assocs $ statements defs
    displayStatement i s = T.pack (show i) <> " <- " <> case s of
        UnionStatement [] -> "false"
        UnionStatement us -> T.intercalate " | " $ fmap displayRef us
        ProjectStatement p patterns -> displayRef p <> "!(" <> T.intercalate "," (fmap displayPattern patterns) <> ")"
        JoinStatement s s' [] -> displayRef s <> " x " <> displayRef s'
        JoinStatement s s' vs -> displayRef s <> " x " <> displayRef s' <> "!(" <> T.intercalate ", " (fmap (\(v1, v2) -> T.pack $ show v1 <> "=" <> show v2) vs)<> ")"
        ShuffleStatement shuf -> "\"" <> shuf <> "\""
        ConstantStatement s -> T.intercalate " | " $ fmap (uncurry displayConstant) s
        AtLeastStatment s Infinite -> displayRef s <> " == inf"
        AtLeastStatment s (Finite n) -> displayRef s <> " >= " <> T.pack (show n)
    displayPattern Any = "_"
    displayPattern (Match n) = T.pack $ show n
    displayRef n = "#" <> T.pack (show n)
    displayConstant OolTrue cols = "[" <> T.intercalate ", " (fmap displayPossiblyScopedName cols) <> "]"
    displayConstant OolOol cols = "ool" <> displayConstant OolTrue cols
    displayConstant OolFalse cols = "false" <> displayConstant OolTrue cols
    displayNames = M.foldMapWithKey (\k v -> displayName k v <> "\n") $ statementNames defs
    displayName (Defined, d) i = d <> ": " <> T.pack (show i)
    displayName (Exported, d) i = "[" <> d <> "]: " <> T.pack (show i)

{-

descriptor(item, "CanTurnMinish", X1, X0) :- ool.

item <- ConstantStatement [(OolOol, ["CanTurnMinish"])]
Join (ConstantStatment [(OolTrue, ["CanTurnMinish"])]) (ConstantStatment [(OolOol, [])]) [])



descriptor(target, X0, X2, X1) :- (shuffle("Warps",X3,X0), (node(X4,[warp,X3]), reachableNode(X4,state))).

warp <- _
target <- Project (Join (Shuffle "Warps") warp [(0, 0)])) [1]

-}