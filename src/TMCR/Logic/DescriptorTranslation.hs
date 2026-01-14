{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
module TMCR.Logic.DescriptorTranslation where

import TMCR.Logic.Common
import TMCR.Logic.Logic
import TMCR.Logic.Descriptor
    ( DescriptorType(County, Truthy),
      DescriptorName,
      DescriptorDeclaration,
      Descriptor(..),
      DescriptorIdent(..), Value' )
import qualified TMCR.Logic.Descriptor as D
import TMCR.Logic.Algebra (DNF(..), Join(..))
import TMCR.Logic.Graphs

import qualified Algebra.Graph.Labelled as Labelled

import Data.Foldable
import Data.Void (Void(..), absurd)

import Data.Map (Map())
import qualified Data.Map as M

import Data.Monoid (Endo(..))

import qualified Data.Text as T
import TMCR.Logic.Merge (GameDef (_defDescriptorDefinitionsTruthy, _defDescriptorDefinitionsCounty), _defLogic, _defDescriptors)


newtype Result = Result [Statement] deriving (Show, Semigroup, Monoid)

data Statement = Statement String (BindVars Void) deriving (Show)
data BindVars v =
      IntroVar (BindVars (Maybe v))
    | Match (Term v) (BindVars v)
    | DefinedBy (Expr v)
    | Defined
    deriving (Show)

data Expr v = Term (Term v)
            | Conj (Expr v) (Expr v)
            | Disj (Expr v) (Expr v)
            | IntroVarExpr (Expr (Maybe v))
            | EqTerms (Term v) (Term v)
            deriving (Show, Functor)

data Term v = Apply String [Term v]
            | VariableTerm v
            | StringTerm String
            | OpTerm String (Term v) (Term v)
            | ListTerm [Term v] (Maybe (Term v))
            deriving (Show, Functor)


intercalate :: (Monoid w) => w -> [w] -> w
intercalate i [] = mempty
intercalate i (x:xs) = x <> foldMap (i <>) xs

--      _defDescriptors :: Map DescriptorName DescriptorDeclaration

--    , _defDescriptorDefinitionsTruthy :: Map (DescriptorIdent Truthy) [Descriptor Truthy]
--    , _defDescriptorDefinitionsCounty :: Map (DescriptorIdent County) [Descriptor County]

--fromTruthyDescriptors :: Map (DescriptorIdent Truthy) [Descriptor Truthy] -> Result

fromThingy :: Thingy -> Term v
fromThingy = StringTerm . T.unpack . displayPossiblyScopedName

fromLogic :: TaggedGraph (Join (DNF (DescriptorName, [Thingy]))) (Maybe LogicNodeName) -> Map LogicNodeName [(DescriptorName, [Thingy])] -> Result
fromLogic g n = Result $ fromNodes n <> fromEdges (Labelled.edgeSet g)

fromNodes m = [fromNode node term | (node, terms) <- M.toList m, term <- terms]

fromNode name (descriptorName, terms) = Statement "node" $ Match (fromLogicNodeName name) $ Match (ListTerm (atom (T.unpack descriptorName) : fmap fromThingy terms) Nothing) Defined

fromLogicNodeName = StringTerm . T.unpack . displayScopedName

fromEdges :: (Foldable f) => f (Join (DNF (DescriptorName, [Thingy])), Maybe LogicNodeName, Maybe LogicNodeName) -> [Statement]
fromEdges = foldMap fromEdge

fromEdge :: (Join (DNF (DescriptorName, [Thingy])), Maybe LogicNodeName, Maybe LogicNodeName) -> [Statement]
fromEdge (_, _, Nothing) = []
fromEdge (cond, Nothing, Just to) = do
    (e, postState) <- fromCond cond (ListTerm [] Nothing)
    return $ Statement "reachableNode" $ IntroVar $ Match (fromLogicNodeName to) $ Match postState $ DefinedBy $ e
fromEdge (cond, Just from, Just to) = do
    (e, postState) <- fromCond cond (VariableTerm $ Nothing)
    return $ Statement "reachableNode" $ IntroVar $ IntroVar $ Match (fromLogicNodeName to) $ Match postState $ DefinedBy $ Conj (Term $ Apply "reachableNode" [fromLogicNodeName from, VariableTerm (Just Nothing)]) $ e

fromCond :: Join (DNF (DescriptorName, [Thingy])) -> Term v -> [(Expr (Maybe v), Term (Maybe v))]
fromCond (Join (DNF ds)) preState = fmap (fromConj preState . toList) . toList $ ds

fromConj :: Term v -> [(DescriptorName, [Thingy])] -> (Expr (Maybe v), Term (Maybe v))
fromConj preState [] = (Term $ atom "true", fmap Just preState)
fromConj preState [(name, args)] = fromDescriptorCall preState name args
fromConj preState ((name, args):ds) =
    let (e1, intermediateState) = fromDescriptorCall (fmap Just preState) name args
        (e2, postState) = fromConj intermediateState ds
    in (IntroVarExpr (Conj e1 $ IntroVarExpr $ Conj e2 $ EqTerms postState (VariableTerm (Just $ Just $ Nothing))), VariableTerm Nothing)

{-

fromConj v [intro, intro2] -> intro(Just v, Nothing), intro2(Just Nothing, Nothing) -> IntroVar (intro(Just Just v, Nothing), intro2(Nothing, Just Nothing))
fromConj v [intro, intro2] -> intro(Just v, Just v), intro2(Just Just v, Nothing) -> IntroVar (intro(Just Just v, Just Just v), intro2(Just Just v, Just Nothing))
fromConj v [intro, intro2] -> intro(Just v, Nothing), intro2(Just Nothing, Just Nothing) -> IntroVar (intro(Just Just v, Just Nothing), intro2(Just Nothing, Just Nothing))
fromConj v [intro, intro2] -> intro(Just v, Just v), intro2(Just Just v, Just Just v) -> IntroVar (intro(Just Just v, Just Just v), intro2(Just Just v, Just Just v))

-}

--fromConj preState = (\e -> (e, preState)) . foldl1' (Term $ atom "false") Conj . fmap (\(name, args) -> Term $ Apply "descriptor" $ atom (T.unpack name) : fmap fromThingy args)

fromDescriptorCall :: Term v -> DescriptorName -> [Thingy] -> (Expr (Maybe v), Term (Maybe v))
--fromDescriptor preState name args = ((Term $ Apply "descriptor" $ atom (T.unpack name) : fmap fromThingy args), fmap Just preState)
fromDescriptorCall preState name args = (Term $ Apply "descriptor" $ atom (T.unpack name) : fmap fromThingy args <> [fmap Just preState, VariableTerm Nothing], VariableTerm Nothing)

fromDescriptors :: Map DescriptorName DescriptorDeclaration -> Map (DescriptorIdent 'Truthy) [Descriptor 'Truthy] -> Map (DescriptorIdent 'County) [Descriptor 'County] -> Result
fromDescriptors defs truthies counties = M.foldMapWithKey (foldMap . fromTruthy)  truthies <> M.foldMapWithKey (foldMap . fromCounty) counties
fromTruthy :: DescriptorIdent 'Truthy -> Descriptor 'Truthy -> Result
fromTruthy ident (Descriptor callValues expr) = Result $ (:[]) $ makeDescriptorStatement ident callValues $ fromExpression expr
fromCounty :: DescriptorIdent 'County -> Descriptor 'County -> Result
fromCounty ident (Descriptor callValues expr) = Result $ (:[]) $ makeCountyDescriptorStatement ident callValues $ fromCountyExpression expr

fromExpression :: D.DescriptorRule Truthy -> Expr (Maybe (Maybe String))
fromExpression = fromExpression' toTerm where
  toTerm (D.Variable v) = VariableTerm $ T.unpack v
  toTerm (D.ConstantValue c) = fromThingy c

fromCountyExpression :: D.DescriptorRule County -> Expr (Maybe (Maybe (Maybe String)))
fromCountyExpression expr = fromCountyExpression' toTerm expr (VariableTerm Nothing) where
  toTerm (D.Variable v) = VariableTerm $ Just $ T.unpack v
  toTerm (D.ConstantValue c) = fromThingy c

fromExpression' :: (Value' v -> Term v') -> D.DescriptorRule' Truthy v -> Expr (Maybe (Maybe v'))
fromExpression' _ (D.Constant lit) = Term $ atom $ case lit of
  D.TruthyLiteral D.OolTrue -> "true"
  D.TruthyLiteral D.OolFalse -> "false"
  D.TruthyLiteral D.OolOol -> "false"
fromExpression' toTerm (D.IsEqual value1 value2) = fmap (Just . Just) $ EqTerms (toTerm value1) (toTerm value2)
fromExpression' toTerm (D.CallDescriptor D.STruthy name vars) = Term $ Apply "descriptor" $ (atom $ T.unpack name) : fmap (fmap (Just . Just) . toTerm) vars <> [VariableTerm Nothing, VariableTerm (Just Nothing)]
fromExpression' toTerm (D.CanAccess D.STruthy name vars state) = IntroVarExpr $ flip Conj (Term $ Apply "reachableNode" [VariableTerm Nothing, atom "state"]) (Term $ Apply "node" [VariableTerm Nothing, ListTerm (atom (T.unpack name): fmap (fmap (Just . Just . Just) . toTerm) vars) Nothing])
fromExpression' toTerm (D.AtLeast expr value) = fromCountyExpression' toTerm expr $ (\case Infinite -> atom "inf"; Finite n -> atom (show n)) value
fromExpression' toTerm (D.Exist rel v expr) = introVarUnder $ Conj (fromShuffle rel (fmap (Just . Just . Just) $ toTerm v) (VariableTerm (Just (Just Nothing)))) $ fromExpression' (\case D.Variable Nothing -> VariableTerm Nothing; D.Variable (Just x) -> fmap Just (toTerm $ D.Variable x); (D.ConstantValue t) -> fmap Just (toTerm $ D.ConstantValue t)){-(maybe (VariableTerm Nothing) (fmap Just . toTerm))-} expr
fromExpression' toTerm (D.Min D.STruthy []) = Term $ atom "true"
fromExpression' toTerm (D.Min D.STruthy xs) = foldl1 Conj $ fmap (fromExpression' toTerm) xs
fromExpression' toTerm (D.Max D.STruthy []) = Term $ atom "false"
fromExpression' toTerm (D.Max D.STruthy xs) = foldl1 Disj $ fmap (fromExpression' toTerm) xs
fromExpression' toTerm (D.Consume _ _ _ _) = Term $ atom "true"

introVarUnder :: Expr (Maybe (Maybe (Maybe v))) -> Expr (Maybe (Maybe v))
introVarUnder = IntroVarExpr . fmap (maybe (Just Nothing) $ maybe (Just (Just Nothing)) $ fmap (Just . Just))

fromCountyExpression' :: (Value' v -> Term v') -> D.DescriptorRule' County v -> Term v' -> Expr (Maybe (Maybe v'))
fromCountyExpression' _ (D.Constant lit) lowerBound = case lit of
  D.CountyLiteral Infinite -> Term $ atom "true"
  D.CountyLiteral (Finite n) -> fmap (Just . Just) $ Term $ OpTerm "#>=" (atom (show n)) lowerBound
fromCountyExpression' toTerm (D.Scale e Infinite) lowerBound = Disj (fmap (Just . Just) $ Term $ OpTerm "#>=" (atom "0") lowerBound) $ fromCountyExpression' toTerm e (atom "1")
fromCountyExpression' toTerm (D.Scale e (Finite n)) lowerBound = introVarUnder $ Conj (fromCountyExpression' (fmap Just . toTerm) e (VariableTerm Nothing)) (Term $ OpTerm "#>=" (OpTerm "*" (atom (show n)) (VariableTerm (Just (Just Nothing)))) (fmap (Just . Just . Just) lowerBound))
fromCountyExpression' toTerm (D.Sum []) lowerBound = fmap (Just . Just) $ Term $ OpTerm "#>=" (atom "0") lowerBound
fromCountyExpression' toTerm (D.Sum (e:es)) lowerBound = let 
    x = VariableTerm (Just (Just Nothing))
    y = VariableTerm (Just (Just (Just Nothing)))
    sumEAtLeastX = (fromCountyExpression' (fmap (Just . Just) . toTerm) e (VariableTerm Nothing))
    sumEsAtLeastY = (fromCountyExpression' (fmap (Just . Just) . toTerm) (D.Sum es) (VariableTerm (Just Nothing)))
  in introVarUnder $ introVarUnder $ Conj (Conj
   (Term $ OpTerm "#>=" x (atom "0"))
   (Term $ OpTerm "#>=" y (atom "0"))) $
  Conj (Conj sumEAtLeastX
             sumEsAtLeastY) $
  Term $ OpTerm "#>=" (OpTerm "+" x y) (fmap (Just . Just . Just . Just) lowerBound)
fromCountyExpression' toTerm (D.CallDescriptor D.SCounty name vars) lowerBound = Term $ Apply "descriptor" $ (atom $ T.unpack name) : fmap (fmap (Just . Just) . toTerm) vars <> [fmap (Just . Just) lowerBound, VariableTerm Nothing, VariableTerm (Just Nothing)]
fromCountyExpression' toTerm (D.CanAccess D.SCounty name vars state) lowerBound = Term $ atom "todo" -- IntroVarExpr $ Conj (Term $ Apply "reachableNode" [VariableTerm Nothing, atom "state"]) (Term $ Apply "node" [VariableTerm Nothing, ListTerm (atom (T.unpack name): fmap (fmap (Just . Just . Just) . toTerm) vars) Nothing])
fromCountyExpression' toTerm (D.Count rel v expr) lowerBound = Term $ atom "todo" -- IntroVarExpr $ Conj (fromShuffle rel (fmap (Just . Just . Just) $ toTerm v) (VariableTerm Nothing)) $ fmap (maybe (Just Nothing) $ maybe (Just (Just Nothing)) $ maybe Nothing (Just . Just . Just)) $ fromExpression' (maybe (VariableTerm Nothing) (fmap Just . toTerm)) expr
fromCountyExpression' toTerm (D.Min D.SCounty []) lowerBound = Term $ atom "true"
fromCountyExpression' toTerm (D.Min D.SCounty xs) lowerBound = foldl1 Conj $ fmap (\e -> fromCountyExpression' toTerm e lowerBound) xs
fromCountyExpression' toTerm (D.Max D.SCounty []) lowerBound = fmap (Just . Just) $ Term $ OpTerm "#>=" (atom "0") lowerBound
fromCountyExpression' toTerm (D.Max D.SCounty xs) lowerBound = foldl1 Disj $ fmap (\e -> fromCountyExpression' toTerm e lowerBound) xs
fromCountyExpression' toTerm (D.Cast expr) lowerBound = Disj (fmap (Just . Just) $ Term $ OpTerm "#>=" (atom "0") lowerBound) (fromExpression' toTerm expr)
fromCountyExpression' toTerm (D.Consume _ _ _ _) lowerBound = Term $ atom "true"

fromShuffle :: D.Relation -> Term v -> Term v -> Expr v
fromShuffle (D.Forward name) to from = Term $ Apply "shuffle" $ [StringTerm (T.unpack name), from, to]
fromShuffle (D.Backward name) to from = Term $ Apply "shuffle" $ [StringTerm (T.unpack name), to, from]

makeDescriptorStatement :: DescriptorIdent 'Truthy -> [D.Value] -> Expr (Maybe (Maybe String)) -> Statement
makeDescriptorStatement (TruthyDescriptorIdent name) values expr = Statement "descriptor" $ Match (atom $ T.unpack name) $ helper values M.empty $ expr where --Conj (Conj (Term $ Apply "State" [VariableTerm Nothing]) (Term $ Apply "State" [VariableTerm $ Just Nothing])) expr where
  helper :: [D.Value] -> Map String v -> Expr (Maybe (Maybe String)) -> BindVars v
  helper [] knownVariables expr = IntroVar $ IntroVar $ Match (VariableTerm Nothing) $ Match (VariableTerm $ Just Nothing) $ DefinedBy $ translateKnownVariables knownVariables expr
  helper (D.Variable varName : values) knownVariables expr = IntroVar $ Match (VariableTerm Nothing) $ helper values (M.insert (T.unpack varName) Nothing $ fmap Just knownVariables) expr
  helper (D.ConstantValue value : values) knownVariables expr = Match (fromThingy value) $ helper values knownVariables expr
  translateKnownVariables knownVariables = fmap (fmap (fmap (knownVariables M.!)))

makeCountyDescriptorStatement :: DescriptorIdent 'County -> [D.Value] -> Expr (Maybe (Maybe (Maybe String))) -> Statement
makeCountyDescriptorStatement (CountyDescriptorIdent name) values expr = Statement "descriptor" $ Match (atom $ T.unpack name) $ helper values M.empty expr where
  helper :: [D.Value] -> Map String v -> Expr (Maybe (Maybe (Maybe String))) -> BindVars v
  helper [] knownVariables expr = IntroVar $ IntroVar $ IntroVar $ Match (VariableTerm (Just (Just Nothing))) $ Match (VariableTerm Nothing) $ Match (VariableTerm $ Just Nothing) $ DefinedBy $ translateKnownVariables knownVariables expr
  helper (D.Variable varName : values) knownVariables expr = IntroVar $ Match (VariableTerm Nothing) $ helper values (M.insert (T.unpack varName) Nothing $ fmap Just knownVariables) expr
  helper (D.ConstantValue value : values) knownVariables expr = Match (fromThingy value) $ helper values knownVariables expr
  translateKnownVariables knownVariables = fmap (fmap (fmap (fmap (knownVariables M.!))))

fromGameDef :: GameDef -> Result
fromGameDef gameDef = uncurry fromLogic (_defLogic gameDef) <> fromDescriptors (_defDescriptors gameDef) (_defDescriptorDefinitionsTruthy gameDef) (_defDescriptorDefinitionsCounty gameDef)

atom s = Apply s []

foldl1' b _ [] = b
foldl1' _ c xs = foldl1 c xs


renderResult :: Result -> String
renderResult (Result rs) = (preamble <>) $ flip appEndo "" $ intercalate (e "\n") $ fmap renderStatement rs

preamble :: String
preamble = unlines [
    ":- set_prolog_flag(verbose, silent)."
  --, ":- use module(library(tabling))."
  , ":- use_module(library(clpfd))."
  , ":- style_check(-singleton)."
  , ":- table reachableNode/2."
  , ":- discontiguous descriptor/3."
  , ":- discontiguous descriptor/4."
  , ":- discontiguous shuffle/3."
  , ":- discontiguous goal/0."
  , ":- discontiguous left/2."
  , ":- discontiguous right/2."
  , "shuffle(A,B,C) :- false." -- keep this here to avoid issues when rendering with empty shuffles (ensures shuffle/3 is defined)
  , "goal :- false."
  ]

renderStatement :: Statement -> Endo String
renderStatement (Statement n s) = e n <> e "(" <> renderBindVarsWith "" absurd (fmap (\n -> "X" <> show n) [0..]) s

renderBindVarsWith :: String -> (v -> String) -> [String] -> BindVars v -> Endo String
renderBindVarsWith prefix showVar (v': freeVars) (IntroVar s) = renderBindVarsWith prefix (maybe v' showVar) freeVars s
renderBindVarsWith prefix showVar freeVars (Match t s) = e prefix <> renderTermWith showVar t <> renderBindVarsWith ", " showVar freeVars s
renderBindVarsWith _ showVar freeVars (DefinedBy expr) = e ") :- " <> renderExprWith showVar freeVars expr <> e "."
renderBindVarsWith _ _ _ Defined = e ")."

renderExprWith :: (v -> String) -> [String] -> Expr v -> Endo String
renderExprWith showVar freeVars = renderExprWith'' showVar freeVars . bubbleIntros

bubbleIntros :: Expr v -> Expr v
bubbleIntros (Conj (bubbleIntros -> e1) (bubbleIntros -> e2)) = bubbleIntrosHelper e1 e2 Conj
bubbleIntros (Disj (bubbleIntros -> e1) (bubbleIntros -> e2)) = bubbleIntrosHelper e1 e2 Disj
bubbleIntros (IntroVarExpr (bubbleIntros -> e)) = IntroVarExpr e
bubbleIntros e = e

bubbleIntrosHelper :: Expr v -> Expr v -> (forall v'. Expr v' -> Expr v' -> Expr v') -> Expr v
bubbleIntrosHelper (IntroVarExpr e1) e2 f = IntroVarExpr $ bubbleIntrosHelper e1 (fmap Just e2) f
bubbleIntrosHelper e1 (IntroVarExpr e2) f = IntroVarExpr $ bubbleIntrosHelper (fmap Just e1) e2 f
bubbleIntrosHelper e1 e2 f = f e1 e2
{-
data Expr v = Term (Term v)
            | Conj (Expr v) (Expr v)
            | Disj (Expr v) (Expr v)
            | IntroVarExpr (Expr (Maybe v))
            | EqTerms (Term v) (Term v)
-}

renderExprWith'' :: (v -> String) -> [String] -> Expr v -> Endo String
renderExprWith'' showVar (v:freeVars) (IntroVarExpr e) = renderExprWith'' (maybe v showVar) freeVars e
renderExprWith'' showVar _ e = renderExprWith' showVar e

renderExprWith' :: (v -> String) -> Expr v -> Endo String
renderExprWith' showVar (Term t) = renderTermWith showVar t
renderExprWith' showVar (Conj e1 e2) = e "(" <> renderExprWith' showVar e1 <> e ", " <> renderExprWith' showVar e2 <> e ")"
renderExprWith' showVar (Disj e1 e2) = e "(" <> renderExprWith' showVar e1 <> e "; " <> renderExprWith' showVar e2 <> e ")"
renderExprWith' showVar (IntroVarExpr e) = error "unexpected introVars"
renderExprWith' showVar (EqTerms t1 t2) = renderTermWith showVar t1 <> e " = " <> renderTermWith showVar t2

renderTermWith :: (v -> String) -> Term v -> Endo String
renderTermWith showVar (Apply s []) = e s
renderTermWith showVar (Apply s ts) = e s <> e "(" <> intercalate (e ",") (fmap (renderTermWith showVar) ts) <> e ")"
renderTermWith showVar (VariableTerm v) = e $ showVar v
renderTermWith showVar (OpTerm o t t') = parens $ renderTermWith showVar t <> e " " <> e o <> e " " <> renderTermWith showVar t'
renderTermWith _ (StringTerm s) = e $ show s
renderTermWith showVar (ListTerm xs t) = e "[" <> intercalate (e ",") (fmap (renderTermWith showVar) xs) <> maybe mempty (\t' -> e "|" <> renderTermWith showVar t') t <> e "]"

parens (Endo r) = Endo $ ('(' :) . r . (')' :)

e :: String -> Endo String
e s = Endo $ (s <>)

{-
target vX:
  ?Y - Warps -> vX: [warp vY].



descriptor(target, X) :-
  shuffle("Warps", X, Y), reachable(warp, Y).

Statement "descriptor" $ Match (Apply "target" []) $ IntroVar $ Match (Apply "cons" [VariableTerm Nothing, Apply "nil" []]) $ IntroVar $ DefinedBy $ Conj (_) $ Term $ Apply "reachable" [Apply "warp" [], listTerm([VariableTerm Nothing])]

item CanSpin:
  item Sword,
  item SpinAttack.

descriptor(item, "CanSpin") :- descriptor(item, "Sword"), descriptor(item, "SpinAttack").



reachable(X, Y) :- node(A, [X|Y]), reachableNode(A).
reachableNode(A) :- edge(B,A,X), X, reachableNode(B).

-}