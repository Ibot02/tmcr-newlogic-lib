{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
module TMCR.Logic.Shuffle where

import TMCR.Logic.Common

import Text.Megaparsec as MP
import Text.Megaparsec.Char as MP
import qualified Text.Megaparsec.Char.Lexer as MPL
import Control.Monad.Combinators.Expr

import Control.Monad.State
import Control.Monad.Except

import Data.Text (Text())
import qualified Data.Text as T

import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as MM
import Data.Traversable (for)

import Data.Functor.Foldable
import Data.Functor.Foldable.TH

import System.Random

import Control.Lens
import Control.Lens.TH
import Control.Monad.Reader (MonadReader, runReader)
import Data.List (partition)
import Data.Maybe (catMaybes)

type Parser = ParserC ()

data ShuffleInstruction =
      ShuffleDataLookup DataLookup
    | ShuffleSetSpec SetSpec
    | ShuffleCountLiteral Nteger
    | ShufflePlaceholder -- ...
    | ShuffleCall ShuffleName
    | ShuffleReverse ShuffleInstruction -- from
    | ShuffleRepeat ShuffleInstruction
    | ShuffleRepeatIndividually ShuffleInstruction
    | ShuffleMap ShuffleInstruction ShuffleInstruction [ShuffleInstruction]
    | ShuffleConnect ShuffleInstruction ShuffleInstruction
    | ShuffleUnion ShuffleInstruction ShuffleInstruction
    | ShuffleThen ShuffleInstruction ShuffleInstruction
    | ShuffleMatch SetSpec ShuffleInstruction [(SetSpec, ShuffleInstruction)]
    deriving (Eq, Ord, Show)

type ShuffleEval = ShuffleEval' ShuffleStepIdent

data ShuffleEval' ident =
      ShuffleEvalConst [(Thingy, Nteger, Thingy)]
    | ShuffleEvalRefer ident
    | ShuffleEvalReverse (ShuffleEval' ident)
    | ShuffleEvalRepeat (ShuffleEval' ident)
    | ShuffleEvalRepeatIndividually (ShuffleEval' ident)
    | ShuffleEvalMap (ShuffleEval' ident) (ShuffleEval' ident) [ShuffleEval' ident]
    | ShuffleEvalMapPartial [[(Thingy, Nteger, Thingy)]] (Maybe (ShuffleEval' ident)) [[(Thingy, Nteger, Thingy)]] (Maybe (ShuffleEval' ident)) [(Thingy, Nteger, Thingy)]
    | ShuffleEvalConnect (ShuffleEval' ident) (ShuffleEval' ident)
    | ShuffleEvalUnion (ShuffleEval' ident) (ShuffleEval' ident)
    | ShuffleEvalThen (ShuffleEval' ident) (ShuffleEval' ident)
    | ShuffleEvalMatch SetSpec (ShuffleEval' ident) [(SetSpec, ShuffleEval' ident)]
    deriving (Eq, Ord, Show, Functor)

data ShuffleStatement =
      DefineShuffle Name ShuffleInstruction
    | ExpandShuffle Name ShuffleInstruction
    deriving (Eq, Ord, Show)

data SetSpec = SetSpec (M.Map PossiblyScopedName Nteger)
    deriving (Eq, Ord, Show)

type ShuffleName = Text

data DataLookup = DataLookup {
      location :: [DataStep]
    , foreach :: Maybe ([DataStep], DataTarget)
    , collect :: ([DataStep], DataTarget)
    } deriving (Eq, Ord, Show)

data DataStep =
      DataTraverse DataTraverseStep
    | DataFilter DataFilterStep
    deriving (Eq, Ord, Show)

data DataTraverseStep = DataTraverseStep {
      traverseAttribute :: Name
    , traversalScoping :: Maybe Name
    } deriving (Eq, Ord, Show)

data DataFilterStep = DataFilterStep {
      filterLocation :: [DataStep]
    , filterAttribute :: DataTarget
    , filterCondition :: FilterCondition
    } deriving (Eq, Ord, Show)

data FilterCondition = --do we want any other filters? e.g. matching regex?
    FilterEQ PossiblyScopedName
    deriving (Eq, Ord, Show)

data DataTarget = DataTarget {
      targetedAttribute :: Name
    , targetScoping :: TargetScoping
    } deriving (Eq, Ord, Show)

data TargetScoping = TargetUnscoped | TargetScoped | TargetGlobal
    deriving (Eq, Ord, Show, Enum, Bounded)

parseDataLookup :: Parser DataLookup
parseDataLookup = do
    loc <- parseDataSteps
    f <- MP.optional $ do
        MPL.symbol sc "foreach"
        parseDataStepsToTarget
    MPL.symbol sc "collect"
    c <- parseDataStepsToTarget
    return $ DataLookup loc f c

parseDataSteps :: Parser [DataStep]
parseDataSteps = parseDataStep `sepBy` MPL.symbol sc ","

parseDataStepsToTarget :: Parser ([DataStep], DataTarget)
parseDataStepsToTarget = do
    loc <- many (parseDataStep <* MPL.symbol sc ",")
    t <- parseDataTarget
    return (loc, t)

parseDataStep :: Parser DataStep
parseDataStep = (DataFilter <$> parseDataFilterStep) <|> (DataTraverse <$> parseDataTraverseStep)

parseDataFilterStep :: Parser DataFilterStep
parseDataFilterStep = do
    MPL.symbol sc "filter"
    MPL.symbol sc "any"
    (loc, t) <- parseDataStepsToTarget
    c <- parseFilterCondition
    return $ DataFilterStep loc t c

parseFilterCondition :: Parser FilterCondition
parseFilterCondition = parseFilterEq where
    parseFilterEq = do
        MPL.symbol sc "is"
        FilterEQ <$> parsePossiblyScopedName

parseDataTraverseStep :: Parser DataTraverseStep
parseDataTraverseStep = do
    n <- parseDataAttrName
    scope <- MP.optional $ do
                MPL.symbol sc "by"
                parseDataAttrName
    return $ DataTraverseStep n scope

parseDataTarget :: Parser DataTarget
parseDataTarget = do
    scope <- (TargetUnscoped <$ MPL.symbol sc "unscoped") <|> (TargetScoped <$ MPL.symbol sc "local") <|> (TargetGlobal <$ MPL.symbol sc "global")
    attr <- parseDataAttrName

    return $ DataTarget attr scope

parseDataAttrName :: Parser Name
parseDataAttrName = MPL.lexeme sc parseDataAttrName'
parseDataAttrName' :: Parser Name
parseDataAttrName' = fmap T.pack $ MP.single '\'' *> MP.manyTill MPL.charLiteral (MP.single '\'')

parseShuffleInstruction :: Parser ShuffleInstruction
parseShuffleInstruction = makeExprParser terms ops where
    terms = parseShuffleDataLookup <|> parseShuffleSetSpec <|> parseShuffleCountLiteral <|> parseShufflePlaceholder <|> parseShuffleCall <|> parseShuffleMatch <|> parseShuffleMap <|> between (MPL.symbol sc "(") (MPL.symbol sc ")") parseShuffleInstruction
    ops = [ [ prefixReverse ]
          , [ binUnion ]
          , [ binThen ]
          , [ prefixRepeats ]
          , [ binConnect ]
          ]
    prefixReverse = Prefix $ op "from" ShuffleReverse
    binUnion = InfixR $ op "union" ShuffleUnion
    binThen = InfixR $ op "then" ShuffleThen
    prefixRepeats = Prefix $ do
        MPL.symbol sc "repeat"
        MP.option ShuffleRepeat $ do
            MPL.symbol sc "individually"
            return ShuffleRepeatIndividually
    binConnect = InfixR $ op "connect" ShuffleConnect
    op n f = f <$ MPL.symbol sc n


parseShuffleMap = parseShuffleMap' <|> parseShuffleTake
parseShuffleMap' = do
    MPL.symbol sc "map"
    s1 <- parseShuffleInstruction
    MPL.symbol sc "to"
    s2 <- parseShuffleInstruction
    sIncl <- MP.option [] $ do
        MPL.symbol sc "including"
        parseShuffleInstruction `sepBy` MPL.symbol sc ","
    return $ ShuffleMap s1 s2 sIncl

parseShuffleTake = do
    MPL.symbol sc "take"
    s1 <- parseShuffleInstruction
    s2 <- parseShuffleInstruction
    return $ ShuffleMap s1 s2 []

parseShuffleDataLookup = do
    MPL.symbol sc "data"
    ShuffleDataLookup <$> parseDataLookup

parseShuffleSetSpec = ShuffleSetSpec <$> parseSetSpec
parseSetSpec = fmap (SetSpec . M.fromList) $ between (MPL.symbol sc "{") (MPL.symbol sc "}") $ parseShuffleSetSpecEntry `sepBy` MPL.symbol sc "," where
    parseShuffleSetSpecEntry = do
        n <- parsePossiblyScopedName
        c <- MP.option (Finite 1) $ do
            MPL.symbol sc ":"
            parseNteger
        return (n,c)
parseShuffleCountLiteral = ShuffleCountLiteral <$> parseNteger
parseShufflePlaceholder = ShufflePlaceholder <$ (MPL.symbol sc "..." <|> MPL.symbol sc "…")
parseShuffleCall = ShuffleCall <$> parseRelName
parseShuffleMatch = do
    MPL.symbol sc "match"
    s1 <- parseSetSpec
    MPL.symbol sc "in"
    s2 <- parseShuffleInstruction
    MPL.symbol sc "with"
    s3 <- between (MPL.symbol sc "(") (MPL.symbol sc ")") $ many $ do
        ss <- parseSetSpec
        MPL.symbol sc "->" <|> MPL.symbol sc "→"
        res <- parseShuffleInstruction
        return (ss, res)
    return $ ShuffleMatch s1 s2 s3

parseShuffleStatements :: Parser [ShuffleStatement]
parseShuffleStatements = many $ MPL.nonIndented sc $ parseShuffleStatementDef <|> parseShuffleStatementExt

parseShuffleStatementDef :: Parser ShuffleStatement
parseShuffleStatementDef = do
    name <- parseName
    MPL.symbol sc ":"
    instr <- parseShuffleInstruction
    return $ DefineShuffle name instr 

parseShuffleStatementExt :: Parser ShuffleStatement
parseShuffleStatementExt = do
    MPL.symbol sc "extend"
    name <- parseName
    MPL.symbol sc "by"
    instr <- parseShuffleInstruction
    return $ ExpandShuffle name instr
    --todo validate no placeholders are used in extensions


{-data ShuffleValue = ShuffleValue {
          mainPart :: ShuffleValue' ShuffleInstruction
        , expansions :: [ShuffleValue' ShuffleInstruction]
    } deriving (Eq, Ord, Show)
    -}
type ShuffleValue = ShuffleValue' ShuffleInstruction

data ShuffleValue' a = Progress (Thingy, Thingy) (ShuffleValue' a)
                     | Delay (ShuffleValue' a)
                     | Remaining a
                     | Loop [(Thingy, Thingy)]
                     | End
                     deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Applicative ShuffleValue' where
    pure = Remaining
    (<*>) = ap

instance Monad ShuffleValue' where
    Progress x y >>= f = Progress x $ y >>= f
    Delay x >>= f = Delay $ x >>= f
    Remaining x >>= f = f x
    Loop xs >>= _ = Loop xs
    End >>= _ = End

getAllPartial' :: ShuffleValue -> (Bool, Thingy) -> [(Thingy, Nteger)]
getAllPartial' x (isForwards, y) = go x M.empty where
    go (Remaining _) m = M.toList m
    go (Progress x v) m | cond x = go v $ M.adjust increment (extr x) m
    go (Delay x) m = go x m
    go (Loop xs) m = M.toList $ M.union (M.fromList $ fmap ((flip (,) Infinite) . extr) $ filter cond xs) m
    go End m = M.toList m
    cond (a,b) = if isForwards then a == y else b == y
    extr (a,b) = if isForwards then b else a
    increment (Finite !x) = Finite $ x + 1
    increment Infinite = Infinite

type RandomSeed = StdGen

data ShuffleStepResult = Final ShuffleValue
                       | Success (ShuffleValue, RandomSeed)
                       | DependsShuffle [(ShuffleName, Bool)]

-- step :: M.Map (ShuffleName, Bool) (ShuffleValue' ShuffleInstruction, Maybe RandomSeed) -> (ShuffleName, Bool) -> ShuffleStepResult
-- step m name = case M.lookup name m of
--     Nothing -> Final $ End
--     Just (x, Nothing) -> Final x
--     Just (x, Just r) -> (\case
--         Left deps -> DependsShuffle deps
--         Right (res, r') -> Success (join res, r')) $ runExcept $ flip runStateT r $ for x $ \case
--             ShuffleDataLookup x -> return $ valFromList $ evalDataLookup x
--             ShuffleSetSpec x -> return $ evalSetSpec x
--             ShuffleCountLiteral Infinite -> return $ Loop [(Global "", Global "")]
--             ShuffleCountLiteral (Finite n) -> return $ valFromList $ replicate n (Global "", Global "")
--             ShufflePlaceholder -> _
--             ShuffleCall name -> _
    -- | ShuffleReverse ShuffleInstruction -- from
    -- | ShuffleRepeat ShuffleInstruction
    -- | ShuffleRepeatIndividually ShuffleInstruction
    -- | ShuffleMap ShuffleInstruction ShuffleInstruction [ShuffleInstruction]
    -- | ShuffleConnect ShuffleInstruction ShuffleInstruction
    -- | ShuffleUnion ShuffleInstruction ShuffleInstruction
    -- | ShuffleThen ShuffleInstruction ShuffleInstruction
    -- | ShuffleMatch SetSpec ShuffleInstruction [(SetSpec, ShuffleInstruction)]

        
valFromList :: [(Thingy, Thingy)] -> ShuffleValue
valFromList [] = End
valFromList (x:xs) = Progress x $ valFromList xs

evalDataLookup :: DataLookup -> [(Thingy, Nteger, Thingy)]
evalDataLookup = undefined

evalSetSpec :: SetSpec -> [(Thingy, Nteger, Thingy)]
evalSetSpec = undefined

data ShuffleValue'' = ValuePartial [(Thingy, Nteger, Thingy)] (Maybe ShuffleStepIdent)
                    | ValueEval ShuffleEval RandomSeed
                    deriving (Eq, Show)

type ShuffleStepIdent = (ShuffleName, Bool, Int)

data ShufflesProgress = ShufflesProgress {
                          _currentLatest :: M.Map (ShuffleName, Bool) ([ShuffleStepIdent], Int)
                        , _current :: M.Map ShuffleStepIdent ShuffleValue''
                        }
                    deriving (Eq, Show)

$(makeLenses 'ShufflesProgress)

instance Semigroup ShufflesProgress where
    ShufflesProgress a b <> ShufflesProgress a' b' = ShufflesProgress (a <> a') (b <> b')

instance Monoid ShufflesProgress where
    mempty = ShufflesProgress mempty mempty

convertShuffles :: RandomSeed -> M.Map ShuffleName (ShuffleInstruction, [ShuffleInstruction]) -> ShufflesProgress
convertShuffles seed = foldMap (\(name, (main, exts), seed) -> makeProgress (name, False) (Just main) seed <> makeProgress (name, True) (foldr makeUnion Nothing exts) seed) . snd . foldr (\(name, content) (seed, xs) -> let (seed', seed'') = split seed in (seed', (name, content, seed'') : xs)) (seed, []) . M.toList where
        makeUnion x Nothing = Just x
        makeUnion x (Just y) = Just (ShuffleUnion x y)
        makeProgress _ Nothing _ = mempty
        makeProgress ident@(name, b) (Just x) seed = ShufflesProgress (M.singleton ident ([(name, b, 0)], 1)) $ M.singleton (name, b, 0) $ ValueEval (convert name x) seed
        convert _    (ShuffleDataLookup x) = ShuffleEvalConst $ evalDataLookup x
        convert _    (ShuffleSetSpec x) = ShuffleEvalConst $ evalSetSpec x
        convert _    (ShuffleCountLiteral n) = ShuffleEvalConst [(Global "", n, Global "")]
        convert name ShufflePlaceholder = ShuffleEvalRefer (name, True, 0)
        convert _    (ShuffleCall name') = ShuffleEvalRefer (name', False, 0)
        convert name (ShuffleReverse x) = ShuffleEvalReverse $ convert name x
        convert name (ShuffleRepeat x) = ShuffleEvalRepeat $ convert name x
        convert name (ShuffleRepeatIndividually x) = ShuffleEvalRepeatIndividually $ convert name x
        convert name (ShuffleMap a b cs) = ShuffleEvalMap (convert name a) (convert name b) (convert name <$> cs)
        convert name (ShuffleConnect a b) = ShuffleEvalConnect (convert name a) (convert name b)
        convert name (ShuffleUnion a b) = ShuffleEvalUnion (convert name a) (convert name b)
        convert name (ShuffleThen a b) = ShuffleEvalThen (convert name a) (convert name b)
        convert name (ShuffleMatch x a xs) = ShuffleEvalMatch x (convert name a) ((\(x', a') -> (x', convert name a')) <$> xs)

data ShuffleStepResult' = ShuffleStepResult ShufflesProgress [ShuffleStepIdent] Bool

stepShuffle :: ShufflesProgress -> ShuffleStepIdent -> ShuffleStepResult'
stepShuffle progress ident = t $ M.lookup ident (progress ^. current) where
        t Nothing = ShuffleStepResult progress [] False
        t (Just x) = t' x
        t' (ValuePartial _ Nothing) = ShuffleStepResult (progress & currentLatest . traverse . _1 %~ filter (/= ident)) [] False
        t' (ValuePartial _ (Just x)) = ShuffleStepResult (progress & currentLatest . traverse . _1 . traverse %~ \y -> if y == ident then x else y) [x] False
        t' (ValueEval x seed) = case flip runReader progress $ runExceptT $ runStateT (eval x) (seed, 0, mempty) of
            Left ident -> ShuffleStepResult progress [ident] False
            Right ((r, e), (rand, count, m)) -> (\p -> ShuffleStepResult p [] True) $ flip execState progress $ do
                let (name, isExt, _) = ident
                offset <- fmap (maybe 0 snd) $ currentLatest . at (name, isExt) <<%= (_Just . _2 +~ count)
                let f :: ShuffleEval' (Either ShuffleStepIdent Int) -> ShuffleEval
                    f = fmap (either id (\c -> (name, isExt, offset + c)))
                rand' <- flip execStateT rand $ for (M.toList m) $ \(i, e) -> do
                    rand'' <- state split
                    lift $ current . at (name, isExt, i + offset) .= (Just $ ValueEval (f e) rand'')
                    return ()
                ix <- for e $ \e -> do
                    ix <- fmap (maybe 0 snd) $ currentLatest . at (name, isExt) <<%= (_Just . _2 +~ 1)
                    current . at (name, isExt, ix) .= (Just $ ValueEval (f e) rand')
                    return (name, isExt, ix)
                current . at ident . _Just .= ValuePartial r ix

eval :: (MonadState (RandomSeed, Int, M.Map Int (ShuffleEval' (Either ShuffleStepIdent Int))) m, MonadError ShuffleStepIdent m, MonadReader ShufflesProgress m) => ShuffleEval -> m ([(Thingy, Nteger, Thingy)], Maybe (ShuffleEval' (Either ShuffleStepIdent Int)))
eval (ShuffleEvalConst a) = return (a, Nothing)
eval (ShuffleEvalRefer ident) = do
    x <- view $ current . at ident
    case x of
        Nothing -> return ([], Nothing)
        Just (ValuePartial v r) -> return (v,ShuffleEvalRefer . Left <$> r)
        Just (ValueEval _ _) -> throwError ident
eval (ShuffleEvalReverse x) = do
    (a,e) <- eval x
    return ((\(a1,n,a2) -> (a2,n,a1)) <$> a, ShuffleEvalReverse <$> e)
eval x'@(ShuffleEvalRepeat x) = eval (ShuffleEvalThen x x')
eval (ShuffleEvalRepeatIndividually x) = do
    (a,_) <- eval x
    eval (ShuffleEvalRepeat (ShuffleEvalConst a))
eval (ShuffleEvalConnect x y) = do
    (a, e) <- eval x
    (b, e') <- eval y
    let 
        ensureRefer x@(ShuffleEvalRefer _) = return x
        ensureRefer e = do
            k <- _2 <<+= 1
            _3 . at k .= Just e
            return $ ShuffleEvalRefer $ Right k
    ex <- traverse ensureRefer e
    ex' <- traverse ensureRefer e'
    let r = case (e, e') of
            (Nothing, Nothing) -> Nothing
            (Just e, Nothing) -> Just $ ShuffleEvalConnect e (ShuffleEvalConst b)
            (Nothing, Just e) -> Just $ ShuffleEvalConnect (ShuffleEvalConst a) e
            (Just e, Just e') -> Just $ ShuffleEvalThen (ShuffleEvalUnion (ShuffleEvalConnect e (ShuffleEvalConst b)) (ShuffleEvalConnect (ShuffleEvalConst a) e')) (ShuffleEvalConnect e e')
    return ([(x, multiplyNteger n m, z) | (x, n, y) <- a, (y', m, z) <- b, y == y'], r) where
        multiplyNteger Infinite Infinite = Infinite
        multiplyNteger Infinite (Finite 0) = Finite 0
        multiplyNteger Infinite (Finite _) = Infinite
        multiplyNteger (Finite 0) Infinite = Finite 0
        multiplyNteger (Finite _) Infinite = Infinite
        multiplyNteger (Finite n) (Finite m) = Finite $ n * m
eval (ShuffleEvalUnion x y) = do
    (a, e) <- eval x
    (b, e') <- eval y
    let r = makeUnionMaybe e e'
    return (a <> b, r)
eval (ShuffleEvalThen x y) = do
    (a, e) <- eval x
    case e of
        Nothing -> return (a,Just $ Left <$> y)
        Just e -> return (a, Just $ ShuffleEvalThen e $ Left <$> y)
eval (ShuffleEvalMap x y zs) = do
    cs <- traverse eval zs
    case (catMaybes $ snd <$> cs) of
        [] -> eval (ShuffleEvalMapPartial [] (Just x) [] (Just y) (foldMap fst cs))
        zs' -> return $ (,) [] $ Just $ ShuffleEvalMap (fmap Left x) (fmap Left y) $ ShuffleEvalConst (foldMap fst cs) : zs'
eval (ShuffleEvalMapPartial [] Nothing bs y []) = return ([], Nothing)
eval (ShuffleEvalMapPartial as x bs y cs) = do
    (r, (as', x', bs', y', cs')) <- evalShuffleMapPartial as x bs y cs
    return (r, Just $ ShuffleEvalMapPartial as' x' bs' y' cs')
eval (ShuffleEvalMatch s'@(SetSpec s) x xs) = do
    (a, e) <- eval x
    let a' = a ^.. traverse . filtered (\(ax,_,_) -> M.member ax s) . _3
        xs' = xs & traverse . _1 %~ (\(SetSpec s) -> SetSpec $ M.difference s $ M.fromList $ fmap (\x -> (x,())) a')
        (xs'', rs) = partition (\(SetSpec s,_) -> null s) xs'
        m = case (e, null rs) of
                (Just e, False) -> Just (ShuffleEvalMatch s' e $ fmap (fmap (fmap Left)) rs)
                _ -> Nothing
        x' = makeUnion $ fmap snd xs''
    (b, e') <- eval x'
    return (b, makeUnionMaybe e' m)

evalShuffleMapPartial :: (MonadState
   (RandomSeed, Int,
    M.Map Int (ShuffleEval' (Either ShuffleStepIdent Int)))
   m,
 MonadError ShuffleStepIdent m, MonadReader ShufflesProgress m) =>
    [[(Thingy, Nteger, Thingy)]]
    -> Maybe ShuffleEval
    -> [[(Thingy, Nteger, Thingy)]]
    -> Maybe (ShuffleEval' ShuffleStepIdent)
    -> [a1]
    -> m ([(Thingy, Nteger, Thingy)],
      ([[(Thingy, Nteger, Thingy)]],
       Maybe (ShuffleEval' (Either ShuffleStepIdent Int)),
       [[(Thingy, Nteger, Thingy)]],
       Maybe (ShuffleEval' (Either ShuffleStepIdent Int)), [a2]))
evalShuffleMapPartial [] (Just x) bs y [] = do
    (a, e) <- eval x
    return ([], ([a],e,bs,(fmap (fmap Left) y),[]))
evalShuffleMapPartial (a:as) x [] Nothing [] = error "map failed" --todo
evalShuffleMapPartial (a:as) x [] (Just y) [] = do
                                                (b, e) <- eval y
                                                return ([], (as,(fmap (fmap Left) x),([b]),e,[]))
evalShuffleMapPartial as@(a:as') x (b:bs) y [] = case [(a',n,x) | (a',n,x) <- a, (x', _, _) <- b, x == x'] of
                                                        [] -> do
                                                            (r,(as',x',bs',y',cs')) <- evalShuffleMapPartial as x bs y []
                                                            return (r, (as', x', b:bs', y', cs'))
                                                        _ -> do
                                                            (r, a', b') <- chooseRandomMatching a b
                                                            return (r, (consNonempty a' as', fmap (fmap Left) x, consNonempty b' bs, fmap (fmap Left) y, []))
evalShuffleMapPartial _ _ _ _ (c:cs) = error "constraints not yet implemented" --todo

consNonempty :: [a] -> [[a]] -> [[a]]
consNonempty [] xs = xs
consNonempty x xs = x:xs

chooseRandomMatching as bs = do
    rand <- use _1
    let cas = M.fromListWith (<>) $ fmap (\(a,n,c) -> (c,[(a,n)])) as
        cbs = M.fromListWith (<>) $ fmap (\(c,n,b) -> (c,[(n,b)])) bs
        (r, (rand', remA, remB)) = flip runState (rand, [], []) $ do
            matches <- MM.mergeA (
                    MM.traverseMaybeMissing $ \c as -> _2 <>= [(a,n,c) | (a,n) <- as] >> pure Nothing
                ) (
                    MM.traverseMaybeMissing $ \c bs -> _3 <>= [(c,n,b) | (n,b) <- bs] >> pure Nothing
                ) (
                    MM.zipWithMatched $ \c as bs -> let go [] r = r; go ((Finite n, a):as) (i,x) = go as (i,replicate n a <> x); go ((Infinite, a):as) (i,x) = (a:i,x) in (go ((\(x,y) -> (y,x)) <$> as) ([],[]), go bs ([],[]))
                ) cas cbs
            fmap concat $ for (M.toList matches) $ \case
                (c,(([],as), ([], bs))) -> do
                    as' <- zoom _1 $ randomOrder as
                    bs' <- zoom _1 $ randomOrder bs
                    _2 <>= [(a, Finite 1, c) | a <- drop (length bs') as']
                    _3 <>= [(b, Finite 1, c) | b <- drop (length as') bs']
                    return $ zipWith (\a b -> (a, Finite 1, b)) as' bs'
                (c,(([],as), (infB, bs))) -> do
                    _3 <>= [(c,Finite 1,b) | b <- bs]
                    for as $ \a -> do
                        b <- zoom _1 $ randomChoice infB
                        return (a, Finite 1, b)
                (c, ((infA,as), ([], bs))) -> do
                    _2 <>= [(a,Finite 1,c) | a <- as]
                    for bs $ \b -> do
                        a <- zoom _1 $ randomChoice infA
                        return (a, Finite 1, b)
                (c, ((infA, as), (infB, bs))) -> do
                    acs <- for as $ \a -> do
                        b <- zoom _1 $ randomChoice infB
                        return (a, Finite 1, b)
                    bcs <- for bs $ \b -> do
                        a <- zoom _1 $ randomChoice infA
                        return (a, Finite 1, b)
                    aib <- fmap concat $ for infA $ \a -> for infB $ \b -> return (a, Infinite, b)
                    return $ aib <> acs <> bcs
    _1 .= rand'
    return (r, remA, remB)

randomChoice :: (MonadState RandomSeed m) => [a] -> m a
randomChoice xs = do
    index <- state $ randomR (0, length xs - 1)
    return $ xs !! index

randomOrder :: (MonadState RandomSeed m) => [a] -> m [a]
randomOrder [] = return []
randomOrder xs = do
    index <- state $ randomR (0, length xs - 1)
    rem <- randomOrder $ take index xs <> drop (index + 1) xs
    return $ xs !! index : rem

makeUnionMaybe = binMaybe ShuffleEvalUnion
binMaybe f e e' = case (e, e') of
            (Nothing, Nothing) -> Nothing
            (Just e, Nothing) -> Just e
            (Nothing, Just e) -> Just e
            (Just e, Just e') -> Just $ f e e'
makeUnion [] = ShuffleEvalConst []
makeUnion [x] = x
makeUnion (x:xs) = ShuffleEvalUnion x $ makeUnion xs

{-

    | ShuffleEvalMap ShuffleEval ShuffleEval [ShuffleEval]
    | ShuffleEvalMatch SetSpec ShuffleEval [(SetSpec, ShuffleEval)]
-}

getNextStep :: ShufflesProgress -> ShuffleName -> Maybe ShuffleStepIdent
getNextStep progress name = M.lookup (name, False) (progress ^. currentLatest) >>= \case
            ([], _) -> Nothing
            (x:xs, _) -> Just x

getAllPartial :: ShufflesProgress -> ShuffleName -> (Bool, Thingy) -> [(Thingy, Nteger)] --note: loops are possible
getAllPartial prog name condition = M.toList $ fst $ goFrom (name, False, 0) [] where
    goFrom ident idents | ident `elem` idents = (mempty, Just ident)
                        | otherwise = case M.lookup ident (prog ^. current) of
                            Nothing -> (mempty, Nothing)
                            Just (ValueEval _ _) -> (mempty, Nothing)
                            Just (ValuePartial vals x) -> 
                                let (m, x') = case x of
                                        Nothing -> (mempty, Nothing)
                                        Just x -> (goFrom x (ident:idents))
                                    res = foldr (f condition) m vals
                                    (res', x'') = if x' == Just ident then (fmap (const Infinite) res, Nothing) else (res, x')
                                    in (res', x'')
    f (b, x) (y, n, z) | b && x == y = M.unionWith addNteger (M.singleton z n)
                       | not b && x == z = M.unionWith addNteger (M.singleton y n)
                       | otherwise = id

addNteger :: Nteger -> Nteger -> Nteger
addNteger (Finite n) (Finite m) = Finite (n + m)
addNteger _ _ = Infinite