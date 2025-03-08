{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module TMCR.Logic.Shuffle where

import TMCR.Logic.Common
import TMCR.Parser.Common

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
import Data.Foldable (toList)

import Data.Functor.Foldable
import Data.Functor.Foldable.TH

import System.Random

import Control.Monad
import Control.Lens
import Control.Lens.TH
import Control.Monad.Reader (MonadReader, runReader, ReaderT(..))
import Data.List (partition)
import Data.Maybe (catMaybes)
import TMCR.Logic.Data (LogicData, DataLookup, evalDataLookup)

import GHC.Generics (Generic)
import Data.Hashable (Hashable)

import Data.Void

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
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data ShuffleStatement =
      DefineShuffle Name ShuffleInstruction
    | ExpandShuffle Name ShuffleInstruction
    deriving (Eq, Ord, Show)

data SetSpec = SetSpec (M.Map PossiblyScopedName Nteger)
    deriving (Eq, Ord, Show)

type ShuffleName = Text

{-data ShuffleValue = ShuffleValue {
          mainPart :: ShuffleValue' ShuffleInstruction
        , expansions :: [ShuffleValue' ShuffleInstruction]
    } deriving (Eq, Ord, Show)
    -}
--type ShuffleValue = ShuffleValue' ShuffleInstruction

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

{-
getAllPartial' :: ShuffleValue -> (Bool, Thingy) -> [(Thingy, Nteger)]
getAllPartial' x (isForwards, y) = go x M.empty where
    go (Remaining _) m = M.toList m
    go (Progress x v) m | cond x = go v $ M.adjust increment (extr x) m
                        | otherwise = go v m
    go (Delay x) m = go x m
    go (Loop xs) m = M.toList $ M.union (M.fromList $ fmap ((flip (,) Infinite) . extr) $ filter cond xs) m
    go End m = M.toList m
    cond (a,b) = if isForwards then a == y else b == y
    extr (a,b) = if isForwards then b else a
    increment (Finite !x) = Finite $ x + 1
    increment Infinite = Infinite
-}

type RandomSeed = StdGen

{-
data ShuffleStepResult = Final ShuffleValue
                       | Success (ShuffleValue, RandomSeed)
                       | DependsShuffle [(ShuffleName, Bool)]
-}

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

        
{-
valFromList :: [(Thingy, Thingy)] -> ShuffleValue
valFromList [] = End
valFromList (x:xs) = Progress x $ valFromList xs
-}

evalSetSpec :: SetSpec -> [(Thingy, Nteger, Thingy)]
evalSetSpec (SetSpec m) = fmap (\(v, n) -> (Global "", n, v)) $ M.toList m

data ShuffleValue'' = ValuePartial [(Thingy, Nteger, Thingy)] (Maybe ShuffleStepIdent)
                    | ValueEval ShuffleEval RandomSeed
                    deriving (Eq, Show)


data ShuffleKey = ShuffleKeyMain ShuffleName | ShuffleKeyExtensions ShuffleName deriving (Eq, Ord, Show, Generic)
shuffleKeyName :: ShuffleKey -> ShuffleName
shuffleKeyName (ShuffleKeyMain name) = name
shuffleKeyName (ShuffleKeyExtensions name) = name
instance Hashable ShuffleKey
type ShuffleStepIdent = (ShuffleKey, Int)

data ShufflesProgress = ShufflesProgress {
                          _currentLatest :: M.Map (ShuffleKey) ([ShuffleStepIdent], Int)
                        , _current :: M.Map ShuffleStepIdent ShuffleValue''
                        }
                    deriving (Eq, Show)

$(makeLenses 'ShufflesProgress)

instance Semigroup ShufflesProgress where
    ShufflesProgress a b <> ShufflesProgress a' b' = ShufflesProgress (a <> a') (b <> b')

instance Monoid ShufflesProgress where
    mempty = ShufflesProgress mempty mempty

convertShuffles :: LogicData -> RandomSeed -> M.Map ShuffleName (ShuffleInstruction, [ShuffleInstruction]) -> ShufflesProgress
convertShuffles lData seed = foldMap (\(name, (main, exts), seed) -> makeProgress (ShuffleKeyMain name) (Just main) seed <> makeProgress (ShuffleKeyExtensions name) (foldr makeUnion Nothing exts) seed) . snd . foldr (\(name, content) (seed, xs) -> let (seed', seed'') = split seed in (seed', (name, content, seed'') : xs)) (seed, []) . M.toList where
        makeUnion x Nothing = Just x
        makeUnion x (Just y) = Just (ShuffleUnion x y)
        makeProgress _ Nothing _ = mempty
        makeProgress ident (Just x) seed = ShufflesProgress (M.singleton ident ([(ident, 0)], 1)) $ M.singleton (ident, 0) $ ValueEval (convert (shuffleKeyName ident) x) seed
        convert _    (ShuffleDataLookup x) = ShuffleEvalConst $ evalDataLookup lData x
        convert _    (ShuffleSetSpec x) = ShuffleEvalConst $ evalSetSpec x
        convert _    (ShuffleCountLiteral n) = ShuffleEvalConst [(Global "", n, Global "")]
        convert name ShufflePlaceholder = ShuffleEvalRefer (ShuffleKeyExtensions name, 0)
        convert _    (ShuffleCall name') = ShuffleEvalRefer (ShuffleKeyMain name', 0)
        convert name (ShuffleReverse x) = ShuffleEvalReverse $ convert name x
        convert name (ShuffleRepeat x) = ShuffleEvalRepeat $ convert name x
        convert name (ShuffleRepeatIndividually x) = ShuffleEvalRepeatIndividually $ convert name x
        convert name (ShuffleMap a b cs) = ShuffleEvalMap (convert name a) (convert name b) (convert name <$> cs)
        convert name (ShuffleConnect a b) = ShuffleEvalConnect (convert name a) (convert name b)
        convert name (ShuffleUnion a b) = ShuffleEvalUnion (convert name a) (convert name b)
        convert name (ShuffleThen a b) = ShuffleEvalThen (convert name a) (convert name b)
        convert name (ShuffleMatch x a xs) = ShuffleEvalMatch x (convert name a) ((\(x', a') -> (x', convert name a')) <$> xs)

data ShuffleStepResult' = ShuffleStepResult ShufflesProgress [ShuffleStepIdent] Bool

class (Monad m) => MonadEvalShuffle m where
  getValue :: ShuffleStepIdent -> m (Maybe ShuffleValue'')
  putValue :: ShuffleStepIdent -> ShuffleValue'' -> m ()
  allocIdent :: ShuffleKey -> m ShuffleStepIdent

instance (MonadEvalShuffle m, MonadTrans t, Monad (t m)) => MonadEvalShuffle (Lift t m) where
  getValue = lift . getValue
  putValue = fmap lift . putValue
  allocIdent = lift . allocIdent

deriving via Lift (ExceptT e) m instance (MonadEvalShuffle m) => MonadEvalShuffle (ExceptT e m)
deriving via Lift (StateT s) m instance (MonadEvalShuffle m) => MonadEvalShuffle (StateT s m)
deriving via Lift (ReaderT r) m instance (MonadEvalShuffle m) => MonadEvalShuffle (ReaderT r m)

newtype OnShufflesProgressT m a = OnShufflesProgressT { runOnShufflesProgressT :: StateT ShufflesProgress m a } deriving newtype (Functor, Applicative, Monad)

instance (Monad m) => MonadEvalShuffle (OnShufflesProgressT m) where
  getValue key = OnShufflesProgressT $ gets (^. current . at key)
  putValue key value = OnShufflesProgressT $ current . at key .= Just value
  allocIdent key = OnShufflesProgressT $ do
    c <- currentLatest . at key <<%= (_Just . _2 +~ 1)
    case c of
      Nothing -> currentLatest . at key .= Just ([], 1) >> return (key, 0)
      Just (_, c') -> return (key, c')

stepShuffle :: ShufflesProgress -> ShuffleStepIdent -> ShuffleStepResult'
stepShuffle progress ident = (\((a, b), c) -> ShuffleStepResult c a b) $ flip runState progress $ runOnShufflesProgressT $ stepShuffle' ident

stepShuffle' :: forall m. (MonadEvalShuffle m) => ShuffleStepIdent -> m ([ShuffleStepIdent], Bool)
stepShuffle' ident = getValue ident >>= \case
  Nothing -> return ([], False)
  Just (ValuePartial _ x) -> return (toList x, False)
  Just (ValueEval x seed) -> do
    (r, rand) <- flip runReaderT (fst ident) $ runStateT (runExceptT $ eval x) seed
    case r of
      Left idents -> putValue ident (ValueEval x rand) >> return (idents, True)
      Right (r, e) -> do
          let (key, _) = ident
          ident' <- for e $ \e -> do
            ident' <- allocIdent key
            putValue ident' $ ValueEval e rand
            return ident'
          putValue ident $ ValuePartial r ident'
          return ([], True)

tryBoth :: (MonadError e m, Semigroup e) => m a -> m b -> m (a,b)
tryBoth a b = do
  a' <- catchError (Right <$> a) (return . Left)
  b' <- catchError (Right <$> b) (return . Left)
  case (a', b') of
    (Right a'', Right b'') -> return (a'', b'')
    (Left e, Right _) -> throwError e
    (Right _, Left e) -> throwError e
    (Left e, Left e') -> throwError (e <> e')

tryAll :: (MonadError e m, Semigroup e) => [m a] -> m [a]
tryAll [] = return []
tryAll (m: ms) = fmap (uncurry (:)) $ tryBoth m (tryAll ms)

eval :: (MonadState RandomSeed m, MonadError [ShuffleStepIdent] m, MonadEvalShuffle m, MonadReader ShuffleKey m) => ShuffleEval -> m ([(Thingy, Nteger, Thingy)], Maybe (ShuffleEval' ShuffleStepIdent))
eval (ShuffleEvalConst a) = return (a, Nothing)
eval (ShuffleEvalRefer ident) = do
    x <- getValue ident
    case x of
        Nothing -> return ([], Nothing)
        Just (ValuePartial v r) -> return (v,ShuffleEvalRefer <$> r)
        Just (ValueEval _ _) -> throwError [ident]
eval (ShuffleEvalReverse x) = do
    (a,e) <- eval x
    return ((\(a1,n,a2) -> (a2,n,a1)) <$> a, ShuffleEvalReverse <$> e)
eval x'@(ShuffleEvalRepeat x) = eval (ShuffleEvalThen x x')
eval (ShuffleEvalRepeatIndividually x) = do --todo: never terminates if a is empty. also, is this even correct?
    (a,_) <- eval x
    eval (ShuffleEvalRepeat (ShuffleEvalConst a))
eval (ShuffleEvalConnect x y) = do
    ((a, e), (b, e')) <- tryBoth (eval x) (eval y)
    let 
        ensureRefer x@(ShuffleEvalRefer _) = return x
        ensureRefer e = do
            key <- view id
            ident <- allocIdent key
            rand' <- state split
            putValue ident (ValueEval e rand')
            return $ ShuffleEvalRefer ident
    ex <- traverse ensureRefer e
    ex' <- traverse ensureRefer e'
    let r = case (ex, ex') of
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
    ((a, e), (b, e')) <- tryBoth (eval x) (eval y)
    let r = makeUnionMaybe e e'
    return (a <> b, r)
eval (ShuffleEvalThen x y) = do
    (a, e) <- eval x
    case e of
        Nothing -> return (a, Just $ y)
        Just e -> return (a, Just $ ShuffleEvalThen e $ y)
eval (ShuffleEvalMap x y zs) = do
    cs <- tryAll $ fmap eval zs
    case (catMaybes $ snd <$> cs) of
        [] -> eval (ShuffleEvalMapPartial [] (Just x) [] (Just y) (foldMap fst cs))
        zs' -> return $ (,) [] $ Just $ ShuffleEvalMap x y $ ShuffleEvalConst (foldMap fst cs) : zs'
eval (ShuffleEvalMapPartial as x bs y cs) = do
    (r, x) <- evalShuffleMapPartial as x bs y cs
    return (r, fmap (\(as', x', bs', y', cs') -> ShuffleEvalMapPartial as' x' bs' y' cs') x)
eval (ShuffleEvalMatch s'@(SetSpec s) x xs) = do
    (a, e) <- eval x
    let a' = a ^.. traverse . filtered (\(ax,_,_) -> M.member ax s) . _3
        xs' = xs & traverse . _1 %~ (\(SetSpec s) -> SetSpec $ M.difference s $ M.fromList $ fmap (\x -> (x,())) a')
        (xs'', rs) = partition (\(SetSpec s,_) -> null s) xs'
        m = case (e, null rs) of
                (Just e, False) -> Just (ShuffleEvalMatch s' e rs)
                _ -> Nothing
        x' = makeUnion $ fmap snd xs''
    (b, e') <- eval x'
    return (b, makeUnionMaybe e' m)

evalShuffleMapPartial :: (MonadState RandomSeed m,
 MonadError [ShuffleStepIdent] m, MonadEvalShuffle m, MonadReader ShuffleKey m) =>
    [[(Thingy, Nteger, Thingy)]]
    -> Maybe ShuffleEval
    -> [[(Thingy, Nteger, Thingy)]]
    -> Maybe (ShuffleEval' ShuffleStepIdent)
    -> [a1]
    -> m ([(Thingy, Nteger, Thingy)],
      Maybe ([[(Thingy, Nteger, Thingy)]],
       Maybe (ShuffleEval' ShuffleStepIdent),
       [[(Thingy, Nteger, Thingy)]],
       Maybe (ShuffleEval' ShuffleStepIdent), [a2]))
evalShuffleMapPartial [] (Just x) bs y [] = do
    (a, e) <- eval x
    return ([], Just ([a],e,bs,y,[]))
evalShuffleMapPartial [] Nothing _ _ [] = return ([], Nothing)
evalShuffleMapPartial ([]:as) x bs y cs = evalShuffleMapPartial as x bs y cs                                                
evalShuffleMapPartial as x ([]:bs) y cs = evalShuffleMapPartial as x bs y cs                                                
evalShuffleMapPartial (a:as) x [] Nothing [] = error "map failed" --todo
evalShuffleMapPartial as x [] (Just y) [] = do
                                                (b, e) <- eval y
                                                return ([], pure (as,x,([b]),e,[]))
evalShuffleMapPartial as@(a:as') x (b:bs) y [] = case [(a',n,x) | (a',n,x) <- a, (x', _, _) <- b, x == x'] of
                                                        [] -> do
                                                            (r,x) <- evalShuffleMapPartial as x bs y []
                                                            return (r, fmap (\(as',x',bs',y',cs') -> (as', x', b:bs', y', cs')) x)
                                                        _ -> do
                                                            (r, a', b') <- chooseRandomMatching a b
                                                            return (r, pure (a':as', x, b':bs, y, []))
evalShuffleMapPartial _ _ _ _ (c:cs) = error "constraints not yet implemented" --todo

chooseRandomMatching :: (MonadState RandomSeed m) => [(a, Nteger, Thingy)] -> [(Thingy, Nteger, c)] -> m ([(a, Nteger, c)], [(a, Nteger, Thingy)], [(Thingy, Nteger, c)])
chooseRandomMatching as bs = do
    rand <- use id
    let cas = M.fromListWith (<>) $ fmap (\(a,n,c) -> (c,[(a,n)])) as
        cbs = M.fromListWith (<>) $ fmap (\(c,n,b) -> (c,[(n,b)])) bs
        (r, (rand', remA, remB)) = flip runState (rand, [], []) $ do
            matches <- MM.mergeA (
                    MM.traverseMaybeMissing $ \c as -> _2 <>= [(a,n,c) | (a,n) <- as] >> pure Nothing
                ) (
                    MM.traverseMaybeMissing $ \c bs -> _3 <>= [(c,n,b) | (n,b) <- bs] >> pure Nothing
                ) (
                    MM.zipWithMatched $ \c as bs -> let
                        go [] r = r
                        go ((Finite n, a):as) (i,x) = go as (i,replicate n a <> x)
                        go ((Infinite, a):as) (i,x) = (a:i,x)
                      in (go ((\(x,y) -> (y,x)) <$> as) ([],[]), go bs ([],[]))
                ) cas cbs
            fmap concat $ for (M.toList matches) $ \case
                (c,(([],as), ([], bs))) -> do
                    as' <- zoom _1 $ randomOrder as
                    bs' <- zoom _1 $ randomOrder bs
                    _2 <>= [(a, Finite 1, c) | a <- drop (length bs') as']
                    _3 <>= [(c, Finite 1, b) | b <- drop (length as') bs']
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
    id .= rand'
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

getNextStep :: ShuffleName -> ShufflesProgress -> Maybe ShuffleStepIdent
getNextStep name progress = M.lookup (ShuffleKeyMain name) (progress ^. currentLatest) >>= \case
            ([], _) -> Nothing
            (x:xs, _) -> Just x

associatedShuffle :: ShuffleStepIdent -> ShuffleName
associatedShuffle = (^. _1 . to shuffleKeyName)


getByConditionM :: (MonadEvalShuffle m, Ord k) => ShuffleName -> Condition k -> m [(k, Nteger)]
getByConditionM = getByCondition'' getValue

getByCondition :: (Ord k) => ShufflesProgress -> ShuffleName -> Condition k -> [(k,Nteger)]
getByCondition prog = getByCondition' (\ident -> M.lookup ident (prog ^. current))

getByCondition' lookup name condition = runIdentity $ getByCondition'' (return . lookup) name condition

getByCondition'' :: (Ord k, Monad m) => (ShuffleStepIdent -> m (Maybe ShuffleValue'')) -> ShuffleName -> Condition k -> m [(k,Nteger)]
getByCondition'' lookup name condition = fmap (M.toList . fst) $ goFrom (ShuffleKeyMain name, 0) [] where
    goFrom ident idents | ident `elem` idents = return (mempty, Just ident)
                        | otherwise = do
                          v <- lookup ident
                          case v of
                            Nothing -> return (mempty, Nothing)
                            Just (ValueEval _ _) -> return (mempty, Nothing)
                            Just (ValuePartial vals x) -> do
                                (m, x') <- case x of
                                        Nothing -> return (mempty, Nothing)
                                        Just x -> goFrom x (ident:idents)
                                let res = foldr (f condition) m vals
                                    (res', x'') = if x' == Just ident then (fmap (const Infinite) res, Nothing) else (res, x')
                                return (res', x'')
    f :: Condition k -> (Thingy, Nteger, Thingy) -> M.Map k Nteger -> M.Map k Nteger
    f (MappedTo x) (y,n,z) | z == x = M.unionWith addNteger (M.singleton y n)
                           | otherwise = id
    f (MappedFrom x) (y,n,z) | y == x = M.unionWith addNteger (M.singleton z n)
                             | otherwise = id
    f All (y,n,z) = M.unionWith addNteger (M.singleton (y,z) n)

data Condition k where
    MappedTo :: Thingy -> Condition Thingy
    MappedFrom :: Thingy -> Condition Thingy
    All :: Condition (Thingy, Thingy)

getPartial :: ShufflesProgress -> ShuffleName -> [(Thingy, Nteger, Thingy)]
getPartial progress name = runIdentity $ evalStateT (runOnShufflesProgressT (getPartialM name)) progress

getPartialM :: (MonadEvalShuffle m) => ShuffleName -> m [(Thingy, Nteger, Thingy)]
getPartialM name = fmap (\((a,b),n) -> (a,n,b)) <$> getByConditionM name All

addNteger :: Nteger -> Nteger -> Nteger
addNteger (Finite n) (Finite m) = Finite (n + m)
addNteger _ _ = Infinite
