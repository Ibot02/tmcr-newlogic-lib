{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
module TMCR.IO.EvalDescriptor where

import TMCR.Logic.DescriptorTranslation
import TMCR.Logic.NewShuffle (NewShuffleProgress(..), Pair(..), NewShuffleProgress' (..), ShuffleIdent)

import System.IO.Temp (withSystemTempFile)
import System.Process (withCreateProcess, proc, CreateProcess(..), StdStream(..))
import System.IO (hPutStr, hPutStrLn, hGetLine, hGetContents, hFlush, Handle, hGetChar)

import Control.Monad.Trans.Cont
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Reader (ReaderT)
import Control.Applicative (Applicative(..), Alternative(..))
import Control.Monad (ap)
import Control.Monad.Trans.Maybe (MaybeT (..))
import Control.Concurrent.MVar (newMVar, readMVar, newEmptyMVar, putMVar)
import Control.Concurrent (tryReadMVar)
import Data.Char (isSpace)

testGoal :: Result -> IO Bool
testGoal res = withSystemTempFile "rando.pl" $ \tempFilePath tempFileHandle -> do
    traverse (hPutStrLn tempFileHandle) $ lines $ renderResult res
    hFlush tempFileHandle
    withCreateProcess ((proc "swipl" [tempFilePath]) {std_in = CreatePipe, std_out = CreatePipe}) $ \(Just stdin) (Just stdout) stderr processHandle -> do
        putStrLn "started prolog"
        hPutStrLn stdin "findall(X, reachableNode(X, _), _)."
        hFlush stdin
        pre <- hGetLine stdout
        putStrLn $ "findall(...): " <> pre
        putStrLn "querying goal"
        hPutStrLn stdin "goal."
        hFlush stdin
        putStrLn "waiting for prolog"
        goal <- mkStreamFromHandle stdout
        --putStrLn $ "prolog: " <> goal
        re' <- runMaybeT $ flip execConsume goal $ (ignoreWhitespace >>) $
                    (expect "false." >> return False)
                    <|> (expect "true" >> return True)
        let re = case re' of
                Just x -> x
                Nothing -> error $ "unexpected result from prolog"
        {-re <- case goal of
            "false" -> return False
            "true." -> return True
            "true" -> do
                hPutStr stdin "."
                hFlush stdin
                return True
            x -> error $ "unexpected result from prolog: " <> x
            -}
        hPutStr stdin "\^D"
        hFlush stdin
        return re

newtype Stream m a = Stream { streamHead :: m (a, Stream m a) }

dropStream :: (Monad m) => Int -> Stream m a -> m (Stream m a)
dropStream 0 s = return s
dropStream n s | n > 0 = do
    (_, s') <- streamHead s
    dropStream (n - 1) s'

mkStreamFromHandle :: Handle -> IO (Stream IO Char)
mkStreamFromHandle = memoizeStream . hGetChar

memoizeStream :: IO a -> IO (Stream IO a)
memoizeStream getOne = do
    v <- newEmptyMVar
    return $ Stream $ do
        x <- tryReadMVar v
        case x of
            Nothing -> do
                x' <- getOne
                s' <- memoizeStream getOne
                putMVar v (x', s')
                return (x', s')
            Just (x', s') -> return (x', s')

newtype MonadConsumeT c m a = MonadConsume { runConsume :: Stream m c -> MaybeT m (a, Int) } deriving (Functor)

instance (Monad m) => Applicative (MonadConsumeT c m) where
    pure x = MonadConsume $ \_ -> pure (x, 0)
    (<*>) = ap

instance (Monad m) => Monad (MonadConsumeT c m) where
    return = pure
    MonadConsume x >>= f = MonadConsume $ \cs -> do
        (a, d) <- x cs
        cs' <- lift (dropStream d cs)
        (r, d') <- runConsume (f a) cs'
        return (r, d + d')

instance (Monad m) => Alternative (MonadConsumeT c m) where
    MonadConsume x <|> MonadConsume y = MonadConsume $ \cs -> x cs <|> y cs
    empty = MonadConsume $ const empty

execConsume :: (Monad m) => MonadConsumeT c m a -> Stream m c -> MaybeT m a
execConsume m = fmap fst <$> runConsume m

consumeOne :: (Monad m) => MonadConsumeT c m c
consumeOne = MonadConsume $ \s -> do
    (x, _) <- lift $ streamHead s
    return (x, 1)

expect :: (Monad m, Eq c) => [c] -> MonadConsumeT c m ()
expect [] = return ()
expect (c : cs) = do
    c' <- consumeOne
    if c == c' then return () else empty

ignoreWhitespace :: (Monad m) => MonadConsumeT Char m ()
ignoreWhitespace = consumeWhitespace <|> return () where
    consumeWhitespace = do
      c <- consumeOne
      if (isSpace c) then ignoreWhitespace
      else empty

toStmts :: ShuffleIdent -> Pair String -> [Statement]
toStmts name (OrderedPair a b) = return $ Statement "shuffle" $ Match (StringTerm name) $ Match (StringTerm a) $ Match (StringTerm b) Defined
toStmts name (UnorderedPair a b) = [OrderedPair a b, OrderedPair b a] >>= toStmts name

instance NewShuffleProgress Result IO String where
    inform :: ShuffleIdent -> [Pair String] -> Result -> IO Result
    inform name pairs (Result stmts) = do
        putStrLn $ "inform: " <> name <> " " <> show pairs
        return $ Result $ (pairs >>= toStmts name) <> stmts
    check = testGoal
instance NewShuffleProgress' Result IO String where
    informOpen name [] _ r = return r
    informOpen name _ [] r = return r
    informOpen shuffleName lefts rights (Result stmts) = return $ Result $ newStmts <> stmts where
        newStmts = [genStatement] <> leftStmts <> rightStmts
        genStatement = let
             x = VariableTerm Nothing
             y = VariableTerm (Just Nothing)
             leftX = Term (Apply leftsName [StringTerm shuffleName, x])
             rightY = Term (Apply rightsName [StringTerm shuffleName, y])
             cut = Term (Apply "!" [])
            in Statement "shuffle" $ IntroVar $ IntroVar $ Match (StringTerm shuffleName) $ Match x $ Match y $ DefinedBy $
          Conj (Conj rightY cut) leftX
        leftsName = "left" --todo: verify this isn't already used, else rename
        rightsName = "right"
        leftStmts = mkStmts leftsName lefts
        rightStmts = mkStmts rightsName rights
        mkStmts name = fmap (mkStmt name)
        mkStmt name value = Statement name $ Match (StringTerm shuffleName) $ Match (StringTerm value) Defined