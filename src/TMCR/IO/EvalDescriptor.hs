{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE InstanceSigs #-}
module TMCR.IO.EvalDescriptor where

import TMCR.Logic.DescriptorTranslation
import TMCR.Logic.NewShuffle (NewShuffleProgress(..), Pair(..), NewShuffleProgress' (..))

import System.IO.Temp (withSystemTempFile)
import System.Process (withCreateProcess, proc, CreateProcess(..), StdStream(..))
import System.IO (hPutStr, hPutStrLn, hGetLine, hGetContents, hFlush)

import Control.Monad.Trans.Cont
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Reader (ReaderT)

testGoal :: Result -> IO Bool
testGoal res = withSystemTempFile "rando.pl" $ \tempFilePath tempFileHandle -> do
    traverse (hPutStrLn tempFileHandle) $ lines $ renderResult res
    hFlush tempFileHandle
    withCreateProcess ((proc "swipl" [tempFilePath]) {std_in = CreatePipe, std_out = CreatePipe}) $ \(Just stdin) (Just stdout) stderr processHandle -> do
        putStrLn "started prolog"
        hPutStrLn stdin "goal."
        hFlush stdin
        hPutStr stdin "\^D"
        hFlush stdin
        putStrLn "waiting for prolog"
        goal <- hGetLine stdout
        putStrLn $ "prolog: " <> goal
        case goal of
            "false." -> return False
            "true." -> return True
            x -> error $ "unexpected result from prolog: " <> x

toStmts :: Pair String -> [Statement]
toStmts (OrderedPair a b) = return $ Statement "shuffle" $ IntroVar $ Match (VariableTerm Nothing) $ Match (StringTerm a) $ Match (StringTerm b) Defined
toStmts (UnorderedPair a b) = [OrderedPair a b, OrderedPair b a] >>= toStmts

instance NewShuffleProgress Result IO String where
    inform :: [Pair String] -> Result -> IO Result
    inform pairs (Result stmts) = do
        putStrLn $ "inform: " <> show pairs
        return $ Result $ (pairs >>= toStmts) <> stmts
    check = testGoal
instance NewShuffleProgress' Result IO String where
    informOpen [] _ r = return r
    informOpen _ [] r = return r
    informOpen lefts rights (Result stmts) = return $ Result $ newStmts <> stmts where
        newStmts = [genStatement] <> leftStmts <> rightStmts
        genStatement = Statement "shuffle" $ IntroVar $ IntroVar $ IntroVar $ Match (VariableTerm (Just (Just Nothing))) $ Match (VariableTerm Nothing) $ Match (VariableTerm (Just Nothing)) $ DefinedBy $
          Conj (Term (Apply leftsName [VariableTerm Nothing])) (Term (Apply rightsName [VariableTerm (Just Nothing)]))
        leftsName = "left" --todo: verify this isn't already used, else rename
        rightsName = "right"
        leftStmts = mkStmts leftsName lefts
        rightStmts = mkStmts rightsName rights
        mkStmts name = fmap (mkStmt name)
        mkStmt name value = Statement name $ Match (StringTerm value) Defined