{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module TMCR.Parser.Descriptor where

import TMCR.Logic.Descriptor

import TMCR.Logic.Common
import TMCR.Parser.Common

import Data.Char (toLower)

import Text.Megaparsec as MP
import Text.Megaparsec.Char as MP
import qualified Text.Megaparsec.Char.Lexer as MPL
import Control.Monad.Combinators.Expr

import Control.Monad

import Control.Monad.Reader

import Control.Lens
import Control.Lens.TH

import Data.Void (Void())

import Data.Text (Text())
import qualified Data.Text as T

import Data.Set (Set())
import qualified Data.Set as S

import Data.Map (Map())
import qualified Data.Map as Map

import qualified Data.Char as C

import Data.Either (either)

import Data.Dependent.Sum (DSum((:=>)))
import qualified Data.Dependent.Sum as DS

import Data.Dependent.Map (DMap())
import qualified Data.Dependent.Map as DM

import Data.GADT.Compare
import Data.Aeson (camelTo2, defaultOptions, Options(..))
import Data.Aeson.TH

import Data.Kind (Type)

import qualified Control.Monad.State as S

import GHC.Generics (Generic)
import Data.Hashable (Hashable(..))

data UntypedDescriptorRule = UntypedDescriptorRule Int UntypedDescriptorRule'

data UntypedDescriptorRule' =
      UTConstant UntypedLiteral
    | UTIsEqual Value Value
    | UTCallDescriptor Name [Value]
    | UTCanAccess Name [Value] [StateBody Value]
    -- | UTProduct UntypedDescriptorRule UntypedDescriptorRule
    | UTScale UntypedDescriptorRule Nteger
    | UTSum [UntypedDescriptorRule]
    | UTAtLeast UntypedDescriptorRule Nteger
    | UTExist VarName Relation Value UntypedDescriptorRule
    | UTCount VarName Relation Value UntypedDescriptorRule
    | UTMin [UntypedDescriptorRule]
    | UTMax [UntypedDescriptorRule]
    -- | UTPriorState [StateBody Value]
    -- | UTPostState [StateBody Value]
    | UTConsume ConsumeUUID Name [Value] UntypedDescriptorRule

data UntypedLiteral =
      UTOolean Oolean
    | UTNteger Nteger

type Parser = ParserCT DescriptorDeclarations (S.State Int)

parseDescriptorDefinitions :: Parser (DMap DescriptorIdent Descriptors)
parseDescriptorDefinitions = DM.fromListWithKey mergeDescriptors . fmap pluralize <$> many parseDescriptorDefinition where
    mergeDescriptors descriptorIdent (Descriptors xs) (Descriptors ys) = Descriptors $ xs <> ys
    pluralize (ident :=> x) = ident :=> Descriptors [x]

parseDescriptorDefinition :: Parser (DSum DescriptorIdent Descriptor)
parseDescriptorDefinition = parseDescriptorDefinition' helper where
    helper :: Name -> SDescriptorType t -> Descriptor t -> DSum DescriptorIdent Descriptor
    helper n s d = case s of
        STruthy -> TruthyDescriptorIdent n DS.:=> d
        SCounty -> CountyDescriptorIdent n DS.:=> d

parseDescriptorDefinition' :: (forall (t :: DescriptorType). Name -> SDescriptorType t -> Descriptor t -> a) -> Parser a
parseDescriptorDefinition' cc = label "descriptor definition" $ do
    name <- parseName
    (argumentScopes, descType) <- fromDecl name DefaultRole
    arguments <- forM argumentScopes $ \_ -> parseValue'
    let boundVars = arguments ^.. traverse . _Variable
    MPL.symbol sc ":"
    parseRule boundVars descType (\s r -> cc name s (Descriptor arguments r))

fromDecl :: Name -> DescriptorRole -> Parser ([Scoping], DescriptorType)
fromDecl name role = do
    m <- ask
    case Map.lookup (name, role) m of
        Nothing -> fail $ "Descriptor `" <> T.unpack name <> "` with role " <> show role <> " not found!"
        Just x -> return x

parseRule :: [VarName] -> DescriptorType -> (forall (t :: DescriptorType). SDescriptorType t -> DescriptorRule t -> a) -> Parser a
parseRule boundVars t cc = label "rule" $ do
    untyped <- parseRule'
    case t of
            Truthy -> fmap (cc STruthy) $ typecheck boundVars untyped STruthy
            County -> fmap (cc SCounty) $ typecheck boundVars untyped SCounty

typecheck :: [VarName] -> UntypedDescriptorRule -> SDescriptorType t -> Parser (DescriptorRule' AllEffs t Value)
typecheck varNames = typecheck' (\pos v -> if v `elem` varNames then return (Variable v) else strErrorWithPos pos "") ConstantValue
typecheck' :: (Int -> VarName -> Parser v) -> (PossiblyScopedName -> v) -> UntypedDescriptorRule -> SDescriptorType t -> Parser (DescriptorRule' AllEffs t v)
typecheck' parseVar c (UntypedDescriptorRule _ (UTConstant (UTOolean b))) s = return $ castIfNeccessary s $ Constant $ TruthyLiteral b
typecheck' parseVar c (UntypedDescriptorRule pos (UTConstant (UTNteger b))) STruthy = strErrorWithPos pos $ "Was expecting Truthy value, but Nteger (" <> show b <> ") is County."
typecheck' parseVar c (UntypedDescriptorRule _ (UTConstant (UTNteger b))) SCounty = return $ Constant $ CountyLiteral b
typecheck' parseVar c (UntypedDescriptorRule pos (UTIsEqual v v')) s = do
    v'' <- parseVal (parseVar pos) c v
    v''' <- parseVal (parseVar pos) c v'
    return $ castIfNeccessary s $ IsEqual v'' v'''
typecheck' parseVar c (UntypedDescriptorRule pos (UTCallDescriptor name args)) s = do
    (argScopes, t) <- fromDecl name DefaultRole
    assertEq (length argScopes) (length args) pos $ \x y -> "Was expecting " <> show x <> " arguments to call to `" <> T.unpack name <> "` but got " <> show y <> "."
    args' <- traverse (parseVal (parseVar pos) c) args
    case t of
        Truthy -> return $ castIfNeccessary s $ CallDescriptor STruthy name args'
        County -> case s of
            STruthy -> strErrorWithPos pos $ "Was expecting a Truthy value, but call to descriptor `" <> T.unpack name <> "` has type County."
            SCounty -> return $ CallDescriptor SCounty name args'
typecheck' parseVar c (UntypedDescriptorRule pos (UTCanAccess name args states)) s = do
    (argScopes, t) <- fromDecl name Reachability
    assertEq (length argScopes) (length args) pos $ \x y -> "Was expecting " <> show x <> " arguments to check with [" <> T.unpack name <> "] but got " <> show y <> "."
    args' <- traverse (parseVal (parseVar pos) c) args
    states' <- traverse (traverse (parseVal (parseVar pos) c)) states
    case t of
        Truthy -> return $ castIfNeccessary s $ CanAccess STruthy name args' states'
        County -> case s of
            STruthy -> strErrorWithPos pos $ "Was expecting a Truthy value, but access to descriptor `" <> T.unpack name <> "` has type County."
            SCounty -> return $ CanAccess SCounty name args' states'
-- typecheck boundVars (UntypedDescriptorRule pos (UTProduct x y)) STruthy = strErrorWithPos pos $ "Was expecting Truthy value, but product is County."
-- typecheck boundVars (UntypedDescriptorRule pos (UTProduct x y)) SCounty = do
--     x' <- typecheck boundVars x SCounty
--     y' <- typecheck boundVars y SCounty
--     return $ Product x' y'
typecheck' parseVar c (UntypedDescriptorRule pos (UTScale x y)) STruthy = strErrorWithPos pos $ "Was expecting Truthy value, but scale is County."
typecheck' parseVar c (UntypedDescriptorRule pos (UTScale x y)) SCounty = do
    x' <- typecheck' parseVar c x SCounty
    return $ Scale x' y
typecheck' parseVar c (UntypedDescriptorRule pos (UTSum xs)) STruthy = strErrorWithPos pos $ "Was expecting Truthy value, but sum is County."
typecheck' parseVar c (UntypedDescriptorRule pos (UTSum xs)) SCounty = do
    xs' <- traverse (flip (typecheck' parseVar c) SCounty) xs
    return $ Sum xs'
typecheck' parseVar c (UntypedDescriptorRule pos (UTAtLeast r v)) s = do
    r' <- typecheck' parseVar c r SCounty
    return $ castIfNeccessary s $ AtLeast r' v
typecheck' parseVar c (UntypedDescriptorRule pos (UTExist vname rel val r)) s = do
    val' <- parseVal (parseVar pos) c val
    let parseVar' = \pos v -> if v == vname then return Nothing else Just <$> parseVar pos v
    r' <- typecheck' parseVar' (Just . c) r STruthy
    return $ castIfNeccessary s $ Exist rel val' $ r'
typecheck' parseVar c (UntypedDescriptorRule pos (UTCount vname rel val r)) STruthy = strErrorWithPos pos $ "Was expecting Truthy value, but count is County."
typecheck' parseVar c (UntypedDescriptorRule pos (UTCount vname rel val r)) SCounty = do
    val' <- parseVal (parseVar pos) c val
    let parseVar' = \pos v -> if v == vname then return Nothing else Just <$> parseVar pos v
    r' <- typecheck' parseVar' (Just . c) r STruthy
    return $ Count rel val' r'
typecheck' parseVar c (UntypedDescriptorRule pos (UTMin rs)) s = do
    rs' <- traverse (flip (typecheck' parseVar c) s) rs
    return $ Min s rs'
typecheck' parseVar c (UntypedDescriptorRule pos (UTMax rs)) s = do
    rs' <- traverse (flip (typecheck' parseVar c) s) rs
    return $ Max s rs'
-- typecheck' parseVar c (UntypedDescriptorRule pos (UTPriorState st)) s = do
    -- st' <- traverse (traverse (parseVal (parseVar pos) c)) st
    -- return $ castIfNeccessary s $ PriorState st'
-- typecheck' parseVar c (UntypedDescriptorRule pos (UTPostState st)) s = do
    -- st' <- traverse (traverse (parseVal (parseVar pos) c)) st
    -- return $ castIfNeccessary s $ PostState st'
typecheck' parseVar c (UntypedDescriptorRule pos (UTConsume uuid name args rule')) s = do
    r' <- typecheck' parseVar c rule' s
    (argScopes, t) <- fromDecl name DefaultRole
    assertEq (length argScopes) (length args) pos $ \x y -> "Was expecting " <> show x <> " arguments to call to `" <> T.unpack name <> "` but got " <> show y <> "."
    args' <- traverse (parseVal (parseVar pos) c) args
    case t of
        Truthy -> strErrorWithPos pos $ "Was expecting a county value, but call to descriptor `" <> T.unpack name <> "`has type Truthy. (In consumer usage, no implicit cast.)"
        County ->
            return $ Consume uuid name args' r'

parseVal :: (Applicative m) => (VarName -> m v) -> (Thingy -> v) -> Value -> m v
parseVal p _ (Variable n) = p n
parseVal _ c (ConstantValue v) = pure $ c v

parseRule' :: Parser UntypedDescriptorRule
parseRule' = parseRule'' <* MPL.symbol sc "." where
    parseRule'' = makeExprParser (terms <|> parenthesised) ops
    ops = [ [quantifiers, consuming]
          , [scaleOps]--[binary "*" UTProduct]
          , [binary' "+" UTSum]
          , [atLeastOp]
          , [binary' "," UTMin]
          , [binary' ";" UTMax]
          ]
    binary s f = InfixR $ do
        MPL.symbol sc s
        p <- stateOffset <$> getParserState
        return (\x y -> UntypedDescriptorRule p $ f x y)
    binary' s f = binary s $ \x y -> f [x, y]
    atLeastOp = Postfix $ do
        MPL.symbol sc ">=" <|> MPL.symbol sc "≥"
        n <- parseNteger
        p <- stateOffset <$> getParserState
        return (\x -> UntypedDescriptorRule p $ UTAtLeast x n)
    scaleOps = Postfix $ foldr1 (.) <$> some scale
    scale = do
        MPL.symbol sc "*" <|> MPL.symbol sc "·" <|> MPL.symbol sc "⋅"
        n <- parseNteger
        p <- stateOffset <$> getParserState
        return (\x -> UntypedDescriptorRule p $ UTScale x n)
    terms = do
        p <- stateOffset <$> getParserState
        UntypedDescriptorRule p <$> terms'
    terms' = try $ (UTConstant <$> constant) <|> isEqual <|> call <|> canAccess <|> statey
    parenthesised = MP.between (MPL.symbol sc "(") (MPL.symbol sc ")") parseRule''
    constant = (UTNteger <$> parseNteger) <|> (UTOolean <$> parseOolean)
    isEqual = try $ do
        v <- parseValue
        MPL.lexeme sc (some (MP.single '='))
        v' <- parseValue
        return $ UTIsEqual v v'
    call = do
        name <- parseName
        args <- many $ parseValue
        return $ UTCallDescriptor name args
    canAccess = do
        (name, args) <- MP.between (MPL.symbol sc "[") (MPL.symbol sc "]") $ do
            name <- parseName
            args <- many $ parseValue
            return (name, args)
        st <- option [] $ do
            MPL.symbol sc "?"
            stateyBody
        return $ UTCanAccess name args st
    quantifiers = Prefix $ try $ do
        f <- (UTExist <$ (MPL.symbol sc "?" <|> MPL.symbol sc "∃")) <|> (UTCount <$ MPL.symbol sc "+")
        name <- parseVarName
        rel <- (Forward <$> MP.between (MPL.symbol sc "-") (MPL.symbol sc "->") parseRelName) <|> (Backward <$> MP.between (MPL.symbol sc "<-") (MPL.symbol sc "-") parseRelName)
        v <- parseValue
        MPL.symbol sc ":"
        p <- stateOffset <$> getParserState
        return $ \rule -> UntypedDescriptorRule p $ f name rel v rule
    statey = mzero{-do
        f <- (UTPriorState <$ MPL.symbol sc "?") <|> (UTPostState <$ MPL.symbol sc "!")
        f <$> stateyBody-}
    stateyBody = MP.between (MPL.symbol sc "[") (MPL.symbol sc "]") $ flip MP.sepBy1 (MPL.symbol sc ",") $ do
        f <- option IsSet $ IsNotSet <$ (MPL.symbol sc "~" <|> MPL.symbol sc "¬")
        f <$> parseValue
    consuming = Prefix $ do
        (name, args) <- MP.between (MPL.symbol sc "@" >> MPL.symbol sc "[") (MPL.symbol sc "]") $ do
            name <- parseName
            args <- many $ parseValue
            return (name, args)
        MPL.symbol sc ":"
        uuid <- nextUUID
        p <- stateOffset <$> getParserState
        return $ \rule -> UntypedDescriptorRule p $ UTConsume uuid name args rule

checkBoundValues pos boundVars vals = traverse (checkBoundValue pos boundVars) vals
checkBoundValue _ _ (ConstantValue _) = return ()
checkBoundValue pos boundVars (Variable v) | v `elem` boundVars = return ()
                                           | otherwise = strErrorWithPos pos $ "Variable v" <> quoteIfNeccessary v <> " not bound anywhere." where
                                                            quoteIfNeccessary v = case T.uncons v of
                                                                Nothing -> "\"\""
                                                                Just (c, cs) -> if C.isUpper c && T.all C.isAlphaNum cs then T.unpack v else show v

nextUUID = S.state (\x -> let !x' = x + 1 in (x', x'))

parseOolean :: Parser Oolean
parseOolean = label "oolean" $ (OolFalse <$ (MPL.symbol sc "false" <|> MPL.symbol sc "⊥")) <|> (OolOol <$ MPL.symbol sc "ool") <|> (OolTrue <$ (MPL.symbol sc "true" <|> MPL.symbol sc "⊤"))

parseValue :: Parser Value
parseValue = label "value" $ do
    v <- parseValue'
    -- case v of
    --     Variable v' -> if v' `elem` boundVars then return () else fail $ "Variable v" <> quoteIfNeccessary v' <> " is not bound anywhere." where
    --                         quoteIfNeccessary v = case T.uncons v of
    --                             Nothing -> "\"\""
    --                             Just (c, cs) -> if C.isUpper c && T.all C.isAlphaNum cs then T.unpack v else show v
    --     _ -> return ()
    return v

parseValue' :: Parser Value
parseValue' = (Variable <$> (MP.single 'v' *> parseVarName)) <|> (ConstantValue <$> parsePossiblyScopedName)
