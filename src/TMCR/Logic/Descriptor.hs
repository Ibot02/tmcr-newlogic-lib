{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
module TMCR.Logic.Descriptor where

import TMCR.Module
import Text.Megaparsec as MP
import Text.Megaparsec.Char as MP
import qualified Text.Megaparsec.Char.Lexer as MPL
import Control.Monad.Combinators.Expr

import Control.Monad

import Control.Monad.Trans.Reader
import Control.Monad.Trans.Class

import Control.Lens
import Control.Lens.TH

import Data.Void (Void())

import Data.Text (Text())
import qualified Data.Text as T

import Data.Set (Set())
import qualified Data.Set as S

import qualified Data.Char as C

import Data.Either (either)

data Descriptor (t :: DescriptorType) where
    Descriptor :: [Value] -> DescriptorRule t -> Descriptor t

data DescriptorRule (t :: DescriptorType) where
    Constant :: Literal t -> DescriptorRule t
    IsEqual :: Value -> Value -> DescriptorRule t
    CallDescriptor :: Name -> [Value] -> DescriptorRule t
    CanAccess :: Name -> [Value] -> [StateBody] -> DescriptorRule Truthy
    Product :: DescriptorRule County -> DescriptorRule County -> DescriptorRule County
    Sum :: [DescriptorRule County] -> DescriptorRule County
    AtLeast :: DescriptorRule County -> Nteger -> DescriptorRule Truthy
    Exist :: VarName -> Relation -> Value -> DescriptorRule Truthy -> DescriptorRule Truthy
    Count :: VarName -> Relation -> Value -> DescriptorRule Truthy -> DescriptorRule County
    Min :: [DescriptorRule t] -> DescriptorRule t
    Max :: [DescriptorRule t] -> DescriptorRule t
    Cast :: DescriptorRule Truthy -> DescriptorRule County -- truth -> infinity, false -> 0
    PriorState :: [StateBody] -> DescriptorRule Truthy
    PostState :: [StateBody] -> DescriptorRule Truthy

type Name = Text

data Literal (t :: DescriptorType) where
    TruthyLiteral :: Oolean -> Literal Truthy
    IntLiteral :: Int -> Literal County
    InfLiteral :: Literal County -- inf

data Oolean = OolFalse | OolOol | OolTrue deriving (Eq, Ord, Show, Enum, Bounded)

data Value = Variable VarName
           | ConstantValue PossiblyScopedName

type VarName = Text

data Nteger = Finite Int | Infinite deriving (Eq, Ord)

data PossiblyScopedName = Global Text
                        | ScopedName [Text]

data StateBody = IsSet Value
               | IsNotSet Value

data Relation = Forward RelName
              | Backward RelName
type RelName = Text

data DescriptorRole = DefaultRole | Reachability deriving (Eq, Ord, Show, Enum, Bounded)

data UntypedDescriptorRule = UntypedDescriptorRule Int UntypedDescriptorRule'

data UntypedDescriptorRule' =
      UTConstant UntypedLiteral
    | UTIsEqual Value Value
    | UTCallDescriptor Name [Value]
    | UTCanAccess Name [Value] [StateBody]
    | UTProduct UntypedDescriptorRule UntypedDescriptorRule
    | UTSum [UntypedDescriptorRule]
    | UTAtLeast UntypedDescriptorRule Nteger
    | UTExist VarName Relation Value UntypedDescriptorRule
    | UTCount VarName Relation Value UntypedDescriptorRule
    | UTMin [UntypedDescriptorRule]
    | UTMax [UntypedDescriptorRule]
    | UTPriorState [StateBody]
    | UTPostState [StateBody]

data UntypedLiteral =
      UTOolean Oolean
    | UTIntLiteral Int
    | UTInfLiteral

$(makePrisms ''Value)

data SDescriptorType :: DescriptorType -> * where
    STruthy :: SDescriptorType Truthy
    SCounty :: SDescriptorType County

type SomeDescriptorRule = Either (DescriptorRule Truthy) (DescriptorRule County)

sc :: (MonadParsec e Text m) => m () 
sc = MPL.space MP.space1 (MPL.skipLineComment "--") (MPL.skipBlockComment "{-" "-}")

type DescriptorDeclarations = ()
type Parser = ParsecT Void Text (Reader DescriptorDeclarations)

parseDescriptorDefinition :: (forall (t :: DescriptorType). (Name, Descriptor t) -> a) -> Parser a
parseDescriptorDefinition cc = do
    name <- parseName
    (argumentScopes, descType) <- lift $ fromDecl name DefaultRole
    arguments <- forM argumentScopes $ \_ -> parseValue'
    let boundVars = arguments ^.. traverse . _Variable
    MPL.symbol sc ":"
    parseRule boundVars descType (\r -> cc (name, Descriptor arguments r))

fromDecl :: Name -> DescriptorRole -> Reader DescriptorDeclarations ([Scoping], DescriptorType)
fromDecl = undefined

parseRule :: [VarName] -> DescriptorType -> (forall (t :: DescriptorType). DescriptorRule t -> a) -> Parser a
parseRule boundVars t cc = do
    untyped <- parseRule' boundVars
    case t of
            Truthy -> fmap cc $ typecheck untyped STruthy
            County -> fmap cc $ typecheck untyped SCounty

typecheck :: UntypedDescriptorRule -> SDescriptorType t -> Parser (DescriptorRule t)
typecheck (UntypedDescriptorRule _ (UTConstant (UTOolean b))) s = return $ castIfNeccessary s $ Constant $ TruthyLiteral b
typecheck (UntypedDescriptorRule _ (UTIsEqual v v')) s = return $ castIfNeccessary s $ IsEqual v v'
typecheck (UntypedDescriptorRule pos (UTCallDescriptor name args)) s = do
    (argScopes, t) <- lift $ fromDecl name DefaultRole
    assertEq (length argScopes) (length args) pos $ \x y -> "Was expecting " <> show x <> " arguments to call to `" <> T.unpack name <> "` but got " <> show y <> "."
    case t of
        Truthy -> return $ castIfNeccessary s $ CallDescriptor @Truthy name args
        County -> case s of
            STruthy -> strErrorWithPos pos $ "Was expecting a Truthy value, but call to descriptor `" <> T.unpack name <> "` has type County."
            SCounty -> return $ CallDescriptor name args
typecheck (UntypedDescriptorRule pos (UTCanAccess name args states)) s = do
    (argScopes, t) <- lift $ fromDecl name Reachability
    assertEq (length argScopes) (length args) pos $ \x y -> "Was expecting " <> show x <> " arguments to check with [" <> T.unpack name <> "] but got " <> show y <> "."
    return $ castIfNeccessary s $ CanAccess name args states
typecheck (UntypedDescriptorRule pos (UTProduct x y)) STruthy = strErrorWithPos pos $ "Was expecting Truthy value, but product is County."
typecheck (UntypedDescriptorRule pos (UTProduct x y)) SCounty = do
    x' <- typecheck x SCounty
    y' <- typecheck y SCounty
    return $ Product x' y'
typecheck (UntypedDescriptorRule pos (UTSum xs)) STruthy = strErrorWithPos pos $ "Was expecting Truthy value, but sum is County."
typecheck (UntypedDescriptorRule pos (UTSum xs)) SCounty = do
    xs' <- traverse (`typecheck` SCounty) xs
    return $ Sum xs'
typecheck (UntypedDescriptorRule pos (UTAtLeast r v)) s = do
    r' <- typecheck r SCounty
    return $ castIfNeccessary s $ AtLeast r' v
typecheck (UntypedDescriptorRule pos (UTExist vname rel val r)) s = do
    r' <- typecheck r STruthy
    return $ castIfNeccessary s $ Exist vname rel val r'
typecheck (UntypedDescriptorRule pos (UTCount vname rel val r)) STruthy = strErrorWithPos pos $ "Was expecting Truthy value, but count is County."
typecheck (UntypedDescriptorRule pos (UTCount vname rel val r)) SCounty = do
    r' <- typecheck r STruthy
    return $ Count vname rel val r'
typecheck (UntypedDescriptorRule pos (UTMin rs)) s = do
    rs' <- traverse (`typecheck` s) rs
    return $ Min rs'
typecheck (UntypedDescriptorRule pos (UTMax rs)) s = do
    rs' <- traverse (`typecheck` s) rs
    return $ Max rs'
typecheck (UntypedDescriptorRule pos (UTPriorState st)) s = return $ castIfNeccessary s $ PriorState st
typecheck (UntypedDescriptorRule pos (UTPostState st)) s = return $ castIfNeccessary s $ PostState st

strErrorWithPos :: Int -> String -> Parser a
strErrorWithPos pos str = parseError $ FancyError pos $ S.singleton $ ErrorFail str

assertEq :: (Eq a) => a -> a -> Int -> (a -> a -> String) -> Parser ()
assertEq x y pos msg | x == y = return ()
                     | otherwise = strErrorWithPos pos $ msg x y

castIfNeccessary :: SDescriptorType t -> DescriptorRule Truthy -> DescriptorRule t
castIfNeccessary STruthy = id
castIfNeccessary SCounty = Cast

parseRule' :: [VarName] -> Parser UntypedDescriptorRule
parseRule' boundVars = makeExprParser (terms boundVars) ops <* MPL.symbol sc "." where
    ops = [ [binary "*" UTProduct]
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
        MPL.symbol sc ">="
        n <- parseNteger
        p <- stateOffset <$> getParserState
        return (\x -> UntypedDescriptorRule p $ UTAtLeast x n)
    terms boundVars = do
        p <- stateOffset <$> getParserState
        UntypedDescriptorRule p <$> terms' boundVars
    terms' boundVars = (UTConstant <$> constant) <|> isEqual boundVars <|> call boundVars <|> canAccess boundVars <|> quantifiers boundVars <|> statey boundVars
    constant = (countyConstant <$> parseNteger) <|> (UTOolean <$> parseOolean)
    countyConstant (Finite n) = UTIntLiteral n
    countyConstant Infinite = UTInfLiteral
    isEqual boundVars = try $ do
        v <- parseValue boundVars
        MPL.lexeme sc (some (MP.single '='))
        v' <- parseValue boundVars
        return $ UTIsEqual v v'
    call boundVars = do
        name <- parseName
        args <- many $ parseValue boundVars
        return $ UTCallDescriptor name args
    canAccess boundVars = do
        (name, args) <- MP.between (MPL.symbol sc "[") (MPL.symbol sc "]") $ do
            name <- parseName
            args <- many $ parseValue boundVars
            return (name, args)
        st <- option [] $ do
            MPL.symbol sc "?"
            stateyBody boundVars
        return $ UTCanAccess name args st
    quantifiers boundVars = try $ do
        f <- (UTExist <$ (MPL.symbol sc "?" <|> MPL.symbol sc "∃")) <|> (UTCount <$ MPL.symbol sc "+")
        name <- parseVarName
        rel <- (Forward <$> MP.between (MPL.symbol sc "-") (MPL.symbol sc "->") parseRelName) <|> (Backward <$> MP.between (MPL.symbol sc "<-") (MPL.symbol sc "-") parseRelName)
        v <- parseValue (name : boundVars)
        rule <- between (MPL.symbol sc "(") (MPL.symbol sc ")") $ parseRule' (name : boundVars)
        return $ f name rel v rule
    statey boundVars = do
        f <- (UTPriorState <$ MPL.symbol sc "?") <|> (UTPostState <$ MPL.symbol sc "!")
        f <$> stateyBody boundVars
    stateyBody boundVars = MP.between (MPL.symbol sc "[") (MPL.symbol sc "]") $ flip MP.sepBy1 (MPL.symbol sc ",") $ do
        f <- option IsSet $ IsNotSet <$ (MPL.symbol sc "~" <|> MPL.symbol sc "¬")
        f <$> parseValue boundVars

parseNteger :: Parser Nteger
parseNteger = (Infinite <$ (MPL.symbol sc "inf" <|> MPL.symbol sc "∞")) <|> (Finite <$> MPL.lexeme sc (read <$> some MP.digitChar))
parseOolean :: Parser Oolean
parseOolean = (OolFalse <$ (MPL.symbol sc "false" <|> MPL.symbol sc "⊥")) <|> (OolOol <$ MPL.symbol sc "ool") <|> (OolTrue <$ (MPL.symbol sc "true" <|> MPL.symbol sc "⊤"))

parseRelName :: Parser RelName
parseRelName = parseVarName

parseValue :: [VarName] -> Parser Value
parseValue boundVars = do
    v <- parseValue'
    case v of
        Variable v' -> if v' `elem` boundVars then return () else fail $ "Variable v" <> quoteIfNeccessary v' <> " is not bound anywhere." where
                            quoteIfNeccessary v = case T.uncons v of
                                Nothing -> "\"\""
                                Just (c, cs) -> if C.isUpper c && T.all C.isAlphaNum cs then T.unpack v else show v
        _ -> return ()
    return v

parseValue' :: Parser Value
parseValue' = (Variable <$> (MP.single 'v' *> parseVarName)) <|> (ConstantValue <$> parsePossiblyScopedName)

parseVarName :: Parser VarName
parseVarName = MPL.lexeme sc parseVarName'
parseVarName' :: Parser VarName
parseVarName' = unquoted <|> quoted where
    unquoted :: Parser VarName
    unquoted = fmap T.pack $ (:) <$> MP.upperChar <*> many MP.alphaNumChar
    quoted :: Parser VarName
    quoted = fmap T.pack $ MP.single '"' *> MP.manyTill MPL.charLiteral (MP.single '"')

parsePossiblyScopedName :: Parser PossiblyScopedName
parsePossiblyScopedName = MPL.lexeme sc parsePossiblyScopedName'
parsePossiblyScopedName' :: Parser PossiblyScopedName
parsePossiblyScopedName' = (Global <$> (MP.single 'g' *> parseVarName')) <|> (ScopedName <$> MP.sepBy1 parseVarName' (MP.single '.'))

parseName :: Parser Name
parseName = MPL.lexeme sc parseName'
parseName' :: Parser Name
parseName' = fmap T.pack $ (:) <$> MP.lowerChar <*> many MP.alphaNumChar
