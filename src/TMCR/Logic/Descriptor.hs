{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE StandaloneDeriving #-}
module TMCR.Logic.Descriptor where

import TMCR.Logic.Common

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

data DescriptorDeclaration = DescriptorDeclaration {
      _descriptorDeclarationExport :: Maybe DescriptorExport
    , _descriptorDeclarationStateful :: Maybe Bool
    , _descriptorDeclarationArguments :: [Scoping]
    , _descriptorDeclarationType :: DescriptorType
    , _descriptorDeclarationConsumes :: Maybe DescriptorConsumeSpec
    } deriving (Eq, Ord, Show)

data DescriptorExport = DescriptorExportNone | DescriptorExportEdge | DescriptorExportSelfEdge | DescriptorExportEdgeFromBeyondTheVoid | DescriptorExportTarget deriving (Eq, Ord, Show, Enum, Bounded)

type DescriptorName = Text

data Scoping = Unscoped | Scoped deriving (Eq, Ord, Show, Enum, Bounded)

data DescriptorType = Truthy | County deriving (Eq, Ord, Show, Enum, Bounded)

data DescriptorConsumeSpec = DescriptorConsumeSpec {
      _descriptorConsumerSpecKey :: Text --todo: add relation for key item type
    , _descriptorConsumerSpecLock :: Text
    } deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions{ fieldLabelModifier = drop (T.length "_descriptorConsumerSpec") . fmap toLower, rejectUnknownFields = True} ''DescriptorConsumeSpec)
$(deriveJSON defaultOptions{ constructorTagModifier = camelTo2 '-' } ''DescriptorType)
$(deriveJSON defaultOptions{ constructorTagModifier = camelTo2 '-' } ''Scoping)
$(deriveJSON defaultOptions{ constructorTagModifier = camelTo2 '-' . drop (T.length "DescriptorExport") } ''DescriptorExport)
$(deriveJSON defaultOptions{ fieldLabelModifier = drop (T.length "_descriptorDeclaration") . fmap toLower, omitNothingFields = True, rejectUnknownFields = True} ''DescriptorDeclaration)
$(makeLenses ''DescriptorDeclaration)
$(makeLenses ''DescriptorConsumeSpec)

data DescriptorIdent t where
    TruthyDescriptorIdent :: DescriptorName -> DescriptorIdent Truthy
    CountyDescriptorIdent :: DescriptorName -> DescriptorIdent County

instance GEq DescriptorIdent where
    TruthyDescriptorIdent _ `geq` TruthyDescriptorIdent _ = Just Refl
    CountyDescriptorIdent _ `geq` CountyDescriptorIdent _ = Just Refl
    _ `geq` _ = Nothing

instance GCompare DescriptorIdent where
    TruthyDescriptorIdent n `gcompare` TruthyDescriptorIdent n' = case compare n n' of
        LT -> GLT
        EQ -> GEQ
        GT -> GGT
    CountyDescriptorIdent n `gcompare` CountyDescriptorIdent n' = case compare n n' of
        LT -> GLT
        EQ -> GEQ
        GT -> GGT
    TruthyDescriptorIdent _ `gcompare` CountyDescriptorIdent _ = GLT
    CountyDescriptorIdent _ `gcompare` TruthyDescriptorIdent _ = GLT

deriving instance Eq (DescriptorIdent t)
deriving instance Ord (DescriptorIdent t)

newtype Descriptors t = Descriptors [Descriptor t]

data Descriptor (t :: DescriptorType) where
    Descriptor :: [Value] -> DescriptorRule t -> Descriptor t
deriving instance Show (Descriptor t)

data DescriptorRule (t :: DescriptorType) where
    Constant :: Literal t -> DescriptorRule t
    IsEqual :: Value -> Value -> DescriptorRule Truthy
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

deriving instance Show (DescriptorRule t)

data Literal (t :: DescriptorType) where
    TruthyLiteral :: Oolean -> Literal Truthy
    IntLiteral :: Int -> Literal County
    InfLiteral :: Literal County -- inf

deriving instance Show (Literal t)

data Oolean = OolFalse | OolOol | OolTrue deriving (Eq, Ord, Show, Enum, Bounded)

data Value = Variable VarName
           | ConstantValue PossiblyScopedName
                deriving (Eq, Ord, Show)

data StateBody = IsSet Value
               | IsNotSet Value
                deriving (Eq, Ord, Show)

data Relation = Forward RelName
              | Backward RelName
                deriving (Eq, Ord, Show)

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

type DescriptorDeclarations = Map (Name, DescriptorRole) ([Scoping], DescriptorType)

getDescriptorDeclarations :: Map DescriptorName DescriptorDeclaration -> DescriptorDeclarations
getDescriptorDeclarations = undefined --todo

type Parser = ParserC DescriptorDeclarations

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
parseDescriptorDefinition' cc = do
    name <- parseName
    (argumentScopes, descType) <- fromDecl name DefaultRole
    arguments <- forM argumentScopes $ \_ -> parseValue'
    let boundVars = arguments ^.. traverse . _Variable
    MPL.symbol sc ":"
    parseRule boundVars descType (\s r -> cc name s (Descriptor arguments r))

fromDecl :: Name -> DescriptorRole -> Parser ([Scoping], DescriptorType)
fromDecl name role = do
    return ()
    m <- ask
    case Map.lookup (name, role) m of
        Nothing -> fail $ "Descriptor `" <> T.unpack name <> "` with role " <> show role <> " not found!"
        Just x -> return x

parseRule :: [VarName] -> DescriptorType -> (forall (t :: DescriptorType). SDescriptorType t -> DescriptorRule t -> a) -> Parser a
parseRule boundVars t cc = do
    untyped <- parseRule' boundVars
    case t of
            Truthy -> fmap (cc STruthy) $ typecheck untyped STruthy
            County -> fmap (cc SCounty) $ typecheck untyped SCounty

typecheck :: UntypedDescriptorRule -> SDescriptorType t -> Parser (DescriptorRule t)
typecheck (UntypedDescriptorRule _ (UTConstant (UTOolean b))) s = return $ castIfNeccessary s $ Constant $ TruthyLiteral b
typecheck (UntypedDescriptorRule _ (UTIsEqual v v')) s = return $ castIfNeccessary s $ IsEqual v v'
typecheck (UntypedDescriptorRule pos (UTCallDescriptor name args)) s = do
    (argScopes, t) <- fromDecl name DefaultRole
    assertEq (length argScopes) (length args) pos $ \x y -> "Was expecting " <> show x <> " arguments to call to `" <> T.unpack name <> "` but got " <> show y <> "."
    case t of
        Truthy -> return $ castIfNeccessary s $ CallDescriptor @Truthy name args
        County -> case s of
            STruthy -> strErrorWithPos pos $ "Was expecting a Truthy value, but call to descriptor `" <> T.unpack name <> "` has type County."
            SCounty -> return $ CallDescriptor name args
typecheck (UntypedDescriptorRule pos (UTCanAccess name args states)) s = do
    (argScopes, t) <- fromDecl name Reachability
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
        MPL.symbol sc ">=" <|> MPL.symbol sc "≥"
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

parseOolean :: Parser Oolean
parseOolean = (OolFalse <$ (MPL.symbol sc "false" <|> MPL.symbol sc "⊥")) <|> (OolOol <$ MPL.symbol sc "ool") <|> (OolTrue <$ (MPL.symbol sc "true" <|> MPL.symbol sc "⊤"))

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
