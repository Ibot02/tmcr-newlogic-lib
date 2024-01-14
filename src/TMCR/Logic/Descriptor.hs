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

import qualified Control.Monad.State as S

data DescriptorDeclaration = DescriptorDeclaration {
      _descriptorDeclarationExport :: Maybe DescriptorExport
    , _descriptorDeclarationStateful :: Maybe Bool
    , _descriptorDeclarationArguments :: [Scoping]
    , _descriptorDeclarationType :: DescriptorType
    -- , _descriptorDeclarationConsumes :: Maybe DescriptorConsumeSpec
    } deriving (Eq, Ord, Show)

data DescriptorExport = DescriptorExportNone | DescriptorExportEdge | DescriptorExportSelfEdge | DescriptorExportEdgeFromBeyondTheVoid | DescriptorExportTarget deriving (Eq, Ord, Show, Enum, Bounded)

type DescriptorName = Text

data Scoping = Unscoped | Scoped deriving (Eq, Ord, Show, Enum, Bounded)

data DescriptorType = Truthy | County deriving (Eq, Ord, Show, Enum, Bounded)

-- data DescriptorConsumeSpec = DescriptorConsumeSpec {
--       _descriptorConsumerSpecKey :: Text --todo: add relation for key item type
--     , _descriptorConsumerSpecLock :: Text
--     } deriving (Eq, Ord, Show)

#if MIN_VERSION_aeson(1,5,0)
-- $(deriveJSON defaultOptions{ fieldLabelModifier = drop (T.length "_descriptorConsumerSpec") . fmap toLower, rejectUnknownFields = True} ''DescriptorConsumeSpec)
#else
-- $(deriveJSON defaultOptions{ fieldLabelModifier = drop (T.length "_descriptorConsumerSpec") . fmap toLower} ''DescriptorConsumeSpec)
#endif
$(deriveJSON defaultOptions{ constructorTagModifier = camelTo2 '-' } ''DescriptorType)
$(deriveJSON defaultOptions{ constructorTagModifier = camelTo2 '-' } ''Scoping)
$(deriveJSON defaultOptions{ constructorTagModifier = camelTo2 '-' . drop (T.length "DescriptorExport") } ''DescriptorExport)
#if MIN_VERSION_aeson(1,5,0)
$(deriveJSON defaultOptions{ fieldLabelModifier = drop (T.length "_descriptorDeclaration") . fmap toLower, omitNothingFields = True, rejectUnknownFields = True} ''DescriptorDeclaration)
#else
$(deriveJSON defaultOptions{ fieldLabelModifier = drop (T.length "_descriptorDeclaration") . fmap toLower, omitNothingFields = True} ''DescriptorDeclaration)
#endif
$(makeLenses ''DescriptorDeclaration)
-- $(makeLenses ''DescriptorConsumeSpec)

data DescriptorIdent t where
    TruthyDescriptorIdent :: DescriptorName -> DescriptorIdent Truthy
    CountyDescriptorIdent :: DescriptorName -> DescriptorIdent County

deriving instance Show (DescriptorIdent a)

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
deriving instance Show (Descriptors t)
deriving instance Eq (Descriptors t)
deriving instance Ord (Descriptors t)

data Descriptor (t :: DescriptorType) where
    Descriptor :: [Value] -> DescriptorRule t -> Descriptor t
deriving instance Show (Descriptor t)
deriving instance Eq (Descriptor t)
deriving instance Ord (Descriptor t)
type ConsumeUUID = Int

data SDescriptorType :: DescriptorType -> * where
    STruthy :: SDescriptorType Truthy
    SCounty :: SDescriptorType County

deriving instance Show (SDescriptorType t)
deriving instance Eq (SDescriptorType t)
deriving instance Ord (SDescriptorType t)

data DescriptorRule (t :: DescriptorType) where
    Constant :: Literal t -> DescriptorRule t
    IsEqual :: Value -> Value -> DescriptorRule Truthy
    CallDescriptor :: SDescriptorType t -> Name -> [Value] -> DescriptorRule t
    CanAccess :: SDescriptorType t -> Name -> [Value] -> [StateBody Value] -> DescriptorRule t
    --Product :: DescriptorRule County -> DescriptorRule County -> DescriptorRule County  -- removed due to being buggy and no know use cases - we'll have scale instead
    Scale :: DescriptorRule County -> Nteger -> DescriptorRule County
    Sum :: [DescriptorRule County] -> DescriptorRule County
    AtLeast :: DescriptorRule County -> Nteger -> DescriptorRule Truthy
    Exist :: VarName -> Relation -> Value -> DescriptorRule Truthy -> DescriptorRule Truthy
    Count :: VarName -> Relation -> Value -> DescriptorRule Truthy -> DescriptorRule County
    Min :: [DescriptorRule t] -> DescriptorRule t
    Max :: [DescriptorRule t] -> DescriptorRule t
    Cast :: DescriptorRule Truthy -> DescriptorRule County -- truth -> infinity, false -> 0
    PriorState :: [StateBody Value] -> DescriptorRule Truthy
    PostState :: [StateBody Value] -> DescriptorRule Truthy
    Consume :: ConsumeUUID -> Name -> [Value] -> DescriptorRule t -> DescriptorRule t

deriving instance Show (DescriptorRule t)
deriving instance Eq (DescriptorRule t)
deriving instance Ord (DescriptorRule t)

data Literal (t :: DescriptorType) where
    TruthyLiteral :: Oolean -> Literal Truthy
    CountyLiteral :: Nteger -> Literal County
    -- IntLiteral :: Int -> Literal County
    -- InfLiteral :: Literal County -- inf

deriving instance Show (Literal t)
deriving instance Eq (Literal t)
deriving instance Ord (Literal t)

data Oolean = OolFalse | OolOol | OolTrue deriving (Eq, Ord, Show, Enum, Bounded)

data Value = Variable VarName
           | ConstantValue PossiblyScopedName
                deriving (Eq, Ord, Show)

data StateBody v = IsSet v
                 | IsNotSet v
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
    | UTCanAccess Name [Value] [StateBody Value]
    -- | UTProduct UntypedDescriptorRule UntypedDescriptorRule
    | UTScale UntypedDescriptorRule Nteger
    | UTSum [UntypedDescriptorRule]
    | UTAtLeast UntypedDescriptorRule Nteger
    | UTExist VarName Relation Value UntypedDescriptorRule
    | UTCount VarName Relation Value UntypedDescriptorRule
    | UTMin [UntypedDescriptorRule]
    | UTMax [UntypedDescriptorRule]
    | UTPriorState [StateBody Value]
    | UTPostState [StateBody Value]
    | UTConsume ConsumeUUID Name [Value] UntypedDescriptorRule

data UntypedLiteral =
      UTOolean Oolean
    | UTNteger Nteger

$(makePrisms ''Value)

type SomeDescriptorRule = Either (DescriptorRule Truthy) (DescriptorRule County)

type DescriptorDeclarations = Map (Name, DescriptorRole) ([Scoping], DescriptorType)
getDescriptorDeclarations :: Map DescriptorName DescriptorDeclaration -> DescriptorDeclarations
getDescriptorDeclarations = Map.fromList . fmap (\(name, decl) -> ((name, case decl ^. descriptorDeclarationExport of {Just DescriptorExportTarget -> Reachability; _ -> DefaultRole}), (decl ^. descriptorDeclarationArguments, decl ^. descriptorDeclarationType))) . Map.toList

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

typecheck :: [VarName] -> UntypedDescriptorRule -> SDescriptorType t -> Parser (DescriptorRule t)
typecheck boundVars (UntypedDescriptorRule _ (UTConstant (UTOolean b))) s = return $ castIfNeccessary s $ Constant $ TruthyLiteral b
typecheck boundVars (UntypedDescriptorRule pos (UTConstant (UTNteger b))) STruthy = strErrorWithPos pos $ "Was expecting Truthy value, but Nteger (" <> show b <> ") is County."
typecheck boundVars (UntypedDescriptorRule _ (UTConstant (UTNteger b))) SCounty = return $ Constant $ CountyLiteral b
typecheck boundVars (UntypedDescriptorRule pos (UTIsEqual v v')) s = do
    checkBoundValues pos boundVars [v, v']
    return $ castIfNeccessary s $ IsEqual v v'
typecheck boundVars (UntypedDescriptorRule pos (UTCallDescriptor name args)) s = do
    (argScopes, t) <- fromDecl name DefaultRole
    assertEq (length argScopes) (length args) pos $ \x y -> "Was expecting " <> show x <> " arguments to call to `" <> T.unpack name <> "` but got " <> show y <> "."
    checkBoundValues pos boundVars args
    case t of
        Truthy -> return $ castIfNeccessary s $ CallDescriptor STruthy name args
        County -> case s of
            STruthy -> strErrorWithPos pos $ "Was expecting a Truthy value, but call to descriptor `" <> T.unpack name <> "` has type County."
            SCounty -> return $ CallDescriptor SCounty name args
typecheck boundVars (UntypedDescriptorRule pos (UTCanAccess name args states)) s = do
    (argScopes, t) <- fromDecl name Reachability
    checkBoundValues pos boundVars args
    assertEq (length argScopes) (length args) pos $ \x y -> "Was expecting " <> show x <> " arguments to check with [" <> T.unpack name <> "] but got " <> show y <> "."
    case t of
        Truthy -> return $ castIfNeccessary s $ CanAccess STruthy name args states
        County -> case s of
            STruthy -> strErrorWithPos pos $ "Was expecting a Truthy value, but access to descriptor `" <> T.unpack name <> "` has type County."
            SCounty -> return $ CanAccess SCounty name args states
-- typecheck boundVars (UntypedDescriptorRule pos (UTProduct x y)) STruthy = strErrorWithPos pos $ "Was expecting Truthy value, but product is County."
-- typecheck boundVars (UntypedDescriptorRule pos (UTProduct x y)) SCounty = do
--     x' <- typecheck boundVars x SCounty
--     y' <- typecheck boundVars y SCounty
--     return $ Product x' y'
typecheck boundVars (UntypedDescriptorRule pos (UTScale x y)) STruthy = strErrorWithPos pos $ "Was expecting Truthy value, but scale is County."
typecheck boundVars (UntypedDescriptorRule pos (UTScale x y)) SCounty = do
    x' <- typecheck boundVars x SCounty
    return $ Scale x' y
typecheck boundVars (UntypedDescriptorRule pos (UTSum xs)) STruthy = strErrorWithPos pos $ "Was expecting Truthy value, but sum is County."
typecheck boundVars (UntypedDescriptorRule pos (UTSum xs)) SCounty = do
    xs' <- traverse (flip (typecheck boundVars) SCounty) xs
    return $ Sum xs'
typecheck boundVars (UntypedDescriptorRule pos (UTAtLeast r v)) s = do
    r' <- typecheck boundVars r SCounty
    return $ castIfNeccessary s $ AtLeast r' v
typecheck boundVars (UntypedDescriptorRule pos (UTExist vname rel val r)) s = do
    checkBoundValue pos (vname : boundVars) val
    r' <- typecheck (vname : boundVars) r STruthy
    return $ castIfNeccessary s $ Exist vname rel val r'
typecheck boundVars (UntypedDescriptorRule pos (UTCount vname rel val r)) STruthy = strErrorWithPos pos $ "Was expecting Truthy value, but count is County."
typecheck boundVars (UntypedDescriptorRule pos (UTCount vname rel val r)) SCounty = do
    checkBoundValue pos (vname : boundVars) val
    r' <- typecheck (vname : boundVars) r STruthy
    return $ Count vname rel val r'
typecheck boundVars (UntypedDescriptorRule pos (UTMin rs)) s = do
    rs' <- traverse (flip (typecheck boundVars) s) rs
    return $ Min rs'
typecheck boundVars (UntypedDescriptorRule pos (UTMax rs)) s = do
    rs' <- traverse (flip (typecheck boundVars) s) rs
    return $ Max rs'
typecheck boundVars (UntypedDescriptorRule pos (UTPriorState st)) s = do
    checkBoundValues pos boundVars $ fmap (\case IsSet v -> v; IsNotSet v -> v) st
    return $ castIfNeccessary s $ PriorState st
typecheck boundVars (UntypedDescriptorRule pos (UTPostState st)) s = do
    checkBoundValues pos boundVars $ fmap (\case IsSet v -> v; IsNotSet v -> v) st
    return $ castIfNeccessary s $ PostState st
typecheck boundVars (UntypedDescriptorRule pos (UTConsume uuid name args rule')) s = do
    r' <- typecheck boundVars rule' s
    checkBoundValues pos boundVars args
    (argScopes, t) <- fromDecl name DefaultRole
    assertEq (length argScopes) (length args) pos $ \x y -> "Was expecting " <> show x <> " arguments to call to `" <> T.unpack name <> "` but got " <> show y <> "."
    case t of
        Truthy -> strErrorWithPos pos $ "Was expecting a county value, but call to descriptor `" <> T.unpack name <> "`has type Truthy. (In consumer usage, no implicit cast.)"
        County ->
            return $ Consume uuid name args r'

checkBoundValues pos boundVars vals = traverse (checkBoundValue pos boundVars) vals
checkBoundValue _ _ (ConstantValue _) = return ()
checkBoundValue pos boundVars (Variable v) | v `elem` boundVars = return ()
                                           | otherwise = strErrorWithPos pos $ "Variable v" <> quoteIfNeccessary v <> " not bound anywhere." where
                                                            quoteIfNeccessary v = case T.uncons v of
                                                                Nothing -> "\"\""
                                                                Just (c, cs) -> if C.isUpper c && T.all C.isAlphaNum cs then T.unpack v else show v
castIfNeccessary :: SDescriptorType t -> DescriptorRule Truthy -> DescriptorRule t
castIfNeccessary STruthy = id
castIfNeccessary SCounty = Cast

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
    statey = do
        f <- (UTPriorState <$ MPL.symbol sc "?") <|> (UTPostState <$ MPL.symbol sc "!")
        f <$> stateyBody
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
