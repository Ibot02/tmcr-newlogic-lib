{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}
module TMCR.IO where

import Control.Lens.TH

import Control.Monad (ap, (>=>), forM, join)

import qualified System.Directory as Sys (withCurrentDirectory, listDirectory, doesDirectoryExist)
import Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString.Lazy as BL
import TMCR.Module
import Control.Monad.Trans.Maybe (MaybeT(..))
import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DM
import TMCR.Logic.Descriptor
import Data.Maybe (catMaybes, maybeToList)
import TMCR.Logic.Merge (MonadMerge (..), GameDef, mergeDescriptorDeclarations, mergeContent)
import Control.Lens
import TMCR.Module.Dependency (makeModuleDependencyInfo)
import qualified Data.Map as M

import Polysemy
import Polysemy.Error
import qualified Data.Text as T
import TMCR.Logic.Common
import Text.Megaparsec (ParseErrorBundle, parseErrorTextPretty, errorBundlePretty)
import Data.Void (Void)
import Data.Text (Text)
import Polysemy.Reader
import Data.Map (Map)
import qualified Data.Text.Encoding as TE
import TMCR.Logic.Logic
    ( logicParser, Sugar, defaultSugar, Scopes )
import TMCR.Logic.Data (LogicData')
import TMCR.Logic.Shuffle (parseShuffleInstruction, parseShuffleStatements)
import Data.Yaml (decodeEither, ParseException, decodeEither')
import Data.Aeson (decode)

import Data.Functor.Foldable.TH
import Data.Functor.Classes

data LocationSpec = LocationSpec {
                      _basePath :: FilePath
                    , _steps :: [String]
                    , _fileName :: String
                    }

data WithDirectory m a where
     InSubdir :: String -> m a -> WithDirectory m a
     ListDirectory :: WithDirectory m [String]
     WithFile :: String -> (FilePath -> ByteString -> m a) -> WithDirectory m [a]
     --maybe WithFile :: String -> WithDirectory m [(FilePath, ByteString)]

newtype Directory = Directory { getDirectory :: (Map FilePath (Either ByteString Directory)) } deriving (Eq, Ord, Show)

$(makeLenses ''LocationSpec)
$(makeSem ''WithDirectory)
$(makeBaseFunctor ''Directory)

instance Eq1 DirectoryF where
    liftEq e (DirectoryF a) (DirectoryF b) = liftEq e' a b where
        e' (Left x) (Left y) = x == y
        e' (Right x) (Right y) = e x y
        e' _ _ = False
instance Ord1 DirectoryF where
    liftCompare e (DirectoryF a) (DirectoryF b) = liftCompare e' a b where
        e' (Left x) (Left y) = compare x y
        e' (Right x) (Right y) = e x y
        e' (Left _) (Right _) = LT
        e' (Right _) (Left _) = GT
    
inSubdir' :: (Member WithDirectory r) => String -> (FilePath -> Sem r a) -> Sem r [a]
inSubdir' name a = do
    xs <- listDirectory
    let xs' = filter (matches name) xs
    forM xs $ \x -> inSubdir x (a x)


readDirectoryFull :: FilePath -> IO Directory
readDirectoryFull path = Sys.withCurrentDirectory path $ do
    dir <- Sys.listDirectory "."
    contents <- forM dir $ \path -> do
        isDir <- Sys.doesDirectoryExist path
        if isDir then do
            contents <- readDirectoryFull path
            return (path, Right contents)
        else do
            contents <- BL.readFile path
            return (path, Left contents)
    return $ Directory $ M.fromList contents

matches :: String -> FilePath -> Bool
matches "*" _ = True
matches xs ys = xs == ys

assertMaybe :: Bool -> Maybe ()
assertMaybe False = Nothing
assertMaybe True = Just ()

runInMemoryDir :: (Member (Error ()) r) => Directory -> Sem (WithDirectory : r)  a -> Sem r a
runInMemoryDir xs = interpretH $ \case
    ListDirectory -> pureT $ M.keys $ getDirectory xs
    WithFile name a -> do
        let files = M.toList $ runIdentity $ M.traverseMaybeWithKey (\k v -> return $ do
                assertMaybe (name `matches` k)
                Left v' <- Just v --only files
                return v') $ getDirectory xs
        --runTSimple $ traverse (uncurry a) files
        a' <- runT $ traverse (uncurry a) files
        raise $ runInMemoryDir xs a'
    InSubdir name a -> do
        let subdirs = M.toList $ runIdentity $ M.traverseMaybeWithKey (\k v -> return $ do
                assertMaybe (name == k)
                Right v' <- Just v --only directories
                return v') $ getDirectory xs
        case subdirs of
            [] -> throw ()
            [(x,s)] -> do
                a' <- runT a
                raise $ runInMemoryDir s a'
            _ -> throw ()

{-
execInBaseDir :: (Member (Final IO) r) => FilePath -> Sem (WithDirectory : r) a -> Sem r a
execInBaseDir path a = resourceToIOFinal $ bracket (embedFinal getCurrentDirectory) (embedFinal . setCurrentDirectory) $ \_ -> do
    embedFinal $ setCurrentDirectory path
    exec $ raiseUnder a where
        exec = interpretFinal $ \case
            ListDirectory -> do
                listDirectory "."
-}

{-withCurrentDirectory path $ exec a where
    exec :: WithDirectoryT a -> IO a
    exec (ListDirectory a) = do
        ls <- listDirectory "."
        exec $ a ls
    exec (InSubdir dir a c) = do
        ls <- listDirectory "."
        let dir'' = filter (match dir) ls
        (catMaybes -> as) <- forM dir'' $ \dir' -> do
            isDir <- doesDirectoryExist dir'
            if isDir then do
                    fmap Just $ withCurrentDirectory dir' $ exec a
                else do
                    isFile <- doesFileExist dir'
                    if isFile && canHandleArchive dir' then
                        fmap Just $ execInArchive dir' a
                    else return Nothing
        exec (c as)
    exec (WithFile name e c) = do
        ls <- listDirectory "."
        let names = filter (match name) ls
        rs <- forM names $ \name' -> do
            bs <- BL.readFile name'
            exec $ e bs
        exec $ c rs
    execInArchive = undefined --TODO
    canHandleArchive _ = False
    match = (==) --todo: wildcards
-}

readGameDefStrErr :: (Members '[Reader Scopes, Error Text, WithDirectory] r) => [FilePath] -> Sem r GameDef
readGameDefStrErr sources = joinErrorTextPrefix @ParseException "ParseException: " $ joinErrorTextPrefix @MergeError "Merge Error: " $ joinErrorTextPrefix @AssertionFailed "Assertion Failed: " $ joinError @(ParseErrorBundle Text Void) @Text (T.pack . errorBundlePretty) $ readGameDef sources where
    joinError :: forall e e' r a. (Member (Error e') r) => (e -> e') -> Sem (Error e ': r) a -> Sem r a
    joinError convert k = runError @e k >>= (either (throw . convert) return)
    joinErrorTextPrefix :: forall e r a. (Member (Error Text) r, Show e) => Text -> Sem (Error e ': r) a -> Sem r a
    joinErrorTextPrefix pre k = joinError (\x -> pre <> T.pack (show x)) k

readGameDef :: (Members '[Error ParseException, Error MergeError, WithDirectory, Reader Scopes, Error AssertionFailed, Error (ParseErrorBundle Text Void)] r) => [FilePath] -> Sem r GameDef
readGameDef sources = do
    xs <- forM sources $ \path -> inSubdirs path $ \path -> do
        m <- readModuleFull
        return (path, m)
    content <- M.traverseWithKey (\k -> \case
        [] -> error "unreachable"
        [x] -> return x
        _ -> throw $ MergeErrorModuleMultipleDefine k) $ M.fromListWith (<>) $ fmap (\(path, m) -> (m ^. moduleFullName, [(path, m ^. moduleFullProvides)])) $ concat xs
    mergeContent content

inSubdirs :: forall r a. (Member WithDirectory r) => FilePath -> (FilePath -> Sem r a) -> Sem r [a]
inSubdirs p a = inSubdirs' a $ splitPath p where
    splitPath x = reverse $ fmap reverse $ go "" [] x where
        go "" [] "" = [""]
        go "" xs "" = xs
        go x xs "" = x:xs
        go "" xs ('/':cs) = go "" xs cs
        go x xs ('/':cs) = go "" (x:xs) cs
        go x xs (c:cs) = go (c:x) xs cs
    inSubdirs' :: forall b. (FilePath -> Sem r b) -> [FilePath] -> Sem r [b]
    inSubdirs' a [] = error "unreachable"
    inSubdirs' a [x] = inSubdir' x a
    inSubdirs' a (x:xs) = fmap concat $ inSubdir' x $ \path -> inSubdirs' (a . (path <>)) xs

readModule :: (Members '[WithDirectory, Error ParseException, Error AssertionFailed] r) => Sem r Module
readModule = withSingleFile "module.yaml" $ \path content -> do
    case decodeEither' $ BL.toStrict content of
        Left err -> throw err
        Right x -> do
            assert "syntaxVerion 0.1" $ (x ^. moduleSyntaxVersion . _Version) `startsWith` [0,1]
            return x

newtype AssertionFailed = AssertionFailed { getAssertionName :: Text } deriving (Eq, Ord, Show)

data MergeError = MergeErrorModuleMultipleDefine Text deriving (Eq, Ord, Show)

instance (Member (Error MergeError) r) => MonadMerge (Sem r) where
    --todo
    dependencies = return ()
    warningIgnoredLogicSubtree _ = return ()

readModuleFull :: (Members '[Reader Scopes, WithDirectory, Error ParseException, Error AssertionFailed, Error (ParseErrorBundle Text Void)] r) => Sem r ModuleFull
readModuleFull = do
    m <- readModule
    content <- readModuleFullContent $ m ^. moduleProvides
    return $ ModuleFull (m ^. moduleName) (m ^. moduleVersion) (m ^. moduleDependencies) (m ^. moduleSoftDependency) content

readModuleFullContent :: (Members '[Reader Scopes, WithDirectory, Error (ParseErrorBundle Text Void)] r) => ModuleContent -> Sem r ModuleFullContent
readModuleFullContent content =
    runReader
        @DescriptorDeclarations
        (getDescriptorDeclarations $ content ^. moduleContentDescriptors) $
    do
        descriptorDefs <- fmap (DM.unionsWithKey (\_ (Descriptors xs) (Descriptors ys) -> Descriptors (xs <> ys)) . concat) $ forM (content ^. moduleContentDescriptorDefinitions) $ \x -> do
            withPath (T.unpack x) $ \p c ->
                runParserC parseDescriptorDefinitions p (TE.decodeUtf8 $ BL.toStrict c)
        scopes <- ask @Scopes
        logic <- fmap concat $ forM (content ^. moduleContentLogic) $ \x -> do
            withPath (T.unpack x) $ \p c ->
                runReader @[Sugar] defaultSugar $
                runParserC (logicParser scopes) p (TE.decodeUtf8 $ BL.toStrict c)
        logicData <- fmap (concat . concat) $ forM (content ^. moduleContentData) $ \x -> do
            withPath (T.unpack x) $ \p c ->
                return $ maybeToList $ decode @LogicData' c
        shuffles <- fmap (concat . concat) $ forM (content ^. moduleContentShuffles) $ \x -> do
            withPath (T.unpack x) $ \p c ->
                runReader @() () $
                runParserC parseShuffleStatements p (TE.decodeUtf8 $ BL.toStrict c)
        return $ ModuleFullContent (content ^. moduleContentDescriptors) descriptorDefs logic (content ^. moduleContentPatches) logicData shuffles

withPath :: forall r a. (Member WithDirectory r) => FilePath -> (FilePath -> ByteString -> Sem r a) -> Sem r [a]
withPath path c = withPath' "" path c where
    withPath' :: FilePath -> FilePath -> (FilePath -> ByteString -> Sem r a) -> Sem r [a]
    withPath' context path c = case dropWhile isDelim path of
        "" -> withFile "" (\path' -> c $ context <> path')
        path' -> if any isDelim path' then
                let (d,path'') = break isDelim path' in
                concat <$> inSubdir' d (\dir' -> withPath' (context <> dir') path'' c)
            else
                withFile path' (\path'' -> c $ context <> path'')

withPathFragments :: forall r a. (Member WithDirectory r) => [FilePath] -> (FilePath -> ByteString -> Sem r a) -> Sem r [a]
withPathFragments [] = withFile ""
withPathFragments [x] = withFile x
withPathFragments (x:xs) = \c -> inSubdir x $ withPathFragments xs c

isDelim :: Char -> Bool
isDelim = (==) '/'

withSingleFile :: (Members '[WithDirectory, Error AssertionFailed] r) => FilePath -> (FilePath -> ByteString -> Sem r a) -> Sem r a
withSingleFile path cont = do
    xs <- withFile path (curry return)
    case xs of
        [x] -> uncurry cont x
        _ -> throw $ AssertionFailed "single file"

assert :: (Member (Error AssertionFailed) r) => Text -> Bool -> Sem r ()
assert _ True = return ()
assert msg False = throw $ AssertionFailed msg

startsWith :: (Eq a) => [a] -> [a] -> Bool
startsWith _ [] = True
startsWith (x:xs) (y:ys) = x == y && xs `startsWith` ys
startsWith _ _ = False

{-
readModule :: WithDirectoryT (Maybe Module)
readModule = fmap join $ withSingleFile "module.yaml" $ \content -> runMaybeT $ do
    m <- MaybeT $ return $ decode content
    assertMaybeT $ (m ^. moduleSyntaxVersion . _Version) `startsWith` [0,1]
    return m

readModules :: (MonadMerge m) => [Module] -> WithDirectoryT (m GameDef)
readModules modules = do
    let (Right deps) = makeModuleDependencyInfo $ fmap (\m -> ((m ^. moduleName, m ^. moduleVersion), m ^. moduleDependencies, m ^. moduleSoftDependency)) modules
        contents = M.fromList $ fmap (\m -> (m ^. moduleName, m ^. moduleProvides)) modules
    --Pure $ mergeDescriptorDeclarations (fmap (^. moduleContentDescriptors) contents)
    return undefined
    
    
     {-fmap join $ withSingleFile "module.yaml" $ \contents -> runMaybeT $ do
                (Module name version (Version syntax) depends softDepends provides) <- MaybeT $ return $ decode contents
                assertMaybeT $ syntax `startsWith` [0,1]
                let (ModuleContent descriptors descriptorDefLocs logicLocs patchLocs dataLocs shuffleLocs) = provides
                descriptorDefs <- fmap (DM.unionsWithKey mergeDescriptors) $ fmap concat $ traverse readDescriptorDefs descriptorDefLocs
                let provides' = ModuleFullContent descriptors descriptorDefs undefined patchLocs undefined undefined
                return $ ModuleFull name version depends softDepends provides'
                -}

withSingleFile :: FilePath -> (ByteString -> WithDirectoryT a) -> WithDirectoryT (Maybe a)
withSingleFile name e = withPath name e $ \case
    [] -> return Nothing
    [x] -> return $ Just x
    _ -> return Nothing

withPath :: FilePath -> (ByteString -> WithDirectoryT a) -> ([a] -> WithDirectoryT b) -> WithDirectoryT b
withPath path e c = case dropWhile isDelim path of
    "" -> WithFile "" e c
    path' -> if any isDelim path' then
            let (d,path'') = break isDelim path' in
            InSubdir d (withPath path'' e pure) (c . concat)
        else
            WithFile path' e c

isDelim :: Char -> Bool
isDelim = (==) '/'

readDescriptorDefs :: ResourceSpecifier -> MaybeT WithDirectoryT [DMap DescriptorIdent Descriptors]
readDescriptorDefs path = undefined --withPath path

mergeDescriptors :: DescriptorIdent t -> Descriptors t -> Descriptors t -> Descriptors t
mergeDescriptors _ (Descriptors xs) (Descriptors ys) = Descriptors (xs <> ys)

assertMaybeT :: (Applicative m) => Bool -> MaybeT m ()
assertMaybeT False = MaybeT $ pure Nothing
assertMaybeT True  = MaybeT $ pure $ Just ()

-}
