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
{-# LANGUAGE CPP #-}
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
import TMCR.Logic.Merge (MonadMerge (..), GameDef, mergeDescriptorDeclarations, mergeHeader, mergeContent)
import Control.Lens
import TMCR.Module.Dependency (makeModuleDependencyInfo, ModuleDependencyInfo, DependencyError, singleModuleDependencies)
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
    ( logicParser, Sugar, Scopes, _ModeAppend )
import TMCR.Logic.Data (LogicData')
import TMCR.Logic.Shuffle (parseShuffleInstruction, parseShuffleStatements)
import Data.Aeson (decode)
#ifdef MIN_VERSION_yaml
import Data.Yaml (decodeEither, ParseException, decodeEither')
#else
import Data.YAML.Aeson
#endif

import Data.Functor.Foldable.TH
import Data.Functor.Classes
import Data.Either (isRight)

#ifndef MIN_VERSION_yaml
type ParseException = String
#endif

#if MIN_VERSION_polysemy(1,4,0)
-- #define USE_NESTED_WITHFILE
-- #define CUSTOM_EFFECTS
#endif

data LocationSpec = LocationSpec {
                      _basePath :: FilePath
                    , _steps :: [String]
                    , _fileName :: String
                    }

#ifdef CUSTOM_EFFECTS
data WithDirectory m a where
     InSubdir :: String -> m a -> WithDirectory m a
     ListDirectory :: WithDirectory m [(String, Bool)] --name, isDirectory
#ifdef USE_NESTED_WITHFILE
     WithFile :: String -> (FilePath -> ByteString -> m a) -> WithDirectory m [a]
#else
     WithFile :: String -> WithDirectory m [(FilePath, ByteString)]
#endif
#else
type WithDirectory = Reader Directory
#endif

newtype Directory = Directory { getDirectory :: (Map FilePath (Either ByteString Directory)) } deriving (Eq, Ord, Show)

$(makeLenses ''LocationSpec)
$(makeBaseFunctor ''Directory)

#ifdef CUSTOM_EFFECTS
$(makeSem ''WithDirectory)
#else
inSubdir :: (Member WithDirectory r) => String -> Sem r a -> Sem r a
inSubdir name = local (^?! to getDirectory . at name . _Just . _Right)
listDirectory :: (Member WithDirectory r) => Sem r [(String, Bool)]
listDirectory = asks (^.. to getDirectory . to M.toList . traverse . to (_2 %~ isRight))
withFile :: (Member WithDirectory r) => String -> Sem r [(FilePath, ByteString)]
withFile name = asks $ catMaybes . (^.. to getDirectory . to M.toList . traverse . to (\case
                    (path, Left content) | name `matches` path -> Just (name, content)
                    _ -> Nothing))
#endif

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
    let xs' = filter (\x -> matches name (fst x) && snd x) xs
    forM xs' $ \(x,_) -> inSubdir x (a x)


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
matches ('*':suffix) ys = hasSuffix suffix ys
matches xs ys = xs == ys

hasSuffix suffix xs = take (length suffix) (reverse xs) == reverse suffix

assertMaybe :: Bool -> Maybe ()
assertMaybe False = Nothing
assertMaybe True = Just ()

data DirectoryErrorWithContext = DirectoryErrorWithContext
                    { _dirErrorContext :: [FilePath]
                    , _dirErrorError :: DirectoryError
                    } deriving (Eq, Ord, Show)
data DirectoryError = DirNotFound
                    | DirAmbiguous
                    deriving (Show, Eq, Ord)

$(makeLenses ''DirectoryErrorWithContext)

#if !MIN_VERSION_polysemy(1,2,0)
subsume :: Sem (Reader a ': Reader a ': r) b -> Sem (Reader a ': r) b
subsume s = do
    a <- ask
    runReader a $ s
#endif

runInMemoryDir :: (Member (Error DirectoryErrorWithContext) r) => Directory -> Sem (WithDirectory : r)  a -> Sem r a
#ifdef CUSTOM_EFFECTS
runInMemoryDir xs = runReader xs . f where
    f :: (Member (Error DirectoryErrorWithContext) r) => Sem (WithDirectory ': r) a -> Sem (Reader Directory ': r) a
    f = reinterpretH @WithDirectory @(Reader Directory) $ \case
        ListDirectory -> do
            dir <- ask @Directory
            pureT $ fmap (fmap isRight) $ M.toList $ getDirectory dir
#ifdef USE_NESTED_WITHFILE
        WithFile name a -> _
#else
        WithFile name -> do
            files <- asks @Directory $ M.toList . runIdentity . M.traverseMaybeWithKey (\k v -> return $ do
                    assertMaybe (name `matches` k)
                    Left v' <- Just v --only files
                    return v') . getDirectory
            pureT files
#endif
        InSubdir name a -> do
            subdirs <- asks @Directory $ M.toList . runIdentity . M.traverseMaybeWithKey (\k v -> return $ do
                assertMaybe (name == k)
                Right v' <- Just v --only directories
                return v') . getDirectory
            case subdirs of
                [] -> throw $ DirectoryErrorWithContext [name] $ DirNotFound
                [(x,s)] -> local @Directory (const s) $ do
                    a' <- runT a
                    let addContext :: forall r a. (Member (Error DirectoryErrorWithContext)r) => FilePath -> Sem r a -> Sem r a
                        addContext name = flip (catch @DirectoryErrorWithContext) (\x -> throw @DirectoryErrorWithContext $ (x & dirErrorContext %~ (name:)))
                    raise $ subsume $ addContext name $ f a'
                _ -> throw $ DirectoryErrorWithContext [name] $ DirAmbiguous
    {-interpretH $ \case
    ListDirectory -> pureT $ fmap (fmap isRight) $ M.toList $ getDirectory xs
#if MIN_VERSION_polysemy(1,4,0)
    WithFile name a -> do
        let files = M.toList $ runIdentity $ M.traverseMaybeWithKey (\k v -> return $ do
                assertMaybe (name `matches` k)
                Left v' <- Just v --only files
                return v') $ getDirectory xs
        --runTSimple $ traverse (uncurry a) files
        a' <- runT $ traverse (uncurry a) files
        raise $ runInMemoryDir xs a'
#else
    WithFile name -> do
        let files = M.toList $ runIdentity $ M.traverseMaybeWithKey (\k v -> return $ do
                assertMaybe (name `matches` k)
                Left v' <- Just v --only files
                return v') $ getDirectory xs
        pureT files
#endif
    InSubdir name a -> do
        let subdirs = M.toList $ runIdentity $ M.traverseMaybeWithKey (\k v -> return $ do
                assertMaybe (name == k)
                Right v' <- Just v --only directories
                return v') $ getDirectory xs
        case subdirs of
            [] -> throw $ DirectoryErrorWithContext [name] $ DirNotFound
            [(x,s)] -> do
                a' <- runT a
                let addContext :: forall r a. (Member (Error DirectoryErrorWithContext)r) => FilePath -> Sem r a -> Sem r a
                    addContext name = flip (catch @DirectoryErrorWithContext) (\x -> throw @DirectoryErrorWithContext $ (x & dirErrorContext %~ (name:)))
                raise $ addContext name $ runInMemoryDir s a'
            _ -> throw $ DirectoryErrorWithContext [name] $ DirAmbiguous
            -}
#else
runInMemoryDir = runReader
#endif

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
            if isDirisRighto
                    fmap Just $ withCurrentDisRighty dir' $ exec a
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
    xs <- fmap concat $ forM sources $ \path -> inSubdirs path $ \path -> do
        m <- readModule
        return (path, m)
    content <- M.traverseWithKey (\k -> \case
        [] -> error "unreachable"
        [x] -> return x
        _ -> throw $ MergeErrorModuleMultipleDefine k) $ M.fromListWith (<>) $ fmap (\(path, m) -> (m ^. moduleName, [(path, m ^. moduleProvides)])) $ xs
    deps <- do
        let depInfo = fmap (singleModuleDependencies . snd) xs
        case makeModuleDependencyInfo depInfo of
            Left err -> throw $ MergeErrorDependencies err
            Right deps -> return deps
    runReader @ModuleDependencyInfo deps $ do
        header <- mergeHeader $ fmap (view $ _2 . moduleContentHeader) content
        content' <- forM content $ \(path, m) -> do
            c <- inSubdirs path $ \_ -> readModuleFullContent (m & moduleContentHeader .~ header)
            let [c'] = c
            return (path, c')
        mergeContent header content'

inSubdirs :: forall r a. (Member WithDirectory r) => FilePath -> (FilePath -> Sem r a) -> Sem r [a]
inSubdirs p a = inSubdirs' a $ splitPath p where
    inSubdirs' :: forall b. (FilePath -> Sem r b) -> [FilePath] -> Sem r [b]
    inSubdirs' a [] = error "unreachable"
    inSubdirs' a [x] = inSubdir' x a
    inSubdirs' a (x:xs) = fmap concat $ inSubdir' x $ \path -> inSubdirs' (a . (path <>)) xs

splitPath x = reverse $ fmap reverse $ go "" [] x where
    go "" [] "" = [""]
    go "" xs "" = xs
    go x xs "" = x:xs
    go "" xs ('/':cs) = go "" xs cs
    go x xs ('/':cs) = go "" (x:xs) cs
    go x xs (c:cs) = go (c:x) xs cs

readModule :: (Members '[WithDirectory, Error ParseException, Error AssertionFailed] r) => Sem r (Module ModuleContent)
readModule = withSingleFile "module.yaml" $ \path content -> do
#ifdef MIN_VERSION_yaml
    case decodeEither' $ BL.toStrict content of
        Left err -> throw err
#else
    case decode1 $ content of
        Left err -> throw @ParseException $ show err
#endif
        Right x -> do
            assert "syntaxVerion 0.1" $ (x ^. moduleSyntaxVersion . _Version) `startsWith` [0,1]
            return x

newtype AssertionFailed = AssertionFailed { getAssertionName :: Text } deriving (Eq, Ord, Show)

data MergeError = MergeErrorModuleMultipleDefine Text
                | MergeErrorDependencies [DependencyError]
                | MergeErrorOther Text
                | MergeErrorContext Text MergeError
                deriving (Eq, Ord, Show)

instance (Member (Error MergeError) r, Member (Reader ModuleDependencyInfo) r) => MonadMerge (Sem r) where
    mergeDescDeclError name _ = throw $ MergeErrorOther $ "Descriptor " <> name <> " has conflicting definitions"
    mergeSugarConflictError name _ = throw $ MergeErrorOther $ "Sugar " <> name <> " has conflicting definitions"
    errorDescriptorNotDeclared name = throw $ MergeErrorOther $ "Descriptor " <> name <> " is missing a declaration"
    errorDescriptorArgsMismatch name expected got = throw $ MergeErrorOther $ "Descriptor " <> name <> " needs " <> T.pack (show $ length expected) <> " arguments but got " <> T.pack (show got)
    errorDescriptorTypeMismatch name actual usedAs = throw $ MergeErrorOther $ "Descriptor " <> name <> " has type " <> T.pack (show actual) <> " not " <> T.pack (show usedAs)
    errorOverspecifiedScope scope = throw $ MergeErrorOther $ "Unable to resolve scope " <> T.pack (show scope)
    mergeErrorAppendToUndefined name = throw $ MergeErrorOther $ "Cannot expand unknown shuffle " <> name
    mergeErrorUnresolvedOrderingOverwrite name1 name2 = throw $ MergeErrorOther $ "Cannot order " <> name1 <> " and " <> name2 <> ". Maybe you forgot to add an (optional) dependency?"
    errorUnexpectedLogicStructure = throw $ MergeErrorOther $ "Unexpected Logic Structure. I know as much about what is wrong as you do"
    errorLogicDataMergeConflict stuff = throw $ MergeErrorOther $ "Failed to merge Logic Data: " <> T.pack (show stuff)
    errorGenericMergeError num = throw $ MergeErrorOther $ "Generic Merge Error " <> T.pack (show num)
    errorContext descr act = act `catch` (throw . MergeErrorContext descr)
    dependencies = ask
    warningIgnoredLogicSubtree _ = return ()

readModuleFullContent :: (Members '[Reader Scopes, WithDirectory, Error (ParseErrorBundle Text Void)] r) => ModuleContent -> Sem r ModuleFullContent
readModuleFullContent content =
    runReader
        @DescriptorDeclarations
        (getDescriptorDeclarations $ content ^. moduleContentDescriptors) $
    runReader @[Sugar]
        (content ^. moduleContentLogicSugar . sugars) $
    do
        descriptorDefs <- fmap (DM.unionsWithKey (\_ (Descriptors xs) (Descriptors ys) -> Descriptors (xs <> ys)) . concat) $ forM (content ^. moduleContentDescriptorDefinitions) $ \x -> do
            withPath (T.unpack x) $ \p c ->
                runParserC parseDescriptorDefinitions p (TE.decodeUtf8 $ BL.toStrict c)
        scopes <- ask @Scopes
        logic <- fmap concat $ forM (content ^. moduleContentLogic) $ \x -> do
            withPath (T.unpack x) $ \p c ->
                runParserC (logicParser scopes) p (TE.decodeUtf8 $ BL.toStrict c)
        logicData <- fmap (concat . concat) $ forM (content ^. moduleContentData) $ \x -> do
            withPath (T.unpack x) $ \p c ->
                return $ maybeToList $ decode @LogicData' c
        shuffles <- fmap (concat . concat) $ forM (content ^. moduleContentShuffles) $ \x -> do
            withPath (T.unpack x) $ \p c ->
                runReader @() () $
                runParserC parseShuffleStatements p (TE.decodeUtf8 $ BL.toStrict c)
        return $ ModuleFullContent descriptorDefs logic (content ^. moduleContentPatches) logicData shuffles

withFile' :: (Member WithDirectory r) => String -> (FilePath -> ByteString -> Sem r a) -> Sem r [a]
#ifdef USE_NESTED_WITHFILE
withFile' = withFile
#else
withFile' filename action = do
    files <- withFile filename
    forM files $ \file -> uncurry action file
#endif

withPath :: forall r a. (Member WithDirectory r) => FilePath -> (FilePath -> ByteString -> Sem r a) -> Sem r [a]
withPath path c = withPath' "" path c where
    withPath' :: FilePath -> FilePath -> (FilePath -> ByteString -> Sem r a) -> Sem r [a]
    withPath' context path c = case dropWhile isDelim path of
        "" -> withFile' "" (\path' -> c $ context <> path')
        path' -> if any isDelim path' then
                let (d,path'') = break isDelim path' in
                concat <$> inSubdir' d (\dir' -> withPath' (context <> dir') path'' c)
            else
                withFile' path' (\path'' -> c $ context <> path'')

withPathFragments :: forall r a. (Member WithDirectory r) => [FilePath] -> (FilePath -> ByteString -> Sem r a) -> Sem r [a]
withPathFragments [] = withFile' ""
withPathFragments [x] = withFile' x
withPathFragments (x:xs) = \c -> inSubdir x $ withPathFragments xs c

isDelim :: Char -> Bool
isDelim = (==) '/'

withSingleFile :: (Members '[WithDirectory, Error AssertionFailed] r) => FilePath -> (FilePath -> ByteString -> Sem r a) -> Sem r a
withSingleFile path cont = do
    xs <- withFile' path (curry return)
    case xs of
        [x] -> uncurry cont x
        xs -> throw $ AssertionFailed $ "expected single file, got " <> T.pack (show (length xs))

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
