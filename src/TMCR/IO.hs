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
module TMCR.IO where

import Control.Lens.TH

import Control.Monad (ap, (>=>), forM, join)

import System.Directory
import Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString.Lazy as BL
import TMCR.Module
import Data.Aeson (decode)
import Control.Monad.Trans.Maybe (MaybeT(..))
import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DM
import TMCR.Logic.Descriptor
import Data.Maybe (catMaybes, maybeToList)
import TMCR.Logic.Merge (MonadMerge (..), GameDef, mergeDescriptorDeclarations)
import Control.Lens
import TMCR.Module.Dependency (makeModuleDependencyInfo)
import qualified Data.Map as M

import Polysemy
import Polysemy.Resource
import Polysemy.Final
import Polysemy.Error
import qualified Data.Text as T
import TMCR.Logic.Common
import Text.Megaparsec (ParseErrorBundle)
import Data.Void (Void)
import Data.Text (Text)
import Polysemy.Reader
import Data.Map (Map)
import qualified Data.Text.Encoding as TE
import TMCR.Logic.Logic
    ( logicParser, Sugar, defaultSugar, Scopes )
import TMCR.Logic.Data (LogicData')
import TMCR.Logic.Shuffle (parseShuffleInstruction, parseShuffleStatements)

data LocationSpec = LocationSpec {
                      _basePath :: FilePath
                    , _steps :: [String]
                    , _fileName :: String
                    }

data WithDirectory m a where
     InSubdir :: String -> (FilePath -> m a) -> WithDirectory m [a]
     ListDirectory :: WithDirectory m [String]
     WithFile :: String -> (FilePath -> ByteString -> m a) -> WithDirectory m [a]

$(makeLenses ''LocationSpec)
$(makeSem ''WithDirectory)

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

readModule :: (Members '[WithDirectory, Error ()] r) => Sem r Module
readModule = withSingleFile "module.yaml" $ \path content -> do
    case decode content of
        Nothing -> throw ()
        Just x -> do
            assert $ (x ^. moduleSyntaxVersion . _Version) `startsWith` [0,1]
            return x

data MergeError = MergeError

instance (Member (Error MergeError) r) => MonadMerge (Sem r) where
    --todo

readModuleFull :: (Members '[Reader Scopes, WithDirectory, Error ()] r) => Sem r ModuleFull
readModuleFull = do
    m <- readModule
    content <- readModuleFullContent $ m ^. moduleProvides
    return $ ModuleFull (m ^. moduleName) (m ^. moduleVersion) (m ^. moduleDependencies) (m ^. moduleSoftDependency) content

readModuleFullContent :: (Members '[Reader Scopes, WithDirectory, Error ()] r) => ModuleContent -> Sem r ModuleFullContent
readModuleFullContent content =
    runReader
        @DescriptorDeclarations
        (getDescriptorDeclarations $ content ^. moduleContentDescriptors) $
    mapError
        @(ParseErrorBundle Text Void)
        (const ()) $
    do
        descriptorDefs <- fmap (DM.unionsWithKey (\_ (Descriptors xs) (Descriptors ys) -> Descriptors (xs <> ys)) . concat) $ forM (content ^. moduleContentDescriptorDefinitions) $ \x -> do
            withPath (T.unpack x) $ \p c ->
                runParserC parseDescriptorDefinitions p (TE.decodeUtf8 $ BL.toStrict c)
        scopes <- ask @Scopes
        logic <- fmap (concat . concat) $ forM (content ^. moduleContentLogic) $ \x -> do
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
            undefined
        return $ ModuleFullContent (content ^. moduleContentDescriptors) descriptorDefs logic (content ^. moduleContentPatches) logicData shuffles

withPath :: forall r a. (Member WithDirectory r) => FilePath -> (FilePath -> ByteString -> Sem r a) -> Sem r [a]
withPath path c = withPath' "" path c where
    withPath' :: FilePath -> FilePath -> (FilePath -> ByteString -> Sem r a) -> Sem r [a]
    withPath' context path c = case dropWhile isDelim path of
        "" -> withFile "" (\path' -> c $ context <> path')
        path' -> if any isDelim path' then
                let (d,path'') = break isDelim path' in
                concat <$> inSubdir d (\dir' -> withPath' (context <> dir') path'' c)
            else
                withFile path' (\path'' -> c $ context <> path'')

isDelim :: Char -> Bool
isDelim = (==) '/'

withSingleFile :: (Members '[WithDirectory, Error ()] r) => FilePath -> (FilePath -> ByteString -> Sem r a) -> Sem r a
withSingleFile path cont = do
    xs <- withFile path (curry return)
    case xs of
        [x] -> uncurry cont x
        _ -> throw ()

assert :: (Member (Error ()) r) => Bool -> Sem r ()
assert True = return ()
assert False = throw ()

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