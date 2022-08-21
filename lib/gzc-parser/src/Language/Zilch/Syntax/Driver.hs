{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

module Language.Zilch.Syntax.Driver where

import qualified Algebra.Graph.Acyclic.AdjacencyMap as Acyclic
import qualified Algebra.Graph.AdjacencyMap as Cyclic
import Control.Monad.Except (MonadError, runExceptT, throwError)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.State (MonadState, modify, runStateT)
import Control.Monad.Writer (MonadWriter, runWriterT)
import Data.Bifunctor (bimap)
import Data.Foldable (fold, foldl')
import Data.Located (Located ((:@)))
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import Error.Diagnose (Diagnostic, addReport, def)
import Language.Zilch.CLI.Flags (WarningFlags (..))
import qualified Language.Zilch.Syntax.Core.AST as AST
import qualified Language.Zilch.Syntax.Core.CST as CST
import Language.Zilch.Syntax.Core.Lexeme (Token)
import Language.Zilch.Syntax.Errors

type ImportGraph = Cyclic.AdjacencyMap (FilePath, [Located Text])

type Files = [(FilePath, Text)]

type MonadDriver m = (?warnings :: WarningFlags, ?includeDirs :: [FilePath], MonadState (ImportGraph, Files) m, MonadWriter [DriverWarning] m, MonadError DriverError m, MonadIO m)

parseModules :: (?warnings :: WarningFlags, ?includeDirs :: [FilePath], MonadIO m) => [Text] -> m ([(FilePath, Text)], Either (Diagnostic String) ([(FilePath, Located AST.Module)], Diagnostic String))
parseModules modules = do
  ((res, (graph, files)), warns) <- runWriterT $ flip runStateT (Cyclic.empty, []) $ runExceptT (parseAndPatchModules modules)
  pure $ (files, adjust res graph warns)
  where
    toErrorDiagnostic err = addReport def $ fromDriverError err
    toWarningDiagnostic warns = foldl' addReport def (fromDriverWarning <$> warns)

    adjust (Left err) _ _ = Left $ toErrorDiagnostic err
    adjust (Right mods) graph warns =
      let sorted = Acyclic.topSort $ fromJust $ Acyclic.toAcyclic graph
          mods' = Map.fromList mods
       in Right (fetchModule mods' <$> reverse sorted, toWarningDiagnostic warns)

    fetchModule mods (path, name) = (path, mods Map.! name)

parseAndPatchModules :: forall m. MonadDriver m => [Text] -> m [([Located Text], Located AST.Module)]
parseAndPatchModules [] = pure []
parseAndPatchModules (m : ms) = do
  m' <- tryParseModuleName m
  path <-
    tryFindModule m' >>= \case
      [] -> throwError $ ModuleNotFound m' ?includeDirs
      ps@(_ : _ : _) -> throwError $ AmbiguousModuleName m' ps
      [path] -> pure path

  content <- liftIO $ Text.readFile path
  modify $ bimap id ((path, content) :)

  tks <- tryLexing path content
  cst <- tryParsing path tks
  (imports, ast) <- tryDesugaring cst
  imports' <- resolveImports imports
  ast' <- patchASTImports imports' ast

  let myself = (path, m')
  let imports'' = (myself,) <$> imports'
  modify $ bimap (`Cyclic.overlay` Cyclic.edges imports'') id

  mods <- parseAndPatchModules ms

  pure ((m', ast') : mods)

tryParseModuleName :: forall m. MonadDriver m => Text -> m [Located Text]
tryParseModuleName m = do
  let parts = fold $ Text.splitOn "∷" <$> Text.splitOn "::" m
  traverse checkValid parts
  where
    checkValid "" = throwError $ EmptyModuleName m
    checkValid part = do
      case Text.findIndex invalidCharacters part of
        Just idx -> throwError $ InvalidModuleName part idx
        Nothing -> pure $ part :@ dummy

    invalidCharacters '/' = True
    invalidCharacters ':' = True
    invalidCharacters '\\' = True
    invalidCharacters '"' = True
    invalidCharacters ',' = True
    invalidCharacters ';' = True
    invalidCharacters '=' = True
    invalidCharacters _ = False

    dummy = def

tryFindModule :: forall m. MonadDriver m => [Located Text] -> m [FilePath]
tryFindModule mod = undefined

tryLexing :: forall m. MonadDriver m => FilePath -> Text -> m [Located Token]
tryLexing path content = undefined

tryParsing :: forall m. MonadDriver m => FilePath -> [Located Token] -> m (Located CST.Module)
tryParsing path tks = undefined

tryDesugaring :: forall m. MonadDriver m => Located CST.Module -> m ([[Located Text]], Located AST.Module)
tryDesugaring cst = undefined

resolveImports :: forall m. MonadDriver m => [[Located Text]] -> m [(FilePath, [Located Text])]
resolveImports imps = undefined

patchASTImports :: forall m. MonadDriver m => [(FilePath, [Located Text])] -> Located AST.Module -> m (Located AST.Module)
patchASTImports imps ast = undefined
