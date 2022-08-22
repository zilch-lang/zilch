{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Syntax.Driver where

import qualified Algebra.Graph.Acyclic.AdjacencyMap as Acyclic
import qualified Algebra.Graph.AdjacencyMap as Cyclic
import Control.Monad (when)
import Control.Monad.Except (MonadError, liftEither, runExceptT, throwError)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.State (MonadState, modify, runStateT)
import Control.Monad.Writer (MonadWriter, runWriterT)
import Data.Bifunctor (bimap, first)
import Data.Foldable (fold, foldl')
import Data.Located (Located ((:@)), Position (file), unLoc)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import Error.Diagnose (Diagnostic, addFile, addReport, def, defaultStyle, hasReports, printDiagnostic, warningsToErrors)
import Language.Zilch.CLI.Flags (WarningFlags (..))
import qualified Language.Zilch.CLI.Flags as W (WarningFlags (..))
import qualified Language.Zilch.Syntax.Core.AST as AST
import qualified Language.Zilch.Syntax.Core.CST as CST
import Language.Zilch.Syntax.Core.Lexeme (Token)
import Language.Zilch.Syntax.Desugarer (desugarCST)
import Language.Zilch.Syntax.Errors
import Language.Zilch.Syntax.Lexer (lexFile)
import Language.Zilch.Syntax.Parser (parseTokens)
import System.Directory (doesFileExist)
import System.Exit (exitFailure)
import System.FilePath (joinPath, (<.>), (</>))
import System.IO (stderr)

type ImportGraph = Cyclic.AdjacencyMap (FilePath, [Located Text])

type Files = [(FilePath, Text)]

type MonadDriver m = (?warnings :: WarningFlags, ?includeDirs :: [FilePath], MonadState (ImportGraph, Files) m, MonadWriter [DriverWarning] m, MonadError DriverError m, MonadIO m)

parseModules :: (?warnings :: WarningFlags, ?includeDirs :: [FilePath], MonadIO m) => [Text] -> m ([(FilePath, Text)], Either (Diagnostic String) ([(FilePath, Located AST.Module)], Diagnostic String))
parseModules modules = do
  ((res, (graph, files)), warns) <- runWriterT $ flip runStateT (Cyclic.empty, []) $ runExceptT (parseAndPatchModules modules)
  pure $ (files, adjust res graph warns)
  where
    toErrorDiagnostic (LexingE d) = d
    toErrorDiagnostic (ParsingE d) = d
    toErrorDiagnostic (DesugaringE d) = d
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

  (tks, warns) <- tryLexing path content
  liftIO $ doOutputWarnings path content warns

  (cst, warns) <- tryParsing path tks
  liftIO $ doOutputWarnings path content warns

  (imports, ast, warns) <- tryDesugaring cst
  liftIO $ doOutputWarnings path content warns

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

    dummy = def {file = "command-line"}

tryFindModule :: forall m. MonadDriver m => [Located Text] -> m [FilePath]
tryFindModule mod = go (toPath mod) ?includeDirs
  where
    go _ [] = pure []
    go path (d : dir) = do
      let p = d </> path
      fileExists <- liftIO $ doesFileExist p
      if fileExists
        then (p :) <$> go path dir
        else go path dir

    toPath mod = joinPath (Text.unpack . unLoc <$> mod) <.> "zc"

tryLexing :: forall m. MonadDriver m => FilePath -> Text -> m ([Located Token], Diagnostic String)
tryLexing path content = liftEither . first LexingE $ lexFile path content

tryParsing :: forall m. MonadDriver m => FilePath -> [Located Token] -> m (Located CST.Module, Diagnostic String)
tryParsing path tks = liftEither . first ParsingE $ parseTokens path tks

tryDesugaring :: forall m. MonadDriver m => Located CST.Module -> m ([[Located Text]], Located AST.Module, Diagnostic String)
tryDesugaring cst = liftEither . bimap DesugaringE swapFirstTwo $ desugarCST cst
  where
    swapFirstTwo ~(a, b, c) = (b, a, c)

resolveImports :: forall m. MonadDriver m => [[Located Text]] -> m [(FilePath, [Located Text])]
resolveImports imps = pure [] -- TODO

patchASTImports :: forall m. MonadDriver m => [(FilePath, [Located Text])] -> Located AST.Module -> m (Located AST.Module)
patchASTImports imps ast = pure ast -- TODO

---------------------------------

doOutputWarnings :: (?warnings :: WarningFlags) => FilePath -> Text -> Diagnostic String -> IO ()
doOutputWarnings path content diag = do
  let erroneous = W.areErrors ?warnings
  let diag' = if erroneous then warningsToErrors diag else diag

  printDiagnostic stderr True True 4 defaultStyle (addFile diag' path $ Text.unpack content)
  when (erroneous && hasReports diag') do
    exitFailure
