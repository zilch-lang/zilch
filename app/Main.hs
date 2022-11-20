{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ImplicitParams #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Eta reduce" #-}

module Main (main) where

import Control.Monad (forM_, unless, when)
import Control.Monad.Except (lift, liftEither, runExceptT)
import Control.Monad.IO.Class (liftIO)
import Data.IORef (newIORef, readIORef, writeIORef)
import Data.List (nub)
import Data.Located (Located)
import Data.Text (Text)
import qualified Data.Text as Text
import Error.Diagnose (Diagnostic, Report (..), addFile, addReport, def, defaultStyle, hasReports, printDiagnostic, warningsToErrors)
import Language.Zilch.CLI.Flags (DebugFlags (..), Flags (..), InputFlags (..), OutputFlags (..), WarningFlags, doDump)
import qualified Language.Zilch.CLI.Flags as W (WarningFlags (..))
import Language.Zilch.CLI.Parser (getFlags)
import Language.Zilch.Optimize.Driver (optimize)
import Language.Zilch.Pretty.ANF ()
import Language.Zilch.Pretty.AST ()
import qualified Language.Zilch.Syntax.Core.AST as AST
import Language.Zilch.Syntax.Driver (parseModules)
import Language.Zilch.Typecheck.Driver (typecheckModules)
import Prettyprinter (pretty)
import System.Directory (makeAbsolute)
import System.Exit (exitFailure)
import System.IO

main :: IO ()
main = do
  !flags <- getFlags

  when (null $ modules $ input flags) do
    printDiagnostic stderr True True 4 defaultStyle $ addReport def $ Err Nothing ("No module specified on command-line." :: String) [] []
    exitFailure

  idirs <- nub <$> traverse makeAbsolute (includeDirs $ input flags)
  let ?warnings = warnings flags
      ?includeDirs = idirs
      ?buildProgress = buildProgress (debug flags)
      ?noMain = noMain (output flags)

  filesRef <- newIORef []
  res <- runExceptT do
    (files, res) <- liftIO $ parseModules $ Text.pack <$> modules (input flags)
    liftIO $ writeIORef filesRef files

    (allASTs, warns) <- liftEither res
    liftIO $ doOutputWarnings files warns
    liftIO $ forM_ allASTs \(path, _, ast) -> doDumpAST flags ast path

    (allANFs, warns) <- liftEither =<< typecheckModules flags allASTs
    liftIO $ doOutputWarnings files warns

    unless ?noMain do
      anf <- lift $ optimize flags allANFs

      pure ()

    pure ()

  case res of
    Left diag -> do
      files <- liftIO $ readIORef filesRef
      printDiagnostic stderr True True 4 defaultStyle (mkDiag diag files)
      exitFailure
    Right _ -> do
      pure ()

doOutputWarnings :: (?warnings :: WarningFlags) => [(FilePath, Text)] -> Diagnostic String -> IO ()
doOutputWarnings files diag = do
  let erroneous = W.areErrors ?warnings
  let diag' = if erroneous then warningsToErrors diag else diag

  printDiagnostic stderr True True 4 defaultStyle (mkDiag diag' files) -- addFile diag' path $ Text.unpack content)
  when (erroneous && hasReports diag') do
    exitFailure

mkDiag :: Diagnostic String -> [(FilePath, Text)] -> Diagnostic String
mkDiag = foldr (\(path, content) diag -> addFile diag path $ Text.unpack content)

doDumpAST :: Flags -> Located AST.Module -> FilePath -> IO ()
doDumpAST flags mod path = doDump flags "ast" (dumpAST . debug) (pretty mod) path
