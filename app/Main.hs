{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ImplicitParams #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Main (main) where

import Control.Monad (forM_, when)
import Control.Monad.Except (liftEither, runExceptT)
import Control.Monad.IO.Class (liftIO)
import Data.Hashable (Hashable (hash))
import Data.IORef (newIORef, readIORef, writeIORef)
import Data.List (nub)
import Data.Located (Located, unLoc)
import Data.Text (Text)
import qualified Data.Text as Text
import Error.Diagnose (Diagnostic, Report (..), addFile, addReport, def, defaultStyle, hasReports, printDiagnostic, warningsToErrors)
import Language.Zilch.CLI.Flags (DebugFlags (..), Flags (..), InputFlags (..), WarningFlags)
import qualified Language.Zilch.CLI.Flags as W (WarningFlags (..))
import Language.Zilch.CLI.Parser (getFlags)
import Language.Zilch.Pretty.AST ()
import Language.Zilch.Pretty.TAST ()
import qualified Language.Zilch.Syntax.Core.AST as AST
import Language.Zilch.Syntax.Driver (parseModules)
import qualified Language.Zilch.Typecheck.Core.AST as TAST
import Prettyprinter (pretty)
import System.Directory (createDirectoryIfMissing, makeAbsolute)
import System.Exit (exitFailure)
import System.FilePath (joinPath, splitPath, (<.>))
import System.IO

main :: IO ()
main = do
  !flags <- getFlags

  when (null $ modules $ input flags) do
    printDiagnostic stderr True True 4 defaultStyle $ addReport def $ Err Nothing ("No module specified on command-line." :: String) [] []
    exitFailure

  let ?warnings = warnings flags
  idirs <- nub <$> traverse makeAbsolute (includeDirs $ input flags)
  let ?includeDirs = idirs

  filesRef <- newIORef []
  res <- runExceptT do
    (files, res) <- liftIO $ parseModules $ Text.pack <$> modules (input flags)
    liftIO $ writeIORef filesRef files

    (allASTs, warns) <- liftEither res
    liftIO $ doOutputWarnings files warns
    liftIO $ forM_ allASTs \(path, _, ast) -> doDumpAST flags ast path
    liftIO $ putStrLn $ "✅ Modules parsed!"

    -- (allTASTs, warns) <- typecheckModules allASTs
    -- liftIO $ doOutputWarnings files warns
    -- liftIO $ forM_ allTASTs \(path, _, tast) -> doDumpTAST flags tast path
    -- liftIO $ putStrLn $ "✅ Modules passed type-checking!"

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

  printDiagnostic stderr True True 4 defaultStyle (mkDiag diag' files) --addFile diag' path $ Text.unpack content)
  when (erroneous && hasReports diag') do
    exitFailure

mkDiag :: Diagnostic String -> [(FilePath, Text)] -> Diagnostic String
mkDiag diag files = foldr (\(path, content) diag -> addFile diag path $ Text.unpack content) diag files

doDumpAST :: Flags -> Located AST.Module -> FilePath -> IO ()
doDumpAST flags mod path
  | dumpAST (debug flags) = do
    let dir = getDumpBasePath flags

    createDirectoryIfMissing True (joinPath dir)
    writeFile (joinPath $ dir <> [show (hash path) <> "-ast" <.> "dbg" <.> "zc"]) (show $ pretty mod)
  | otherwise = pure ()

doDumpTAST :: Flags -> Located TAST.Module -> FilePath -> IO ()
doDumpTAST flags mod path
  | dumpTAST (debug flags) = do
    let dir = getDumpBasePath flags

    createDirectoryIfMissing True (joinPath dir)
    writeFile (joinPath $ dir <> [show (hash path) <> "tast" <.> "dbg" <.> "zc"]) (show $ pretty mod)
  | otherwise = pure ()

getDumpBasePath :: Flags -> [FilePath]
getDumpBasePath flags = maybe [".zilch", "dump"] splitPath $ dumpDir (debug flags)
