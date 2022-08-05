{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ImplicitParams #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Main (main) where

import Control.Monad (forM, forM_, when)
import Control.Monad.Except (liftEither, runExceptT)
import Control.Monad.IO.Class (liftIO)
import Data.Located (Located)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import Error.Diagnose (Diagnostic, addFile, defaultStyle, hasReports, printDiagnostic, warningsToErrors)
import Language.Zilch.CLI.Flags (DebugFlags (..), Flags (..), InputFlags (..), WarningFlags)
import qualified Language.Zilch.CLI.Flags as W (WarningFlags (..))
import Language.Zilch.CLI.Parser (getFlags)
import Language.Zilch.Pretty.AST ()
import Language.Zilch.Pretty.TAST ()
import qualified Language.Zilch.Syntax.Core.AST as AST
import Language.Zilch.Syntax.Desugarer (desugarCST)
import Language.Zilch.Syntax.Lexer (lexFile)
import Language.Zilch.Syntax.Parser (parseTokens)
import qualified Language.Zilch.Typecheck.Core.AST as TAST
import Language.Zilch.Typecheck.Elaborator (elabProgram)
import Prettyprinter (pretty)
import System.Directory (createDirectoryIfMissing)
import System.Exit (exitFailure)
import System.FilePath.Posix (joinPath, splitPath)
import System.IO

data File = File FilePath Text

main :: IO ()
main = do
  !flags <- getFlags

  files <- case files (input flags) of
    [] -> pure . File "stdin" <$> Text.getContents
    fs -> forM fs \f -> File f <$> Text.readFile f

  let ?warnings = warnings flags

  forM_ files \(File path content) -> do
    ast <- runExceptT do
      (!tks, warns) <- liftEither $ lexFile path content
      liftIO $ doOutputWarnings path content warns

      (!cst, warns) <- liftEither $ parseTokens path tks
      liftIO $ doOutputWarnings path content warns

      (!ast, warns) <- liftEither $ desugarCST cst
      liftIO $ doOutputWarnings path content warns
      liftIO $ doDumpAST flags ast
      liftIO $ putStrLn $ "✅ Module '" <> path <> "' parsed"

      (!tast, warns) <- liftEither $ elabProgram ast
      liftIO $ doOutputWarnings path content warns
      liftIO $ doDumpTAST flags tast
      liftIO $ putStrLn $ "✅ Module '" <> path <> "' passed type-checking"

      pure (tks, cst, ast, tast)

    case ast of
      Left diag -> do
        printDiagnostic stderr True True 4 defaultStyle (addFile diag path $ Text.unpack content)
        exitFailure
      Right (_, _, _, _) -> pure ()

    pure ()

doOutputWarnings :: (?warnings :: WarningFlags) => FilePath -> Text -> Diagnostic String -> IO ()
doOutputWarnings path content diag = do
  let erroneous = W.areErrors ?warnings
  let diag' = if erroneous then warningsToErrors diag else diag
      
  printDiagnostic stderr True True 4 defaultStyle (addFile diag' path $ Text.unpack content)
  when (erroneous && hasReports diag') do
    exitFailure

doDumpAST :: Flags -> Located AST.Module -> IO ()
doDumpAST flags mod
  | dumpAST (debug flags) = do
    let dir = getDumpBasePath flags

    createDirectoryIfMissing True (joinPath dir)
    writeFile (joinPath $ dir <> ["ast.dbg.zc"]) (show $ pretty mod)
  | otherwise = pure ()

doDumpTAST :: Flags -> Located TAST.Module -> IO ()
doDumpTAST flags mod
  | dumpTAST (debug flags) = do
    let dir = getDumpBasePath flags

    createDirectoryIfMissing True (joinPath dir)
    writeFile (joinPath $ dir <> ["tast.dbg.zc"]) (show $ pretty mod)
  | otherwise = pure ()

getDumpBasePath :: Flags -> [FilePath]
getDumpBasePath flags = maybe [".zilch", "dump"] splitPath $ dumpDir (debug flags)
