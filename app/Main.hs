{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Main (main) where

import Control.Monad (forM, forM_)
import Data.Bifunctor (second)
import Data.Located (Located)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import Error.Diagnose (Diagnostic, addFile, defaultStyle, printDiagnostic)
import Language.Zilch.CLI.Flags (Flags (..), InputFlags (..), DebugFlags (..))
import Language.Zilch.CLI.Parser (getFlags)
import Language.Zilch.Pretty.TAST ()
import Language.Zilch.Pretty.AST ()
import Language.Zilch.Syntax.Desugarer (desugarCST)
import Language.Zilch.Syntax.Lexer (lexFile)
import Language.Zilch.Syntax.Parser (parseTokens)
import Language.Zilch.Typecheck.Elaborator (elabProgram)
import qualified Language.Zilch.Syntax.Core.AST as AST
import Prettyprinter (pretty)
import Prettyprinter.Render.Text (putDoc)
import System.Directory (createDirectoryIfMissing)
import System.FilePath.Posix (joinPath)
import System.IO
import Control.Monad.Except (liftEither, runExceptT)
import Control.Monad.IO.Class (liftIO)

data File = File FilePath Text

main :: IO ()
main = do
  flags <- getFlags

  files <- case files (input flags) of
    [] -> pure . File "stdin" <$> Text.getContents
    fs -> forM fs \f -> File f <$> Text.readFile f

  forM_ files \(File path content) -> do
    ast <- runExceptT do
          (tks, warns) <- liftEither $ lexFile path content
          liftIO $ doOutputWarnings path content warns
          
          (!cst, warns) <- liftEither $ parseTokens path tks
          liftIO $ doOutputWarnings path content warns

          (!ast, warns) <- liftEither $ desugarCST cst
          liftIO $ doOutputWarnings path content warns
          liftIO $ doDumpAST flags ast
          
          (!tast, warns) <- liftEither $ elabProgram ast
          liftIO $ doOutputWarnings path content warns

          pure (tks, cst, ast, tast)

    case ast of
      Left diag -> printDiagnostic stderr True True 4 defaultStyle (addFile diag path $ Text.unpack content)
      Right (_, _, _, tast) -> do
        putStrLn "\n✅ Following program passed typechecking:"
        putDoc (pretty tast)

    pure ()

doOutputWarnings :: FilePath -> Text -> Diagnostic String -> IO ()
doOutputWarnings path content diag = printDiagnostic stderr True True 4 defaultStyle (addFile diag path $ Text.unpack content)

doDumpAST :: Flags -> Located AST.Module -> IO ()
doDumpAST flags mod
  | dumpAST (debug flags) = do
    createDirectoryIfMissing True (joinPath [".zilch", "dump"])
    writeFile (joinPath [".zilch", "dump", "ast.dbg.zc"]) (show $ pretty mod)
  | otherwise = pure ()
