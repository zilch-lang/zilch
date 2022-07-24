{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Main where

import Control.Monad (forM, forM_)
import Data.Bifunctor (second)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import Error.Diagnose (addFile, defaultStyle, printDiagnostic)
import Language.Zilch.CLI.Flags (Flags (..), InputFlags (..))
import Language.Zilch.CLI.Parser (getFlags)
import Language.Zilch.Pretty.TAST ()
import Language.Zilch.Syntax.Desugarer (desugarCST)
import Language.Zilch.Syntax.Lexer (lexFile)
import Language.Zilch.Syntax.Parser (parseTokens)
import Language.Zilch.Typecheck.Elaborator (elabProgram)
import Prettyprinter (pretty)
import Prettyprinter.Render.Text (putDoc)
import System.IO

data File = File FilePath Text

main :: IO ()
main = do
  flags <- getFlags

  files <- case files (input flags) of
    [] -> pure . File "stdin" <$> Text.getContents
    fs -> forM fs \f -> File f <$> Text.readFile f

  forM_ files \(File path content) -> do
    let ast = do
          (tks, warns) <- lexFile path content
          (!cst, warns) <- second (warns <>) <$> parseTokens path tks
          (!ast, warns) <- second (warns <>) <$> desugarCST cst
          second (warns <>) <$> elabProgram ast

    case ast of
      Left diag -> printDiagnostic stderr True True 4 defaultStyle (addFile diag path $ Text.unpack content)
      Right (ast, diag) -> do
        printDiagnostic stderr True True 4 defaultStyle (addFile diag path $ Text.unpack content)

        putStrLn "\n✅ Following program passed typechecking:"
        putDoc (pretty ast)

    pure ()
