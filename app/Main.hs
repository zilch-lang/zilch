{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TupleSections #-}

module Main where

import Data.Bifunctor (second)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import Error.Diagnose (addFile, printDiagnostic, defaultStyle)
import Language.Zilch.Pretty.TAST ()
import Language.Zilch.Syntax.Desugarer (desugarCST)
import Language.Zilch.Syntax.Lexer (lexFile)
import Language.Zilch.Syntax.Parser (parseTokens)
import Language.Zilch.Typecheck.Elaborator (elabProgram)
import Prettyprinter (pretty)
import Prettyprinter.Render.Text (putDoc)
import System.IO

main :: IO ()
main = do
  stdin <- Text.getContents

  let ast = do
        (tks, warns) <- lexFile "stdin" stdin
        (!cst, warns) <- second (warns <>) <$> parseTokens "stdin" tks
        (!ast, warns) <- second (warns <>) <$> desugarCST cst
        (,warns) <$> elabProgram ast

  case ast of
    Left diag -> printDiagnostic stderr True True 4 defaultStyle (addFile diag "stdin" $ Text.unpack stdin)
    Right (ast, diag) -> do
      printDiagnostic stderr True True 4 defaultStyle (addFile diag "stdin" $ Text.unpack stdin)

      putStrLn "✅ Following program passed typechecking:"
      putDoc (pretty ast)

  pure ()
