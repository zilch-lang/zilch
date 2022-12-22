{-# LANGUAGE PackageImports #-}

import "gzc-lib" Data.Located (unLoc)
import Error.Diagnose (printDiagnostic, stdout, defaultStyle)
import Syntax.Tokens
import Syntax.Lexer (runLexer)
import qualified Data.Text.IO as Text
import Text.Pretty.Simple (pPrint)

main :: IO ()
main = do
  input <- Text.getContents

  case runLexer "stdin" input of
    Left diag -> printDiagnostic stdout True True 4 defaultStyle diag
    Right (toks, warnings) -> do
      printDiagnostic stdout True True 4 defaultStyle warnings
      pPrint $ unLoc <$> toks
