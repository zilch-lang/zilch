{-# LANGUAGE PackageImports #-}

import qualified Data.Text.IO as Text
import Error.Diagnose (defaultStyle, printDiagnostic, stdout)
import Located (unLoc)
import Syntax.Lexer (runLexer)
import Syntax.Tokens
import Text.Pretty.Simple (pPrint)

main :: IO ()
main = do
  input <- Text.getContents

  case runLexer "stdin" input of
    Left diag -> printDiagnostic stdout True True 4 defaultStyle diag
    Right (toks, warnings) -> do
      printDiagnostic stdout True True 4 defaultStyle warnings
      pPrint $ unLoc <$> toks
