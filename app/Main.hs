module Main where

import qualified Data.Text.IO as Text
import Error.Diagnose (printDiagnostic)
import Language.Zilch.Parser.Lexer
import System.IO

main :: IO ()
main = do
  stdin <- Text.getContents

  let tokens = lexFile "stdin" stdin
  case tokens of
    Left diag -> printDiagnostic stderr True True diag
    Right (tks, diag) -> do
      printDiagnostic stderr True True diag
      print tks

  pure ()
