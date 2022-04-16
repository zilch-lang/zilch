{-# LANGUAGE TupleSections #-}

module Main where

import qualified Data.Text.IO as Text
import Error.Diagnose (printDiagnostic)
import Language.Zilch.Parser.Lexer (lexFile)
import Language.Zilch.Parser.Parser (parseTokens)
import System.IO

main :: IO ()
main = do
  stdin <- Text.getContents

  let cst =
        lexFile "stdin" stdin
          >>= \(tks, warns) -> (,warns) <$> parseTokens "stdin" tks
  case cst of
    Left diag -> printDiagnostic stderr True True diag
    Right ((cst, diag2), diag1) -> do
      printDiagnostic stderr True True diag1
      printDiagnostic stderr True True diag2
      print cst

  pure ()
