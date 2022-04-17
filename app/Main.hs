{-# LANGUAGE TupleSections #-}

module Main where

import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import Error.Diagnose (addFile, printDiagnostic)
import Language.Zilch.Syntax.Lexer (lexFile)
import Language.Zilch.Syntax.Parser (parseTokens)
import System.IO

main :: IO ()
main = do
  stdin <- Text.getContents

  let cst =
        lexFile "stdin" stdin
          >>= \(tks, warns) -> (,warns) <$> parseTokens "stdin" tks
  case cst of
    Left diag -> printDiagnostic stderr True True (addFile diag "stdin" $ Text.unpack stdin)
    Right ((cst, diag2), diag1) -> do
      printDiagnostic stderr True True (addFile diag1 "stdin" $ Text.unpack stdin)
      printDiagnostic stderr True True (addFile diag2 "stdin" $ Text.unpack stdin)
      print cst

  pure ()
