module Language.Zilch.Syntax.Errors where

import qualified Text.Megaparsec as MP
data LexerError
  = InvalidEscapeSequence Char
  deriving (Eq, Ord)

instance Show LexerError where
  show (InvalidEscapeSequence c) = "invalid escape sequence '\\" <> [c] <> "'"

instance MP.ShowErrorComponent LexerError where
  showErrorComponent = show
