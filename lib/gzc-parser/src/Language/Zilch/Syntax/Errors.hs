module Language.Zilch.Syntax.Errors where

import qualified Text.Megaparsec as MP
import Language.Zilch.Syntax.Internal (Hintable(..))

data LexerError
  = InvalidEscapeSequence Char
  deriving (Eq, Ord)

instance Show LexerError where
  show (InvalidEscapeSequence c) = "invalid escape sequence '\\" <> [c] <> "'"

instance MP.ShowErrorComponent LexerError where
  showErrorComponent = show

instance Hintable LexerError where
  hints _ = []
