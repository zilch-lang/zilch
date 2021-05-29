module Language.Zilch.Syntax.Errors where

import qualified Text.Megaparsec as MP
import Language.Zilch.Syntax.Internal (Hintable(..))
import Text.Diagnose (hint)

data LexerError
  = InvalidEscapeSequence Char
  deriving (Eq, Ord)

instance Show LexerError where
  show (InvalidEscapeSequence c) = "invalid escape sequence '\\" <> [c] <> "'"

instance MP.ShowErrorComponent LexerError where
  showErrorComponent = show

instance Hintable LexerError where
  hints _ = []

data ParseError
  = MissingEnumVariantParameter
  deriving (Eq, Ord)

instance Show ParseError where
  show MissingEnumVariantParameter = "missing parameter list for enumeration constructor"

instance MP.ShowErrorComponent ParseError where
  showErrorComponent = show

instance Hintable ParseError where
  hints MissingEnumVariantParameter = [hint "You can specify an empty parameter list '()' if your constructor does not take parameters."]
