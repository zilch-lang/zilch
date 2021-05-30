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
  = MissingEnumVariantParameterList
  | HashWithSpaceInMetaAttributes
  | UnsupportedEmptyEnums
  deriving (Eq, Ord)

instance Show ParseError where
  show MissingEnumVariantParameterList = "missing parameter list for enumeration constructor"
  show HashWithSpaceInMetaAttributes   = "there should not be any space between the two '#' and '[' tokens"
  show UnsupportedEmptyEnums           = "enumerations with no constructors are not supported"

instance MP.ShowErrorComponent ParseError where
  showErrorComponent = show

instance Hintable ParseError where
  hints MissingEnumVariantParameterList = [hint "You can specify an empty parameter list '()' if your constructor does not take parameters."]
  hints HashWithSpaceInMetaAttributes   = []
  hints UnsupportedEmptyEnums           = []
