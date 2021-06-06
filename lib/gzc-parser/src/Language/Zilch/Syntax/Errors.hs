module Language.Zilch.Syntax.Errors where

import qualified Text.Megaparsec as MP
import Language.Zilch.Syntax.Internal (Hintable(..))
import Text.Diagnose (hint, Diagnostic, Position)
import Data.Text (Text)

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

data ResolverError
  = Lexing (Diagnostic [] String Char)             -- ^ A lexing error happened
  | Parsing (Diagnostic [] String Char)            -- ^ A parsing error happened
  | CyclicImports [(Text, Text)] Position          -- ^ @A@ includes @B@, which ends up including @A@
  | FileNotFoundInIncludePath FilePath Position    -- ^ A filename was not found in the include path
  | MultipleFilesFound Text [FilePath] Position    -- ^ Multiple files with the same name were found in the include path
