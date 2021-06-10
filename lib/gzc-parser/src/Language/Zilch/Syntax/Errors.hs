{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Syntax.Errors where

import qualified Text.Megaparsec as MP
import Language.Zilch.Syntax.Internal (Hintable(..))
import Text.Diagnose (hint, Diagnostic, Position, diagnostic, (<++>), reportError, Marker(..), Report)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Vector as V
import Data.Vector (Vector)
import Data.List (intercalate)
import Data.Functor ((<&>))

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

fromResolverError :: (?includePath :: Vector Text) => ResolverError -> Diagnostic [] String Char
fromResolverError (Lexing d)                      = d
fromResolverError (Parsing d)                     = d
fromResolverError (CyclicImports ids p)           =
  diagnostic <++> reportError "Cyclic imports detected"
                              [(p, Where showCycle)]
                              []
  where
    showCycle = "From top to bottom:\n- " <> intercalate "\n- " (ids <&> \ (f, i) -> "'" <> Text.unpack f <> "' is included by '" <> Text.unpack i <> "'")
fromResolverError (FileNotFoundInIncludePath f p) =
  diagnostic <++> reportError ("File '" <> f <> "' not found in the include path")
                              [(p, Where . showIncludePath $ V.toList ?includePath)]
                              []
  where
    showIncludePath [] = ""
    showIncludePath l  = "Current include path:\n- " <> intercalate "\n- " (Text.unpack <$> l)
fromResolverError (MultipleFilesFound m fs p)     =
  diagnostic <++> reportError ("Multiple files were found to match the import of '" <> Text.unpack m <> "'")
                              [(p, Where showFiles)]
                              []
  where
    showFiles = "These files match the import:\n- " <> intercalate "\n- " fs

data ScopeCheckError
  = UnboundExportedFunction Text Position
  | MultipleDefinitionsForExportedFunction Text Position [Position]
  | ModuleDoesNotExportFunction Text Position
  | AmbiguousFunctionUsage Text Position [(Text, Position)]

fromScopeCheckError :: ScopeCheckError -> Report String
fromScopeCheckError (UnboundExportedFunction f p) =
  reportError ("Cannot export function '" <> Text.unpack f <> "' because it is not bound in this module")
    [(p, This "")]
    []
fromScopeCheckError (MultipleDefinitionsForExportedFunction f p ps) =
  reportError ("Trying to export function '" <> Text.unpack f <> "' but it has been defined multiple times")
    ((p, This "") : generateDefinitionSites 0 ps)
    []
  where
    generateDefinitionSites :: Int -> [Position] -> [(Position, Marker String)]
    generateDefinitionSites _ []     = []
    generateDefinitionSites i (p:ps) = (p, Where $ "Definition #" <> show i) : generateDefinitionSites (i + 1) ps
fromScopeCheckError (ModuleDoesNotExportFunction f p) =
  reportError ("Module does not export function '" <> Text.unpack f <> "'")
    [(p, This "")]
    []
fromScopeCheckError (AmbiguousFunctionUsage f p is) =
  reportError ("Ambiguous occurrence of function '" <> Text.unpack f <> "'")
    ((p, This "here") : generateAmbiguousImports)
    [hint "You may resolve this issue by restricting what functions are imported using explicit import lists."
    ,hint "Alternatively, you may also import modules qualified or using 'as'-aliases."]
  where
    generateAmbiguousImports = is <&> \ (i, p) -> (p, Where $ "Importing the module '" <> Text.unpack i <> "' exposes a function named '" <> Text.unpack f <> "'")
