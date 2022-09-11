{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Syntax.Errors where

import Data.Functor ((<&>))
import Data.Located (Located, Position, getPos, spanOf, unLoc)
import Data.Text (Text)
import qualified Data.Text as Text
import Debug.Trace (traceId, traceShow, traceShowId)
import Error.Diagnose (Diagnostic, Marker (This, Where), Note (Hint, Note), Report (Err, Warn))
import Error.Diagnose.Compat.Megaparsec
import Language.Zilch.Syntax.Core.AST (HoleLocation (..))
import qualified Text.Megaparsec as MP

data LexicalWarning

fromLexicalWarning :: LexicalWarning -> Report String
fromLexicalWarning _ = Warn Nothing "sorry" [] []

data LexicalError
  deriving (Show, Eq, Ord)

instance MP.ShowErrorComponent LexicalError where
  showErrorComponent = show

instance HasHints LexicalError String where
  hints _ = []

----------------------------------------------

data ParsingWarning

fromParsingWarning :: ParsingWarning -> Report String
fromParsingWarning _ = Warn Nothing "sorry" [] []

data ParsingError
  deriving (Show, Eq, Ord)

instance MP.ShowErrorComponent ParsingError where
  showErrorComponent = show

instance HasHints ParsingError String where
  hints _ = []

-------------------------------------------------

data DesugarError
  = -- | An integer literal has an unidentified suffix.
    InvalidIntegerSuffix
      Text
      Position
  | -- | A top-level binding is bound with a 1 multiplicity.
    LinearTopLevelBinding
      Text
      Position
  | -- | Assumptions bound publicly.
    PublicAssumptions
      Position
  | -- | An assumption has at least one hole inside its type.
    TypelessAssumption
      Text
      Position
  | -- | Cannot bind assumptions inside @mutual@ blocks.
    AssumptionsInMutualBlock
      Position
  | -- | There is at least one hole inside a @val@.
    HoleInValType
      HoleLocation
      Position
      Position
  | -- | The dependent parameter of the product cannot be implicit.
    ImplicitProductType
      Position
  | -- | An additive product has a multiplicity attached on its dependent argument.
    AdditiveProductWithMultiplicity
      Text
      Position
  | -- | Access number for additive pair has a suffix.
    NumberSuffixInAccess
      Position
  | -- | There are multiple of the same binding in the same eliminator.
    DuplicateBindingInMultiplicativeTuplesEliminator
      Text
      Position
      [Position]
  | -- | Multiplicative tuple eliminator with a single element.
    SingletonMultiplicativeTupleElim
      Position
  | -- | An access syntax is used with neither a number nor an identifier.
    UnsupportedAccessKind
      Position
  | -- | A by-ref operator has not been used where it was meant to be.
    InvalidUseOfByRef
      Text
      Position
  | -- | Assumptions bound with meta attributes.
    AssumptionWithMetaAttributes
      Position
  | -- | @val@ binding has an @inline@ attribute.
    InlineAttributeOnVal
      Position
      Position
  | -- | @import@ is only allowed on @val@s.
    ImportAttributeOnlyAllowedOnVal
      Position
      Position

data DesugarWarning
  = SingletonAdditivePair
      Position

fromDesugarerError :: DesugarError -> Report String
fromDesugarerError (InvalidIntegerSuffix suffix pos) =
  Err
    Nothing
    "Invalid integer suffix in integer literal."
    [(pos, This $ "Integral constant contains the suffix '" <> Text.unpack suffix <> "', which is invalid")]
    ["Numeric prefixes are only available for builtin integer and floating point types."]
fromDesugarerError (LinearTopLevelBinding name pos) =
  Err
    Nothing
    "Linear top-level 'let' or 'rec' binding."
    [(pos, This $ "Top-level binding '" <> Text.unpack name <> "' cannot be made linear")]
    ["Top-level bindings may only be either erased (usage 0) or unrestricted (usage ω)."]
fromDesugarerError (PublicAssumptions pos) =
  Err
    Nothing
    "Public assumptions in module."
    [(pos, This "Cannot bind assumptions publicly")]
    [Hint "Remove the 'public' modifier from this declaration."]
fromDesugarerError (TypelessAssumption name pos) =
  Err
    Nothing
    "Type of assumption is not fully known."
    [(pos, This $ "Assumption '" <> Text.unpack name <> "' is missing a type")]
    ["Every top-level assumption must have a type to be complete."]
fromDesugarerError (AssumptionsInMutualBlock pos) =
  Err
    Nothing
    "Assumptions bound within mutually recursive definitions."
    [(pos, This "Cannot bind assumptions inside a 'mutual' block")]
    []
fromDesugarerError (HoleInValType loc p1 p2) =
  Err
    Nothing
    "Hole found within a 'val' type binding."
    messages
    []
  where
    messages = case loc of
      SourceHole -> [(p1, This "Found hole in a 'val' type binding"), (p2, Where "While checking this type declaration")]
      InsertedHole -> [(p1, This "Binding is missing an explicit type signature"), (p2, Where "While checking this type declaration")]
fromDesugarerError (ImplicitProductType p) =
  Err
    Nothing
    "Implicit dependent product parameter."
    [(p, This $ "Product dependent parameter cannot be made implicit")]
    []
fromDesugarerError (AdditiveProductWithMultiplicity x p) =
  Err
    Nothing
    "Restricted bindings not allowed here."
    [(p, This $ "Binding named '" <> Text.unpack x <> "' cannot have a multiplicity attached")]
    [Note "The dependent parameter of an additive product cannot have a multiplicity."]
fromDesugarerError (NumberSuffixInAccess p) =
  Err
    Nothing
    "Additive product access with integer literal type suffix."
    [(p, This "The accessor of an additive tuple cannot have a type suffix.")]
    []
fromDesugarerError (DuplicateBindingInMultiplicativeTuplesEliminator x p ps) =
  Err
    Nothing
    "Non-linear eliminator pattern."
    ([(p, This $ "Binding '" <> Text.unpack x <> "' is present multiple times in this eliminator pattern")] <> poss)
    []
  where
    poss = (,Where "Found here") <$> ps
fromDesugarerError (SingletonMultiplicativeTupleElim p) =
  Err
    Nothing
    "Multiplicative singleton eliminator pattern"
    [(p, This "Invalid singleton pattern in eliminator")]
    []
fromDesugarerError (UnsupportedAccessKind p) =
  Err
    Nothing
    "Unsupported field access."
    [(p, This "Cannot access an element whose index is neither a number nor an identifier")]
    []
fromDesugarerError (InvalidUseOfByRef _ p) =
  Err
    Nothing
    "Invalid by-ref operator usage."
    [(p, This "By-ref operator (&) used in a context where it was unexpected")]
    []
fromDesugarerError (AssumptionWithMetaAttributes p) =
  Err
    Nothing
    "Cannot put meta attributes on 'assume' construct."
    [(p, This "Found some meta attributes while binding these assumptions")]
    []
fromDesugarerError (InlineAttributeOnVal p p1) =
  Err
    Nothing
    "Cannot make 'val' bindings inlineable."
    [ (p, This "This binding has an 'inline' meta attribute attached to it"),
      (p1, Where "While checking that this attribute should not be here")
    ]
    []
fromDesugarerError (ImportAttributeOnlyAllowedOnVal p p1) =
  Err
    Nothing
    "'import' meta attribute is only allowed on 'val' bindings."
    [ (p, This "This binding is not a 'val' binding"),
      (p1, Where "While checking that this attribute should not be here")
    ]
    []

fromDesugarerWarning :: DesugarWarning -> Report String
fromDesugarerWarning (SingletonAdditivePair p) =
  Warn
    (Just "-Wadditive-singleton")
    "Singleton additive product."
    [(p, This "Additive dependent tuple only contains a single element")]
    [Note "This is equivalent to removing the tuple completely."]

------------------------------------

data DriverError
  = LexingE (Diagnostic String)
  | ParsingE (Diagnostic String)
  | DesugaringE (Diagnostic String)
  | InvalidModuleName Text Int
  | EmptyModuleName Text
  | CyclicImports [[Located Text]]
  | AmbiguousModuleName [Located Text] [FilePath]
  | ModuleNotFound [Located Text] [FilePath]
  | UnresolvedImport [Located Text] [FilePath]
  | CannotImportPrivateMember (Located Text) [Located Text]
  | CyclicModuleImports [([Located Text], FilePath)]

data DriverWarning

fromDriverError :: DriverError -> Report String
fromDriverError (InvalidModuleName mod idx) =
  Err
    Nothing
    ("Invalid character '" <> (Text.index mod idx : "") <> "' found at index " <> show idx <> " in name '" <> Text.unpack mod <> "'.")
    []
    []
fromDriverError (EmptyModuleName mod) =
  Err
    Nothing
    ("Module '" <> Text.unpack mod <> "' contains an empty path.")
    []
    []
fromDriverError (AmbiguousModuleName mod dirs) =
  Err
    Nothing
    ("Namespace '" <> show' mod <> "' found in multiple include directories.")
    []
    [Note $ "The following files were found in the include directories:\n" <> unlines (mappend "- " <$> dirs)]
  where
    show' = Text.unpack . Text.intercalate "∷" . fmap unLoc
fromDriverError (ModuleNotFound mod dirs) =
  Err
    Nothing
    ("Namespace '" <> show' mod <> "' not found in include path.")
    []
    [Note $ "None of the following directories contain this namespace:\n" <> unlines (mappend "- " <$> dirs)]
  where
    show' = Text.unpack . Text.intercalate "∷" . fmap unLoc
fromDriverError (UnresolvedImport mod dirs) =
  Err
    Nothing
    ("Namespace '" <> show' mod <> "' not found in include path.")
    [(p, This "While checking that this namespace exists")]
    [Note $ "None of the following directories contain this namespace:\n" <> unlines (mappend "- " <$> dirs)]
  where
    show' = Text.unpack . Text.intercalate "∷" . fmap unLoc

    p = foldr1 spanOf (getPos <$> mod)
fromDriverError (CannotImportPrivateMember id mod) =
  Err
    Nothing
    ("'" <> Text.unpack (unLoc id) <> "' is private within the module '" <> show' mod <> "'.")
    [(getPos id, This "While checking that this namespace exists")]
    []
  where
    show' = Text.unpack . Text.intercalate "∷" . fmap unLoc
fromDriverError (CyclicModuleImports mods) =
  Err
    Nothing
    ("Module ended up importing itself.")
    messages
    []
  where
    messages = mods <&> \(mod, _) -> (foldr1 spanOf (getPos <$> mod), Where $ "'" <> show' mod <> "' is included here")

    show' = Text.unpack . Text.intercalate "∷" . fmap unLoc
fromDriverError _ = undefined

fromDriverWarning :: DriverWarning -> Report String
fromDriverWarning _ = undefined
