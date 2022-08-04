{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}

module Language.Zilch.Syntax.Errors where

import Data.Located (Position)
import Data.Text (Text)
import qualified Data.Text as Text
import Error.Diagnose (Marker (This, Where), Note (Hint, Note), Report, err, warn)
import Error.Diagnose.Compat.Megaparsec
import Language.Zilch.Syntax.Core.AST (HoleLocation (..))
import qualified Text.Megaparsec as MP

data LexicalWarning

fromLexicalWarning :: LexicalWarning -> Report String
fromLexicalWarning _ = warn Nothing "sorry" [] []

data LexicalError
  deriving (Show, Eq, Ord)

instance MP.ShowErrorComponent LexicalError where
  showErrorComponent = show

instance HasHints LexicalError String where
  hints _ = []

----------------------------------------------

data ParsingWarning

fromParsingWarning :: ParsingWarning -> Report String
fromParsingWarning _ = warn Nothing "sorry" [] []

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

data DesugarWarning
  = SingletonAdditivePair
      Position

fromDesugarerError :: DesugarError -> Report String
fromDesugarerError (InvalidIntegerSuffix suffix pos) =
  err
    Nothing
    "Parse error"
    [(pos, This $ "Integral constant contains the suffix '" <> Text.unpack suffix <> "', which is invalid")]
    ["Numeric prefixes are only available for builtin integer and floating point types."]
fromDesugarerError (LinearTopLevelBinding name pos) =
  err
    Nothing
    "Parse error"
    [(pos, This $ "Top-level binding '" <> Text.unpack name <> "' cannot be made linear")]
    ["Top-level bindings may only be either erased (usage 0) or unrestricted (usage ω)."]
fromDesugarerError (PublicAssumptions pos) =
  err
    Nothing
    "Parse error"
    [(pos, This "Cannot bind assumptions publicly")]
    [Hint "Remove the 'public' modifier from this declaration."]
fromDesugarerError (TypelessAssumption name pos) =
  err
    Nothing
    "Parse error"
    [(pos, This $ "Assumption '" <> Text.unpack name <> "' is missing a type")]
    ["Every top-level assumption must have a type to be complete."]
fromDesugarerError (AssumptionsInMutualBlock pos) =
  err
    Nothing
    "Parse error"
    [(pos, This "Cannot bind assumptions inside a 'mutual' block")]
    []
fromDesugarerError (HoleInValType loc p1 p2) =
  err
    Nothing
    "Parse error"
    messages 
    []
  where
    messages = case loc of
      SourceHole -> [(p1, This "Found hole in a 'val' type binding"), (p2, Where "While checking this type declaration")]
      InsertedHole -> [(p1, This "Binding is missing an explicit type signature"), (p2, Where "While checking this type declaration")]
fromDesugarerError (ImplicitProductType p) =
  err
    Nothing
    "Parse error"
    [(p, This $ "Product dependent parameter cannot be made implicit")]
    []
fromDesugarerError (AdditiveProductWithMultiplicity x p) =
  err
    Nothing
    "Parse error"
    [(p, This $ "Binding named '" <> Text.unpack x <> "' cannot have a multiplicity attached")]
    [Note "The dependent parameter of an additive product cannot have a multiplicity."]
fromDesugarerError (NumberSuffixInAccess p) =
  err
    Nothing
    "Parse error"
    [(p, This "The accessor of an additive tuple cannot have a type suffix.")]
    []
fromDesugarerError (DuplicateBindingInMultiplicativeTuplesEliminator x p ps) =
  err
    Nothing
    "Parse error"
    ([(p, This $ "Binding '" <> Text.unpack x <> "' is present multiple times in this eliminator pattern")] <> poss)
    []
  where
    poss = (, Where "Found here") <$> ps

fromDesugarerWarning :: DesugarWarning -> Report String
fromDesugarerWarning (SingletonAdditivePair p) =
  warn
    Nothing
    "Parse warning"
    [(p, This "Additive dependent tuple only contains a single element")]
    [Note "This is equivalent to removing the tuple completely."]
fromDesugarerWarning _ = warn Nothing "sorry" [] []
