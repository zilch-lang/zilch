{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Language.Zilch.Syntax.Errors where

import Data.Located (Located ((:@)), Position)
import Data.Text (Text)
import qualified Data.Text as Text
import Error.Diagnose (Marker (This, Where), Report, err, warn)
import Error.Diagnose.Compat.Megaparsec
import qualified Text.Megaparsec as MP

data LexicalWarning

fromLexicalWarning :: LexicalWarning -> Report String
fromLexicalWarning _ = warn "sorry" [] []

data LexicalError
  deriving (Show, Eq, Ord)

instance MP.ShowErrorComponent LexicalError where
  showErrorComponent = show

instance HasHints LexicalError String where
  hints _ = []

----------------------------------------------

data ParsingWarning

fromParsingWarning :: ParsingWarning -> Report String
fromParsingWarning _ = warn "sorry" [] []

data ParsingError
  deriving (Show, Eq, Ord)

instance MP.ShowErrorComponent ParsingError where
  showErrorComponent = show

instance HasHints ParsingError String where
  hints _ = []

-------------------------------------------------

data DesugarError
  = -- | An implicit argument has been found right after explicit ones
    ImplicitAfterExplicit
      (Located Text)
      Position

data DesugarWarning

fromDesugarerError :: DesugarError -> Report String
fromDesugarerError (ImplicitAfterExplicit (name :@ pos1) pos2) =
  err
    "Parse error on input"
    [ (pos1, This $ "Parameter `" <> Text.unpack name <> "` found at incorrect position"),
      (pos2, Where "This parameter is implicit and was found after an explicit one")
    ]
    ["Implicit arguments can only be found *before* any explicit argument."]

fromDesugarerWarning :: DesugarWarning -> Report String
fromDesugarerWarning _ = warn "sorry" [] []
