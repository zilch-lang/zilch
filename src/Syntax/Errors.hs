{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Syntax.Errors where

import Error.Diagnose (Report (..))
import Error.Diagnose.Compat.Megaparsec (HasHints (..))
import Syntax.Tokens (Token, showToken)
import qualified Text.Megaparsec as MP

data LexicalWarning

fromLexicalWarning :: LexicalWarning -> Report String
fromLexicalWarning _ = Warn Nothing "sorry" [] []

data LexicalError
  = UnexpectedKeywordAsNumberSuffix Token
  deriving (Show, Eq, Ord)

instance MP.ShowErrorComponent LexicalError where
  showErrorComponent = fromLexicalError

instance HasHints LexicalError String where
  hints _ = []

fromLexicalError :: LexicalError -> String
fromLexicalError (UnexpectedKeywordAsNumberSuffix tk) =
  "Cannot make use of keyword " <> showToken tk <> " as the suffix of a number literal."

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
