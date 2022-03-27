{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Language.Zilch.Parser.Errors where

import Error.Diagnose (Report, warn)
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
