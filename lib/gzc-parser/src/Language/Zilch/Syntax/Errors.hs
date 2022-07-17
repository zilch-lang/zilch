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
  = InvalidIntegerSuffix
      Text
      Position
  | LinearTopLevelBinding
      Text
      Position

data DesugarWarning

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
fromDesugarerError _ = err Nothing "sorry" [] []

fromDesugarerWarning :: DesugarWarning -> Report String
fromDesugarerWarning _ = warn Nothing "sorry" [] []
