module Language.Zilch.Typecheck.Errors where

import Data.Located (Position)
import Data.Text (Text)
import qualified Data.Text as Text
import Error.Diagnose (Report, err)
import Error.Diagnose.Report (Marker (This))

data EvalError
  = -- | A @rec@ binding is being normalized
    RecursiveBindingNormalisation
      Position
  | -- | Identifier not found in current context
    NoSuchBinding
      Text
      Position

fromEvalError :: EvalError -> Report String
fromEvalError (RecursiveBindingNormalisation pos) =
  err
    "Normalisation error"
    [(pos, This "Trying to normalise a recursive binding may lead to non-termination")]
    []
fromEvalError (NoSuchBinding name pos) =
  err
    "Normalisation error"
    [(pos, This $ "Binding named " <> Text.unpack name <> " not found in current environment")]
    []
