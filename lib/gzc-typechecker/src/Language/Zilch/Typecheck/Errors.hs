module Language.Zilch.Typecheck.Errors where

import Data.Located (Located ((:@)), Position)
import Data.Text (Text)
import qualified Data.Text as Text
import Error.Diagnose (Marker (This, Where), Report, err)
import Language.Zilch.Pretty.AST ()
import Language.Zilch.Syntax.Core.AST (Expression)
import Prettyprinter (group, pretty)

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
    [(pos, This $ "Binding named `" <> Text.unpack name <> "` not found in current environment")]
    []

-------------------

data ElabError
  = -- | Binding not found in environment
    BindingNotFound
      Text
      Position
  | -- | A function type was expected in an application
    PiTypeExpected
      (Located Expression)
      Position
  | -- | Types are not equal
    TypesAreNotEqual
      (Located Expression)
      (Located Expression)
      Position
  | -- | An error happened while evaluating
    FromEvalError
      EvalError

fromElabError :: ElabError -> Report String
fromElabError (BindingNotFound name pos) =
  err
    "Type-checking error"
    [(pos, This $ "Binding named `" <> Text.unpack name <> "` not found in current environment")]
    []
fromElabError (PiTypeExpected (ty :@ p1) pos) =
  let ty' = show (group $ pretty $ ty :@ p1)
   in err
        "Type-checking error"
        [ (pos, This $ "Types do not match: expected a function type, but got type `" <> ty' <> "`"),
          (p1, Where $ "Type `" <> ty' <> "` infered from here")
        ]
        []
fromElabError (TypesAreNotEqual (ty1 :@ p1) (ty2 :@ p2) pos) =
  let ty1' = show (group $ pretty $ ty1 :@ p1)
      ty2' = show (group $ pretty $ ty2 :@ p2)
   in err
        "Type-checking error"
        [ (pos, This $ "While checking this expression,\ntypes do not match: expected type `" <> ty1' <> "` but got type `" <> ty2' <> "`"),
          (p1, Where $ "Type `" <> ty1' <> "` infered from here"),
          (p2, Where $ "Type `" <> ty2' <> "` infered from here")
        ]
        []
fromElabError (FromEvalError e) = fromEvalError e
