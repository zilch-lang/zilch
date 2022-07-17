module Language.Zilch.Typecheck.Errors where

import Data.Located (Located ((:@)), Position)
import Data.Text (Text)
import qualified Data.Text as Text
import Error.Diagnose (Marker (This, Where), Report, err)
import Language.Zilch.Pretty.AST ()
import Language.Zilch.Pretty.TAST ()
import Language.Zilch.Typecheck.Core.AST (Expression)
import Language.Zilch.Typecheck.Core.Eval (Implicitness, explicit, implicit)
import Language.Zilch.Typecheck.Core.Usage (Usage (..))
import Prettyprinter (group, pretty)

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
  | -- | An error occured in the unification process.
    --
    --   /Note:/ This is only a placeholder replaced when actually calling the unification
    UnificationError
  | -- | Cannot unify two terms together
    CannotUnify
      (Located Expression)
      (Located Expression)
  | -- | Actual usage cannot be used in place of expected usage
    UsageMismatch
      (Located Usage)
      (Located Usage)
  | -- | A linear variable has not been used
    UnusedLinearVariable
      (Located Text)
      Position
  | -- | Implicit function applied to explicit argument (or the other way around)
    ImplicitMismatch
      Implicitness
      Implicitness
      Position
  | -- | A variable has been used non-linearly
    NonLinearUseOfVariable
      Text
      Position

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
fromElabError UnificationError = undefined
fromElabError (CannotUnify (t1 :@ p1) (t2 :@ p2)) =
  err
    "Type-checking error"
    [ (p1, This $ "Cannot unify term `" <> show (pretty $ t1 :@ p1) <> "`..."),
      (p2, This $ "...with term `" <> show (pretty $ t2 :@ p2) <> "`")
    ]
    []
fromElabError (UsageMismatch u1@(_ :@ p1) u2@(_ :@ p2)) =
  err
    "Type-checking error"
    [ (p1, This $ "Expected value with usage " <> show (pretty u1) <> "..."),
      (p2, This $ "...but got value with usage " <> show (pretty u2))
    ]
    []
fromElabError (UnusedLinearVariable (x :@ p) p2) =
  err
    "Type-checking error"
    [ (p, This $ "Variable named `" <> Text.unpack x <> "` was marked linear but has not been used"),
      (p2, Where $ "It should have been used in this expression")
    ]
    ["If the variable is intended not to be used, it must have an unrestricted usage."]
fromElabError (ImplicitMismatch expected got pos) =
  err
    "Type-checking error"
    [(pos, This $ "Function application was expected on an " <> showImp expected <> " argument, but an " <> showImp got <> " argument was found")]
    []
  where
    showImp b
      | b == implicit = "implicit"
      | b == explicit = "explicit"
      | otherwise = undefined
fromElabError (NonLinearUseOfVariable x pos) =
  err
    "Type-checking error"
    [(pos, This $ "Variable " <> Text.unpack x <> " has been used non linearly")]
    []
