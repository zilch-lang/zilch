{-# LANGUAGE NoOverloadedLists #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Typecheck.Errors where

import Data.Located (Located ((:@)), Position, getPos, unLoc)
import Data.Text (Text)
import qualified Data.Text as Text
import Error.Diagnose (Marker (This, Where), Note (..), Report (Err, Warn))
import Language.Zilch.Pretty.AST ()
import Language.Zilch.Pretty.TAST ()
import qualified Language.Zilch.Syntax.Core.AST as AST
import Language.Zilch.Typecheck.Core.AST (Expression)
import Language.Zilch.Typecheck.Core.Eval (Implicitness, explicit, implicit)
import Language.Zilch.Typecheck.Core.Multiplicity (Multiplicity (..))
import qualified Language.Zilch.Typecheck.IR as IR
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
    MultiplicityMismatch
      (Located Multiplicity)
      (Located Multiplicity)
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
  | -- | A multiplicity mismatch happened.
    UsageMismatches
      [(Multiplicity, Multiplicity, Located Text, Located Expression)]
      Position
  | ErasedInRelevantContext
      Position
  | -- | A relevant variable has been used in an erased context.
    RelevantVariableInIrrelevantContext
      Text
      Multiplicity
      Position
  | -- | Top-level identifier already bound.
    IdentifierAlreadyBound
      Text
      Position
      Position
  | -- | A recursive value binding.
    RecursiveValueBinding
      Text
      Position
  | -- | A hole could not solved.
    CannotSolveHole
      [(Text, Multiplicity, Located Expression)]
      Position
      AST.HoleLocation
  | -- | A value has a declared type using a @val@ binding but has no value associated.
    UndefinedValue
      Text
      Position
  | -- | A recursive value will call itself.
    BindingWillEndUpCallingItself
      Text
      Position
      Position
      [Located Text]
  | -- | Cannot infer type of term.
    CannotInferType
      Position
  | -- | Cannot access the N-th element inside a dependent additive tuple.
    CannotAccessNthElementOfAdditiveTuple
      Integer
      Position
  | -- | Cannot access N-th element of a non dependent additive tuple.
    CannotAccessNthElementOfNonAdditiveTuple
      Integer
      Position
  | -- | An additive product was expected at this position.
    ExpectedAdditiveProduct
      (Located Expression)
      Position
  | -- | A multiplicative product was expected at this position.
    ExpectedMultiplicativeProduct
      (Located Expression)
      Position
  | -- | A module was not found in the import cache.
    UnresolvedModule
      [Located Text]
      Position
  | -- | Trying to import a private namespace member.
    PrivateModuleImport
      (Located Text)
      Position
  | -- | An unresolved namespace is being imported.
    UnresolvedNamespace
      [Located Text]
      (Located Text)
      Position
  | -- | Expected either a module (from an @import@) or a record literal.
    ExpectedRecordOrModule
      (Located Expression)
      Position
  | -- | A record or module does not contain the given field.
    FieldNotFound
      (Located Text)
      Position
  | -- | There are some fields missing in the record literal.
    RecordMissingFields
      [Located Text]
      Position
  | -- | Record literal has fields which should not be here.
    RecordHasTooManyFields
      [Located Text]
      Position

data ElabWarning
  = -- | A recursive binding isn't used recursively.
    NonRecursiveRecursiveBinding
      Text
      Position
  | -- | Binding isn't used.
    UnusedBinding
      Text
      Position
  deriving (Eq)

fromElabWarning :: ElabWarning -> Report String
fromElabWarning (NonRecursiveRecursiveBinding x p) =
  Warn
    (Just "-Wrec-non-rec")
    "Non-recursive recursive binding."
    [(p, This $ "Identifier '" <> Text.unpack x <> "' is defined recursively but isn't used in its own definition.")]
    ["Consider transforming this 'rec' binding into a 'let' binding."]
fromElabWarning (UnusedBinding x p) =
  Warn
    (Just "-Wunused-binding")
    "Unused bound identifier."
    [(p, This $ "Binding '" <> Text.unpack x <> "' has not been used")]
    []

fromElabError :: ElabError -> Report String
fromElabError (BindingNotFound name pos) =
  Err
    Nothing
    "Unknown binding."
    [(pos, This $ "Binding named `" <> Text.unpack name <> "` not found in current environment")]
    []
fromElabError (PiTypeExpected (ty :@ p1) pos) =
  let ty' = show (group $ pretty $ ty :@ p1)
   in Err
        Nothing
        "Unification error."
        [ (pos, This $ "Types do not match: expected a function type, but got type `" <> ty' <> "`"),
          (p1, Where $ "Type `" <> ty' <> "` infered from here")
        ]
        []
fromElabError (TypesAreNotEqual (ty1 :@ p1) (ty2 :@ p2) pos) =
  let ty1' = show (group $ pretty $ ty1 :@ p1)
      ty2' = show (group $ pretty $ ty2 :@ p2)
   in Err
        Nothing
        "Unification error."
        [ (pos, This $ "While checking this expression,\ntypes do not match: expected type `" <> ty1' <> "` but got type `" <> ty2' <> "`"),
          (p1, Where $ "Type `" <> ty1' <> "` infered from here"),
          (p2, Where $ "Type `" <> ty2' <> "` infered from here")
        ]
        []
fromElabError UnificationError = undefined
fromElabError (CannotUnify (t1 :@ p1) (t2 :@ p2)) =
  Err
    Nothing
    "Unification error."
    [ (p1, This $ "Cannot unify term `" <> show (pretty $ t1 :@ p1) <> "`..."),
      (p2, This $ "...with term `" <> show (pretty $ t2 :@ p2) <> "`")
    ]
    []
fromElabError (MultiplicityMismatch u1@(_ :@ p1) u2@(_ :@ p2)) =
  Err
    Nothing
    "Multiplicity mismatch."
    [ (p1, This $ "Expected value with usage " <> show (pretty u1) <> "..."),
      (p2, This $ "...but got value with usage " <> show (pretty u2))
    ]
    []
fromElabError (UnusedLinearVariable (x :@ p) p2) =
  Err
    Nothing
    "Unused linear binding."
    [ (p, This $ "Variable named `" <> Text.unpack x <> "` was marked linear but has not been used"),
      (p2, Where $ "It should have been used in this expression")
    ]
    ["If the variable is intended not to be used, it must have an unrestricted usage."]
fromElabError (ImplicitMismatch expected got pos) =
  Err
    Nothing
    "Argument implicitness mismatch."
    [(pos, This $ "Function application was expected on an " <> showImp expected <> " argument, but an " <> showImp got <> " argument was found")]
    []
  where
    showImp b
      | b == implicit = "implicit"
      | b == explicit = "explicit"
      | otherwise = undefined
fromElabError (NonLinearUseOfVariable x pos) =
  Err
    Nothing
    "Non-linear use of linear binding."
    [(pos, This $ "Variable " <> Text.unpack x <> " has been used non linearly")]
    []
fromElabError (UsageMismatches matches pos) =
  Err
    Nothing
    "Usage mismatch."
    messages
    []
  where
    messages =
      [(getPos x, This $ "Variable " <> Text.unpack (unLoc x) <> " of type " <> show (pretty ty) <> " was expected to be used " <> showMult q <> " times\nbut has been used " <> showMult p <> " times") | (p, q, x, ty) <- matches]
        <> [(pos, Where $ "...while type-checking this expression")]
fromElabError (ErasedInRelevantContext pos) =
  Err
    Nothing
    "Relevant use in irrelevant context."
    [(pos, This $ "This term was meant to be used in an irrelevant position\nbut was found in a relevant context")]
    []
fromElabError (RelevantVariableInIrrelevantContext x m p) =
  Err
    Nothing
    "Relevant use in irrelevant context."
    [(p, This $ "Cannot use relevant variable " <> Text.unpack x <> " (usage " <> showMult m <> ") inside\nan irrelevant context.")]
    []
fromElabError (IdentifierAlreadyBound x p1 p2) =
  Err
    Nothing
    "Top-level function shadowing."
    [ (p1, This $ "Identifier '" <> Text.unpack x <> "' is already bound at the top-level"),
      (p2, Where "While trying to type-check this definition")
    ]
    []
fromElabError (RecursiveValueBinding x p) =
  Err
    Nothing
    "Recursive value binding."
    [(p, This $ "Identifier '" <> Text.unpack x <> "' is recursively bound to a value which is not a function")]
    [Hint "Potential fixes include transforming this binding into a function"]
fromElabError (CannotSolveHole env p loc) =
  Err
    Nothing
    "Cannot infer hole."
    [(p, This msg)]
    (if null env then [] else [Note $ "Local bindings include:\n" <> genEnv env])
  where
    msg = case loc of
      AST.InsertedHole -> "Cannot infer the type of this term"
      AST.SourceHole -> "Cannot infer any term to replace this hole"

    genEnv [] = ""
    genEnv [(x, mult, expr)] = "• " <> showMult mult <> " " <> Text.unpack x <> " : " <> show (pretty expr)
    genEnv (e : env) = genEnv [e] <> "\n" <> genEnv env
fromElabError (UndefinedValue x p) =
  Err
    Nothing
    "Forward declaration without binding."
    [(p, This $ "Binding '" <> Text.unpack x <> "' has a type declared but has no value associated with it.")]
    []
fromElabError (BindingWillEndUpCallingItself x p p1 stack) =
  Err
    Nothing
    "Mutually recursive values."
    messages
    []
  where
    messages =
      [(p, This $ "Binding '" <> Text.unpack x <> "' will end up evaluating itself when evaluating its value")]
        <> [(p, Where $ "After evaluating binding '" <> Text.unpack x <> "'...") | x :@ p <- stack]
        <> [(p1, Where $ "'" <> Text.unpack x <> "' ends up being evaluated here")]
fromElabError (CannotInferType p) =
  Err
    Nothing
    "Cannot infer hole."
    [(p, This "Cannot infer the type of this term")]
    []
fromElabError (CannotAccessNthElementOfAdditiveTuple n p) =
  Err
    Nothing
    "Additive product access out of bounds."
    [(p, This $ "Cannot access the " <> show n <> ordinal n <> " element of the given additive tuple")]
    []
fromElabError (CannotAccessNthElementOfNonAdditiveTuple n p) =
  Err
    Nothing
    "Additive product access on non-additive product."
    [(p, This $ "Cannot access the " <> show n <> ordinal n <> " element of a non-additive dependent tuple")]
    []
fromElabError (ExpectedAdditiveProduct ty p) =
  Err
    Nothing
    "Unification error."
    [(p, This $ "An additive dependent pair (&-type) was expected here\nbut a term of type '" <> show (pretty ty) <> "' was found")]
    []
fromElabError (ExpectedMultiplicativeProduct ty p) =
  Err
    Nothing
    "Unification error"
    [(p, This $ "A multiplicative dependent pair (⊗-type) was expected here\nbut a term of type '" <> show (pretty ty) <> "' was found")]
    []
fromElabError (UnresolvedModule mod p) =
  Err
    Nothing
    "Cannot find module."
    [(p, This $ "Cannot resolve module '" <> show' mod <> "' inside this import")]
    []
  where
    show' = Text.unpack . Text.intercalate "∷" . fmap unLoc
fromElabError (ExpectedRecordOrModule _ p) =
  Err
    Nothing
    "Expected a module or a record."
    [(p, This $ "Expected either a module or a record here")]
    []
fromElabError (FieldNotFound x p) =
  Err
    Nothing
    ("Unknown member '" <> Text.unpack (unLoc x) <> "'.")
    [(p, This $ "Is a record or a module which does not contain a binding for '" <> Text.unpack (unLoc x) <> "'")]
    []
fromElabError (PrivateModuleImport x p) =
  Err
    Nothing
    ("Private member import.")
    [(p, This $ "Trying to import the private member '" <> Text.unpack (unLoc x) <> "'")]
    []
fromElabError (UnresolvedNamespace mod x p) =
  Err
    Nothing
    ("Unresolved namespace.")
    [(p, This $ "Trying to import the unresolved namespace '" <> Text.unpack (Text.intercalate "∷" $ unLoc <$> (mod <> [x])) <> "'.")]
    []

data MonomorphiserError
  = AmbiguousMainOccurrence [[Located Text]]
  | NoMainFunction
  | MaximumMonomorphisationDepthReached (Located IR.Expression)

fromMonomorphiserError :: MonomorphiserError -> Report String
fromMonomorphiserError (AmbiguousMainOccurrence mains) =
  Err
    Nothing
    "Ambiguous reference to function named 'main'."
    [(getPos (last x), Where "This is a candidate") | x <- mains]
    ["There can only be a single candidate for the entry point of a program."]
fromMonomorphiserError NoMainFunction =
  Err
    Nothing
    "No 'main' function found in any module."
    []
    ["A 'main' function is required to be the entry point of the program.\nIf this is intentional, pass '--no-main' in the command-line."]

-----------------------------------

ordinal :: Integral a => a -> String
ordinal number
  | remainder100 `elem` [11 .. 13] = "th"
  | remainder10 == 1 = "st"
  | remainder10 == 2 = "nd"
  | remainder10 == 3 = "rd"
  | otherwise = "th"
  where
    abs_number = abs number
    remainder10 = abs_number `mod` 10
    remainder100 = abs_number `mod` 100

showMult :: Multiplicity -> String
showMult O = "0"
showMult I = "1"
showMult W = "ω"
showMult A = "_"
