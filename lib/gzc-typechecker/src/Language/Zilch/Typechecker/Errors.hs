module Language.Zilch.Typechecker.Errors where

import Data.Located (Located, Position)
import Data.Text (Text)
import qualified Language.Zilch.Syntax.Core.AST as AST
import Language.Zilch.Typecheck.Core.AST (Expression)
import Language.Zilch.Typecheck.Core.Eval (Value)
import Language.Zilch.Typecheck.Core.Multiplicity (Multiplicity)

data InternalElabError
  = UnboundMetaVariable Integer
  | InvalidApplication (Located Value) (Located Value)
  | InconsistentPathWithEnv Integer Integer
  | QuotingUndefined
  | NonVariableMetavariableArgument Value Position
  | CannotRenameThisTerm (Located Value)
  | NoSuchMetaVariable Integer
  | CannotConstructMetaLambdasFromTerm (Located Value)

data ElabError
  = InternalError InternalElabError
  | UnboundVariableIndex (Located Text) Integer Position
  | IdentifierAlreadyBound Text Position Position
  | MultiplicityMismatch (Located Multiplicity) (Located Multiplicity)
  | ResourceUsageInIrrelevantContext Position [(Text, Multiplicity)]
  | IrrelevantTermOutsideIrrelevantContext Position
  | NonLinearMetavariableSpine (Located Text)
  | MetavarOccurCheck Integer Position
  | EscapingVariableInMetavar (Located Text) Position
  | CannotUnify [(Located Expression, Located Expression)]
  | ImplicitnessMismatch Implicitness Implicitness Position Position
  | CannotInferTypeOfTerm AST.Expression Position
  | UsageMismatch [(Multiplicity, Multiplicity, Text, Located Expression)] Position
  | UnsolvedMetavariable [(Text, Multiplicity, Located Expression)] AST.HoleLocation Position
  | UndefinedValueBinding Text Position
