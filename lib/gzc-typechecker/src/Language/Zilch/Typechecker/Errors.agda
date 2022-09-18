module Language.Zilch.Typechecker.Errors where

open import Data.Located using (Located; Position)
open import Language.Zilch.Typechecker.Core using (Value; Multiplicity; Expression; Implicitness)
import Language.Zilch.Typechecker.Foreign.AST as AST

open import Prelude.Nat using (Nat)
open import Prelude.String using (String)
open import Prelude.List using (List)
open import Prelude.Product using (_×_)
open import Prelude.Functor using (_<$>_)

open import Data.HsTuple 

{-# FOREIGN GHC import Language.Zilch.Typechecker.Errors #-}

data InternalElabError : Set where 
  UnboundMetaVariable : Nat → InternalElabError
  InvalidApplication : Located Value → Located Value → InternalElabError
  InconsistentPathWithEnv : Nat → Nat → InternalElabError
  QuotingUndefined : InternalElabError
  NonVariableMetavariableArgument : Value → Position → InternalElabError
  CannotRenameThisTerm : Located Value → InternalElabError
  NoSuchMetaVariable : Nat → InternalElabError
  CannotConstructMetaLambdasFromTerm : Located Value → InternalElabError
{-# COMPILE GHC InternalElabError = data InternalElabError 
        ( UnboundMetaVariable | InvalidApplication | InconsistentPathWithEnv | QuotingUndefined
        | NonVariableMetavariableArgument | CannotRenameThisTerm | NoSuchMetaVariable | CannotConstructMetaLambdasFromTerm
        )
#-}

data ElabError : Set where
  InternalError : InternalElabError → ElabError 
  UnboundVariableIndex : Located String → Nat → Position → ElabError
  IdentifierAlreadyBound : String → Position → Position → ElabError
  MultiplicityMismatch : Located Multiplicity → Located Multiplicity → ElabError
  ResourceUsageInIrrelevantContext : Position → List (String × Multiplicity) → ElabError
  IrrelevantTermOutsideIrrelevantContext : Position → ElabError
  NonLinearMetavariableSpine : Located String → ElabError
  MetavarOccurCheck : Nat → Position → ElabError
  EscapingVariableInMetavar : Located String → Position → ElabError
  CannotUnify : List (Located Expression × Located Expression) → ElabError
  ImplicitnessMismatch : Implicitness → Implicitness → Position → Position → ElabError
  CannotInferTypeOfTerm : AST.Expression → Position → ElabError
  UsageMismatch : List (Multiplicity × Multiplicity × String × Located Expression) → Position → ElabError
  UnsolvedMetavariable : List (String × Multiplicity × Located Expression) → AST.HoleLoc → Position → ElabError
  UndefinedValueBinding : String → Position → ElabError

data ElabWarning : Set where

-- export to FFI

-- | The purpose of this data type is only to be exported to Haskell via the FFI.
--
--   This cannot be done (unfortunately) with 'ElabError' directly because of the use of '_×_'.
data ElabError′ : Set where
  InternalError : InternalElabError → ElabError′ 
  UnboundVariableIndex : Located String → Nat → Position → ElabError′
  IdentifierAlreadyBound : String → Position → Position → ElabError′
  MultiplicityMismatch : Located Multiplicity → Located Multiplicity → ElabError′
  ResourceUsageInIrrelevantContext : Position → List (String ×′ Multiplicity) → ElabError′
  IrrelevantTermOutsideIrrelevantContext : Position → ElabError′
  NonLinearMetavariableSpine : Located String → ElabError′
  MetavarOccurCheck : Nat → Position → ElabError′
  EscapingVariableInMetavar : Located String → Position → ElabError′
  CannotUnify : List (Located Expression ×′ Located Expression) → ElabError′
  ImplicitnessMismatch : Implicitness → Implicitness → Position → Position → ElabError′
  CannotInferTypeOfTerm : AST.Expression → Position → ElabError′
  UsageMismatch : List (×××′ Multiplicity Multiplicity String (Located Expression)) → Position → ElabError′
  UnsolvedMetavariable : List (××′ String Multiplicity (Located Expression)) → AST.HoleLoc → Position → ElabError′
  UndefinedValueBinding : String → Position → ElabError′
{-# COMPILE GHC ElabError′ = data ElabError 
        ( InternalError | UnboundVariableIndex | IdentifierAlreadyBound | MultiplicityMismatch
        | ResourceUsageInIrrelevantContext | IrrelevantTermOutsideIrrelevantContext | NonLinearMetavariableSpine
        | MetavarOccurCheck | EscapingVariableInMetavar | CannotUnify | ImplicitnessMismatch | CannotInferTypeOfTerm
        | UsageMismatch | UnboundMetaVariable | UndefinedValueBinding 
        )
#-}

ElabError→ElabError′ : ElabError → ElabError′ 
ElabError→ElabError′ (InternalError err) = InternalError err
ElabError→ElabError′ (UnboundVariableIndex x idx p) = UnboundVariableIndex x idx p
ElabError→ElabError′ (IdentifierAlreadyBound x p₁ p₂) = IdentifierAlreadyBound x p₁ p₂ 
ElabError→ElabError′ (MultiplicityMismatch m₁ m₂) = MultiplicityMismatch m₁ m₂ 
ElabError→ElabError′ (ResourceUsageInIrrelevantContext p us) = ResourceUsageInIrrelevantContext p (×→×′ <$> us)
ElabError→ElabError′ (IrrelevantTermOutsideIrrelevantContext p) = IrrelevantTermOutsideIrrelevantContext p 
ElabError→ElabError′ (NonLinearMetavariableSpine x) = NonLinearMetavariableSpine x 
ElabError→ElabError′ (MetavarOccurCheck idx p) = MetavarOccurCheck idx p 
ElabError→ElabError′ (EscapingVariableInMetavar x p) = EscapingVariableInMetavar x p 
ElabError→ElabError′ (CannotUnify errs) = CannotUnify (×→×′ <$> errs)
ElabError→ElabError′ (ImplicitnessMismatch i₁ i₂ p₁ p₂) = ImplicitnessMismatch i₁ i₂ p₁ p₂ 
ElabError→ElabError′ (CannotInferTypeOfTerm t p) = CannotInferTypeOfTerm t p 
ElabError→ElabError′ (UsageMismatch errs p) = UsageMismatch (×××→×××′ <$> errs) p 
ElabError→ElabError′ (UnsolvedMetavariable scope loc p) = UnsolvedMetavariable (××→××′ <$> scope) loc p 
ElabError→ElabError′ (UndefinedValueBinding x p) = UndefinedValueBinding x p 