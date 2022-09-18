module Language.Zilch.Typechecker.Core.Internal where

open import Data.Located using (Located; _at_)
open import Language.Zilch.Typechecker.Core.Multiplicity using (Multiplicity)
open import Language.Zilch.Typechecker.Core.Builtins using (BuiltinType)

open import Prelude.Product using (_×_)
open import Prelude.Bool using (Bool; true; false; IsTrue)
open import Prelude.Equality using (_≡_; refl; Eq; _==_)
open import Prelude.Decidable using (yes; no)
open import Prelude.Vec using (Vec)
open import Prelude.String using (String)
open import Prelude.Int using (Int)
open import Prelude.Nat using (Nat; suc)
open import Prelude.List using (List; [])
open import Prelude.Char using (Char)
open import Prelude.Maybe using (Maybe)

{-# FOREIGN GHC import Language.Zilch.Typecheck.Core.Internal #-}

-- | A data-type to record the “implicitness” of a function argument.
data Implicitness : Set where
  -- | The parameter is implicit, meaning it can be automagically infered from its context.
  Implicit : Implicitness
  -- | The parameter is explicit, i.e. it must be given by hand.
  Explicit : Implicitness
{-# COMPILE GHC Implicitness = data Implicitness (Implicit | Explicit) #-}

instance 
  eqImplicitness : Eq Implicitness
  _==_ {{eqImplicitness}} Implicit Implicit = yes refl 
  _==_ {{eqImplicitness}} Explicit Explicit = yes refl 
  _==_ {{eqImplicitness}} Implicit Explicit = no λ () 
  _==_ {{eqImplicitness}} Explicit Implicit = no λ ()

DeBruijnLvl : Set
DeBruijnLvl = Nat

DeBruijnIdx : Set
DeBruijnIdx = Nat

MetaVar : Set
MetaVar = Nat

mutual 
  Environment : Nat → Set
  Environment = Vec (Located Value)
  {-# INLINE Environment #-}

  Environment′ : Set 
  Environment′ = List (Located Value)
  {-# INLINE Environment′ #-}

  data Closure : Set where
    ⟨_⟦_⟧⟩ : Environment′ → Located Expression → Closure
  {-# COMPILE GHC Closure = data Closure (Clos) #-}

  data ×sp : Set where 
    _,sp_ : Located Value → Implicitness → ×sp 
  {-# COMPILE GHC ×sp = data SpineElem (SpineElem) #-}

  Spine : Set
  Spine = List ×sp
  {-# INLINE Spine #-}

  ------------ TAST ----------------

  data Path : @0 Nat → Set where
    Here : Path 0
    Bind : ∀ {@0 n} → Path n → Located Multiplicity → Located String → Located Value → Path (suc n)
    Define : ∀ {@0 n} → Path n → Located Multiplicity → Located String → Located Value → Located Value → Path (suc n)
  {-# COMPILE GHC Path = data Path (Here | Bind | Define) #-}

  data Definition : Set where
    -- | This records a basic `let` or `rec` definition.
    D-let : Bool → Located Multiplicity → Located String → Located Expression → Located Expression → Definition
    -- | A simple `val` type binding.
    D-val : Located Multiplicity → Located String → Located Expression → Definition
  {-# COMPILE GHC Definition = data Definition (Let | Val) #-}

  private 
    is-let : Located Definition → Bool
    is-let (D-let _ _ _ _ _ at _) = true
    is-let (D-val _ _ _ at _) = false

  data Parameter : Set where
    Param : Implicitness → Located Multiplicity → Located String → Located Expression → Parameter
  {-# COMPILE GHC Parameter = data Parameter (Parameter) #-}

  data Expression : Set where
    -- | The `type` universe.
    E-type : Expression
    E-λ_,_ : Located Parameter → Located Expression → Expression
    E-Π_,_ : Located Parameter → Located Expression → Expression
    _E-&_ : Located Parameter → Located Expression → Expression
    _E-⊗_ : Located Parameter → Located Expression → Expression
    E-let : (d : Located Definition) → Located Expression → Expression
    E-application : Located Expression → Implicitness → Located Expression → Expression
    E-identifier : Located String → DeBruijnIdx → Expression
    E-integer : Located String → BuiltinType → Expression
    E-character : Located String → Expression
    E-meta : MetaVar → Expression
    E-insmeta : ∀ {n} → MetaVar → Path n → Expression
    E-builtin : BuiltinType → Expression
    E-boolean : Bool → Expression
    E-if_then_else_ : Located Expression → Located Expression → Located Expression → Expression
    _E-&,_ : Located Expression → Located Expression → Expression
    _E-⊗,_ : Located Expression → Located Expression → Expression
    E-⊗unit : Expression
    E-&unit : Expression
    E-one : Expression
    E-⊤ : Expression
    E-fst : Located Expression → Expression
    E-snd : Located Expression → Expression
    E-⊗,-elim : Maybe (Located String) → Located Multiplicity → Located String → Located String → Located Expression → Located Expression → Expression
    E-⊗unit-elim : Maybe (Located String) → Located Multiplicity → Located Expression → Located Expression → Expression
  {-# COMPILE GHC Expression = data Expression 
              ( EType | ELam | EPi | EAdditiveProduct | EMultiplicativeProduct | ELet 
              | EApplication | EIdentifier | EInteger | ECharacter | EMeta | EInsertedMeta 
              | EBuiltin | EBoolean | EIfThenElse | EAdditivePair | EMultiplicativePair 
              | EMultiplicativeUnit | EAdditiveUnit | EOne | ETop | EFst | ESnd
              | EMultiplicativePairElim | EMultiplicativeUnitElim 
              )
  #-}

  ----------- Values ---------------

  data Value : Set where
    -- | A rigid variable which can only be unified with itself.
    V-rigid : Located String → DeBruijnLvl → Spine → Value
    -- | A flexible variable (usually indicating a meta-variable) which can be unified with any
    --   term as long as solving succeeds.
    V-flexible : Nat → Spine → Value
    -- | ???
    V-application : Located Value → Located Value → Value
    -- | An un-applied λ function, where the body is closed over the current environment.
    V-λ : Located Multiplicity → Located String → Implicitness → Located Value → Closure → Value
    -- | An un-applied Π type, where the body is closed over the current environment.
    V-Π : Located Multiplicity → Located String → Implicitness → Located Value → Closure → Value
    -- | The type of dependent multiplicative pairs (also called “Σ type”).
    V-⊗ : Located Multiplicity → Located String → Located Value → Closure → Value
    -- | The type of dependent additive pairs.
    V-& : Located String → Located Value → Closure → Value
    -- | The universe type.
    V-type : Value
    -- | A simple integral value.
    V-integer : Located String → BuiltinType → Value
    -- | A simple character.
    V-character : Located String → Value
    -- | A thunk is an unevaluated piece of typed AST.
    --
    --   This is used merely with recursive functions.
    V⟦_⟧ : Located Expression → Value
    -- | 
    V-if_then_else_ : Located Value → Located Value → Located Value → Value
    -- | The true boolean value.
    V-true : Value
    -- | The false boolean value.
    V-false : Value 
    -- | The constructor for multiplicative dependent pairs.
    _V-⊗,_ : Located Value → Located Value → Value
    -- | The constructor for additive dependent pairs.
    _V-&,_ : Located Value → Located Value → Value
    -- | The multiplicative unit.
    V-⊗unit : Value
    -- | The additive unit.
    V-&unit : Value
    -- | The type of the multiplicative unit.
    V-one : Value
    -- | The type of the additive unit.
    V-⊤ : Value 
    -- | The first destructor for additive pairs, projecting the first element out.
    V-fst : Located Value → Value
    -- | The second destructor for additive pairs, projecting the second element out.
    V-snd : Located Value → Value
    -- | Any builtin type.
    V-builtin : BuiltinType → Value
    -- | An undefined value.
    V-undef : Value
  {-# COMPILE GHC Value = data Value 
          ( VRigid | VFlexible | VApplication | VLam | VPi | VMultiplicativeProduct | VAdditiveProduct 
          | VType | VInteger | VCharacter | VThunk | VIfThenElse | VTrue | VFalse 
          | VMultiplicativePair | VAdditivePair | VMultiplicativeUnit | VAdditiveUnit | VOne | VTop 
          | VFst | VSnd | VBuiltin | VUndefined 
          )
  #-}

pattern V-variable x lvl = V-rigid x lvl []

pattern V-meta m = V-flexible m []

data Pub|Priv : Set where 
  Public : Pub|Priv 
  Private : Pub|Priv
{-# COMPILE GHC Pub|Priv = data PubOrPriv (Public | Private) #-}

data CallingConvention : Set where 
  CCall : CallingConvention
{-# COMPILE GHC CallingConvention = data CallingConvention (CCall) #-}

data MetaAttribute : Set where
  Foreign : CallingConvention → Located String → MetaAttribute
  Inline : MetaAttribute
{-# COMPILE GHC MetaAttribute = data MetaAttribute (Foreign | Inline) #-}

data TopLevel : Set where
  TopBind : List (Located MetaAttribute) → Pub|Priv → Located Definition → TopLevel 
{-# COMPILE GHC TopLevel = data TopLevel (TopLevel) #-}

data Module : Set where
  Mod : List (Located TopLevel) → Module
{-# COMPILE GHC Module = data Module (Mod) #-}

-- TODO: add COMPILE pragmas to export the typed AST to be used on the Haskell side.