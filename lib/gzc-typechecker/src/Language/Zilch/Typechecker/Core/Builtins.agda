module Language.Zilch.Typechecker.Core.Builtins where

open import Prelude.Decidable
open import Prelude.Equality
open import Prelude.Bool
open import Prelude.Empty

data BuiltinType : Set where
  Builtin-U64 : BuiltinType
  Builtin-U32 : BuiltinType
  Builtin-U16 : BuiltinType
  Builtin-U8 : BuiltinType
  Builtin-S64 : BuiltinType
  Builtin-S32 : BuiltinType
  Builtin-S16 : BuiltinType
  Builtin-S8 : BuiltinType
  Builtin-Bool : BuiltinType
{-# COMPILE GHC BuiltinType = data BuiltinType 
              ( TyU64 | TyU32 | TyU16 | TyU8 
              | TyS64 | TyS32 | TyS16 | TyS8 | TyBool
              )
#-}

private
  eqBuiltinBool : BuiltinType → BuiltinType → Bool
  eqBuiltinBool Builtin-U64 Builtin-U64 = true
  eqBuiltinBool Builtin-U32 Builtin-U32 = true
  eqBuiltinBool Builtin-U16 Builtin-U16 = true
  eqBuiltinBool Builtin-U8 Builtin-U8 = true
  eqBuiltinBool Builtin-S64 Builtin-S64 = true
  eqBuiltinBool Builtin-S32 Builtin-S32 = true
  eqBuiltinBool Builtin-S16 Builtin-S16 = true
  eqBuiltinBool Builtin-S8 Builtin-S8 = true
  eqBuiltinBool Builtin-Bool Builtin-Bool = true
  eqBuiltinBool _ _ = false

  eqBuiltinSound : (τ₁ τ₂ : BuiltinType) → IsTrue (eqBuiltinBool τ₁ τ₂) → τ₁ ≡ τ₂
  eqBuiltinSound Builtin-U64 Builtin-U64 _ = refl
  eqBuiltinSound Builtin-U32 Builtin-U32 _ = refl
  eqBuiltinSound Builtin-U16 Builtin-U16 _ = refl
  eqBuiltinSound Builtin-U8 Builtin-U8 _ = refl
  eqBuiltinSound Builtin-S64 Builtin-S64 _ = refl
  eqBuiltinSound Builtin-S32 Builtin-S32 _ = refl
  eqBuiltinSound Builtin-S16 Builtin-S16 _ = refl
  eqBuiltinSound Builtin-S8 Builtin-S8 _ = refl
  eqBuiltinSound Builtin-Bool Builtin-Bool _ = refl

  eqBuiltinComplete : (τ₁ τ₂ : BuiltinType) → IsFalse (eqBuiltinBool τ₁ τ₂) → ¬ (τ₁ ≡ τ₂)
  eqBuiltinComplete Builtin-U64 Builtin-U64 () eq
  eqBuiltinComplete Builtin-U32 Builtin-U32 () eq
  eqBuiltinComplete Builtin-U16 Builtin-U16 () eq 
  eqBuiltinComplete Builtin-U8 Builtin-U8 () eq
  eqBuiltinComplete Builtin-S64 Builtin-S64 () eq
  eqBuiltinComplete Builtin-S32 Builtin-S32 () eq
  eqBuiltinComplete Builtin-S16 Builtin-S16 () eq 
  eqBuiltinComplete Builtin-S8 Builtin-S8 () eq
  eqBuiltinComplete Builtin-Bool Builtin-Bool () eq

  eqBuiltin' : (τ₁ τ₂ : BuiltinType) → Dec (τ₁ ≡ τ₂)
  eqBuiltin' τ₁ τ₂ with eqBuiltinBool τ₁ τ₂ | eqBuiltinSound τ₁ τ₂ | eqBuiltinComplete τ₁ τ₂ 
  ... | true | eq | _ = yes (eq true)
  ... | false | _ | neq = no (neq false)

instance
  eqBuiltin : Eq BuiltinType
  _==_ {{eqBuiltin}} = eqBuiltin'