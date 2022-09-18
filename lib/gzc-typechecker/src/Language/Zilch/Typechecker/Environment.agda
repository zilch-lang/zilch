module Language.Zilch.Typechecker.Environment where 

open import Data.Located
open import Language.Zilch.Typechecker.Core.Internal 
open import Language.Zilch.Typechecker.Core.Internal using (Environment) public

open import Prelude.Vec using (_∷_; indexVec)
open import Prelude.Nat using (Nat; suc; lessNat)
open import Prelude.Maybe using (Maybe; just; nothing)
open import Prelude.Function using (_$_)
open import Prelude.Fin using (natToFin)
open import Prelude.Bool using (if′_then_else_)

-- | Returns the length of the evaluation environment.
length : ∀ {n} → Environment n → Nat 
length {n} _ = n
{-# INLINE length #-}

-- | Insert a new value on top of the current environment stack.
extend : ∀ {n} → Located Value → Environment n → Environment (suc n)
extend = _∷_
{-# INLINE extend #-} 

-- | Lookup a value in the environment by its index.
--
--   The smaller the index is, the closer it is to the top of the stack.
lookup : ∀ {n} → Environment n → Nat → Maybe (Located Value)
lookup {n} env m =
  if′ lessNat m n
  then just (indexVec env $ natToFin m)
  else nothing
