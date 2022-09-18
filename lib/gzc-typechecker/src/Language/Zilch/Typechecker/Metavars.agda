module Language.Zilch.Typechecker.Metavars where

open import Language.Zilch.Typechecker.Core.Internal using (Value; Path)
open import Language.Zilch.Typechecker.Core.Multiplicity using (Multiplicity)
open import Data.Located using (Located; Position)
open import Language.Zilch.Typechecker.Foreign using (HoleLoc)

open import Prelude.Nat using (Nat)
open import Prelude.Fin using (Fin)
open import Prelude.Vec using (Vec)
open import Prelude.Product using (_×_; Σ; Exist)
open import Prelude.Equality using (_≡_)

data MetaEntry : Set where
  Solved : Value → Multiplicity → Located Value → MetaEntry
  Unsolved : Multiplicity → Located Value → MetaEntry

MetaMapEntry : Set 
MetaMapEntry = ∃ m , MetaEntry × Path m × Located HoleLoc

record MetaContext (n : Nat) : Set where
  field
    mapping : Vec MetaMapEntry n

open MetaContext using (mapping) public