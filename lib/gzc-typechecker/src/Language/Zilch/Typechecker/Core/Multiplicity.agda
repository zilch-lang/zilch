module Language.Zilch.Typechecker.Core.Multiplicity where

open import Prelude.Bool
open import Prelude.Equality
open import Prelude.Empty
open import Prelude.Decidable
open import Prelude.Semiring

{-# FOREIGN GHC import Language.Zilch.Typecheck.Core.Multiplicity (Multiplicity (..)) #-}

-- | The type of multiplicities in a QTT setting with 0,1,ω.
data Multiplicity : Set where
  -- | The multiplicity of erased (“compile-time”) terms.
  ^0 : Multiplicity
  -- | The multiplicity of linear (“single-use runtime”) terms.
  ^1 : Multiplicity
  -- | The multiplicity of unrestricted terms 
  --   (terms which can be used multiple times at runtime).
  ^ω : Multiplicity
{-# COMPILE GHC Multiplicity = data Multiplicity (Erased | Linear | Unrestricted) #-}

instance 
  eqMultiplicity : Eq Multiplicity
  _==_ {{eqMultiplicity}} ^0 ^0 = yes refl
  _==_ {{eqMultiplicity}} ^0 ^1 = no λ ()
  _==_ {{eqMultiplicity}} ^0 ^ω = no λ ()
  _==_ {{eqMultiplicity}} ^1 ^1 = yes refl 
  _==_ {{eqMultiplicity}} ^1 ^0 = no λ ()
  _==_ {{eqMultiplicity}} ^1 ^ω = no λ ()
  _==_ {{eqMultiplicity}} ^ω ^ω = yes refl
  _==_ {{eqMultiplicity}} ^ω ^0 = no λ ()
  _==_ {{eqMultiplicity}} ^ω ^1 = no λ ()


-- | Defines the usual ordering of multiplicity according to the linear rules of the 0,1,ω fragment.
--
--   `ρ ⩽ π` really means that a value with multiplicity `π` can be used in place of a value with multiplicity `ρ`.
--
--   Note that we do not allow `0 ⩽ 1`, as to prevent dropping linear ressources (with this rule, our type system becomes “affine”).
_⩽_ : Multiplicity → Multiplicity → Bool
^0 ⩽ ^0 = true 
^0 ⩽ ^ω = true
^1 ⩽ ^1 = true 
^1 ⩽ ^ω = true 
^ω ⩽ ^ω = true 
{-# CATCHALL #-}
_ ⩽ _ = false


instance 
  semiringMultiplicity : Semiring Multiplicity
  -- | The erased multiplicity.
  zro {{semiringMultiplicity}} = ^0

  -- | The linear multiplicity.
  one {{semiringMultiplicity}} = ^1

  -- | The 0-preserving multiplication of multiplicities, given as:
  --
  -- ╔═══╦═══╦═══╦═══╗
  -- ║ × ║ 0 ║ 1 ║ ω ║
  -- ╠═══╬═══╬═══╬═══╣
  -- ║ 0 ║ 0 ║ 0 ║ 0 ║
  -- ║ 1 ║ 0 ║ 1 ║ ω ║
  -- ║ ω ║ 0 ║ ω ║ ω ║
  -- ╚═══╩═══╩═══╩═══╝
  _*_ {{semiringMultiplicity}} ^0 _ = ^0
  _*_ {{semiringMultiplicity}} _ ^0 = ^0
  _*_ {{semiringMultiplicity}} ^1 ρ = ρ
  _*_ {{semiringMultiplicity}} ρ ^1 = ρ
  _*_ {{semiringMultiplicity}} ^ω _ = ^ω

  -- | The addition of multiplicities, given as:
  --
  -- ╔═══╦═══╦═══╦═══╗
  -- ║ + ║ 0 ║ 1 ║ ω ║
  -- ╠═══╬═══╬═══╬═══╣
  -- ║ 0 ║ 0 ║ 1 ║ ω ║
  -- ║ 1 ║ 1 ║ ω ║ ω ║
  -- ║ ω ║ ω ║ ω ║ ω ║
  -- ╚═══╩═══╩═══╩═══╝
  _+_ {{semiringMultiplicity}} ^0 ρ = ρ
  _+_ {{semiringMultiplicity}} ρ ^0 = ρ
  _+_ {{semiringMultiplicity}} ^1 ^1 = ^ω
  _+_ {{semiringMultiplicity}} ^ω _ = ^ω
  _+_ {{semiringMultiplicity}} _ ^ω = ^ω

-- | Computes the least upper bound between two multiplicities.
lub : Multiplicity → Multiplicity → Multiplicity
lub ^0 ^0 = ^0
lub ^1 ^1 = ^1
lub _ _ = ^ω

-- | Represents the runtime relevance of the current context.
data Relevance : Set where 
  -- | Currently irrelevant: we are most probably type-checking a type
  Irrelevant : Relevance 
  -- | Present: we are typechecking runtime resources
  Present : Relevance 

-- | Returns the smallest multiplicity related to the runtime relevance given.
--
--   - For 'Irrelevant', this is '^0'
--   - For 'Present', this is '^1'
extend : Relevance → Multiplicity 
extend Irrelevant = ^0
extend Present = ^1

-- | Extracts the runtime relevance of a given multiplicity.
--
--   - '^0' is considered 'Irrelevant'
--   - all other multiplicities are 'Present'
relevance : Multiplicity → Relevance 
relevance ^0 = Irrelevant
relevance ^1 = Present 
relevance ^ω = Present