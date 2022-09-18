module Language.Zilch.Typechecker.Usage where

open import Data.Located using (Located)
open import Language.Zilch.Typechecker.Core.Multiplicity using (Multiplicity; ^0; lub)

open import Prelude.String using (String)
open import Prelude.Nat using (Nat)
open import Prelude.String using (String)
open import Prelude.Product using (_×_; fst; second)
open import Prelude.Semiring using (_*_; _+_; _-_)
open import Prelude.Functor using (_<$>_)
open import Prelude.List using (FunctorList; foldr; _++_)
open import Prelude.Semigroup using (Semigroup; _<>_)

open import Data.Maybe using (fromMaybe; Maybe; nothing; just)
open import Data.These using (fold)
open import Data.String.Properties using (<-strictTotalOrder-≈)
open import Data.Tree.AVL.Map (<-strictTotalOrder-≈) public

-- | Records how much of a variable has actually been used in the process of type-checking an expression.
Usage : Set 
Usage = Map Multiplicity

-- | This is a more general variant of 'Usage' which captures what each function used at the top-level.
UsageRecord : Set 
UsageRecord = Map Usage 

-- | Scales a usage record by the given multiplicity @ρ@.
--
--   This merely multiplies all the multiplicities inside the usage record by @ρ@.
scale : Multiplicity → Usage → Usage 
scale ρ = map (_* ρ)

-- | Concatenates two usage records by adding the multiplicities for the same entries.
concat : Usage → Usage → Usage 
concat = unionWith (λ ρ₁ ρ₂ → ρ₁ + fromMaybe ^0 ρ₂)

instance 
  semigroupUsage : Semigroup Usage
  _<>_ {{semigroupUsage}} = concat

-- | Merge two usage records by computing the least upper bound between elements for the same key.
--
--   If a key is present in one usage record and not the other, the least upper bound is computed with '^0'.
merge : Usage → Usage → Usage 
merge u₁ u₂ = alignAndLubMaps u₁ u₂
  where
    combine : Maybe Multiplicity → Maybe Multiplicity → Multiplicity
    combine nothing nothing = ^0
    combine (just ρ) nothing = lub ρ ^0
    combine nothing (just ρ) = lub ^0 ρ 
    combine (just ρ₁) (just ρ₂) = lub ρ₁ ρ₂ 

    alignAndLubMaps : Usage → Usage → Usage 
    alignAndLubMaps u₁ u₂ = 
      let keys = fst <$> (toList u₁ ++ toList u₂)
       in foldr (λ k → insert k (combine (lookup k u₁) (lookup k u₂))) empty keys
