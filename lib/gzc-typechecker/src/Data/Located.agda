module Data.Located where

open import Agda.Primitive
open import Prelude.Equality 
open import Prelude.Decidable

{-# FOREIGN GHC import Data.Located (Located (..), Position) #-}

postulate Position : Set

{-# COMPILE GHC Position = type Position #-}

data Located {a} (A : Set a) : Set a where
  -- | Stores a value alongside a position.
  --
  --   Note that the constructor for positions is not exposed in Agda.
  --   We should not need it anyways.
  _at_ : A → Position → Located A
infixl 10 _at_

{-# FOREIGN GHC type AgdaLocated a = Located #-}
{-# COMPILE GHC Located = data AgdaLocated ((:@)) #-}

private 
  -- careful about this!
  postulate p₁≡p₂ : ∀ {p₁ p₂ : Position} → p₁ ≡ p₂

  located-inj : ∀ {a} {A : Set a} {x₁ x₂ : A} {p₁ p₂ : Position} → (x₁ at p₁) ≡ (x₂ at p₂) → x₁ ≡ x₂ 
  located-inj refl = refl

instance 
  eqLocated : ∀ {a} {A : Set a} → {{_ : Eq A}} → Eq (Located A)
  eqLocated = record { _==_ = eq }
    where 
      eq : ∀ {a} {A : Set a} → {{_ : Eq A}} → (x y : Located A) → Dec (x ≡ y) 
      eq (x₁ at p₁) (x₂ at p₂) with x₁ == x₂
      ... | yes eq₁ = yes (cong₂ _at_ eq₁ p₁≡p₂)
      ... | no neq = no λ eq → neq (located-inj eq) 

-- | Remove the position annotation from a 'Located' piece of data.
_-pos : ∀ {a} {A : Set a} → Located A → A 
(x at _) -pos = x
