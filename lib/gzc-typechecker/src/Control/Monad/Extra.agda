module Control.Monad.Extra where 

open import Prelude.Monad 
open import Prelude.Bool using (Bool; true; false; IsTrue; IsFalse)
open import Prelude.Unit
open import Prelude.Decidable using (Dec; yes; no)
open import Prelude.Empty
open import Prelude.Vec using (Vec)
import Prelude.Vec as Vec
open import Prelude.List using (List)
import Prelude.List as List

module _ {a} {M : Set a → Set a} {{_ : Monad M}} where 
  _>=>_ : ∀ {A B C : Set a} → (A → M B) → (B → M C) → A → M C
  f >=> g = λ x → f x >>= g
  {-# INLINE _>=>_ #-}

  --------------------------------

  when : Bool → M ⊤′ → M ⊤′
  when true m = m 
  when false _ = return tt

  when′ : (b : Bool) → ({{_ : IsTrue b}} → M ⊤′) → M ⊤′ 
  when′ true m = m 
  when′ false _ = return tt

  -- | Execute an action only if @P@ is “true”.
  whenDec : ∀ {P : Set a} → Dec P → M ⊤′ → M ⊤′ 
  whenDec (yes _) m = m 
  whenDec (no _) _ = return tt 

  whenDec′ : ∀ {P : Set a} → Dec P → (P → M ⊤′) → M ⊤′ 
  whenDec′ (yes eq) m = m eq 
  whenDec′ (no _) _ = return tt

  unless : Bool → M ⊤′ → M ⊤′
  unless false m = m 
  unless true _ = return tt 

  unless′ : (b : Bool) → ({{_ : IsFalse b}} → M ⊤′) → M ⊤′
  unless′ false m = m 
  unless′ true _ = return tt

  -- | Execute an action only if @P@ is “false”.
  unlessDec : ∀ {P : Set a} → Dec P → M ⊤′ → M ⊤′
  unlessDec (no _) m = m 
  unlessDec (yes _) _ = return tt 

  unlessDec′ : ∀ {P : Set a} → Dec P → (¬ P → M ⊤′) → M ⊤′
  unlessDec′ (no neq) m = m neq 
  unlessDec′ (yes _) _ = return tt

  ---------------------

  traverseVec : ∀ {A B : Set a} {n} → Vec A n → (A → M B) → M (Vec B n)
  traverseVec Vec.[] f = return Vec.[]
  traverseVec (x Vec.∷ xs) f = do 
    x ← f x 
    xs ← traverseVec xs f 
    return (x Vec.∷ xs)

  traverseVec′ : ∀ {A B n} → Vec A n → (A → M B) → M ⊤′ 
  traverseVec′ v f = do 
    _ ← traverseVec v f 
    return tt
  {-# INLINE traverseVec′ #-}

  foldlM : ∀ {A B : Set a} → (A → B → M A) → A → List B → M A
  foldlM f x List.[] = return x
  foldlM f x (y List.∷ ys) = f x y >>= λ x → foldlM f x ys