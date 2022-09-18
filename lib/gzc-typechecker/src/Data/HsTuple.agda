module Data.HsTuple where 

open import Agda.Primitive
open import Prelude.Product using (_×_; _,_)

data _×′_ (A B : Set) : Set where 
  _,′_ : A → B → A ×′ B 

{-# COMPILE GHC _×′_ = data (,) ((,)) #-}

data ××′ (A B C : Set) : Set where 
  ,,′ : A → B → C → ××′ A B C 

{-# COMPILE GHC ××′ = data (,,) ((,,)) #-}

data ×××′ (A B C D : Set) : Set where 
  ,,,′ : A → B → C → D → ×××′ A B C D 

{-# COMPILE GHC ×××′ = data (,,,) ((,,,)) #-}

×→×′ : ∀ {A B} → A × B → A ×′ B 
×→×′ (x , y) = x ,′ y
{-# INLINE ×→×′ #-}

××→××′ : ∀ {A B C} → A × B × C → ××′ A B C 
××→××′ (x , y , z) = ,,′ x y z 
{-# INLINE ××→××′ #-}

×××→×××′ : ∀ {A B C D} → A × B × C × D → ×××′ A B C D 
×××→×××′ (w , x , y , z) = ,,,′ w x y z
{-# INLINE ×××→×××′ #-}