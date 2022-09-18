module Language.Zilch.Typechecker.Checker.Internal where

open import Data.Located 
import Language.Zilch.Typechecker.Core as TAST 
open import Language.Zilch.Typechecker.Core.Multiplicity
import Language.Zilch.Typechecker.Foreign as AST 
open import Language.Zilch.Typechecker.Context using (Context; env)
open import Language.Zilch.Typechecker.Elaborator.Class
open import Language.Zilch.Typechecker.Usage using (Usage)
import Language.Zilch.Typechecker.Usage as Usage 
open import Language.Zilch.Typechecker.Errors
open import Language.Zilch.Typechecker.Normaliser
open import Language.Zilch.Typechecker.Unifier using (_~[_]_)
open import Language.Zilch.Typechecker.Metavars.Fresh using (fresh-meta)

open import Prelude.Product using (_×_; _,_)
open import Prelude.List using (filter; null)
open import Prelude.Bool using (not; _==?_)
open import Prelude.Function using (_$_)
open import Prelude.Unit 

open import Control.Monad.Extra

private 
  uncurry₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} → (f : A → B → C → D) → A × B × C → D
  uncurry₃ f (x , y , z) = f x y z

  mutual 
    insert : ∀ {n} → Context n → Located TAST.Expression → Located TAST.Value → Usage → Elaborator (Located TAST.Expression × Located TAST.Value × Usage)
    insert Γ t@((TAST.E-λ (TAST.Param TAST.Implicit _ _ _ at _) , _) at _) v qs = return (t , v , qs)
    {-# CATCHALL #-}
    insert Γ t v qs = insert′ Γ t v qs

    {-# TERMINATING #-}
    insert′ : ∀ {n} → Context n → Located TAST.Expression → Located TAST.Value → Usage → Elaborator (Located TAST.Expression × Located TAST.Value × Usage)
    insert′ Γ t v qs = ⇓ v >>= λ where 
      (TAST.V-Π mult _ TAST.Implicit a@(_ at p₂) b at p) → do 
        m ← fresh-meta Γ mult a p AST.InsertedHole 
        let m = m at p₂
        mv ← [ Γ .env ]↝ m 
        b ← open-and-eval mv b
        insert′ Γ (TAST.E-application t TAST.Implicit m at p) b qs
      v → return (t , v , qs)

mutual 
  -- | Type checking rules.
  --
  --   These are mainly type-formation and introduction rules.
  _⊢_⇐[_]_ : ∀ {n} → Context n → Located AST.Expression → TAST.Relevance → Located TAST.Value → Elaborator (Located TAST.Expression × Usage)
  Γ ⊢ e ⇐[ s ] τ = (Γ ⊢′ e ⇐[ s ]_) =<< ⇓ τ
  {-# INLINE _⊢_⇐[_]_ #-}

  -- | Type synthesis rules.
  --
  --   These are mainly elimination rules.
  _⊢_⇒[_] : ∀ {n} → Context n → Located AST.Expression → TAST.Relevance → Elaborator (Located TAST.Expression × Located TAST.Value × Usage)
  _ ⊢ (e at p) ⇒[ _ ] = liftE $ throwError $ CannotInferTypeOfTerm e p

  private 
    _⊢′_⇐[_]_ : ∀ {n} → Context n → Located AST.Expression → TAST.Relevance → Located TAST.Value → Elaborator (Located TAST.Expression × Usage)
    -- add other cases before
    Γ ⊢′ e ⇐[ s ] τ = do 
      {-
      -}
      e , τ₂ , qs ← uncurry₃ (insert Γ) =<< Γ ⊢ e ⇒[ s ]
      τ₂ ~[ Γ ] τ 
      return $ e , qs

    check-is-in-irrelevant-context : TAST.Relevance → Position → Elaborator ⊤′
    check-is-in-irrelevant-context TAST.Irrelevant _ = return tt 
    check-is-in-irrelevant-context TAST.Present p = liftE $ throwError $ IrrelevantTermOutsideIrrelevantContext p 

-- | Type-checking in an irrelevant context.
--
--   Must not consume any resource at all.
_⊢_⇐⁰_ : ∀ {n} → Context n → Located AST.Expression → Located TAST.Value → Elaborator (Located TAST.Expression)
Γ ⊢ e@(_ at p) ⇐⁰ τ = do 
  -- iff 
  e , u ← Γ ⊢ e ⇐[ TAST.Irrelevant ] τ 
  
  let used = filter (λ (_ , x) → not (x ==? ^0)) $ Usage.toList u
  unless (null used) do 
    liftE $ throwError $ ResourceUsageInIrrelevantContext p used

  return e 