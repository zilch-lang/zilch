module Language.Zilch.Typechecker.Checker.TopLevel where 

open import Data.Located 
open import Language.Zilch.Typechecker.Elaborator.Class 
import Language.Zilch.Typechecker.Foreign.AST as AST 
import Language.Zilch.Typechecker.Core as TAST 
open import Language.Zilch.Typechecker.Usage using (UsageRecord)
open import Language.Zilch.Typechecker.Context using (Context; Binding; types; env; lvl; def; Source; define; define′)
import Language.Zilch.Typechecker.Context as Context
open import Language.Zilch.Typechecker.Environment using (Environment)
open import Language.Zilch.Typechecker.Errors
open import Language.Zilch.Typechecker.Normaliser
open import Language.Zilch.Typechecker.Checker.Internal
open import Language.Zilch.Typechecker.Usage using (Usage)
import Language.Zilch.Typechecker.Usage as Usage

open import Prelude.Product using (_×_; Exist; _,_)
open import Prelude.Maybe using (Maybe; nothing; just)
open import Prelude.String using (String)
open import Prelude.Vec using (Vec; []; _∷_)
open import Prelude.Equality using (_==_)
open import Prelude.Decidable using (yes; no)
open import Prelude.Function using (_$_; case_of_)
open import Prelude.Unit
open import Prelude.Bool using (if_then_else_)
open import Prelude.List using (List)
import Prelude.List as List
open import Prelude.Nat using (suc)

private
  check-bound : ∀ {n} → Located String → Context n → Position → Elaborator (Maybe (Located TAST.Multiplicity × Located TAST.Value))
  check-bound name ctx p = go (ctx .types) (ctx .env) 
    where 
      go : ∀ {n} → Vec Binding n → Environment n → Elaborator (Maybe (Located TAST.Multiplicity × Located TAST.Value))
      go [] [] = return nothing
      go (def mult x@(x′ at p₁) Source τ ∷ types) (v ∷ env) with x == name | v 
      ... | yes _ | TAST.V-undef at _ = return $ just (mult , τ)
      ... | yes _ | _ = liftE $ throwError $ IdentifierAlreadyBound x′ p₁ p
      ... | no _ | _ = go types env
      go (def _ _ _ _ ∷ types) (_ ∷ env) = go types env
  {-# INLINE check-bound #-}

  check-usage : ∀ {n} → Context n → Usage → Position → Elaborator ⊤′
  check-usage {n} Γ qs p = do
    let qs = Usage.toList qs 
        errs = List.catMaybes $ List.foldr findMismatches List.[] qs
    
    unless (List.null errs) do 
      errs ← quoteTypes errs 
      liftE $ throwError $ UsageMismatch errs p
    where
      findMismatches : (String × TAST.Multiplicity) → List (Maybe _) → List (Maybe _)
      findMismatches (x , mult) acc =
        case Context.lookup (x at p) Γ of λ where 
          nothing → nothing List.∷ acc 
          (just ((m′ at _) , τ)) → 
             if mult TAST.⩽ m′ 
                then nothing List.∷ acc
                else just (mult , m′ , x , τ) List.∷ acc 

      quoteTypes : List _ → Elaborator (List _)
      quoteTypes List.[] = return List.[]
      quoteTypes ((p , q , x , τ) List.∷ qs) = do  
        τ ← ⟦ Γ .lvl , τ ⟧ 
        qs ← quoteTypes qs 
        return $ (p , q , x , τ) List.∷ qs

checkTopLevel : ∀ {n} → Context n → Located AST.TopLevel → Elaborator (Located TAST.TopLevel × Exist Context × UsageRecord)
checkTopLevel {n} Γ (AST.TopBind isPublic _ (AST.D-let isRec (mult at p₆) name@(name′ at p₄) τ@(_ at p₃) ex@(_ at p₅) at p₂) at p₁) = do 
  {-
     0Γ ⊢ A ⇐⁰ type ℓ            0Γ ⊢ e ⇐⁰ A          i = 0
    ──────────────────────────────────────────────────────── [⇐ let-I₀]
                        Γ ⊢ let x :ⁱ A ≔ e

     0Γ₁ ⊢ A ⇐⁰ type ℓ             Γ₂ ⊢ e ⇐¹ A
    ─────────────────────────────────────────── [⇐ let-I₁]
              Γ₁ + iΓ₂ ⊢ let x :ⁱ A ≔ e 
  -}
  τ? ← check-bound name Γ p₄
  τ , τ′ ← case τ? of λ where 
    nothing → do 
      τ ← Γ ⊢ τ ⇐⁰ (TAST.V-type at p₃)
      τ′ ← [ Γ .env ]↝ τ 
      return $ τ , τ′
    (just (m , τ′)) → do 
      unlessDec (mult == (m -pos)) do 
        liftE $ throwError $ MultiplicityMismatch m (mult at p₆)

      τ ← ⟦ Γ .lvl , τ′ ⟧
      return $ τ , τ′ 

  ex , ex′ , qs ← do
    let new-ctx : ∃ n , Context n 
        new-ctx = 
          if isRec 
          then (Context.define-new-size name Γ , define (TAST.^ω at p₆) name τ′ (TAST.V-undef at p₅) Γ)
          else (n , Γ)
    
        n , Γ′ = new-ctx
    ex , qs ← case mult of λ where
      TAST.^0 → (_, Usage.empty) <$> (Γ′ ⊢ ex ⇐⁰ τ′)
      _ → Γ′ ⊢ ex ⇐[ TAST.Present ] τ′ 
    let qs = Usage.scale mult qs

    check-usage Γ′ qs p₅

    ex′ ← case τ of λ where
      ((TAST.E-Π _ , _) at _) → [ Γ′ .env ]↝ ex 
      _ → return (TAST.V⟦ ex ⟧ at p₅)

    return $ ex , ex′ , qs

  return $ (TAST.TopBind List.[] (if isPublic then TAST.Public else TAST.Private) (TAST.D-let isRec (mult at p₄) name τ ex at p₂) at p₁) 
         , (Context.define-new-size name Γ , define (mult at p₄) name τ′ ex′ Γ)
         , Usage.singleton name′ qs
checkTopLevel {n} Γ (AST.TopBind isPublic _ (AST.D-val mult name τ@(_ at p₃) at p₂) at p₁) = do 
  τ ← Γ ⊢ τ ⇐⁰ (TAST.V-type at p₃)
  τ′ ← [ Γ .env ]↝ τ 

  let val = TAST.V-undef at p₂

      new-ctx : ∃ n , Context n 
      new-ctx = suc n , define′ mult name τ′ val Γ 

  return $ (TAST.TopBind List.[] (if isPublic then TAST.Public else TAST.Private) (TAST.D-val mult name τ at p₂) at p₁)
         , new-ctx
         , Usage.empty