module Language.Zilch.Typechecker.Simplifier where 

open import Data.Located 
import Language.Zilch.Typechecker.Core as TAST 
open import Language.Zilch.Typechecker.Elaborator.Class
open import Language.Zilch.Typechecker.Errors
open import Language.Zilch.Typechecker.Metavars using (mapping; Unsolved)
open import Language.Zilch.Typechecker.Normaliser.Quote using (⟦_,_⟧)
open import Language.Zilch.Typechecker.Normaliser.Eval using ([_]↝_; ⇓_; open-and-eval)
open import Language.Zilch.Typechecker.Context using (Context; env; lvl; define′; define; define-new-size; bind; Source)
open import Language.Zilch.Typechecker.Context.Defaults using (default-context)

open import Prelude.Unit
open import Prelude.Product using (_,_; _×_; snd; Exist)
open import Prelude.List using ([]; _∷_; List; [_]; _++_)
open import Prelude.Function using (_$_; _∘_; case_of_)
open import Prelude.String using (String)
open import Prelude.Nat using (suc)
open import Prelude.Bool using (true; false; if_then_else_)

private 
  mutual 
    simp : (∃ n , Context n) × List (Located TAST.TopLevel) → Located TAST.TopLevel → Elaborator ((∃ n , Context n) × List (Located TAST.TopLevel))
    simp ((n , ctx) , ts) (TAST.TopBind isPublic attrs def at p) = do 
      ctx , def ← case def of λ where 
        (TAST.D-let true mult name@(_ at p₃) τ v at p₂) → do 
          let var = TAST.V-variable name (ctx .lvl) at p₃

              ctx′ : ∃ m , Context m 
              ctx′ = define-new-size name ctx , define mult name var var ctx

          τ ← simplify′ (snd ctx′) τ 
          v ← simplify′ (snd ctx′) v 
          
          return $ ctx′ , (TAST.D-let true mult name τ v at p₂)
        (TAST.D-let false mult name@(_ at p₃) τ v at p₂) → do 
          τ ← simplify′ ctx τ 
          v ← simplify′ ctx v 

          let var = TAST.V-variable name (ctx .lvl) at p₃

              ctx′ : ∃ m , Context m 
              ctx′ = define-new-size name ctx , define mult name var var ctx

          return $ ctx′ , (TAST.D-let false mult name τ v at p₂)
        (TAST.D-val mult name@(_  at p₃) τ at p₂) → do 
          τ ← simplify′ ctx τ 

          let var = TAST.V-variable name (ctx .lvl) at p₃

              ctx′ : ∃ m , Context m
              ctx′ = suc n , define′ mult name var (TAST.V-undef at p₃) ctx
              -- see note 1 underneath the code

          return $ ctx′ , (TAST.D-val mult name τ at p₂)
      return $ ctx , (ts ++ [ TAST.TopBind isPublic attrs def at p ])

    simplify′ : ∀ {n} → Context n → Located TAST.Expression → Elaborator (Located TAST.Expression)
    simplify′ Γ e = [ Γ .env ]↝ e >>= resimplify Γ >>= ⟦ Γ .lvl ,_⟧

    {-# TERMINATING #-}
    resimplify : ∀ {n} → Context n → Located TAST.Value → Elaborator (Located TAST.Value)
    resimplify Γ = ⇓_ >=> λ where 
      (TAST.V-Π mult x@(_ at p₂) icit τ clos at p) → do 
        τ ← resimplify Γ τ 
        let Γ′ = bind mult x τ Source Γ 
        v ← open-and-eval (TAST.V-variable x (Γ .lvl) at p₂) clos >>= resimplify Γ′ >>= ⟦ Γ′ .lvl ,_⟧ 
        return $ TAST.V-Π mult x icit τ TAST.⟨ Γ′ .env ⟦ v ⟧⟩ at p
      (TAST.V-λ mult x@(_ at p₂) icit τ clos at p) → do 
        τ ← resimplify Γ τ 
        let Γ′ = bind mult x τ Source Γ 
        v ← open-and-eval (TAST.V-variable x (Γ .lvl) at p₂) clos >>= resimplify Γ′ >>= ⟦ Γ′ .lvl ,_⟧ 
        return $ TAST.V-λ mult x icit τ TAST.⟨ Γ′ .env ⟦ v ⟧⟩ at p
      (TAST.V-⊗ mult x@(_ at p₂)  τ clos at p) → do 
        τ ← resimplify Γ τ 
        let Γ′ = bind mult x τ Source Γ 
        v ← open-and-eval (TAST.V-variable x (Γ .lvl) at p₂) clos >>= resimplify Γ′ >>= ⟦ Γ′ .lvl ,_⟧ 
        return $ TAST.V-⊗ mult x τ TAST.⟨ Γ′ .env ⟦ v ⟧⟩ at p
      (TAST.V-& x@(_ at p₂)  τ clos at p) → do 
        τ ← resimplify Γ τ 
        let Γ′ = bind (TAST.^ω at p₂) x τ Source Γ 
        v ← open-and-eval (TAST.V-variable x (Γ .lvl) at p₂) clos >>= resimplify Γ′ >>= ⟦ Γ′ .lvl ,_⟧ 
        return $ TAST.V-& x τ TAST.⟨ Γ′ .env ⟦ v ⟧⟩ at p
      v → return v

  simplify : List (Located TAST.TopLevel) → Elaborator (List (Located TAST.TopLevel))
  simplify = fmap snd ∘ foldlM simp ((0 , default-context), [])

-- | Inline all generated metavariables in the module.
inlineAllMetavars : Located TAST.Module → Elaborator (Located TAST.Module)
inlineAllMetavars mod@(TAST.Mod binds at p) = do 
  _ , ctx ← liftS get 
  let metas = ctx .mapping
  traverseVec′ {B = ⊤′} metas λ where 
    (_ , Unsolved _ _ , path , loc at p) → do 

      path′ ← mk-env path 
      liftE $ throwError $ UnsolvedMetavariable path′ loc p
    _ → return tt

  binds ← simplify binds 
  return $ TAST.Mod binds at p
  where
    mk-env : ∀ {m} → TAST.Path m → Elaborator (List (String × TAST.Multiplicity × Located TAST.Expression))
    mk-env TAST.Here = return []
    mk-env (TAST.Bind path (mult at _) (x at _) τ) = do 
      τ ← ⟦ 0 , τ ⟧ 
      path′ ← mk-env path 
      return $ (x , mult , τ) ∷ path′ 
    mk-env (TAST.Define path _ _ _ _) = mk-env path

{- 
  NOTE 1:
  ~~~~~~~

    There will be a small problem with how 'val's are handled. 
    See for example this code:

    > val f : u64 
    > let g : u64 ≔ f 
    > let f : u64 ≔ 3

    In this case, the occurrence of 'f' in 'g' will actually be reduced to 'undefined' instead of 'v'.
    To fix this, we'd need to record the position of every 'val' that we insert and not insert if we 
      encounter a 'let' associated to any 'val' in the scope.
-}