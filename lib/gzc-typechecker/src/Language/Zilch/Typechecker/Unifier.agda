module Language.Zilch.Typechecker.Unifier where 

open import Data.Located
open import Language.Zilch.Typechecker.Core
open import Language.Zilch.Typechecker.Elaborator.Class
open import Language.Zilch.Typechecker.Normaliser.Eval using (⇓_; open-and-eval; [_]↝_; apply)
open import Language.Zilch.Typechecker.Normaliser.Quote using (⟦_,_⟧; level→index)
open import Language.Zilch.Typechecker.Errors
open import Language.Zilch.Typechecker.Metavars using (mapping; Solved; Unsolved)
open import Language.Zilch.Typechecker.Context using (Context; env; lvl)

open import Data.Nat.Properties using (<-strictTotalOrder)
open import Data.Tree.AVL.Map (<-strictTotalOrder) 
import Data.Maybe as M

open import Prelude.Nat using (Nat; suc; eqNat; lessNat)
open import Prelude.Product using (_×_; _,_; snd)
open import Prelude.Function using (_$_; _∘_; case_of_)
open import Prelude.List using ([]; _∷_; _++_; length; [_])
open import Prelude.Bool using (if_then_else_; true; false; if′_then_else_; IsTrue; _||_)
open import Prelude.Unit
open import Prelude.Vec using (indexVec; Vec)
import Prelude.Vec as Vec
open import Prelude.Fin using (natToFin; Fin; finToNat)
open import Prelude.Show using (show; ShowNat)
open import Prelude.String using (primStringAppend)
open import Prelude.Decidable using (Dec; yes; no; fromDec)
open import Prelude.Ord using (_<_; _<-dec_)
open import Prelude.Equality using (_≡_; _==_)
open import Prelude.Sum using (left; right)

-- This module implements pattern unification.
--
-- See [here](https://github.com/AndrasKovacs/elaboration-zoo/blob/master/03-holes/Main.hs#L412) for an 
-- explanation of the inner workings of this module.
--
-- The main ideas to understand is that working with DeBruijn indices makes it so that we can't simply
-- solve `?N spine = term` (with `λ spine ⇒ term`) because we can't shuffle the `spine` on the other side.
--
-- So we:
-- 
-- 1. Generate a partial renaming to create the correct indices for each variable of the spine 
--
-- 2. Quote the `term` while renaming local variables (this fails if either a variable is not bound or `?N` occurs in `?N`)
--
--
--
-- As a quick example, consider the following metavariable head: `?2 5 4 6`.
-- The partial renaming generated from this is `[5 ↦ 0; 4 ↦ 1; 6 ↦ 2]`. 
-- Any occurrence of a variable index other than 5, 4 and 6 is an error.

private 
  -- | A partial renaming from a domain Γ to a co-domain Δ
  record PartialRenaming : Set where 
    constructor PRen
    field
      -- | This is the size of Γ, the context where the `term` lives.
      domain : DeBruijnLvl
      -- | This is the size of Δ, which should be equal to the length of the `spine`.
      co-domain : DeBruijnLvl
      -- | This is the renaming being generated from Γ to Δ.
      rename : Map DeBruijnLvl
    
  -- | Insert a new variable in the partial renaming.
  ↑_ : PartialRenaming → PartialRenaming
  ↑_ ren = PRen (suc domain) (suc co-domain) (insert co-domain domain rename)
    where open PartialRenaming ren

  -- | The obvious solution to the problem `?N spine ≟ term` is `?N = λ spine ⇒ term`.
  --
  --   This first step is the one in charge of “transferring” the spine onto the other side of the equality,
  --   by generating a partial renaming (given the context 'Γ').
  invert : DeBruijnLvl → Spine → Elaborator PartialRenaming
  invert Γ spine = do 
    dom , ren ← go spine 
    return $ PRen dom Γ ren 
    where
      go : Spine → Elaborator (DeBruijnLvl × Map DeBruijnLvl)
      go [] = return (0 , empty)
      go ((t , _) ∷ spine) = do 
        dom , ren ← go spine 
        ⇓ t >>= λ where
          (V-variable name lvl at p) → 
            if lvl ∈? ren
            then liftE (throwError $ NonLinearMetavariableSpine name)
            else return (suc dom , insert lvl dom ren)
          (v at p) → liftE (throwError $ InternalError $ NonVariableMetavariableArgument v p)

  module _ where 
    {-# TERMINATING #-}
    mutual
      -- | Second step: apply the partial renaming to the `term`, and quote it.
      rename : Nat → PartialRenaming → Located Value → Elaborator (Located Expression)
      rename m ren v = ⇓ v >>= do-rename m ren

      do-rename : Nat → PartialRenaming → Located Value → Elaborator (Located Expression)
      do-rename m ren (V-flexible m′ sp at p) with eqNat m m′
      ... | true = liftE $ throwError $ MetavarOccurCheck m p 
      ... | false = do-rename-spine m ren (E-meta m′ at p) sp
      do-rename m ren@(PRen dom _ env) (V-rigid name m′ sp at p) with lookup m′ env
      ... | M.nothing = liftE $ throwError $ EscapingVariableInMetavar name p 
      ... | M.just m′ = do-rename-spine m ren (E-identifier name (level→index dom m′) at p) sp
      do-rename m ren@(PRen _ cod _) (V-λ mult name icit τ clos at p) = do 
        τ ← rename m ren τ 
        e ← rename m (↑ ren) =<< open-and-eval (V-variable name cod at p) clos 
        return $ (E-λ (Param icit mult name e at p), e) at p
      do-rename m ren@(PRen _ cod _) (V-Π mult name icit τ clos at p) = do 
        τ ← rename m ren τ 
        e ← rename m (↑ ren) =<< open-and-eval (V-variable name cod at p) clos 
        return $ (E-Π (Param icit mult name e at p), e) at p
      do-rename m ren@(PRen _ cod _) (V-⊗ mult name τ clos at p) = do 
        τ ← rename m ren τ 
        e ← rename m (↑ ren) =<< open-and-eval (V-variable name cod at p) clos 
        return $ ((Param Explicit mult name e at p) E-⊗ e) at p
      do-rename m ren@(PRen _ cod _) (V-& name@(_ at p₂) τ clos at p) = do 
        τ ← rename m ren τ 
        e ← rename m (↑ ren) =<< open-and-eval (V-variable name cod at p) clos 
        return $ ((Param Explicit (^ω at p₂) name e at p) E-& e) at p
      do-rename _ _ (V-⊤ at p) = return $ E-⊤ at p
      do-rename _ _ (V-one at p) = return $ E-one at p
      do-rename _ _ (V-type at p) = return $ E-type at p
      do-rename _ _ (V-integer n τ at p) = return $ E-integer n τ at p 
      do-rename _ _ (V-character c at p) = return $ E-character c at p
      do-rename _ _ (V-true at p) = return $ E-boolean true at p 
      do-rename _ _ (V-false at p) = return $ E-boolean false at p
      do-rename _ _ (V-⊗unit at p) = return $ E-⊗unit at p 
      do-rename _ _ (V-&unit at p) = return $ E-&unit at p
      do-rename _ _ (V-builtin τ at p) = return $ E-builtin τ at p
      do-rename m ren ((V-if cond then t else e) at p) = do 
        cond ← rename m ren cond 
        t ← rename m ren t 
        e ← rename m ren e 
        return $ (E-if cond then t else e) at p
      do-rename m ren (V-fst v at p) = do 
        e ← rename m ren v 
        return $ E-fst e at p
      do-rename m ren (V-snd v at p) = do 
        e ← rename m ren v 
        return $ E-snd e at p
      do-rename m ren ((x V-⊗, y) at p) = do 
        x ← rename m ren x 
        y ← rename m ren y 
        return $ (x E-⊗, y) at p 
      do-rename m ren ((x V-&, y) at p) = do 
        x ← rename m ren x 
        y ← rename m ren y 
        return $ (x E-&, y) at p 
      do-rename _ _ v@(V⟦ _ ⟧ at _) = liftE $ throwError $ InternalError $ CannotRenameThisTerm v
      do-rename _ _ v@(V-undef at _) = liftE $ throwError $ InternalError $ CannotRenameThisTerm v

      do-rename-spine : Nat → PartialRenaming → Located Expression → Spine → Elaborator (Located Expression)
      do-rename-spine _ _ v [] = return v
      do-rename-spine m ren v@(_ at p) ((u , i) ∷ sp) = do 
        v₁ ← do-rename-spine m ren v sp 
        v₂ ← rename m ren u 
        return $ E-application v₁ i v₂ at p

  lams : DeBruijnLvl → Located Value → Located Expression → Position → Elaborator (Located Expression)
  lams l a t p = go a t l
    where 
      go : Located Value → Located Expression → DeBruijnLvl → Elaborator (Located Expression)
      go a acc 0 = return acc
      go (V-Π mult ("_" at p₃) icit τ clos at p₂) acc k@(suc l′) = do 
        let idx = level→index l k
        let name = primStringAppend "@" (show idx) at p₃
        e ← open-and-eval (V-variable name idx at p₃) clos 
        τ ← ⟦ 0 , τ ⟧ 
        go e ((E-λ (Param icit mult name τ at p₂) , acc) at p) l′
      go (V-Π mult name@(_ at p₃) icit τ clos at p₂) acc k@(suc l′) = do 
        let idx = level→index l k
        e ← open-and-eval (V-variable name idx at p₃) clos 
        τ ← ⟦ 0 , τ ⟧ 
        go e ((E-λ (Param icit mult name τ at p₂) , acc) at p) l′
      {-# CATCHALL #-}
      go v _ _ = liftE $ throwError $ InternalError $ CannotConstructMetaLambdasFromTerm v
  {-# INLINE lams #-}

  -- | The actual algorithm to solve the goal `Γ ⊢ ?N spine ≟ term`.
  solve : DeBruijnLvl → Nat → Spine → Located Value → Elaborator ⊤′ 
  solve lvl m spine t = do 
    m′ , mult , τ , path , loc ← do 
      n , ctx ← liftS get 
      sol ← if′ lessNat m n
        then return $ indexVec (ctx .mapping) (natToFin m)
        else liftE (throwError $ InternalError $ NoSuchMetaVariable m)
      case sol of λ where
        (m′ , Unsolved mult τ , path , loc) → return $ m′ , mult , τ , path , loc 
        (m′ , Solved _ mult τ , path , loc) → return $ m′ , mult , τ , path , loc 
        
    pren@(PRen dom _ _) ← invert lvl spine 
    val@(_ at p) ← rename m pren t

    sol at _ ← ([ Vec.[] ]↝_) =<< lams dom τ val p 

    n , ctx ← liftS get 
    if′ lessNat m n
      then liftS (put $ n , record { mapping = insert′ (natToFin m) (m′ , Solved sol mult τ , path , loc) (ctx .mapping) })
      else liftE (throwError $ InternalError $ NoSuchMetaVariable m)

    return tt
    where 
      insert′ : ∀ {A n} → Fin n → A → Vec A n → Vec A n
      insert′ Fin.zero x (_ Vec.∷ ys) = x Vec.∷ ys
      insert′ (Fin.suc n) x (y Vec.∷ ys) = x Vec.∷ insert′ n x ys

  mutual 
    unify-spine : DeBruijnLvl → (sp₁ : Spine) → (sp₂ : Spine) → {{_ : IsTrue (eqNat (length sp₁) (length sp₂))}} → Elaborator ⊤′ 
    unify-spine _ [] [] = return tt 
    unify-spine lvl ((u₁ , _) ∷ sp₁) ((u₂ , _) ∷ sp₂) = do 
      unify-spine lvl sp₁ sp₂
      unify₁ lvl u₁ u₂

    {-# TERMINATING #-}
    unify₁ : DeBruijnLvl → Located Value → Located Value → Elaborator ⊤′ 
    unify₁ lvl v₁ v₂ = do
      v₁ ← ⇓ v₁ 
      v₂ ← ⇓ v₂
      n , mctx ← liftS get

      case (runElaborator {n = n} mctx (unify₂ lvl v₁ v₂)) of λ where 
        (left (CannotUnify terms)) → do 
          e₁ ← ⟦ lvl , v₁ ⟧ 
          e₂ ← ⟦ lvl , v₂ ⟧
          liftE $ throwError $ CannotUnify $ (e₁ , e₂) ∷ terms 
        (left err) → liftE $ throwError err 
        (right ((res , warns) , n , mctx)) → do 
          liftW $ tell warns 
          liftS $ put (n , mctx)
          return res

    unify₂ : DeBruijnLvl → Located Value → Located Value → Elaborator ⊤′
    unify₂ _ (V-type at _) (V-type at _) = return tt
    unify₂ _ (V-true at _) (V-true at _) = return tt 
    unify₂ _ (V-false at _) (V-false at _) = return tt 
    unify₂ lvl v₁@(V-builtin τ₁ at _) v₂@(V-builtin τ₂ at _) with τ₁ == τ₂ 
    ... | yes _ = return tt 
    ... | no _ = cannotUnify lvl v₁ v₂
    unify₂ _ (V-one at _) (V-one at _) = return tt 
    unify₂ _ (V-⊤ at _) (V-⊤ at _) = return tt
    unify₂ _ (V-⊗unit at _) (V-⊗unit at _) = return tt
    unify₂ _ (V-&unit at _) (V-&unit at _) = return tt
    unify₂ lvl v₁@(V-integer n₁ τ₁ at _) v₂@(V-integer n₂ τ₂ at _) with n₁ == n₂ | τ₁ == τ₂ 
    ... | yes _ | yes _ = return tt 
    ... | _ | _ = cannotUnify lvl v₁ v₂
    unify₂ lvl v₁@(V-character c₁ at _) v₂@(V-character c₂ at _) with c₁ == c₂ 
    ... | yes _ = return tt 
    ... | no _ = cannotUnify lvl v₁ v₂
    unify₂ lvl v₁@(V-rigid _ l₁ sp₁ at _) v₂@(V-rigid _ l₂ sp₂ at _) with l₁ == l₂ 
    ... | yes _ = 
      if′ eqNat (length sp₁) (length sp₂)
        then unify-spine lvl sp₁ sp₂ 
        else cannotUnify lvl v₁ v₂
    ... | no _ = cannotUnify lvl v₁ v₂
    unify₂ lvl v₁@(V-flexible m₁ sp₁ at _) v₂@(V-flexible m₂ sp₂ at _) with m₁ == m₂ 
    ... | yes _ = 
      if′ eqNat (length sp₁) (length sp₂)
        then unify-spine lvl sp₁ sp₂ 
        else cannotUnify lvl v₁ v₂
    ... | no _ = cannotUnify lvl v₁ v₂
    unify₂ lvl (V-flexible m sp at _) v₂ = solve lvl m sp v₂ 
    unify₂ lvl v₁ (V-flexible m sp at _) = solve lvl m sp v₁
    unify₂ lvl ((x₁ V-⊗, y₁) at _) ((x₂ V-⊗, y₂) at _) = do
      unify₁ lvl x₁ x₂ 
      unify₁ lvl y₁ y₂
    unify₂ lvl ((x₁ V-&, y₁) at _) ((x₂ V-&, y₂) at _) = do
      unify₁ lvl x₁ x₂ 
      unify₁ lvl y₁ y₂
    unify₂ lvl ((V-if c₁ then t₁ else e₁) at _) ((V-if c₂ then t₂ else e₂) at _) = do 
      unify₁ lvl c₁ c₂ 
      unify₁ lvl t₁ t₂ 
      unify₁ lvl e₁ e₂
    unify₂ lvl (V-fst v₁ at _) (V-fst v₂ at _) = do 
      unify₁ lvl v₁ v₂ 
    unify₂ lvl (V-snd v₁ at _) (V-snd v₂ at _) = do 
      unify₁ lvl v₁ v₂ 
    unify₂ lvl (V-& (_ at p) a₁ b₁ at _) (V-& _ a₂ b₂ at _) = do 
      unify₁ lvl a₁ a₂ 
      let name = primStringAppend "@" (show lvl) at p
      let var = V-variable name lvl at p
      b₁ ← open-and-eval var b₁
      b₂ ← open-and-eval var b₂ 
      unify₁ (suc lvl) b₁ b₂
    unify₂ lvl (V-⊗ m₁ (_ at p) a₁ b₁ at _) (V-⊗ m₂ _ a₂ b₂ at _) with m₁ == m₂ 
    ... | yes _ = do 
      unify₁ lvl a₁ a₂
      let name = primStringAppend "@" (show lvl) at p
      let var = V-variable name lvl at p
      b₁ ← open-and-eval var b₁
      b₂ ← open-and-eval var b₂ 
      unify₁ (suc lvl) b₁ b₂
    ... | no _ = liftE $ throwError $ MultiplicityMismatch m₁ m₂
    unify₂ lvl (V-Π m₁ (_ at p) i₁ a₁ b₁ at p₁) (V-Π m₂ _ i₂ a₂ b₂ at p₂) with m₁ == m₂ | i₁ == i₂ 
    ... | yes _ | yes _ = do 
      unify₁ lvl a₁ a₂ 
      let name = primStringAppend "@" (show lvl) at p
      let var = V-variable name lvl at p
      b₁ ← open-and-eval var b₁
      b₂ ← open-and-eval var b₂ 
      unify₁ (suc lvl) b₁ b₂
    ... | no _ | _ = liftE $ throwError $ MultiplicityMismatch m₁ m₂ 
    ... | _ | no _ = liftE $ throwError $ ImplicitnessMismatch i₁ i₂ p₁ p₂
    unify₂ lvl (V-λ m₁ (_ at p) i₁ a₁ b₁ at p₁) (V-λ m₂ _ i₂ a₂ b₂ at p₂) with m₁ == m₂ | i₁ == i₂ 
    ... | yes _ | yes _ = do 
      unify₁ lvl a₁ a₂ 
      let name = primStringAppend "@" (show lvl) at p
      let var = V-variable name lvl at p
      b₁ ← open-and-eval var b₁
      b₂ ← open-and-eval var b₂ 
      unify₁ (suc lvl) b₁ b₂
    ... | no _ | _ = liftE $ throwError $ MultiplicityMismatch m₁ m₂ 
    ... | _ | no _ = liftE $ throwError $ ImplicitnessMismatch i₁ i₂ p₁ p₂
    unify₂ lvl (V-λ _ (_ at p) i₁ _ b₁ at _) v₂ = do 
      let name = primStringAppend "@" (show lvl) at p
      let var = V-variable name lvl at p
      b₁ ← open-and-eval var b₁
      v₂ ← apply v₂ i₁ var 
      unify₁ (suc lvl) b₁ v₂
    unify₂ lvl v₁ (V-λ _ (_ at p) i₂ _ b₂ at _) = do 
      let name = primStringAppend "@" (show lvl) at p
      let var = V-variable name lvl at p
      b₂ ← open-and-eval var b₂
      v₁ ← apply v₁ i₂ var 
      unify₁ (suc lvl) b₂ v₁
    unify₂ lvl v₁ v₂ = cannotUnify lvl v₁ v₂ 

    cannotUnify : DeBruijnLvl → Located Value → Located Value → Elaborator ⊤′
    cannotUnify lvl v₁ v₂ = do 
      e₁ ← ⟦ lvl , v₁ ⟧ 
      e₂ ← ⟦ lvl , v₂ ⟧
      liftE $ throwError $ CannotUnify [ e₁ , e₂ ]

_~[_]_ : ∀ {n} → Located Value → Context n → Located Value → Elaborator ⊤′ 
v₁ ~[ ctx ] v₂ = unify₁ (ctx .lvl) v₁ v₂ 