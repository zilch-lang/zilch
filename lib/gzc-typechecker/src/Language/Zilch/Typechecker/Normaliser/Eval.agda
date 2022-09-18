module Language.Zilch.Typechecker.Normaliser.Eval where

open import Data.Located
open import Language.Zilch.Typechecker.Environment using (Environment)
import Language.Zilch.Typechecker.Environment as Env
import Language.Zilch.Typechecker.Core as TAST
open import Language.Zilch.Typechecker.Core using (Value; Expression; ⟨_⟦_⟧⟩; Closure; Implicitness; Path; Spine)
open import Language.Zilch.Typechecker.Elaborator.Class 
open import Language.Zilch.Typechecker.Errors
open import Language.Zilch.Typechecker.Metavars using (MetaMapEntry; Solved; Unsolved; mapping)

open import Prelude.Function using (_$_; case_of_)
open import Prelude.Bool using (if_then_else_; Bool; true; false; if′_then_else_; IsTrue)
open import Prelude.Maybe using (Maybe; nothing; just)
open import Prelude.Nat using (Nat; lessNat; eqNat)
open import Prelude.Product using (_,_; Exist; Σ)
open import Prelude.Vec using (indexVec; []; _∷_)
open import Prelude.Fin using (finToNat; natToFin)
import Prelude.List as List using (_∷_; [])
open import Prelude.Equality using (_≡_)

private 
  lookup-meta : Nat → Elaborator MetaMapEntry
  lookup-meta m = do 
    n , ctx ← liftS get
    if′ lessNat m n
      then return (indexVec (ctx .mapping) (natToFin m))
      else liftE (throwError (InternalError $ UnboundMetaVariable m))

  meta-value : Nat → Position → Elaborator (Located Value)
  meta-value m p = lookup-meta m >>= λ where 
    (_ , Solved v _ _ , _ , _) → return $ v at p 
    (_ , Unsolved _ _ , _ , _) → return $ TAST.V-meta m at p

mutual
  private
    apply-path : ∀ {m n} → {{_ : IsTrue (eqNat m n)}} → Environment m → Path n → Located Value → Elaborator (Located Value)
    apply-path [] TAST.Here v = return v
    apply-path (_ ∷ env) (TAST.Define p _ _ _ _) v = apply-path env p v 
    apply-path (t ∷ env) (TAST.Bind p _ _ _) v = do 
      v₁ ← apply-path env p v 
      apply v₁ TAST.Explicit t

    apply-spine : Located Value → Spine → Elaborator (Located Value)
    apply-spine v List.[] = return v 
    apply-spine v ((u , i) List.∷ sp) = do 
      v₁ ← apply-spine v sp 
      apply v₁ i u

  -- | Try applying a term to another, but only succeeds if either:
  --
  --   * The term is a rigid/flexible variable
  --   * The term is a lambda abstraction
  apply : Located Value → Implicitness → Located Value → Elaborator (Located Value)
  apply (TAST.V-λ _ _ _ _ clos at _) _ v = open-and-eval v clos
  apply (TAST.V-flexible x sp at p) imp v = return $ TAST.V-flexible x ((v , imp) List.∷ sp) at p
  apply (TAST.V-rigid x name sp at p) imp v = return $ TAST.V-rigid x name ((v , imp) List.∷ sp) at p
  apply f _ x = liftE $ throwError $ InternalError $ InvalidApplication f x

  -- | Destroy a closure and evaluate the term within, while adding a new value to the environment.
  --
  --   The new value added to the environment is always a variable binding.
  --
  --   For example, let's say that the closure @C[τ]@ comes from the original term @(x : A) → τ@.
  --   In order to evaluate @τ@, we have to know what @x@ is. 
  --   Thus closures allow us to "delay" the evaluation of @τ@ right when we know what @x@ actually is at some point.
  --   This new value represents the part "what @x@ actually is".
  open-and-eval : Located Value → Closure → Elaborator (Located Value)
  open-and-eval v ⟨ env ⟦ e ⟧⟩ = eval (Env.extend v env) e

  -- | Reduce a given chunk of code into a term in normal form.
  --
  --   Note: this may not terminate on unbounded recursive calls.
  {-# NON_TERMINATING #-}
  eval : ∀ {n} → Environment n → Located Expression → Elaborator (Located Value)
  eval _ (TAST.E-integer n ty at p) = return $ TAST.V-integer n ty at p
  eval _ (TAST.E-character c at p) = return $ TAST.V-character c at p
  eval _ (TAST.E-boolean b at p) = return $ (if b then TAST.V-true else TAST.V-false) at p
  eval _ (TAST.E-type at p) = return $ TAST.V-type at p
  eval _ (TAST.E-⊗unit at p) = return $ TAST.V-⊗unit at p 
  eval _ (TAST.E-&unit at p) = return $ TAST.V-&unit at p 
  eval _ (TAST.E-⊤ at p) = return $ TAST.V-⊤ at p
  eval _ (TAST.E-one at p) = return $ TAST.V-one at p
  eval _ (TAST.E-builtin ty at p) = return $ TAST.V-builtin ty at p
  eval env (TAST.E-identifier name idx at p) = evalIfNeeded $ Env.lookup env idx
    where 
      evalIfNeeded : _
      evalIfNeeded nothing = liftE $ throwError (UnboundVariableIndex name idx p)
      evalIfNeeded (just (TAST.V⟦ e ⟧ at _)) = eval env e 
      evalIfNeeded (just v) = return v
  eval env ((TAST.E-if cond then t else e) at p) = do 
    cond ← eval env cond 
    -- the type-level is pure so this is ok
    -- and because we are compiling to lazy haskell, both will not necessarily be evaluated
    t ← eval env t 
    e ← eval env e
    performIf cond t e 
    where 
      performIf : Located Value → Located Value → Located Value → Elaborator (Located Value)
      performIf (TAST.V-true at _) t _ = return t
      performIf (TAST.V-false at _) _ e = return e 
      performIf cond t e = return $ (TAST.V-if cond then t else e) at p
  eval env (TAST.E-fst x at p) = do 
    x ← eval env x
    performFST x
    where 
      performFST : Located Value → Elaborator (Located Value)
      performFST ((fst TAST.V-⊗, _) at _) = return fst 
      -- this case should /not/ really happen, but turns out it does...
      performFST ((fst TAST.V-&, _) at _) = return fst 
      performFST e = return $ TAST.V-fst e at p
  eval env (TAST.E-snd x at p) = do 
    x ← eval env x
    performSND x
    where 
      performSND : Located Value → Elaborator (Located Value)
      performSND ((_ TAST.V-⊗, snd) at _) = return snd 
      -- this case should /not/ really happen, but turns out it does...
      performSND ((_ TAST.V-&, snd) at _) = return snd
      performSND e = return $ TAST.V-snd e at p
  eval env ((TAST.E-λ (TAST.Param isImp mult name τ₁ at _) , e) at p) = do 
    τ₁ ← eval env τ₁
    let clos = ⟨ env ⟦ e ⟧⟩
    return $ TAST.V-λ mult name isImp τ₁ clos at p
  eval env ((TAST.E-Π (TAST.Param isImp mult name τ₁ at _) , e) at p) = do
    τ₁ ← eval env τ₁
    let clos = ⟨ env ⟦ e ⟧⟩
    return $ TAST.V-Π mult name isImp τ₁ clos at p
  eval env (((TAST.Param _ mult name τ₁ at _) TAST.E-⊗ e) at p) = do 
    τ₁ ← eval env τ₁
    let clos = ⟨ env ⟦ e ⟧⟩
    return $ TAST.V-⊗ mult name τ₁ clos at p
  eval env (((TAST.Param _ _ name τ₁ at _) TAST.E-& e) at p) = do 
    τ₁ ← eval env τ₁
    let clos = ⟨ env ⟦ e ⟧⟩
    return $ TAST.V-& name τ₁ clos at p
  eval env ((x TAST.E-⊗, y) at p) = do 
    x ← eval env x 
    y ← eval env y
    return $ (x TAST.V-⊗, y) at p 
  eval env ((x TAST.E-&, y) at p) = do 
    x ← eval env x 
    y ← eval env y
    return $ (x TAST.V-&, y) at p
  eval _ (TAST.E-meta idx at p) = meta-value idx p
  eval env (TAST.E-⊗unit-elim nothing _ _ n at _) = 
    -- don't care about the value of 'm' because it is a pure '⊗-unit' '()'
    eval env n 
  eval env (TAST.E-⊗unit-elim (just _) _ m n at _) = do 
    m ← eval env m 
    -- in case we bind 'z', bind it in 'n'
    eval (Env.extend m env) n
  eval env (TAST.E-⊗,-elim nothing _ _ _ m@(_ at p) n at _) = do 
    x ← eval env (TAST.E-fst m at p)
    y ← eval env (TAST.E-snd m at p)
    eval (Env.extend y $ Env.extend x env) n 
  eval env (TAST.E-⊗,-elim (just _) _ _ _ m@(_ at p) n at _) = do 
    m′ ← eval env m 
    x ← eval env (TAST.E-fst m at p)
    y ← eval env (TAST.E-snd m at p)
    -- in case we want 'z', bind it *first* in 'n'
    eval (Env.extend y $ Env.extend x $ Env.extend m′ env) n 
  eval env (TAST.E-application f imp x@(_ at p) at _) = do 
    f ← eval env f 
    apply f imp (TAST.V⟦ x ⟧ at p)
  eval {n₁} env (TAST.E-insmeta {n₂} m path at p) = do 
    v ← meta-value m p 
    if′ eqNat n₁ n₂
      then apply-path env path v 
      else liftE (throwError $ InternalError $ InconsistentPathWithEnv n₁ n₂)
  eval env (TAST.E-let (TAST.D-let false _ _ _ v at _) _ e at _) = do 
    v ← eval env v 
    eval (Env.extend v env) e
  eval env (TAST.E-let (TAST.D-let true _ _ _ v@(_ at p) at _) _ e at _) = do 
    -- when evaluating a recursive definition, we actually don't evaluate 'v' directly
    -- instead, we put it in a thunk "for later"
    --
    -- if we were to evaluate the recursive call in 'e', it would be forced as needed.
    eval (Env.extend (TAST.V⟦ v ⟧ at p) env) e

-- | Try to force metavariables so as to solve them with the value they were found
--   to be equal to.
--
--   Does nothing for all othet terms.
{-# TERMINATING #-}
force : Located Value → Elaborator (Located Value)
force t@(TAST.V-flexible m sp at p) = do 
  lookup-meta m >>= λ where 
    (_ , Solved t _ _ , _ , _) → force =<< apply-spine (t at p) sp 
    _ → return t 
force t = return t

-- | An alias for 'force'.
⇓_ : Located Value → Elaborator (Located Value)
⇓_ = force 

-- | An alias for 'eval'.
[_]↝_ : ∀ {n} → Environment n → Located Expression → Elaborator (Located Value)
[_]↝_ = eval