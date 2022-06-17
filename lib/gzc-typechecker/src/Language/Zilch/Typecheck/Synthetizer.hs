{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecursiveDo #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Typecheck.Synthetizer where

import Control.Monad.Except (throwError)
import Data.Located (Located ((:@)), unLoc)
import Debug.Trace (trace)
import qualified Language.Zilch.Syntax.Core.AST as AST
import {-# SOURCE #-} Language.Zilch.Typecheck.Checker (check)
import Language.Zilch.Typecheck.Context
import qualified Language.Zilch.Typecheck.Core.AST as TAST
import Language.Zilch.Typecheck.Core.Eval (Closure (Clos), Value (..))
import {-# SOURCE #-} Language.Zilch.Typecheck.Elaborator (MonadElab)
import Language.Zilch.Typecheck.Errors
import Language.Zilch.Typecheck.Evaluator (apply, eval, force, plugNormalisation, quote)
import Language.Zilch.Typecheck.Unification (freshMeta, unify)
import Prelude hiding (lookup)

-- | @Ρ, Γ ⊢ e ⇒ τ@
synthetize :: forall m. MonadElab m => Context -> Located AST.Expression -> m (Located TAST.Expression, Located Value, Located TAST.Usage)
synthetize ctx (AST.EInteger i :@ p) =
  {-
      n is a literal number
    ─────────────────────────
          Γ ⊢ n ⇒^ω nat
  -}
  pure (TAST.EInteger i :@ p, VVariable ("nat" :@ p) 1 :@ p, TAST.Unrestricted :@ p)
synthetize ctx (AST.ECharacter c :@ p) =
  {-
      c is a literal character
    ────────────────────────────
           Γ ⊢ c ⇒^ω char
  -}
  pure (TAST.ECharacter c :@ p, VVariable ("char" :@ p) 0 :@ p, TAST.Unrestricted :@ p)
synthetize ctx (AST.EApplication e1@(_ :@ p1) e2 :@ p) = do
  {-
      Γ ⊢ e₁ ⇒^σ (x :^π A) → B        Γ ⊢ e₂ ⇐^σ' A
               σ' = 0 ⇔ (π = 0 ∨ σ = 0)
    ─────────────────────────────────────────────────
                Γ + πΓ ⊢ (e₁ e₂) ⇒^σ B
  -}
  (e1, t1, usage) <- synthetize ctx e1

  t1 <- plugNormalisation $ force ctx t1
  (u2, a, b) <- case t1 of
    VPi u _ a b :@ p2 -> pure (u :@ p2, a, b)
    t1@(_ :@ p2) -> do
      -- try η-expanding
      let usage = TAST.Erased
      a <- plugNormalisation $ eval ctx (freshMeta ctx :@ p)
      let b = Clos (env ctx) $ freshMeta (bind usage ("x?" :@ p) a ctx) :@ p
      unify ctx t1 (VPi usage "x?" a b :@ p)
      pure (usage :@ p2, a, b)

  e2 <- check ctx u2 e2 a
  t2 <- plugNormalisation do
    e2 <- eval ctx e2
    apply ctx b e2
  pure (TAST.EApplication e1 e2 :@ p, t2, usage)
synthetize ctx (AST.EIdentifier (x :@ _) :@ p) = do
  {-
    ────────────────────────
      Γ, x :^σ A ⊢ x ⇒^σ A
  -}
  (ex, ty, usage) <- go 0 (types ctx)
  pure (ex, ty, usage :@ p)
  where
    go _ [] = throwError $ BindingNotFound x p
    go ix ((usage, x', a) : types)
      | x == x' = pure (TAST.EIdentifier (x' :@ p) ix :@ p, a, usage)
      | otherwise = go (ix + 1) types
synthetize ctx (AST.EType :@ p) =
  {-
    ──────────────────────
      Γ ⊢ type ⇒^0 type
  -}
  pure (TAST.EType :@ p, VType :@ p, TAST.Linear :@ p)
synthetize ctx (AST.EPi (AST.Parameter isImplicit usage name ty :@ p2) expr :@ p) = do
  {-
      0Γ ⊢ A ⇐^0 type       0Γ, x :^0 A ⊢ B ⇐^0 type
    ──────────────────────────────────────────────────
               0Γ ⊢ (x :^σ A) → B ⇒^0 type
  -}
  let usage' = TAST.Erased
  ty <- check (scale ctx usage') usage ty (VType :@ p)
  ty' <- plugNormalisation $ eval ctx ty
  b <- check (scale (bind usage' name ty' ctx) usage') (usage' :@ p) expr (VType :@ p)
  pure (TAST.EPi (TAST.Parameter isImplicit usage name ty :@ p2) b :@ p, VType :@ p, usage' :@ p)
-- synthetize ctx (AST.ELet (AST.Let False (name :@ p1) ty val :@ p2) expr :@ p) = do
--   {-
--       Ρ, Γ ⊢ A ⇐ type        Ρ, Γ ⊢ e₁ ⇐ A        Ρ, Γ, x : A ⊢ e₂ ⇐ B
--     ────────────────────────────────────────────────────────────────────
--                     Ρ, Γ ⊢ let x : A = e₁ ; e₂ ⇒ B
--   -}
--   ty <- check ctx ty (VType :@ p)
--   ty' <- plugNormalisation $ eval ctx ty
--   val <- check ctx val ty'
--   val' <- plugNormalisation $ eval ctx val
--   (u, b) <- synthetize (define (name :@ p1) val' ty' ctx) expr
--   pure (TAST.ELet (TAST.Let False (name :@ p1) ty val :@ p2) u :@ p, b)
-- synthetize ctx (AST.ELet (AST.Let True (name :@ p1) ty val :@ p2) expr :@ p) = do
--   {-
--       Ρ, Γ ⊢ A ⇐ type        Ρ, Γ, x : A ⊢ e₁ ⇐ A        Ρ, Γ, x : A ⊢ e₂ ⇐ B
--     ───────────────────────────────────────────────────────────────────────────
--                          Ρ, Γ ⊢ rec x : A = e₁ ; e₂ ⇒ B
--   -}
--   ty <- check ctx ty (VType :@ p)
--   ty' <- plugNormalisation $ eval ctx ty

--   (val, val') <- mdo
--     let ctx' = define (name :@ p1) ty' (VThunk val' :@ p2) ctx
--     val' <- check ctx' val ty'
--     val'' <- plugNormalisation $ eval ctx' val'
--     pure (val', val'')
--   (u, b) <- synthetize (define (name :@ p1) val' ty' ctx) expr
--   pure (TAST.ELet (TAST.Let False (name :@ p1) ty val :@ p2) u :@ p, b)
synthetize ctx (AST.ELam (AST.Parameter isImplicit usage name ty :@ p2) ex :@ p) = do
  {-
      0Γ ⊢ A ⇐^0 type ℓ       Γ, x :^σπ A ⊢ e ⇒^σ B
    ─────────────────────────────────────────────────
          Γ ⊢ lam(x :^π A) → e ⇒^σ (x :^π A) → B
  -}
  ty <- check (scale ctx TAST.Erased) (TAST.Erased :@ p) ty (VType :@ p)
  ty' <- plugNormalisation $ eval ctx ty
  (ex, b, u2) <- synthetize (bind (unLoc usage) name ty' ctx) ex
  clos <- closeVal ctx b
  pure (TAST.ELam (TAST.Parameter isImplicit usage name ty :@ p2) ex :@ p, VPi (unLoc usage) (unLoc name) ty' clos :@ p, u2)
synthetize ctx (AST.EHole :@ p1) = do
  a <- plugNormalisation do eval ctx (freshMeta ctx :@ p1)
  let t = freshMeta ctx :@ p1
  pure (t, a, TAST.Unrestricted :@ p1)
synthetize _ expr = error $ "not yet handled: " <> show expr

closeVal :: forall m. MonadElab m => Context -> Located Value -> m Closure
closeVal ctx ty = do
  ty <- plugNormalisation $ quote ctx (lvl ctx + 1) ty
  pure $ Clos (env ctx) ty
