{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.Zilch.Typecheck.Checker (check) where

import Control.Monad (unless)
import Control.Monad.Except (throwError)
import Data.Located (Located ((:@)), Position)
import Debug.Trace (traceShow)
import Language.Zilch.Syntax.Core.AST (Definition (..), Expression (..), Parameter (Parameter))
import Language.Zilch.Typecheck.Context
import qualified Language.Zilch.Typecheck.Context as Ctx
import Language.Zilch.Typecheck.Core.Eval (Environment, Value (..))
import Language.Zilch.Typecheck.Elaborator (MonadElab)
import qualified Language.Zilch.Typecheck.Environment as Env
import Language.Zilch.Typecheck.Errors
import Language.Zilch.Typecheck.Evaluator (apply, eval, plugNormalisation, quote)
import Language.Zilch.Typecheck.Fresh (fresh)
import {-# SOURCE #-} Language.Zilch.Typecheck.Synthetizer

-- | @Ρ, Γ ⊢ e ⇐ τ@
check :: forall m. MonadElab m => Environment -> Context -> Located Expression -> Located Value -> m ()
check env ctx (ELam (Parameter _ (x :@ _) _ :@ _) expr :@ _) (VPi y ty2 ty3 :@ p2) = do
  {-
      Ρ, Γ, x : A ⊢ e ⇐ B[y\z]
    ─────────────────────────────
      Ρ, Γ ⊢ λx.e ⇐ (y : A) → B
  -}
  let x' = fresh env y
  ty3' <- plugNormalisation $ apply ty3 y (VIdentifier x' :@ p2)
  check (Env.extend env x (VIdentifier x' :@ p2)) (Ctx.extend ctx x ty2) expr ty3'
check env ctx (ELet (Let False (x :@ _) ty ex :@ p1) expr :@ _) ty2 = do
  {-
      Ρ, Γ ⊢ A ⇐ type      Ρ, Γ ⊢ e₁ ⇐ A         Ρ, Γ, x : A ⊢ e₂ ⇐ B
    ───────────────────────────────────────────────────────────────────
                    Ρ, Γ ⊢ let x : A = e₁ ; e₂ ⇐ B
  -}
  check env ctx ty (VType :@ p1)
  ty' <- plugNormalisation $ eval env ty
  check env ctx ex ty'
  ex' <- plugNormalisation $ eval env ex
  check (Env.extend env x ex') (Ctx.extend ctx x ty') expr ty2
check env ctx e@(_ :@ p) v = do
  {-
      Ρ, Γ ⊢ e ⇒ τ₁          τ₁ ~ τ₂
    ──────────────────────────────────
              Ρ, Γ ⊢ e ⇐ τ₂
  -}
  ty <- synthetize env ctx e
  convertibleTo env ty v >>= \true -> unless true do
    (ty', v') <- plugNormalisation do
      (,)
        <$> quote env ty
        <*> quote env v
    throwError $ TypesAreNotEqual ty' v' p

------------------------------------

-- | beta-eta conversion checking @τ₁ ~ τ₂@
convertibleTo :: forall m. MonadElab m => Environment -> Located Value -> Located Value -> m Bool
convertibleTo _ (VType :@ _) (VType :@ _) =
  {-
    ───────────────
      type ~ type
  -}
  pure True
convertibleTo env (VPi x1 a1 b1 :@ p1) (VPi x2 a2 b2 :@ _) = do
  {-
      A ~ C         B[x\z] ~ D[y\z]
    ─────────────────────────────────
        (x : A) → B ~ (y : C) → D
  -}

  let x1' = fresh env x1

  b1' <- plugNormalisation $ apply b1 x1 (VIdentifier x1' :@ p1)
  b2' <- plugNormalisation $ apply b2 x2 (VIdentifier x1' :@ p1)

  (&&)
    <$> convertibleTo env a1 a2
    <*> convertibleTo (Env.extend env x1' (VIdentifier x1' :@ p1)) b1' b2'
convertibleTo env (VLam x1 t1 :@ p1) (VLam x2 t2 :@ _) = do
  {-
      t₁[x\z] ~ t₂[y\z]
    ─────────────────────
       λx.t₁ ~ λy.t₂
  -}
  let x1' = fresh env x1

  t1' <- plugNormalisation $ apply t1 x1 (VIdentifier x1' :@ p1)
  t2' <- plugNormalisation $ apply t2 x2 (VIdentifier x1' :@ p1)

  convertibleTo (Env.extend env x1' (VIdentifier x1' :@ p1)) t1' t2'
-- next two cases : eta conversion for lambdas
convertibleTo env (VLam x t :@ p1) u = do
  {-
      t₁[x\z] ~ (u z)
    ───────────────────
        λx.t₁ ~ u
  -}
  let x' = fresh env x

  t' <- plugNormalisation $ apply t x (VIdentifier x' :@ p1)

  convertibleTo (Env.extend env x' (VIdentifier x' :@ p1)) t' (VApplication u (VIdentifier x' :@ p1) :@ p1)
convertibleTo env u (VLam x t :@ p1) = do
  {-
      (u z) ~ t₁[x\z]
    ───────────────────
        u ~ λx.t₁
  -}
  let x' = fresh env x

  t' <- plugNormalisation $ apply t x (VIdentifier x' :@ p1)

  convertibleTo (Env.extend env x' (VIdentifier x' :@ p1)) (VApplication u (VIdentifier x' :@ p1) :@ p1) t'
convertibleTo _ (VIdentifier x1 :@ _) (VIdentifier x2 :@ _) =
  {-
    ─────────
      x ~ x
  -}
  pure $ x1 == x2
convertibleTo env (VApplication v1 v2 :@ _) (VApplication v3 v4 :@ _) =
  {-
      e₁ ~ e₃        e₂ ~ e₄
    ──────────────────────────
        (e₁ e₂) ~ (e₃ e₄)
  -}
  (&&)
    <$> convertibleTo env v1 v3
    <*> convertibleTo env v2 v4
convertibleTo _ _ _ = pure False
