{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Zilch.Typecheck.Synthetizer where

import Control.Monad.Except (throwError)
import Data.Located (Located ((:@)), Position)
import Debug.Trace (traceShow)
import Language.Zilch.Syntax.Core.AST (Definition (..), Expression (..), Parameter (..))
import {-# SOURCE #-} Language.Zilch.Typecheck.Checker (check)
import Language.Zilch.Typecheck.Context
import qualified Language.Zilch.Typecheck.Context as Ctx
import Language.Zilch.Typecheck.Core.Eval (Environment, Value (..))
import {-# SOURCE #-} Language.Zilch.Typecheck.Elaborator (MonadElab)
import qualified Language.Zilch.Typecheck.Environment as Env
import Language.Zilch.Typecheck.Errors
import Language.Zilch.Typecheck.Evaluator (apply, eval, plugNormalisation, quote)
import Prelude hiding (lookup)

-- | @Ρ, Γ ⊢ e ⇒ τ@
synthetize :: forall m. MonadElab m => Environment -> Context -> Located Expression -> m (Located Value)
synthetize _ _ (EInteger _ :@ p) =
  {-
      n is a literal number
    ─────────────────────────
         Ρ, Γ ⊢ n ⇒ ℕ
  -}
  pure $ VIdentifier "nat" :@ p
synthetize _ _ (ECharacter _ :@ p) =
  {-
      c is a literal character
    ────────────────────────────
          Ρ, Γ ⊢ c ⇒ char
  -}
  pure $ VIdentifier "char" :@ p
synthetize env ctx (EApplication e1 e2 :@ p) = do
  {-
      Ρ, Γ ⊢ e₁ ⇒ (x : A) → B          Ρ, Γ ⊢ e₂ ⇐ A
    ───────────────────────────────────────────────────
                  Ρ, Γ ⊢ (e₁ e₂) ⇒ B
  -}
  synthetize env ctx e1 >>= \case
    VPi x argTy bodyTy :@ _ -> do
      check env ctx e2 argTy
      plugNormalisation do
        arg <- eval env e2
        apply bodyTy x arg
    ty -> do
      ty' <- plugNormalisation do quote env ty
      throwError $ PiTypeExpected ty' p
synthetize _ ctx (EIdentifier (x :@ _) :@ p) =
  {-
    ───────────────────────
      Ρ, Γ, x : A ⊢ x ⇒ A
  -}
  maybe (throwError $ BindingNotFound x p) pure (lookup ctx x)
synthetize _ _ (EType :@ p) =
  {-
    ──────────────────────
      Ρ, Γ ⊢ type ⇒ type
  -}
  pure $ VType :@ p
synthetize env ctx (EPi (Parameter _ (name :@ p1) ty :@ _) expr :@ p) = do
  {-
      Ρ, Γ ⊢ A ⇐ type       Ρ, Γ ⊢ B ⇐ type
    ────────────────────────────────────────
         Ρ, Γ ⊢ (x : A) → B ⇒ type
  -}
  check env ctx ty (VType :@ p)
  ty' <- plugNormalisation $ eval env ty
  check (Env.extend env name (VIdentifier name :@ p1)) (Ctx.extend ctx name ty') expr (VType :@ p)
  pure $ VType :@ p
synthetize env ctx (ELet (Let _ (name :@ _) ty val :@ _) expr :@ p) = do
  {-
      Ρ, Γ ⊢ A ⇐ type        Ρ, Γ ⊢ e₁ ⇐ A        Ρ, Γ, x : A ⊢ e₂ ⇐ B
    ────────────────────────────────────────────────────────────────────
                    Ρ, Γ ⊢ let x : A = e₁ ; e₂ ⇒ B
  -}
  check env ctx ty (VType :@ p)
  ty' <- plugNormalisation $ eval env ty
  check env ctx val ty'
  val' <- plugNormalisation $ eval env val
  synthetize (Env.extend env name val') (Ctx.extend ctx name ty') expr
synthetize _ _ expr = error $ "not yet handled: " <> show expr
