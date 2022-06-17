{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecursiveDo #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Typecheck.Checker (checkProgram, check) where

import Control.Monad (forM, guard, unless, when)
import Control.Monad.Except (throwError)
import Data.IORef (readIORef)
import qualified Data.IntMap as IntMap
import Data.Located (Located ((:@)), getPos, unLoc)
import Debug.Trace (traceShow)
import qualified Language.Zilch.Syntax.Core.AST as AST
import Language.Zilch.Typecheck.Context
import qualified Language.Zilch.Typecheck.Core.AST as TAST
import Language.Zilch.Typecheck.Core.Eval (DeBruijnLvl, MetaEntry (Solved, Unsolved), Value (..))
import {-# SOURCE #-} Language.Zilch.Typecheck.Elaborator (MonadElab)
import Language.Zilch.Typecheck.Errors (ElabError (TypesAreNotEqual, UnusedLinearVariable))
import Language.Zilch.Typecheck.Evaluator (apply, eval, force, plugNormalisation, quote)
import Language.Zilch.Typecheck.Metavariables (mcxt, nextMeta)
import {-# SOURCE #-} Language.Zilch.Typecheck.Synthetizer
import Language.Zilch.Typecheck.Unification (freshMeta, unify, unifyUsage)
import System.IO.Unsafe (unsafePerformIO)

checkProgram :: forall m. MonadElab m => Context -> Located AST.Module -> m (Located TAST.Module)
checkProgram ctx mod = do
  TAST.Mod binds :@ p <- checkProgram' ctx mod

  let metas = unsafePerformIO $ IntMap.toList <$> readIORef mcxt
  addBinds <- forM metas \(m, e) -> do
    case e of
      Unsolved -> pure (TAST.LetMeta m Nothing :@ p)
      Solved val -> do
        val@(_ :@ p1) <- plugNormalisation do quote ctx (lvl ctx) (val :@ p)
        pure (TAST.LetMeta m (Just val) :@ p1)
  let addBinds' = (:@ p) . TAST.TopLevel [] False <$> addBinds

  pure $ TAST.Mod (addBinds' <> binds) :@ p

checkProgram' :: forall m. MonadElab m => Context -> Located AST.Module -> m (Located TAST.Module)
checkProgram' ctx (AST.Mod imports defs :@ p) = do
  case defs of
    [] -> do
      pure (TAST.Mod [] :@ p)
    ((AST.TopLevel isPublic (AST.Let isRec name@(_ :@ p5) ty ex :@ p3) :@ p4) : ds) -> do
      (_, ty) <- check (scale ctx TAST.Erased) (TAST.Erased :@ p4) ty (VType :@ p3)
      ty' <- plugNormalisation $ eval ctx ty

      (ex, ex') <- mdo
        let ctx' = if isRec then define TAST.Unrestricted name (VThunk ex' :@ p3) ty' ctx else ctx
        (_, ex') <- check ctx' (TAST.Unrestricted :@ p5) ex ty'
        ex'' <- plugNormalisation $ eval ctx' ex'
        pure (ex', ex'')

      TAST.Mod defs :@ p <- checkProgram' (define TAST.Unrestricted name ex' ty' ctx) (AST.Mod imports ds :@ p)

      pure (TAST.Mod ((TAST.TopLevel [] isPublic (TAST.Let isRec name ty ex :@ p3) :@ p4) : defs) :@ p)

-- | @Ρ, Γ ⊢ e ⇐ τ@
check :: forall m. MonadElab m => Context -> Located TAST.Usage -> Located AST.Expression -> Located Value -> m (Context, Located TAST.Expression)
check ctx usage expr ty = do
  ty <- plugNormalisation $ force ctx ty
  case (expr, ty) of
    (AST.ELam (AST.Parameter isImplicit u1 x ty :@ p1) expr :@ p3, VPi u2 _ ty2 ty3 :@ p2) -> do
      {-
          0Γ ⊢ (y :^π A) → B ⇐^0 type ℓ       Γ, x :^σπ A ⊢ e ⇐^σ B
        ─────────────────────────────────────────────────────────────
                  Γ ⊢ λ(x :^π A) → e ⇐^σ (y :^π A) → B
      -}
      unifyUsage u1 (u2 :@ p2)
      (_, ty) <- check (scale ctx TAST.Erased) (TAST.Erased :@ p2) ty (VType :@ p1)
      ty3' <- plugNormalisation $ apply ctx ty3 (VVariable x (lvl ctx) :@ p2)

      let xUsage = unLoc usage * unLoc u1

      (ctx', u) <- check (bind xUsage x ty2 ctx) usage expr ty3'

      when (xUsage == TAST.Linear) do
        let xUsage = indexContext ctx' x
        when (xUsage == TAST.Linear) do
          throwError $ UnusedLinearVariable x (getPos expr)

      ty' <- plugNormalisation $ eval ctx ty
      unify ctx ty' ty2
      pure (unbind ctx', TAST.ELam (TAST.Parameter isImplicit u1 x ty :@ p1) u :@ p3)
    (AST.ELet (AST.Let False x ty ex :@ p1) expr :@ p2, ty2) -> do
      {-
           0Γ ⊢ A ⇐^0 type ℓ₁                 Γ ⊢ e₁ ⇐^σ A
          Γ, x :^σ A ⊢ e₂ ⇐^π B        0Γ, x :^0 A ⊢ B ⇐^0 type ℓ₂
        ────────────────────────────────────────────────────────────
                      Γ ⊢ let x :^σ A = e₁ ; e₂ ⇐^π B
      -}
      (_, ty) <- check (scale ctx TAST.Erased) (TAST.Erased :@ p1) ty (VType :@ p1)
      ty' <- plugNormalisation $ eval ctx ty
      (_, ex) <- check ctx (TAST.Unrestricted :@ p1) ex ty'
      ex' <- plugNormalisation $ eval ctx ex
      (ctx', u) <- check (define TAST.Unrestricted x ex' ty' ctx) usage expr ty2
      -- TODO: add usage in AST for `x` and check if used when linear
      pure (unbind ctx', TAST.ELet (TAST.Let False x ty ex :@ p1) u :@ p2)
    (AST.ELet (AST.Let True x ty ex :@ p1) expr :@ p2, ty2) -> do
      {-
           0Γ ⊢ A ⇐^0 type ℓ₁             Γ, x :^σ' A ⊢ e₁ ⇐^σ A
          Γ, x :^σ A ⊢ e₂ ⇐^π B        0Γ, x :^0 A ⊢ B ⇐^0 type ℓ₂
                         σ' = ω if σ ≠ 0 else 0
        ────────────────────────────────────────────────────────────
                      Γ ⊢ rec x :^σ A = e₁ ; e₂ ⇐^π B
      -}
      (_, ty) <- check (scale ctx TAST.Erased) (TAST.Erased :@ p1) ty (VType :@ p1)
      ty' <- plugNormalisation $ eval ctx ty

      (ex, ex') <- mdo
        let ctx' = define TAST.Unrestricted x (VThunk ex' :@ p1) ty' ctx
        -- TODO: put correct usage for recursive call
        (ctx'', ex') <- check ctx' (TAST.Unrestricted :@ p1) ex ty'
        -- TODO: add usage check for `x` in ctx'' if it is linear

        ex'' <- plugNormalisation $ eval ctx' ex'
        pure (ex', ex'')
      (ctx', u) <- check (define TAST.Unrestricted x ex' ty' ctx) usage expr ty2
      -- TODO: check that local binding has been used if linear
      pure (unbind ctx', TAST.ELet (TAST.Let False x ty ex :@ p1) u :@ p2)
    (AST.EPi (AST.Parameter isImplicit u1 x ty :@ p1) ty2 :@ p2, VType :@ p3) -> do
      {-
          0Γ ⊢ S ⇐^0 type ℓ₁          0Γ, x :^0 A ⊢ B ⇐^0 type ℓ₂
        ───────────────────────────────────────────────────────────
                0Γ ⊢ (x :^σ S) -> T ⇐^0 type (ℓ₁ ⊔ ℓ₂)
      -}
      unifyUsage (TAST.Erased :@ p2) usage
      let ctx' = scale ctx TAST.Erased
      (_, ty) <- check ctx' (TAST.Erased :@ p1) ty (VType :@ p1)
      ty' <- plugNormalisation $ eval ctx' ty
      (_, ty2) <- check (bind TAST.Erased x ty' ctx') (TAST.Erased :@ p1) ty2 (VType :@ p2)
      pure (ctx, TAST.EPi (TAST.Parameter isImplicit u1 x ty :@ p1) ty2 :@ p2)
    (AST.EHole :@ p1, _) -> do
      pure (ctx, freshMeta ctx :@ p1)
    (e@(_ :@ p), v) -> do
      {-
          Γ ⊢ e ⇒ τ₁          τ₁ ≡ τ₂
        ───────────────────────────────
                 Γ ⊢ e ⇐ τ₂
      -}
      (ctx', e, ty, u1) <- synthetize ctx e

      -- traceShow (show e <> " ⇐^" <> show u1 <> " " <> show ty) $ pure ()
      -- traceShow ("Expected :^" <> show usage <> " " <> show v) $ pure ()

      unifyUsage usage u1
      unify ctx' v ty
      pure (ctx', e)
