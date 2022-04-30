{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Typecheck.Checker (checkProgram, check) where

import Control.Monad (unless, when)
import Control.Monad.Except (throwError)
import Data.Located (Located ((:@)))
import qualified Language.Zilch.Syntax.Core.AST as AST
import Language.Zilch.Typecheck.Context
import qualified Language.Zilch.Typecheck.Core.AST as TAST
import Language.Zilch.Typecheck.Core.Eval (DeBruijnLvl, Value (..))
import {-# SOURCE #-} Language.Zilch.Typecheck.Elaborator (MonadElab)
import Language.Zilch.Typecheck.Errors (ElabError (TypesAreNotEqual))
import Language.Zilch.Typecheck.Evaluator (apply, eval, plugNormalisation, quote)
import {-# SOURCE #-} Language.Zilch.Typecheck.Synthetizer

checkProgram :: forall m. MonadElab m => Context -> Located AST.Module -> m (Located TAST.Module)
checkProgram ctx (AST.Mod imports defs :@ p) = do
  case defs of
    [] -> do
      pure (TAST.Mod [] :@ p)
    ((AST.TopLevel isPublic (AST.Let isRec name ty ex :@ p3) :@ p4) : ds) -> do
      when isRec do
        error "Recursive bindings are not yet handled"

      ty <- check ctx ty (VType :@ p3)
      ty' <- plugNormalisation $ eval ctx ty

      ex <- check ctx ex ty'
      ex' <- plugNormalisation $ eval ctx ex

      TAST.Mod defs :@ p <- checkProgram (define name ex' ty' ctx) (AST.Mod imports ds :@ p)

      pure (TAST.Mod ((TAST.TopLevel [] isPublic (TAST.Let isRec name ty ex :@ p3) :@ p4) : defs) :@ p)

-- | @Ρ, Γ ⊢ e ⇐ τ@
check :: forall m. MonadElab m => Context -> Located AST.Expression -> Located Value -> m (Located TAST.Expression)
check ctx expr ty =
  case (expr, ty) of
    (AST.ELam (AST.Parameter isImplicit x ty :@ p1) expr :@ p3, VPi _ ty2 ty3 :@ p2) -> do
      {-
          Ρ, Γ, x : A ⊢ e ⇐ B[y\z]
        ─────────────────────────────
          Ρ, Γ ⊢ λx.e ⇐ (y : A) → B
      -}
      ty <- check ctx ty (VType :@ p1)
      ty3' <- plugNormalisation $ apply ctx ty3 (VIdentifier (lvl ctx) :@ p2)
      u <- check (bind x ty2 ctx) expr ty3'
      -- TODO: unify `ty` with `ty2`
      pure (TAST.ELam u :@ p3)
    (AST.ELet (AST.Let False x ty ex :@ p1) expr :@ p2, ty2) -> do
      {-
          Ρ, Γ ⊢ A ⇐ type      Ρ, Γ ⊢ e₁ ⇐ A         Ρ, Γ, x : A ⊢ e₂ ⇐ B
        ───────────────────────────────────────────────────────────────────
                        Ρ, Γ ⊢ let x : A = e₁ ; e₂ ⇐ B
      -}
      ty <- check ctx ty (VType :@ p1)
      ty' <- plugNormalisation $ eval ctx ty
      ex <- check ctx ex ty'
      ex' <- plugNormalisation $ eval ctx ex
      u <- check (define x ex' ty' ctx) expr ty2
      pure (TAST.ELet (TAST.Let False x ty ex :@ p1) u :@ p2)
    (e@(_ :@ p), v) -> do
      {-
          Ρ, Γ ⊢ e ⇒ τ₁          τ₁ ~ τ₂
        ──────────────────────────────────
                  Ρ, Γ ⊢ e ⇐ τ₂
      -}
      (e, ty) <- synthetize ctx e
      convertibleTo ctx ty v >>= flip unless do
        (ty, v) <- plugNormalisation do
          (,) <$> quote ctx (lvl ctx) ty <*> quote ctx (lvl ctx) v
        throwError $ TypesAreNotEqual ty v p
      pure e

convertibleTo :: forall m. MonadElab m => Context -> Located Value -> Located Value -> m Bool
convertibleTo _ (VType :@ _) (VType :@ _) = pure True
convertibleTo ctx (VPi _ a b :@ p1) (VPi _ a' b' :@ p2) = do
  (b, b') <-
    plugNormalisation do
      (,)
        <$> apply ctx b (VIdentifier (lvl ctx) :@ p1)
        <*> apply ctx b' (VIdentifier (lvl ctx) :@ p2)

  (&&)
    <$> convertibleTo ctx a a'
    <*> convertibleTo (ctx {lvl = lvl ctx + 1}) b b'
convertibleTo ctx (VLam a :@ p1) (VLam a' :@ p2) = do
  (a, a') <- plugNormalisation do
    (,)
      <$> apply ctx a (VIdentifier (lvl ctx) :@ p1)
      <*> apply ctx a' (VIdentifier (lvl ctx) :@ p2)

  convertibleTo (ctx {lvl = lvl ctx + 1}) a a'
convertibleTo ctx (VLam a :@ p1) u@(_ :@ p2) = do
  a <- plugNormalisation $ apply ctx a (VIdentifier (lvl ctx) :@ p1)
  convertibleTo (ctx {lvl = lvl ctx + 1}) a (VApplication u (VIdentifier (lvl ctx) :@ p2) :@ p2)
convertibleTo ctx u@(_ :@ p1) (VLam a :@ p2) = do
  a <- plugNormalisation $ apply ctx a (VIdentifier (lvl ctx) :@ p2)
  convertibleTo (ctx {lvl = lvl ctx + 1}) (VApplication u (VIdentifier (lvl ctx) :@ p1) :@ p1) a
convertibleTo _ (VIdentifier l1 :@ _) (VIdentifier l2 :@ _) = pure $ l1 == l2
convertibleTo ctx (VApplication v1 v2 :@ _) (VApplication v3 v4 :@ _) =
  (&&)
    <$> convertibleTo ctx v1 v3
    <*> convertibleTo ctx v2 v4
convertibleTo _ _ _ = pure False
