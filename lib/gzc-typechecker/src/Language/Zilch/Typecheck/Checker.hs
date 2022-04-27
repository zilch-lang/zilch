{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Typecheck.Checker (checkProgram, check) where

import Control.Monad (forM_, when)
import qualified Data.IntMap as IntMap
import Data.Located (Located ((:@)))
import Data.Tuple (swap)
import Debug.Trace (trace)
import qualified Language.Zilch.Syntax.Core.AST as AST
import Language.Zilch.Typecheck.Context
import qualified Language.Zilch.Typecheck.Core.AST as TAST
import Language.Zilch.Typecheck.Core.Eval (MetaEntry (Solved, Unsolved), Value (..))
import {-# SOURCE #-} Language.Zilch.Typecheck.Elaborator (MonadElab)
import Language.Zilch.Typecheck.Evaluator (apply, eval, force, plugNormalisation, quote)
import {-# SOURCE #-} Language.Zilch.Typecheck.Synthetizer
import {-# SOURCE #-} Language.Zilch.Typecheck.Unification (unify)
import Prettyprinter (pretty)

checkProgram :: forall m. MonadElab m => Context -> Located AST.Module -> m (Located TAST.Module)
checkProgram ctx (AST.Mod imports defs :@ p) = do
  case defs of
    [] -> do
      showMetas ctx
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
  where
    showMetas ctx =
      forM_ (metas ()) \(m, ty) -> do
        let str = "let ?" <> show m <> " := "
        str <-
          mappend str <$> case ty of
            Solved v -> show . pretty <$> plugNormalisation do quote ctx (lvl ctx) v
            Unsolved -> pure "?"
        trace str $ pure ()

-- | @Ρ, Γ ⊢ e ⇐ τ@
check :: forall m. MonadElab m => Context -> Located AST.Expression -> Located Value -> m (Located TAST.Expression)
check ctx expr ty =
  plugNormalisation ((expr,) <$> force ctx ty) >>= \case
    (AST.ELam (AST.Parameter isImplicit x ty :@ p1) expr :@ p3, VPi _ ty2 ty3 :@ p2) -> do
      {-
          Ρ, Γ, x : A ⊢ e ⇐ B[y\z]
        ─────────────────────────────
          Ρ, Γ ⊢ λx.e ⇐ (y : A) → B
      -}
      ty <- check ctx ty (VType :@ p1)
      ty3' <- plugNormalisation $ apply ctx ty3 (VIdentifier (lvl ctx) [] :@ p2)
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
    (AST.EHole :@ p, _) -> do
      let m = freshMeta ctx p
      trace ("Ρ, Γ ⊢ _ ⇐ ?" <> show m) $ pure ()
      pure m
    (e, v) -> do
      {-
          Ρ, Γ ⊢ e ⇒ τ₁          τ₁ ~ τ₂
        ──────────────────────────────────
                  Ρ, Γ ⊢ e ⇐ τ₂
      -}
      (e, ty) <- synthetize ctx e
      unify ctx v ty
      pure e
