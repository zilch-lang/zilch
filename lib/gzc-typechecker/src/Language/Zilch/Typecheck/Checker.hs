{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecursiveDo #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Typecheck.Checker (checkProgram, check) where

import Control.Monad (forM, unless, when)
import Control.Monad.Except (throwError)
import Data.IORef (readIORef)
import qualified Data.IntMap as IntMap
import Data.Located (Located ((:@)), unLoc)
import qualified Language.Zilch.Syntax.Core.AST as AST
import Language.Zilch.Typecheck.Context
import qualified Language.Zilch.Typecheck.Core.AST as TAST
import Language.Zilch.Typecheck.Core.Eval (DeBruijnLvl, MetaEntry (Solved, Unsolved), Value (..))
import {-# SOURCE #-} Language.Zilch.Typecheck.Elaborator (MonadElab)
import Language.Zilch.Typecheck.Errors (ElabError (TypesAreNotEqual))
import Language.Zilch.Typecheck.Evaluator (apply, eval, force, plugNormalisation, quote)
import Language.Zilch.Typecheck.Metavariables (mcxt, nextMeta)
import {-# SOURCE #-} Language.Zilch.Typecheck.Synthetizer
import Language.Zilch.Typecheck.Unification (freshMeta, unify)
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
      ty <- check ctx ty (VType :@ p3)
      ty' <- plugNormalisation $ eval ctx ty

      (ex, ex') <- mdo
        let ctx' = if isRec then define name (VThunk ex' :@ p3) ty' ctx else ctx
        ex' <- check ctx' ex ty'
        ex'' <- plugNormalisation $ eval ctx' ex'
        pure (ex', ex'')

      TAST.Mod defs :@ p <- checkProgram' (define name ex' ty' ctx) (AST.Mod imports ds :@ p)

      pure (TAST.Mod ((TAST.TopLevel [] isPublic (TAST.Let isRec name ty ex :@ p3) :@ p4) : defs) :@ p)

-- | @Ρ, Γ ⊢ e ⇐ τ@
check :: forall m. MonadElab m => Context -> Located AST.Expression -> Located Value -> m (Located TAST.Expression)
check ctx expr ty = do
  ty <- plugNormalisation $ force ctx ty
  case (expr, ty) of
    (AST.ELam (AST.Parameter isImplicit x ty :@ p1) expr :@ p3, VPi _ ty2 ty3 :@ p2) -> do
      {-
          Ρ, Γ, x : A ⊢ e ⇐ B[y\z]
        ─────────────────────────────
          Ρ, Γ ⊢ λx.e ⇐ (y : A) → B
      -}
      ty <- check ctx ty (VType :@ p1)
      ty3' <- plugNormalisation $ apply ctx ty3 (VVariable x (lvl ctx) :@ p2)
      u <- check (bind x ty2 ctx) expr ty3'
      ty' <- plugNormalisation $ eval ctx ty
      unify ctx ty' ty2
      pure (TAST.ELam (TAST.Parameter isImplicit x ty :@ p1) u :@ p3)
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
    (AST.EHole :@ p1, ty) -> do
      pure $ freshMeta ctx :@ p1
    (e@(_ :@ p), v) -> do
      {-
          Ρ, Γ ⊢ e ⇒ τ₁          τ₁ ~ τ₂
        ──────────────────────────────────
                  Ρ, Γ ⊢ e ⇐ τ₂
      -}
      (e, ty) <- synthetize ctx e
      unify ctx v ty
      pure e
