{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
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
import {-# SOURCE #-} Language.Zilch.Typecheck.Unification (unify)
import Prelude hiding (lookup)

-- | @Ρ, Γ ⊢ e ⇒ τ@
synthetize :: forall m. MonadElab m => Context -> Located AST.Expression -> m (Located TAST.Expression, Located Value)
synthetize ctx (AST.EInteger i :@ p) =
  {-
      n is a literal number
    ─────────────────────────
         Ρ, Γ ⊢ n ⇒ ℕ
  -}
  pure (TAST.EInteger i :@ p, VIdentifier 0 [] :@ p)
synthetize ctx (AST.ECharacter c :@ p) =
  {-
      c is a literal character
    ────────────────────────────
          Ρ, Γ ⊢ c ⇒ char
  -}
  pure (TAST.ECharacter c :@ p, VIdentifier 1 [] :@ p)
synthetize ctx (AST.EApplication e1 e2 :@ p) = do
  {-
      Ρ, Γ ⊢ e₁ ⇒ (x : A) → B          Ρ, Γ ⊢ e₂ ⇐ A
    ───────────────────────────────────────────────────
                  Ρ, Γ ⊢ (e₁ e₂) ⇒ B
  -}
  (e1, t1) <- synthetize ctx e1

  (a, b) <-
    plugNormalisation (force ctx t1) >>= \case
      VPi _ a b :@ _ -> pure (a, b)
      t1@(_ :@ p1) -> do
        let tmpVarName = "ɑ"
        let !m1 = freshMeta ctx p1
        a <- plugNormalisation $ eval ctx m1
        let !m2 = freshMeta (bind (tmpVarName :@ p1) a ctx) p1
        unify ctx t1 (VPi tmpVarName a (Clos (env ctx) m2) :@ p1)
        pure (a, Clos (env ctx) m2)

  e2 <- check ctx e2 a
  t3 <- plugNormalisation do
    c <- eval ctx e2
    apply ctx b c
  pure (TAST.EApplication e1 e2 :@ p, t3)
synthetize ctx (AST.EIdentifier (x :@ _) :@ p) = do
  {-
    ───────────────────────
      Ρ, Γ, x : A ⊢ x ⇒ A
  -}
  (ix, ty) <- go 0 (types ctx)
  pure (TAST.EIdentifier (ix :@ p) :@ p, ty)
  where
    go _ [] = throwError $ BindingNotFound x p
    go ix ((x', a) : types)
      | x == x' = pure (ix, a)
      | otherwise = go (ix + 1) types
synthetize ctx (AST.EType :@ p) =
  {-
    ──────────────────────
      Ρ, Γ ⊢ type ⇒ type
  -}
  pure (TAST.EType :@ p, VType :@ p)
synthetize ctx (AST.EPi (AST.Parameter isImplicit name ty :@ p2) expr :@ p) = do
  {-
      Ρ, Γ ⊢ A ⇐ type       Ρ, Γ, x : A ⊢ B ⇐ type
    ────────────────────────────────────────────────
               Ρ, Γ ⊢ (x : A) → B ⇒ type
  -}
  ty <- check ctx ty (VType :@ p)
  ty' <- plugNormalisation $ eval ctx ty
  b <- check (bind name ty' ctx) expr (VType :@ p)
  pure (TAST.EPi (TAST.Parameter isImplicit name ty :@ p2) b :@ p, VType :@ p)
synthetize ctx (AST.ELet (AST.Let False (name :@ p1) ty val :@ p2) expr :@ p) = do
  {-
      Ρ, Γ ⊢ A ⇐ type        Ρ, Γ ⊢ e₁ ⇐ A        Ρ, Γ, x : A ⊢ e₂ ⇐ B
    ────────────────────────────────────────────────────────────────────
                    Ρ, Γ ⊢ let x : A = e₁ ; e₂ ⇒ B
  -}
  ty <- check ctx ty (VType :@ p)
  ty' <- plugNormalisation $ eval ctx ty
  val <- check ctx val ty'
  val' <- plugNormalisation $ eval ctx val
  (u, b) <- synthetize (define (name :@ p1) val' ty' ctx) expr
  pure (TAST.ELet (TAST.Let False (name :@ p1) ty val :@ p2) u :@ p, b)
synthetize ctx (AST.EHole :@ p) = do
  let !m = freshMeta ctx p
  trace (">>> Ρ, Γ ⊢ _ ⇒ ?" <> show m) $ pure ()
  a <- plugNormalisation $ eval ctx m
  let !t = freshMeta ctx p
  trace ("<<< Ρ, Γ ⊢ " <> show t <> " ⇒ " <> show a) $ pure ()
  pure (t, a)
synthetize ctx (AST.ELam (AST.Parameter isImplicit name ty :@ p2) ex :@ p) = do
  ty <- check ctx ty (VType :@ p)
  ty' <- plugNormalisation $ eval ctx ty
  (ex, b) <- synthetize (bind name ty' ctx) ex
  clos <- closeVal ctx b
  pure (TAST.ELam ex :@ p, VPi (unLoc name) ty' clos :@ p)
synthetize _ expr = error $ "not yet handled: " <> show expr

closeVal :: forall m. MonadElab m => Context -> Located Value -> m Closure
closeVal ctx ty = do
  ty <- plugNormalisation $ quote ctx (lvl ctx + 1) ty
  pure $ Clos (env ctx) ty
