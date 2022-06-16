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
synthetize :: forall m. MonadElab m => Context -> Located AST.Expression -> m (Located TAST.Expression, Located Value)
synthetize ctx (AST.EInteger i :@ p) =
  {-
      n is a literal number
    ─────────────────────────
         Ρ, Γ ⊢ n ⇒ ℕ
  -}
  pure (TAST.EInteger i :@ p, VVariable ("nat" :@ p) 1 :@ p)
synthetize ctx (AST.ECharacter c :@ p) =
  {-
      c is a literal character
    ────────────────────────────
          Ρ, Γ ⊢ c ⇒ char
  -}
  pure (TAST.ECharacter c :@ p, VVariable ("char" :@ p) 0 :@ p)
synthetize ctx (AST.EApplication e1@(_ :@ p1) e2 :@ p) = do
  {-
      Ρ, Γ ⊢ e₁ ⇒ (x : A) → B          Ρ, Γ ⊢ e₂ ⇐ A
    ───────────────────────────────────────────────────
                  Ρ, Γ ⊢ (e₁ e₂) ⇒ B
  -}
  (e1, t1) <- synthetize ctx e1

  t1 <- plugNormalisation $ force ctx t1
  (a, b) <- case t1 of
    VPi _ _ a b :@ _ -> pure (a, b)
    t1 -> do
      a <- plugNormalisation $ eval ctx (freshMeta ctx :@ p)
      let b = Clos (env ctx) $ freshMeta (bind ("x?" :@ p) a ctx) :@ p
      unify ctx t1 (VPi Nothing "x?" a b :@ p)
      pure (a, b)

  e2 <- check ctx e2 a
  t2 <- plugNormalisation do
    e2 <- eval ctx e2
    apply ctx b e2
  pure (TAST.EApplication e1 e2 :@ p, t2)
synthetize ctx (AST.EIdentifier (x :@ _) :@ p) = do
  {-
    ───────────────────────
      Ρ, Γ, x : A ⊢ x ⇒ A
  -}
  (ex, ty) <- go 0 (types ctx)
  pure (ex, ty)
  where
    go _ [] = throwError $ BindingNotFound x p
    go ix ((x', a) : types)
      | x == x' = pure (TAST.EIdentifier (x' :@ p) ix :@ p, a)
      | otherwise = go (ix + 1) types
synthetize ctx (AST.EType :@ p) =
  {-
    ──────────────────────
      Ρ, Γ ⊢ type ⇒ type
  -}
  pure (TAST.EType :@ p, VType :@ p)
synthetize ctx (AST.EPi (AST.Parameter isImplicit usage name ty :@ p2) expr :@ p) = do
  {-
      Ρ, Γ ⊢ A ⇐ type       Ρ, Γ, x : A ⊢ B ⇐ type
    ────────────────────────────────────────────────
               Ρ, Γ ⊢ (x : A) → B ⇒ type
  -}
  ty <- check ctx ty (VType :@ p)
  ty' <- plugNormalisation $ eval ctx ty
  b <- check (bind name ty' ctx) expr (VType :@ p)
  pure (TAST.EPi (TAST.Parameter isImplicit usage name ty :@ p2) b :@ p, VType :@ p)
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
synthetize ctx (AST.ELet (AST.Let True (name :@ p1) ty val :@ p2) expr :@ p) = do
  {-
      Ρ, Γ ⊢ A ⇐ type        Ρ, Γ, x : A ⊢ e₁ ⇐ A        Ρ, Γ, x : A ⊢ e₂ ⇐ B
    ───────────────────────────────────────────────────────────────────────────
                         Ρ, Γ ⊢ rec x : A = e₁ ; e₂ ⇒ B
  -}
  ty <- check ctx ty (VType :@ p)
  ty' <- plugNormalisation $ eval ctx ty

  (val, val') <- mdo
    let ctx' = define (name :@ p1) ty' (VThunk val' :@ p2) ctx
    val' <- check ctx' val ty'
    val'' <- plugNormalisation $ eval ctx' val'
    pure (val', val'')
  (u, b) <- synthetize (define (name :@ p1) val' ty' ctx) expr
  pure (TAST.ELet (TAST.Let False (name :@ p1) ty val :@ p2) u :@ p, b)
synthetize ctx (AST.ELam (AST.Parameter isImplicit usage name ty :@ p2) ex :@ p) = do
  ty <- check ctx ty (VType :@ p)
  ty' <- plugNormalisation $ eval ctx ty
  (ex, b) <- synthetize (bind name ty' ctx) ex
  clos <- closeVal ctx b
  pure (TAST.ELam (TAST.Parameter isImplicit usage name ty :@ p2) ex :@ p, VPi (unLoc <$> usage) (unLoc name) ty' clos :@ p)
synthetize ctx (AST.EHole :@ p1) = do
  a <- plugNormalisation do eval ctx (freshMeta ctx :@ p1)
  let t = freshMeta ctx :@ p1
  pure (t, a)
synthetize _ expr = error $ "not yet handled: " <> show expr

closeVal :: forall m. MonadElab m => Context -> Located Value -> m Closure
closeVal ctx ty = do
  ty <- plugNormalisation $ quote ctx (lvl ctx + 1) ty
  pure $ Clos (env ctx) ty
