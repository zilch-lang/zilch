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
import Language.Zilch.Syntax.Core.AST (IntegerSuffix (..))
import qualified Language.Zilch.Syntax.Core.AST as AST
import Language.Zilch.Typecheck.Context
import qualified Language.Zilch.Typecheck.Core.AST as TAST
import Language.Zilch.Typecheck.Core.Eval (Closure (Clos), DeBruijnLvl, MetaEntry (Solved, Unsolved), Value (..), explicit, implicit)
import qualified Language.Zilch.Typecheck.Core.Usage as TAST
import {-# SOURCE #-} Language.Zilch.Typecheck.Elaborator (MonadElab)
import Language.Zilch.Typecheck.Errors (ElabError (..))
import Language.Zilch.Typecheck.Evaluator (apply, eval, force, plugNormalisation, quote)
import Language.Zilch.Typecheck.Metavariables (mcxt, nextMeta)
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
    ((AST.TopLevel isPublic (AST.Let isRec usage name@(_ :@ p5) ty ex :@ p3) :@ p4) : ds) -> do
      (_, ty) <- check (scale ctx TAST.Erased) (TAST.Erased :@ p4) ty (VType :@ p3)
      ty' <- plugNormalisation $ eval ctx ty

      (ex, ex') <- mdo
        let ctx' = if isRec then define TAST.Unrestricted name (VThunk ex' :@ p3) ty' ctx else ctx
        (_, ex') <- check ctx' usage ex ty'
        ex'' <- plugNormalisation $ eval ctx' ex'
        pure (ex', ex'')

      TAST.Mod defs :@ p <- checkProgram' (define TAST.Unrestricted name ex' ty' ctx) (AST.Mod imports ds :@ p)

      pure (TAST.Mod ((TAST.TopLevel [] isPublic (TAST.Let isRec usage name ty ex :@ p3) :@ p4) : defs) :@ p)

insert' :: forall m. MonadElab m => (Context, Located TAST.Expression, Located Value, Located TAST.Usage) -> m (Context, Located TAST.Expression, Located Value, Located TAST.Usage)
insert' (ctx, expr, ty, usage) = do
  ty <- plugNormalisation $ force ctx ty
  case ty of
    VPi _ _ imp _ b :@ p | imp == implicit -> do
      let m = freshMeta ctx :@ p
      mv <- plugNormalisation $ eval ctx m
      ty <- plugNormalisation $ apply ctx b mv
      insert' (ctx, TAST.EApplication expr True m :@ p, ty, usage)
    va -> pure (ctx, expr, va, usage)

insert :: forall m. MonadElab m => (Context, Located TAST.Expression, Located Value, Located TAST.Usage) -> m (Context, Located TAST.Expression, Located Value, Located TAST.Usage)
insert (ctx, expr, ty, usage) = case (expr, ty) of
  (t@(TAST.ELam (TAST.Parameter True _ _ _ :@ _) _ :@ _), va) -> pure (ctx, t, va, usage)
  (t, va) -> insert' (ctx, t, va, usage)

-- | @Ρ, Γ ⊢ e ⇐ τ@
check :: forall m. MonadElab m => Context -> Located TAST.Usage -> Located AST.Expression -> Located Value -> m (Context, Located TAST.Expression)
check ctx usage expr ty = do
  ty <- plugNormalisation $ force ctx ty
  case (expr, ty) of
    (AST.ELam (AST.Parameter isImplicit u1 x ty :@ p1) expr :@ p3, VPi u2 _ imp ty2 ty3 :@ p2) | isImplicit == not imp -> do
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
    (expr@(_ :@ p1), VPi u2 x imp ty2 ty3 :@ p2) | imp == implicit -> do
      ty' <- plugNormalisation $ apply ctx ty3 (VVariable ("x?" :@ p2) (lvl ctx) :@ p2)
      (ctx', u) <- check (insertBinder u2 (x :@ p2) ty2 ctx) (TAST.Unrestricted :@ p2) expr ty'

      ty2 <- plugNormalisation $ quote ctx (lvl ctx) ty2

      pure (unbind ctx', TAST.ELam (TAST.Parameter True (TAST.Unrestricted :@ p1) (x :@ p1) ty2 :@ p1) u :@ p1)
    (AST.ELet (AST.Let False usage x ty ex :@ p1) expr :@ p2, ty2) -> do
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
      pure (unbind ctx', TAST.ELet (TAST.Let False usage x ty ex :@ p1) u :@ p2)
    (AST.ELet (AST.Let True usage x ty ex :@ p1) expr :@ p2, ty2) -> do
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
      pure (unbind ctx', TAST.ELet (TAST.Let False usage x ty ex :@ p1) u :@ p2)
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
      (ctx', e, ty, u1) <- insert =<< synthetize ctx e

      -- traceShow (show e <> " ⇐^" <> show u1 <> " " <> show ty) $ pure ()
      -- traceShow ("Expected :^" <> show usage <> " " <> show v) $ pure ()

      unifyUsage usage u1
      unify ctx' v ty
      pure (ctx', e)

-- | @Ρ, Γ ⊢ e ⇒ τ@
synthetize :: forall m. MonadElab m => Context -> Located AST.Expression -> m (Context, Located TAST.Expression, Located Value, Located TAST.Usage)
synthetize ctx (AST.EInteger i suffix :@ p) =
  {-
      n is a literal number
    ─────────────────────────
          Γ ⊢ n ⇒^ω nat
  -}
  pure (ctx, TAST.EInteger i :@ p, typeForSuffix suffix :@ p, TAST.Unrestricted :@ p)
  where
    typeForSuffix SuffixU64 = VBuiltinU64
    typeForSuffix SuffixU32 = VBuiltinU32
    typeForSuffix SuffixU16 = VBuiltinU16
    typeForSuffix SuffixU8 = VBuiltinU8
    typeForSuffix SuffixS64 = VBuiltinS64
    typeForSuffix SuffixS32 = VBuiltinS32
    typeForSuffix SuffixS16 = VBuiltinS16
    typeForSuffix SuffixS8 = VBuiltinS8
synthetize ctx (AST.ECharacter c :@ p) =
  {-
      c is a literal character
    ────────────────────────────
           Γ ⊢ c ⇒^ω char
  -}
  pure (ctx, TAST.ECharacter c :@ p, VVariable ("char" :@ p) 0 :@ p, TAST.Unrestricted :@ p)
synthetize ctx (AST.EApplication e1@(_ :@ p1) e2 :@ p) = do
  {-
      Γ ⊢ e₁ ⇒^σ (x :^π A) → B        Γ ⊢ e₂ ⇐^σ' A
               σ' = 0 ⇔ (π = 0 ∨ σ = 0)
    ─────────────────────────────────────────────────
                Γ + πΓ ⊢ (e₁ e₂) ⇒^σ B
  -}
  (icit, e1, ctx', t1, usage) <- case e2 of
    AST.EImplicit _ :@ _ -> do
      (ctx', e1, t1, usage) <- synthetize ctx e1
      pure (implicit, e1, ctx', t1, usage)
    _ -> do
      (ctx', e1, t1, usage) <- insert' =<< synthetize ctx e1
      pure (explicit, e1, ctx', t1, usage)

  -- (ctx', e1, t1, usage) <- synthetize ctx e1

  t1 <- plugNormalisation $ force ctx t1
  (u2, a, b) <- case t1 of
    VPi u _ i a b :@ p2
      | i == icit -> pure (u :@ p2, a, b)
      | otherwise -> throwError $ ImplicitMismatch icit i p2
    t1@(_ :@ p2) -> do
      -- try η-expanding
      let usage = TAST.Unrestricted
      a <- plugNormalisation $ eval ctx (freshMeta ctx :@ p)
      let b = Clos (env ctx) $ freshMeta (bind usage ("x?" :@ p) a ctx) :@ p
      unify ctx t1 (VPi usage "x?" explicit a b :@ p)
      pure (usage :@ p2, a, b)

  let u1 =
        if unLoc u2 == TAST.Erased || unLoc usage == TAST.Erased
          then TAST.Erased
          else TAST.Linear

  (ctx'', e2) <- check ctx' (u1 :@ getPos e2) e2 a
  t2 <- plugNormalisation do
    e2 <- eval ctx e2
    apply ctx b e2
  pure (ctx'', TAST.EApplication e1 (not icit) e2 :@ p, t2, usage)
synthetize ctx (AST.EImplicit e2 :@ _) = synthetize ctx e2
synthetize ctx (AST.EIdentifier (x :@ _) :@ p) = do
  {-
    ────────────────────────
      Γ, x :^σ A ⊢ x ⇒^σ A
  -}
  (ex, ty, usage) <- go 0 (types ctx)

  let ctx' =
        if usage == TAST.Linear
          then setContext ctx x TAST.Erased
          else ctx
  -- TODO: if usage is Linear, then set it to Erased in the context
  pure (ctx', ex, ty, usage :@ p)
  where
    go _ [] = throwError $ BindingNotFound x p
    go ix ((usage, x', origin, a) : types)
      | x == x' && origin == Source = pure (TAST.EIdentifier (x' :@ p) ix :@ p, a, usage)
      | otherwise = go (ix + 1) types
synthetize ctx (AST.EType :@ p) =
  {-
    ──────────────────────
      Γ ⊢ type ⇒^0 type
  -}
  pure (ctx, TAST.EType :@ p, VType :@ p, TAST.Erased :@ p)
synthetize ctx (AST.EPi (AST.Parameter isImplicit usage name ty :@ p2) expr :@ p) = do
  {-
      0Γ ⊢ A ⇐^0 type       0Γ, x :^0 A ⊢ B ⇐^0 type
    ──────────────────────────────────────────────────
               0Γ ⊢ (x :^σ A) → B ⇒^0 type
  -}
  let usage' = TAST.Erased
  (_, ty) <- check (scale ctx usage') usage ty (VType :@ p)
  ty' <- plugNormalisation $ eval ctx ty
  (_, b) <- check (scale (bind usage' name ty' ctx) usage') (usage' :@ p) expr (VType :@ p)
  pure (ctx, TAST.EPi (TAST.Parameter isImplicit usage name ty :@ p2) b :@ p, VType :@ p, usage' :@ p)
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
  (_, ty) <- check (scale ctx TAST.Erased) (TAST.Erased :@ p) ty (VType :@ p)
  ty' <- plugNormalisation $ eval ctx ty
  (ctx', ex, b, u2) <- synthetize (bind (unLoc usage) name ty' ctx) ex
  clos <- closeVal ctx b
  pure (unbind ctx', TAST.ELam (TAST.Parameter isImplicit usage name ty :@ p2) ex :@ p, VPi (unLoc usage) (unLoc name) (not isImplicit) ty' clos :@ p, u2)
synthetize ctx (AST.EHole :@ p1) = do
  a <- plugNormalisation do eval ctx (freshMeta ctx :@ p1)
  let t = freshMeta ctx :@ p1
  pure (ctx, t, a, TAST.Unrestricted :@ p1)
synthetize _ expr = error $ "not yet handled: " <> show expr

closeVal :: forall m. MonadElab m => Context -> Located Value -> m Closure
closeVal ctx ty = do
  ty <- plugNormalisation $ quote ctx (lvl ctx + 1) ty
  pure $ Clos (env ctx) ty
