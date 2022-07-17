{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecursiveDo #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Typecheck.Checker (checkProgram, check) where

import Control.Monad (forM, guard, unless, when)
import Control.Monad.Except (throwError)
import Data.IORef (readIORef)
import qualified Data.IntMap as IntMap
import qualified Data.List as List
import Data.Located (Located ((:@)), Position, getPos, unLoc)
import Data.Maybe (mapMaybe)
import Debug.Trace (traceShow)
import Language.Zilch.Syntax.Core.AST (IntegerSuffix (..))
import qualified Language.Zilch.Syntax.Core.AST as AST
import Language.Zilch.Typecheck.Context
import qualified Language.Zilch.Typecheck.Core.AST as TAST
import Language.Zilch.Typecheck.Core.Eval (Closure (Clos), DeBruijnLvl, MetaEntry (Solved, Unsolved), Value (..), explicit, implicit)
import qualified Language.Zilch.Typecheck.Core.Usage as TAST
import {-# SOURCE #-} Language.Zilch.Typecheck.Elaborator (MonadElab)
import Language.Zilch.Typecheck.Errors (ElabError (..))
import Language.Zilch.Typecheck.Evaluator (apply, eval, force, quote)
import Language.Zilch.Typecheck.Metavariables (mcxt, nextMeta)
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
        val@(_ :@ p1) <- quote ctx (lvl ctx) (val :@ p)
        pure (TAST.LetMeta m (Just val) :@ p1)
  let addBinds' = (:@ p) . TAST.TopLevel [] False <$> addBinds

  pure $ TAST.Mod (addBinds' <> binds) :@ p

checkProgram' :: forall m. MonadElab m => Context -> Located AST.Module -> m (Located TAST.Module)
checkProgram' ctx (AST.Mod imports defs :@ p) = do
  case defs of
    [] -> do
      pure (TAST.Mod [] :@ p)
    ((AST.TopLevel isPublic (AST.Let isRec usage name@(_ :@ p5) ty ex :@ p3) :@ p4) : ds) -> do
      {-
         0Γ ⊢ A ⇐⁰ type ℓ            Γ, x :ⁱ A ⊢ f ⇒ⁱ B            0Γ ⊢ e ⇐⁰ A          i = 0
        ──────────────────────────────────────────────────────────────────────────────────────── [⇐ let-I₀]
                                       Γ ⊢ let x :ⁱ A := e

         0Γ₁ ⊢ A ⇐⁰ type ℓ             Γ₁, x :ⁱ A ⊢ f ⇒ⁱ B           Γ₂ ⊢ e ⇐¹ A
        ────────────────────────────────────────────────────────────────────────── [⇐ let-I₁]
                                 Γ₁ + iΓ₂ ⊢ let x :ⁱ A := e

      -}
      (_, ty) <- check (scale ctx TAST.Erased) (TAST.Erased :@ p4) ty (VType :@ p3)
      ty' <- eval ctx ty

      (ex, ex') <- mdo
        let ctx' = if isRec then define TAST.Unrestricted name (VThunk ex' :@ p3) ty' ctx else ctx
        (_, ex') <- case unLoc usage of
          TAST.O -> check (scale ctx' TAST.O) (TAST.O :@ getPos usage) ex ty'
          _ -> check ctx' (TAST.I :@ getPos usage) ex ty'
        ex'' <- eval ctx' ex'
        pure (ex', ex'')

      TAST.Mod defs :@ p <- checkProgram' (define (unLoc usage) name ex' ty' ctx) (AST.Mod imports ds :@ p)

      pure (TAST.Mod ((TAST.TopLevel [] isPublic (TAST.Let isRec usage name ty ex :@ p3) :@ p4) : defs) :@ p)

insert' :: forall m. MonadElab m => (Context, Located TAST.Expression, Located Value, Located TAST.Usage) -> m (Context, Located TAST.Expression, Located Value, Located TAST.Usage)
insert' (ctx, expr, ty, usage) = do
  ty <- force ctx ty
  case ty of
    VPi _ _ imp _ b :@ p | imp == implicit -> do
      let m = freshMeta ctx :@ p
      mv <- eval ctx m
      ty <- apply ctx b mv
      insert' (ctx, TAST.EApplication expr True m :@ p, ty, usage)
    va -> pure (ctx, expr, va, usage)

insert :: forall m. MonadElab m => (Context, Located TAST.Expression, Located Value, Located TAST.Usage) -> m (Context, Located TAST.Expression, Located Value, Located TAST.Usage)
insert (ctx, expr, ty, usage) = case (expr, ty) of
  (t@(TAST.ELam (TAST.Parameter True _ _ _ :@ _) _ :@ _), va) -> pure (ctx, t, va, usage)
  (t, va) -> insert' (ctx, t, va, usage)

-- | @check Γ i e τ@ is the typing judgment @Γ ⊢ e ⇐ⁱ τ@.
check :: forall m. MonadElab m => Context -> Located TAST.Usage -> Located AST.Expression -> Located Value -> m (Context, Located TAST.Expression)
check ctx usage expr ty = do
  ty <- force ctx ty
  case (expr, ty) of
    (AST.ELam (AST.Parameter isImplicit u1 x ty :@ p1) expr :@ p3, VPi u2 _ imp ty2 ty3 :@ p2) | isImplicit == not imp -> do
      when (unLoc u1 /= u2) do
        throwError $ UsageMismatch (u2 :@ p2) u1
      {-
         0Γ ⊢ A :⁰ type ℓ        Γ, x :ⁱᵖ A ⊢ e ⇐ⁱ B
        ───────────────────────────────────────────── [⇐ λ-I]
          Γ ⊢ (λ(x :ᵖ A) ⇒ e) ⇐ⁱ (x :ᵖ A) → B
      -}
      (_, ty) <- check (scale ctx TAST.Erased) (TAST.Erased :@ p2) ty (VType :@ p1)
      ty3' <- apply ctx ty3 (VVariable x (lvl ctx) :@ p2)

      let xUsage = unLoc usage * unLoc u1

      (ctx', u) <- check (bind xUsage x ty2 ctx) usage expr ty3'

      case (xUsage, indexContext ctx' x) of
        -- if @x@ has not been used and was bound as linear, then throw an error
        (TAST.I, TAST.I) -> throwError $ UnusedLinearVariable x (getPos expr)
        _ -> pure ()

      ty' <- eval ctx ty
      unify ctx ty' ty2
      pure (unbind ctx', TAST.ELam (TAST.Parameter isImplicit u1 x ty :@ p1) u :@ p3)
    (expr@(_ :@ p1), VPi u2 x imp ty2 ty3 :@ p2) | imp == implicit -> do
      ty' <- apply ctx ty3 (VVariable ("x?" :@ p2) (lvl ctx) :@ p2)
      (ctx', u) <- check (insertBinder u2 (x :@ p2) ty2 ctx) (TAST.Unrestricted :@ p2) expr ty'
      -- TODO: is @ω@ the correct multiplicity to be infered for the parameter here?

      ty2 <- quote ctx (lvl ctx) ty2

      pure (unbind ctx', TAST.ELam (TAST.Parameter True (TAST.Unrestricted :@ p1) (x :@ p1) ty2 :@ p1) u :@ p1)
    (AST.ELet (AST.Let False usage' x ty ex :@ p1) expr :@ p2, ty2) -> do
      {-
         0Γ ⊢ A ⇐⁰ type ℓ            Γ, x :ⁱᵖ A ⊢ f ⇐ᵖ B            0Γ ⊢ e ⇐⁰ A          ip = 0
        ──────────────────────────────────────────────────────────────────────────────────────── [⇐ let-I₀]
                               Γ ⊢ (let x :ⁱ A := e; f) ⇐ᵖ B

         0Γ₁ ⊢ A ⇐⁰ type ℓ             Γ₁, x :ⁱᵖ A ⊢ f ⇐ᵖ B           Γ₂ ⊢ e ⇐¹ A
        ────────────────────────────────────────────────────────────────────────── [⇐ let-I₁]
                         Γ₁ + ipΓ₂ ⊢ (let x :ⁱ A := e; f) ⇐ᵖ B
      -}
      (_, ty) <- check (scale ctx TAST.Erased) (TAST.Erased :@ p1) ty (VType :@ p1)
      ty' <- eval ctx ty

      case unLoc usage * unLoc usage' of
        TAST.O -> do
          -- apply [⇐ let-I₀]
          (_, ex) <- check (scale ctx TAST.O) (TAST.O :@ getPos usage') ex ty'
          ex' <- eval ctx ex

          (ctx, u) <- check (define TAST.O x ex' ty' ctx) usage expr ty2

          pure (unbind ctx, TAST.ELet (TAST.Let False usage' x ty ex :@ p1) u :@ p2)
        xUsage -> do
          -- apply [⇐ let-I₁]

          (ctx2, ex) <- check ctx (TAST.I :@ getPos usage') ex ty'
          ex' <- eval ctx ex

          (ctx1, u) <- check (define xUsage x ex' ty' ctx) usage expr ty2

          case (xUsage, indexContext ctx1 x) of
            -- if @x@ has not been used and was bound as linear, then throw an error
            (TAST.I, TAST.I) -> throwError $ UnusedLinearVariable x (getPos expr)
            _ -> pure ()
          ctx <- combineContexts ctx (unbind ctx1) (scale ctx2 xUsage) (getPos expr)

          pure (ctx, TAST.ELet (TAST.Let False usage' x ty ex :@ p1) u :@ p2)
    (AST.ELet (AST.Let True usage' x ty ex :@ p1) expr :@ p2, ty2) -> do
      {-
         0Γ ⊢ A ⇐⁰ type ℓ            Γ, x :ⁱᵖ A ⊢ f ⇐ᵖ B            0Γ, x :⁰ A ⊢ e ⇐⁰ A          ip = 0
        ──────────────────────────────────────────────────────────────────────────────────────────────── [⇐ rec-I₀]
                                     Γ ⊢ (rec x :ⁱ A := e; f) ⇐ᵖ B

         0Γ₁ ⊢ A ⇐⁰ type ℓ             Γ₁, x :ⁱᵖ A ⊢ f ⇐ᵖ B           Γ₂, x :⁻ A ⊢ e ⇐¹ A
        ────────────────────────────────────────────────────────────────────────────────── [⇐ rec-I₁]
                                Γ₁ + ipΓ₂ ⊢ (rec x :ⁱ A := e; f) ⇐ᵖ B
      -}
      (_, ty) <- check (scale ctx TAST.Erased) (TAST.Erased :@ p1) ty (VType :@ p1)
      ty' <- eval ctx ty

      case unLoc usage * unLoc usage' of
        TAST.O -> do
          -- apply [⇐ rec-I₀]

          (ctx, ex) <- mdo
            let ctx' = define TAST.O x (VThunk ex' :@ p1) ty' ctx
            (ctx'', ex') <- check (scale ctx' TAST.O) (TAST.O :@ p1) ex ty'
            pure (ctx'', ex')

          ex' <- eval ctx ex
          (ctx, u) <- check (define TAST.O x ex' ty' ctx) usage expr ty2

          pure (unbind ctx, TAST.ELet (TAST.Let False usage' x ty ex :@ p1) u :@ p2)
        xUsage -> do
          -- apply [⇐ rec-I₁]

          (ctx2, ex) <- mdo
            let ctx' = define TAST.Unrestricted x (VThunk ex' :@ p1) ty' ctx
            (ctx'', ex') <- check ctx' (TAST.I :@ p1) ex ty'
            pure (ctx'', ex')

          ex' <- eval ctx ex
          (ctx1, u) <- check (define xUsage x ex' ty' ctx) usage expr ty2

          case (xUsage, indexContext ctx1 x) of
            -- if @x@ has not been used and was bound as linear, then throw an error
            (TAST.I, TAST.I) -> throwError $ UnusedLinearVariable x (getPos expr)
            _ -> pure ()
          ctx <- combineContexts ctx (unbind ctx1) (scale ctx2 xUsage) (getPos expr)

          pure (ctx, TAST.ELet (TAST.Let True usage' x ty ex :@ p1) u :@ p2)
    (AST.EPi (AST.Parameter isImplicit u1 x ty :@ p1) ty2 :@ p2, VType :@ p3) -> do
      when (unLoc usage /= TAST.O) do
        throwError $ UsageMismatch usage (TAST.O :@ p3)
      {-
         0Γ ⊢ S ⇐⁰ type ℓ₁          0Γ, x :⁰ A ⊢ B ⇐⁰ type ℓ₂
        ────────────────────────────────────────────────────── [⇐ Π-F]
                 0Γ ⊢ (x :ᵖ S) → T ⇐⁰ type (ℓ₁ ⊔ ℓ₂)
      -}
      let ctx' = scale ctx TAST.Erased
      (_, ty) <- check ctx' (TAST.Erased :@ p1) ty (VType :@ p1)
      ty' <- eval ctx' ty
      (_, ty2) <- check (bind TAST.Erased x ty' ctx') (TAST.Erased :@ p1) ty2 (VType :@ p2)
      pure (ctx, TAST.EPi (TAST.Parameter isImplicit u1 x ty :@ p1) ty2 :@ p2)
    (AST.EHole :@ p1, _) -> do
      pure (ctx, freshMeta ctx :@ p1)
    (e@(_ :@ p), v) -> do
      {-
         Γ ⊢ e ⇒ⁱ A        A ≅ B       p ⩽ i
        ───────────────────────────────────── [⇐ ≅-F]
                     Γ ⊢ e ⇐ᵖ B
      -}
      (ctx', e, ty, u1) <- insert =<< synthetize ctx e

      if unLoc usage <= unLoc u1
        then do
          unify ctx' v ty
          pure (ctx', e)
        else throwError $ UsageMismatch u1 usage

-- | @Ρ, Γ ⊢ e ⇒ τ@
synthetize :: forall m. MonadElab m => Context -> Located AST.Expression -> m (Context, Located TAST.Expression, Located Value, Located TAST.Usage)
synthetize ctx (AST.EInteger i suffix :@ p) =
  {-
     n is a literal number
    ─────────────────────── [⇒ integer-I]
         Γ ⊢ n ⇒^ω uN
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
    ────────────────────────── [⇒ char-I]
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

  t1 <- force ctx t1
  (u2, a, b) <- case t1 of
    VPi u _ i a b :@ p2
      | i == icit -> pure (u :@ p2, a, b)
      | otherwise -> throwError $ ImplicitMismatch icit i p2
    t1@(_ :@ p2) -> do
      -- try η-expanding
      let usage = TAST.Unrestricted
      a <- eval ctx (freshMeta ctx :@ p)
      let b = Clos (env ctx) $ freshMeta (bind usage ("x?" :@ p) a ctx) :@ p
      unify ctx t1 (VPi usage "x?" explicit a b :@ p)
      pure (usage :@ p2, a, b)

  let u1 =
        if unLoc u2 == TAST.Erased || unLoc usage == TAST.Erased
          then TAST.Erased
          else TAST.Linear

  (ctx'', e2) <- check ctx' (u1 :@ getPos e2) e2 a
  t2 <- do
    e2 <- eval ctx e2
    apply ctx b e2
  pure (ctx'', TAST.EApplication e1 (not icit) e2 :@ p, t2, usage)
synthetize ctx (AST.EImplicit e2 :@ _) = synthetize ctx e2
synthetize ctx (AST.EIdentifier (x :@ _) :@ p) = do
  {-
    ──────────────────── [⇒ var-I]
     Γ, x :ᵖ A ⊢ x ⇒ᵖ A
  -}
  (ex, ty, usage) <- go 0 (types ctx)

  let ctx' =
        if usage == TAST.Linear
          then setContext ctx x TAST.Erased
          else ctx
  -- if usage is Linear, then set it to Erased in the context
  pure (ctx', ex, ty, usage :@ p)
  where
    go _ [] = throwError $ BindingNotFound x p
    go ix ((usage, x', origin, a) : types)
      | x == x' && origin == Source = pure (TAST.EIdentifier (x' :@ p) ix :@ p, a, usage)
      | otherwise = go (ix + 1) types
synthetize ctx (AST.EType :@ p) =
  {-
    ────────────────── [⇒ type-F]
     Γ ⊢ type ⇒⁰ type
  -}
  pure (ctx, TAST.EType :@ p, VType :@ p, TAST.Erased :@ p)
synthetize ctx (AST.EPi (AST.Parameter isImplicit usage name ty :@ p2) expr :@ p) = do
  {-
     0Γ ⊢ A ⇐⁰ type       0Γ, x :⁰ A ⊢ B ⇐⁰ type
    ───────────────────────────────────────────── [⇒ Π-F]
              0Γ ⊢ (x :ᵖ A) → B ⇒⁰ type
  -}
  let usage' = TAST.Erased
  (_, ty) <- check (scale ctx usage') usage ty (VType :@ p)
  ty' <- eval ctx ty
  (_, b) <- check (scale (bind usage' name ty' ctx) usage') (usage' :@ p) expr (VType :@ p)
  pure (ctx, TAST.EPi (TAST.Parameter isImplicit usage name ty :@ p2) b :@ p, VType :@ p, usage' :@ p)
synthetize ctx (AST.ELam (AST.Parameter isImplicit usage name ty :@ p2) ex :@ p) = do
  {-
     0Γ ⊢ A ⇐⁰ type ℓ       Γ, x :ⁱ A ⊢ e ⇒¹ B
    ─────────────────────────────────────────── [⇒ λ-I]
       Γ ⊢ (λ(x :ⁱ A) ⇒ e) ⇒¹ (x :ⁱ A) → B

   NOTE: We trick a little bit here by only infering a linear use.
         There are cases where we could want 0 too, so this might be considered kind of erroneous.
         Ideally, we'd say that we cannot infer the type of the literal lambda, and it should be fine as such case may not happen that frequently
         (if at all, who writes @(λ(x :ⁱ A). x) e@ anyway?).

         Instead, we choose to infer a usage of @1@ because such functions are applied directly, hence only once.
  -}
  (_, ty) <- check (scale ctx TAST.Erased) (TAST.Erased :@ p) ty (VType :@ p)
  ty' <- eval ctx ty
  (ctx', ex, b, u2) <- synthetize (bind (unLoc usage) name ty' ctx) ex

  case (unLoc usage, indexContext ctx' name) of
    (TAST.I, TAST.I) -> throwError $ UnusedLinearVariable name (getPos ex)
    _ -> pure ()

  clos <- closeVal ctx' b
  pure (unbind ctx', TAST.ELam (TAST.Parameter isImplicit usage name ty :@ p2) ex :@ p, VPi (unLoc usage) (unLoc name) (not isImplicit) ty' clos :@ p, u2)
synthetize ctx (AST.EHole :@ p1) = do
  a <- eval ctx (freshMeta ctx :@ p1)
  let t = freshMeta ctx :@ p1
  pure (ctx, t, a, TAST.Unrestricted :@ p1)
synthetize _ expr = error $ "not yet handled: " <> show expr

closeVal :: forall m. MonadElab m => Context -> Located Value -> m Closure
closeVal ctx ty = do
  ty <- quote ctx (lvl ctx + 1) ty
  pure $ Clos (env ctx) ty

combineContexts :: forall m. MonadElab m => Context -> Context -> Context -> Position -> m Context
combineContexts base c1 c2 pos = do
  let vars1 = map (\(_, x, _, _) -> x) (types base)
      vars2 = map (\(_, x, _, _) -> x) (types c1)
      vars3 = map (\(_, x, _, _) -> x) (types c2)

      vars = vars1 `List.union` vars2 `List.union` vars3

  types' <- forM' vars (types base) (types c1) (types c2) checkLinearVar
  pure $ base {types = types'}
  where
    forM' [] _ _ _ _ = pure []
    forM' (x : xs) v1 v2 v3 f = do
      y <- f (lookup' x v1) (lookup' x v2) (lookup' x v3)
      ys <- forM' xs v1 v2 v3 f

      case y of
        Nothing -> pure ys
        Just y -> pure (y : ys)

    lookup' _ [] = Nothing
    lookup' x (u@(_, y, _, _) : ys)
      | x == y = Just u
      | otherwise = lookup' x ys

    checkLinearVar (Just (TAST.I, x, src, ty)) v2 v3 = case (v2, v3) of
      (Just (TAST.O, _, _, _), Just (TAST.O, _, _, _)) -> throwError $ NonLinearUseOfVariable x pos
      (Just (TAST.I, _, _, _), Just (TAST.O, _, _, _)) -> pure $ Just (TAST.O, x, src, ty)
      (Just (TAST.O, _, _, _), Just (TAST.I, _, _, _)) -> pure $ Just (TAST.O, x, src, ty)
      (Just (TAST.I, _, _, _), Just (TAST.I, _, _, _)) -> pure $ Just (TAST.I, x, src, ty)
      (Just (u2, _, _, _), Nothing) -> pure $ Just (u2, x, src, ty)
      (Nothing, Just (u2, _, _, _)) -> pure $ Just (u2, x, src, ty)
      (_, _) -> pure $ Just (TAST.I, x, src, ty)
    checkLinearVar (Just (u, x, src, ty)) _ _ = pure $ Just (u, x, src, ty)
    checkLinearVar Nothing _ _ = pure Nothing
