{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecursiveDo #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Typecheck.Checker (checkProgram, check) where

import Control.Monad (forM, guard, unless, when)
import Control.Monad.Except (throwError)
import Data.Bifunctor (first)
import Data.IORef (readIORef)
import qualified Data.IntMap as IntMap
import qualified Data.List as List
import Data.Located (Located ((:@)), Position, getPos, unLoc)
import qualified Data.Map as Map
import Data.Maybe (catMaybes, fromMaybe, mapMaybe)
import Data.Text (Text)
import Debug.Trace (traceShow)
import Language.Zilch.Syntax.Core.AST (IntegerSuffix (..))
import qualified Language.Zilch.Syntax.Core.AST as AST
import Language.Zilch.Typecheck.Context
import qualified Language.Zilch.Typecheck.Core.AST as TAST
import Language.Zilch.Typecheck.Core.Eval (Closure (Clos), DeBruijnLvl, MetaEntry (Solved, Unsolved), Value (..), explicit, implicit)
import qualified Language.Zilch.Typecheck.Core.Multiplicity as TAST
import {-# SOURCE #-} Language.Zilch.Typecheck.Elaborator (MonadElab)
import Language.Zilch.Typecheck.Errors (ElabError (..))
import Language.Zilch.Typecheck.Evaluator (apply, eval, force, quote)
import Language.Zilch.Typecheck.Metavariables (mcxt, nextMeta)
import Language.Zilch.Typecheck.Unification (freshMeta, unify)
import Language.Zilch.Typecheck.Usage (Usage)
import qualified Language.Zilch.Typecheck.Usage as Usage
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
    ((AST.TopLevel isPublic (AST.Let isRec mult name@(_ :@ p5) ty ex :@ p3) :@ p4) : ds) -> do
      {-
         0Γ ⊢ A ⇐⁰ type ℓ            0Γ ⊢ e ⇐⁰ A          i = 0
        ──────────────────────────────────────────────────────── [⇐ let-I₀]
                               Γ ⊢ let x :ⁱ A := e

         0Γ₁ ⊢ A ⇐⁰ type ℓ             Γ₂ ⊢ e ⇐¹ A
        ─────────────────────────────────────────── [⇐ let-I₁]
                 Γ₁ + iΓ₂ ⊢ let x :ⁱ A := e
      -}
      (_, ty) <- check TAST.Irrelevant ctx ty (VType :@ p3)
      ty' <- eval ctx ty

      (ex, ex') <- mdo
        let ctx' = if isRec then define TAST.Unrestricted name (VThunk ex' :@ p3) ty' ctx else ctx
        (usage, ex') <-
          first (Usage.scale $ unLoc mult) <$> case unLoc mult of
            TAST.O -> check TAST.Irrelevant ctx' ex ty'
            _ -> check TAST.Present ctx' ex ty'
        checkUsage ctx' usage (getPos ex)

        ex'' <- eval ctx' ex'
        pure (ex', ex'')

      TAST.Mod defs :@ p <- checkProgram' (define (unLoc mult) name ex' ty' ctx) (AST.Mod imports ds :@ p)

      pure (TAST.Mod ((TAST.TopLevel [] isPublic (TAST.Let isRec mult name ty ex :@ p3) :@ p4) : defs) :@ p)

insert' :: forall m. MonadElab m => Context -> (Usage, Located TAST.Expression, Located Value, Located TAST.Multiplicity) -> m (Usage, Located TAST.Expression, Located Value, Located TAST.Multiplicity)
insert' ctx (qs, expr, ty, usage) = do
  ty <- force ctx ty
  case ty of
    VPi _ _ imp _ b :@ p | imp == implicit -> do
      let m = freshMeta ctx :@ p
      mv <- eval ctx m
      ty <- apply ctx b mv
      insert' ctx (qs, TAST.EApplication expr True m :@ p, ty, usage)
    va -> pure (qs, expr, va, usage)

insert :: forall m. MonadElab m => Context -> (Usage, Located TAST.Expression, Located Value, Located TAST.Multiplicity) -> m (Usage, Located TAST.Expression, Located Value, Located TAST.Multiplicity)
insert ctx (qs, expr, ty, usage) = case (expr, ty) of
  (t@(TAST.ELam (TAST.Parameter True _ _ _ :@ _) _ :@ _), va) -> pure (qs, t, va, usage)
  (t, va) -> insert' ctx (qs, t, va, usage)

-- | Check that the context and the usage information gathered are compatible.
checkUsage :: forall m. MonadElab m => Context -> Usage -> Position -> m ()
checkUsage ctx usage pos = do
  -- for every bound variable, check if usages are compatible
  let errs = catMaybes $ Map.foldrWithKey findMismatches [] usage
  unless (List.null errs) do
    errs <- quoteTypes errs
    throwError $ UsageMismatches errs pos
  where
    findMismatches x mult acc =
      let (m', _, ty) = indexContext ctx (x :@ pos)
       in if mult <= m'
            then acc
            else Just (mult, m', x, ty) : acc

    quoteTypes :: forall m. MonadElab m => [(TAST.Multiplicity, TAST.Multiplicity, Text, Located Value)] -> m [(TAST.Multiplicity, TAST.Multiplicity, Located Text, Located TAST.Expression)]
    quoteTypes [] = pure []
    quoteTypes ((p, q, x, ty) : xs) = do
      ty <- quote ctx (lvl ctx) ty
      xs <- quoteTypes xs
      pure $ (p, q, x :@ getPos ty, ty) : xs

-- | Locally bind a variable for use in a typechecking computation, and check afterwards that its usage matches the one expected.
withLocalVar :: forall m a. MonadElab m => Located Text -> TAST.Multiplicity -> Located Value -> Context -> (Context -> m (Usage, Position, a)) -> m (Usage, a)
withLocalVar x mult ty ctx f = do
  let ctx' = bind mult x ty ctx
  (qs, pos, exp) <- f ctx'
  qs' <- checkVar ctx' (unLoc x) qs pos
  pure (qs', exp)
  where
    checkVar ctx x qs pos = do
      let (q, qs') = splitUsage x qs
      checkUsage ctx (Map.singleton x q) pos
      pure qs'

    splitUsage x m = (fromMaybe TAST.O $ Map.lookup x m, Map.delete x m)

-- | Locally bind a variable for use in a typechecking computation, and check afterwards that its usage matches the one expected.
defineLocal :: forall m. MonadElab m => Located Text -> TAST.Multiplicity -> Located Value -> Located Value -> Context -> (Context -> m (Usage, Located TAST.Expression)) -> m (Usage, Located TAST.Expression)
defineLocal x mult ex ty ctx f = do
  let ctx' = define mult x ex ty ctx
  (qs, exp) <- f ctx'
  qs' <- checkVar ctx' (unLoc x) qs (getPos exp)
  pure (qs', exp)
  where
    checkVar ctx x qs pos = do
      let (q, qs') = splitUsage x qs
      checkUsage ctx (Map.singleton x q) pos
      pure qs'

    splitUsage x m = (fromMaybe TAST.O $ Map.lookup x m, Map.delete x m)

-- | @check Γ i e τ@ is the typing judgment @Γ ⊢ e ⇐ⁱ τ@.
check :: forall m. MonadElab m => TAST.Relevance -> Context -> Located AST.Expression -> Located Value -> m (Usage, Located TAST.Expression)
check rel ctx expr ty = do
  ty <- force ctx ty
  case (expr, ty) of
    (AST.ELam (AST.Parameter isImplicit m1 x ty :@ p1) expr :@ p3, VPi m2 _ imp ty2 ty3 :@ p2) | isImplicit == not imp -> do
      when (unLoc m1 /= m2) do
        throwError $ MultiplicityMismatch (m2 :@ p2) m1
      {-
         0Γ ⊢ A :⁰ type ℓ        Γ, x :ⁱᵖ A ⊢ e ⇐ⁱ B
        ───────────────────────────────────────────── [⇐ λ-I]
          Γ ⊢ (λ(x :ᵖ A) ⇒ e) ⇐ⁱ (x :ᵖ A) → B
      -}
      (qs1, ty) <- check TAST.Irrelevant ctx ty (VType :@ p1)
      ty3' <- apply ctx ty3 (VVariable x (lvl ctx) :@ p2)

      let xMultiplicity = TAST.extend rel * unLoc m1

      (qs2, u) <- withLocalVar x xMultiplicity ty2 ctx \ctx -> do
        (qs, e) <- check rel ctx expr ty3'
        pure (qs, getPos e, e)

      ty' <- eval ctx ty
      unify ctx ty' ty2
      pure (Usage.concat qs1 qs2, TAST.ELam (TAST.Parameter isImplicit m1 x ty :@ p1) u :@ p3)
    (expr@(_ :@ p1), VPi m2 x imp ty2 ty3 :@ p2) | imp == implicit -> do
      ty' <- apply ctx ty3 (VVariable ("x?" :@ p2) (lvl ctx) :@ p2)
      (qs, u) <- check TAST.Present (insertBinder m2 (x :@ p2) ty2 ctx) expr ty'
      -- TODO: is @ω@ the correct multiplicity to be infered for the parameter here?

      ty2 <- quote ctx (lvl ctx) ty2

      pure (qs, TAST.ELam (TAST.Parameter True (TAST.Unrestricted :@ p1) (x :@ p1) ty2 :@ p1) u :@ p1)
    (AST.ELet (AST.Let False m1 x ty ex :@ p1) expr :@ p2, ty2) -> do
      {-
         0Γ ⊢ A ⇐⁰ type ℓ            Γ, x :ⁱᵖ A ⊢ f ⇐ᵖ B            0Γ ⊢ e ⇐⁰ A          ip = 0
        ──────────────────────────────────────────────────────────────────────────────────────── [⇐ let-I₀]
                               Γ ⊢ (let x :ⁱ A := e; f) ⇐ᵖ B

         0Γ₁ ⊢ A ⇐⁰ type ℓ             Γ₁, x :ⁱᵖ A ⊢ f ⇐ᵖ B           Γ₂ ⊢ e ⇐¹ A
        ────────────────────────────────────────────────────────────────────────── [⇐ let-I₁]
                         Γ₁ + ipΓ₂ ⊢ (let x :ⁱ A := e; f) ⇐ᵖ B
      -}
      (qs1, ty) <- check TAST.Irrelevant ctx ty (VType :@ p1)
      ty' <- eval ctx ty

      case TAST.extend rel * unLoc m1 of
        TAST.O -> do
          -- apply [⇐ let-I₀]
          (qs2, ex) <- check TAST.Irrelevant ctx ex ty'
          ex' <- eval ctx ex

          (qs3, u) <- defineLocal x TAST.O ex' ty' ctx \ctx ->
            check rel ctx expr ty2

          pure (mempty, TAST.ELet (TAST.Let False m1 x ty ex :@ p1) u :@ p2)
        xMultiplicity -> do
          -- apply [⇐ let-I₁]

          (qs2, ex) <- check TAST.Present ctx ex ty'
          ex' <- eval ctx ex

          (qs3, u) <- defineLocal x xMultiplicity ex' ty' ctx \ctx ->
            check rel ctx expr ty2

          -- ctx <- combineContexts ctx (unbind ctx1) (scale ctx2 xMultiplicity) (getPos expr)
          let qs1' = qs1 `Usage.merge` qs3

          pure (qs1' `Usage.concat` Usage.scale xMultiplicity qs2, TAST.ELet (TAST.Let False m1 x ty ex :@ p1) u :@ p2)
    (AST.ELet (AST.Let True m1 x ty ex :@ p1) expr :@ p2, ty2) -> do
      {-
         0Γ ⊢ A ⇐⁰ type ℓ            Γ, x :ⁱᵖ A ⊢ f ⇐ᵖ B            0Γ, x :⁰ A ⊢ e ⇐⁰ A          ip = 0
        ──────────────────────────────────────────────────────────────────────────────────────────────── [⇐ rec-I₀]
                                     Γ ⊢ (rec x :ⁱ A := e; f) ⇐ᵖ B

         0Γ₁ ⊢ A ⇐⁰ type ℓ             Γ₁, x :ⁱᵖ A ⊢ f ⇐ᵖ B           Γ₂, x :⁻ A ⊢ e ⇐¹ A
        ────────────────────────────────────────────────────────────────────────────────── [⇐ rec-I₁]
                                Γ₁ + ipΓ₂ ⊢ (rec x :ⁱ A := e; f) ⇐ᵖ B
      -}
      (qs1, ty) <- check TAST.Irrelevant ctx ty (VType :@ p1)
      ty' <- eval ctx ty

      case TAST.extend rel * unLoc m1 of
        TAST.O -> do
          -- apply [⇐ rec-I₀]

          (qs2, ex) <- do
            rec (qs2, ex') <- defineLocal x TAST.O (VThunk ex' :@ p1) ty' ctx \ctx ->
                  check TAST.Irrelevant ctx ex ty'
            -- let ctx' = define TAST.O x (VThunk ex' :@ p1) ty' ctx
            -- (qs2, ex') <- check TAST.Irrelevant ctx' ex ty'
            pure (qs2, ex')

          ex' <- eval ctx ex
          (qs3, u) <- defineLocal x TAST.O ex' ty' ctx \ctx ->
            check rel ctx expr ty2

          pure (mempty, TAST.ELet (TAST.Let False m1 x ty ex :@ p1) u :@ p2)
        xMultiplicity -> do
          -- apply [⇐ rec-I₁]

          (qs2, ex) <- mdo
            rec (qs2, ex') <- defineLocal x TAST.W (VThunk ex' :@ p1) ty' ctx \ctx ->
                  check TAST.Present ctx ex ty'
            -- let ctx' = define TAST.Unrestricted x (VThunk ex' :@ p1) ty' ctx
            -- (qs2, ex') <- check TAST.Present ctx' ex ty'
            pure (qs2, ex')

          ex' <- eval ctx ex
          (qs3, u) <- defineLocal x xMultiplicity ex' ty' ctx \ctx ->
            check TAST.Present ctx expr ty2

          -- ctx <- combineContexts ctx (unbind ctx1) (scale ctx2 xMultiplicity) (getPos expr)
          let qs1' = qs1 `Usage.merge` qs3

          pure (qs1' `Usage.concat` Usage.scale xMultiplicity qs2, TAST.ELet (TAST.Let True m1 x ty ex :@ p1) u :@ p2)
    (AST.EPi (AST.Parameter isImplicit m1 x ty :@ p1) ty2 :@ p2, VType :@ p3) -> do
      when (rel /= TAST.Irrelevant) do
        throwError $ MultiplicityMismatch (TAST.extend rel :@ p3) (TAST.O :@ p3)
      {-
         0Γ ⊢ S ⇐⁰ type ℓ₁          0Γ, x :⁰ A ⊢ B ⇐⁰ type ℓ₂
        ────────────────────────────────────────────────────── [⇐ Π-F]
                 0Γ ⊢ (x :ᵖ S) → T ⇐⁰ type (ℓ₁ ⊔ ℓ₂)
      -}
      (_, ty) <- check TAST.Irrelevant ctx ty (VType :@ p1)
      ty' <- eval ctx ty
      (_, ty2) <- withLocalVar x TAST.O ty' ctx \ctx -> do
        (qs, e) <- check TAST.Irrelevant ctx ty2 (VType :@ p2)
        pure (qs, getPos e, e)
      pure (mempty, TAST.EPi (TAST.Parameter isImplicit m1 x ty :@ p1) ty2 :@ p2)
    (AST.EHole :@ p1, _) -> do
      pure (mempty, freshMeta ctx :@ p1)
    (e@(_ :@ p), v) -> do
      {-
         Γ ⊢ e ⇒ⁱ A        A ≅ B       p ⩽ i
        ───────────────────────────────────── [⇐ ≅-F]
                     Γ ⊢ e ⇐ᵖ B
      -}
      (qs, e, ty, m1) <- insert ctx =<< synthetize rel ctx e

      if TAST.extend rel <= unLoc m1
        then do
          unify ctx v ty
          pure (qs, e)
        else throwError $ MultiplicityMismatch (TAST.extend rel :@ p) m1

-- | @Ρ, Γ ⊢ e ⇒ τ@
synthetize :: forall m. MonadElab m => TAST.Relevance -> Context -> Located AST.Expression -> m (Usage, Located TAST.Expression, Located Value, Located TAST.Multiplicity)
synthetize rel ctx (AST.EInteger i suffix :@ p) =
  {-
     n is a literal number
    ─────────────────────── [⇒ integer-I]
         Γ ⊢ n ⇒^ω uN
  -}
  pure (mempty, TAST.EInteger i :@ p, typeForSuffix suffix :@ p, TAST.extend rel :@ p)
  where
    typeForSuffix SuffixU64 = VBuiltinU64
    typeForSuffix SuffixU32 = VBuiltinU32
    typeForSuffix SuffixU16 = VBuiltinU16
    typeForSuffix SuffixU8 = VBuiltinU8
    typeForSuffix SuffixS64 = VBuiltinS64
    typeForSuffix SuffixS32 = VBuiltinS32
    typeForSuffix SuffixS16 = VBuiltinS16
    typeForSuffix SuffixS8 = VBuiltinS8
synthetize rel ctx (AST.ECharacter c :@ p) =
  {-
     c is a literal character
    ────────────────────────── [⇒ char-I]
          Γ ⊢ c ⇒^ω char
  -}
  pure (mempty, TAST.ECharacter c :@ p, VVariable ("char" :@ p) 0 :@ p, TAST.extend rel :@ p)
synthetize rel ctx (AST.EApplication e1@(_ :@ p1) e2 :@ p) = do
  {-
     Γ ⊢ f ⇒ⁱ (y :ᵖ A) → B          0Γ ⊢ x ⇐⁰ A          ip = 0
    ──────────────────────────────────────────────────────────── [⇐ λ-E₀]
                        Γ ⊢ f x ⇐ᵖ B[y\x]

     Γ₁ ⊢ f ⇒ⁱ (y :ᵖ A) → B          Γ₂ ⊢ x ⇐¹ A
    ───────────────────────────────────────────── [⇐ λ-E₁]
              Γ₁ + ipΓ₂ ⊢ f x ⇒ⁱ B[y\x]
    -}
  (icit, e1, qs1, t1, m1) <- case e2 of
    AST.EImplicit _ :@ _ -> do
      (qs, e1, t1, m1) <- synthetize rel ctx e1
      pure (implicit, e1, qs, t1, m1)
    _ -> do
      (qs, e1, t1, m1) <- insert' ctx =<< synthetize rel ctx e1
      pure (explicit, e1, qs, t1, m1)

  t1 <- force ctx t1
  (m2, a, b) <- case t1 of
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

  case unLoc m1 * unLoc m2 of
    TAST.O -> do
      (qs2, e2) <- check TAST.Irrelevant ctx e2 a

      e2' <- eval ctx e2
      b <- apply ctx b e2'
      pure (qs1 `Usage.merge` qs2, TAST.EApplication e1 (not icit) e2 :@ p, b, m2)
    xMultiplicity -> do
      (qs2, e2) <- check TAST.Present ctx e2 a

      e2' <- eval ctx e2
      b <- apply ctx b e2'

      pure (qs1 `Usage.concat` Usage.scale xMultiplicity qs2, TAST.EApplication e1 (not icit) e2 :@ p, b, m2)
synthetize rel ctx (AST.EImplicit e2 :@ _) = synthetize rel ctx e2
synthetize rel ctx (AST.EIdentifier (x :@ _) :@ p) = do
  {-
    ──────────────────── [⇒ var-I]
     Γ, x :ᵖ A ⊢ x ⇒ᵖ A
  -}
  (ex, ty, usage) <- go 0 (types ctx)
  pure (Map.singleton x $ TAST.extend rel, ex, ty, usage :@ p)
  where
    go _ [] = throwError $ BindingNotFound x p
    go ix ((usage, x', origin, a) : types)
      | x == x' && origin == Source = pure (TAST.EIdentifier (x' :@ p) ix :@ p, a, usage)
      | otherwise = go (ix + 1) types
synthetize rel ctx (AST.EType :@ p) = do
  when (rel /= TAST.Irrelevant) do
    error $ "TODO: error for EType in non-erased context"
  {-
    ────────────────── [⇒ type-F]
     Γ ⊢ type ⇒⁰ type
  -}
  pure (mempty, TAST.EType :@ p, VType :@ p, TAST.O :@ p)
synthetize rel ctx (AST.EPi (AST.Parameter isImplicit m1 name ty :@ p2) expr :@ p) = do
  {-
     0Γ ⊢ A ⇐⁰ type       0Γ, x :⁰ A ⊢ B ⇐⁰ type
    ───────────────────────────────────────────── [⇒ Π-F]
              0Γ ⊢ (x :ᵖ A) → B ⇒⁰ type
  -}
  (_, ty) <- check TAST.Irrelevant ctx ty (VType :@ p)
  ty' <- eval ctx ty
  (_, b) <- withLocalVar name TAST.O ty' ctx \ctx -> do
    (qs, e) <- check TAST.Irrelevant ctx expr (VType :@ p)
    pure (qs, getPos e, e)
  pure (mempty, TAST.EPi (TAST.Parameter isImplicit m1 name ty :@ p2) b :@ p, VType :@ p, TAST.O :@ p)
synthetize rel ctx (AST.ELam (AST.Parameter isImplicit m1 name ty :@ p2) ex :@ p) = do
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
  (_, ty) <- check TAST.Irrelevant ctx ty (VType :@ p)
  ty' <- eval ctx ty
  (qs1, (ex, b, u2)) <- withLocalVar name (unLoc m1) ty' ctx \ctx -> do
    (u, ex, b, u2) <- synthetize TAST.Present ctx ex
    pure (u, getPos ex, (ex, b, u2))

  clos <- closeVal ctx b
  pure (qs1, TAST.ELam (TAST.Parameter isImplicit m1 name ty :@ p2) ex :@ p, VPi (unLoc m1) (unLoc name) (not isImplicit) ty' clos :@ p, u2)
synthetize rel ctx (AST.EHole :@ p1) = do
  a <- eval ctx (freshMeta ctx :@ p1)
  let t = freshMeta ctx :@ p1
  pure (mempty, t, a, TAST.extend rel :@ p1)
synthetize _ _ expr = error $ "not yet handled: " <> show expr

closeVal :: forall m. MonadElab m => Context -> Located Value -> m Closure
closeVal ctx ty = do
  ty <- quote ctx (lvl ctx + 1) ty
  pure $ Clos (env ctx) ty

-- combineContexts :: forall m. MonadElab m => Context -> Context -> Context -> Position -> m Context
-- combineContexts base c1 c2 pos = do
--   let vars1 = map (\(_, x, _, _) -> x) (types base)
--       vars2 = map (\(_, x, _, _) -> x) (types c1)
--       vars3 = map (\(_, x, _, _) -> x) (types c2)

--       vars = vars1 `List.union` vars2 `List.union` vars3

--   types' <- forM' vars (types base) (types c1) (types c2) checkLinearVar
--   pure $ base {types = types'}
--   where
--     forM' [] _ _ _ _ = pure []
--     forM' (x : xs) v1 v2 v3 f = do
--       y <- f (lookup' x v1) (lookup' x v2) (lookup' x v3)
--       ys <- forM' xs v1 v2 v3 f

--       case y of
--         Nothing -> pure ys
--         Just y -> pure (y : ys)

--     lookup' _ [] = Nothing
--     lookup' x (u@(_, y, _, _) : ys)
--       | x == y = Just u
--       | otherwise = lookup' x ys

--     checkLinearVar (Just (TAST.I, x, src, ty)) v2 v3 = case (v2, v3) of
--       (Just (TAST.O, _, _, _), Just (TAST.O, _, _, _)) -> throwError $ NonLinearUseOfVariable x pos
--       (Just (TAST.I, _, _, _), Just (TAST.O, _, _, _)) -> pure $ Just (TAST.O, x, src, ty)
--       (Just (TAST.O, _, _, _), Just (TAST.I, _, _, _)) -> pure $ Just (TAST.O, x, src, ty)
--       (Just (TAST.I, _, _, _), Just (TAST.I, _, _, _)) -> pure $ Just (TAST.I, x, src, ty)
--       (Just (u2, _, _, _), Nothing) -> pure $ Just (u2, x, src, ty)
--       (Nothing, Just (u2, _, _, _)) -> pure $ Just (u2, x, src, ty)
--       (_, _) -> pure $ Just (TAST.I, x, src, ty)
--     checkLinearVar (Just (u, x, src, ty)) _ _ = pure $ Just (u, x, src, ty)
--     checkLinearVar Nothing _ _ = pure Nothing
