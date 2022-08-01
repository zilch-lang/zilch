{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Typecheck.Checker (checkProgram, check) where

import Control.Monad (forM, unless, void, when)
import Control.Monad.Except (catchError, throwError)
import Control.Monad.State (gets)
import Control.Monad.Writer (tell)
import Data.Bifunctor (first)
import Data.Functor ((<&>))
import qualified Data.IntMap as IntMap
import qualified Data.List as List
import Data.List.Safe (indexed)
import Data.Located (Located ((:@)), Position, getPos, unLoc)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (catMaybes)
import Data.Text (Text)
import qualified Data.Text as Text
import Language.Zilch.Syntax.Core.AST (IntegerSuffix (..))
import qualified Language.Zilch.Syntax.Core.AST as AST
import Language.Zilch.Typecheck.Context
import qualified Language.Zilch.Typecheck.Core.AST as TAST
import Language.Zilch.Typecheck.Core.Eval (Closure (Clos), Environment, MetaEntry (Solved, Unsolved), Value (..), explicit, implicit)
import qualified Language.Zilch.Typecheck.Core.Multiplicity as TAST
import {-# SOURCE #-} Language.Zilch.Typecheck.Elaborator (MonadElab)
import Language.Zilch.Typecheck.Errors (ElabError (..), ElabWarning (..))
import Language.Zilch.Typecheck.Evaluator (apply, eval, force, quote)
import Language.Zilch.Typecheck.Metavars (freshMeta)
import Language.Zilch.Typecheck.Unification (unify)
import Language.Zilch.Typecheck.Usage (Usage)
import qualified Language.Zilch.Typecheck.Usage as Usage

checkProgram :: forall m. MonadElab m => Context -> Located AST.Module -> m (Located TAST.Module)
checkProgram ctx mod = do
  (TAST.Mod binds :@ p, ctx, usages) <- checkProgram' ctx mod

  metas <- gets (IntMap.toList . snd)
  addBinds <- forM metas \(m, e) -> do
    case e of
      (Unsolved _ _, path, p, loc) -> do
        let go TAST.Here = pure []
            go (TAST.Bind path mult x ty) = do
              ty' <- quote ctx (lvl ctx) ty
              ((unLoc x, mult, ty') :) <$> go path
            go (TAST.Define path _ _ _ _) = go path

        path' <- go path
        throwError $ CannotSolveHole path' p loc
      (Solved val mult ty, _, p, _) -> do
        val@(_ :@ p1) <- quote ctx (lvl ctx) (val :@ p)
        ty' <- quote ctx (lvl ctx) ty
        pure (TAST.Let False (mult :@ p) (Text.pack ("?" <> show m) :@ p) ty' val :@ p1)
  let addBinds' = (:@ p) . TAST.TopLevel [] False <$> addBinds

  checkAllDefined (types ctx) (env ctx)
  checkMutuallyRecursiveValues ctx (types ctx) usages

  pure $ TAST.Mod (addBinds' <> binds) :@ p
  where
    checkAllDefined :: forall m. MonadElab m => [(TAST.Multiplicity, Located Text, Origin, Located Value)] -> Environment -> m ()
    checkAllDefined [] [] = pure ()
    checkAllDefined ((_, x :@ p, _, _) : _) ((VUndefined :@ _) : _) = throwError $ UndefinedValue x p
    checkAllDefined (_ : types) (_ : env) = checkAllDefined types env
    checkAllDefined _ _ = error "checkAllDefined: impossible"

    checkMutuallyRecursiveValues :: forall m. MonadElab m => Context -> [(TAST.Multiplicity, Located Text, Origin, Located Value)] -> Map (Located Text) Usage -> m ()
    checkMutuallyRecursiveValues _ [] _ = pure ()
    checkMutuallyRecursiveValues ctx ((_, _, _, VPi {} :@ _) : types) usages = checkMutuallyRecursiveValues ctx types usages
    checkMutuallyRecursiveValues ctx ((_, x, _, _ :@ _) : types) usages = do
      checkRecursivity ctx [] x usages
      checkMutuallyRecursiveValues ctx types usages

    checkRecursivity _ stack@(_ : _ : _) x _
      | x == last stack =
        let y = last stack
         in throwError $ BindingWillEndUpCallingItself (unLoc y) (getPos y) (getPos x) (init stack)
    checkRecursivity ctx stack x usages = do
      usageX <- removeFunctionals ctx (usages Map.! x)
      let (_, _ :@ pos, _) = indexContext ctx x
      void $ flip Map.traverseWithKey usageX \k _ -> Just <$> checkRecursivity ctx ((unLoc x :@ pos) : stack) k usages

    removeFunctionals ctx usage = flip Map.traverseWithKey usage \k mult ->
      case indexContext ctx k of
        (_, _, VPi {} :@ _) -> pure Nothing
        (_, _, _) -> pure $ Just mult

checkProgram' :: forall m. MonadElab m => Context -> Located AST.Module -> m (Located TAST.Module, Context, Map (Located Text) Usage)
checkProgram' ctx (AST.Mod imports defs :@ p) = do
  case defs of
    [] -> pure (TAST.Mod [] :@ p, ctx, mempty)
    b : bs -> do
      (!b, ctx, u1) <- checkToplevel ctx b
      (TAST.Mod defs :@ p, ctx, u2) <- checkProgram' ctx (AST.Mod imports bs :@ p)

      pure (TAST.Mod (b : defs) :@ p, ctx, u1 <> u2)

checkToplevel :: forall m. MonadElab m => Context -> Located AST.TopLevel -> m (Located TAST.TopLevel, Context, Map (Located Text) Usage)
checkToplevel ctx (AST.TopLevel isPublic (AST.Let isRec mult name@(_ :@ p5) ty ex :@ p3) :@ p4) = do
  {-
     0Γ ⊢ A ⇐⁰ type ℓ            0Γ ⊢ e ⇐⁰ A          i = 0
    ──────────────────────────────────────────────────────── [⇐ let-I₀]
                           Γ ⊢ let x :ⁱ A := e

     0Γ₁ ⊢ A ⇐⁰ type ℓ             Γ₂ ⊢ e ⇐¹ A
    ─────────────────────────────────────────── [⇐ let-I₁]
             Γ₁ + iΓ₂ ⊢ let x :ⁱ A := e
  -}
  mty <- checkAlreadyBound name (types ctx) (env ctx) p5

  (ty, ty') <- case mty of
    Nothing -> do
      (_, ty) <- check TAST.Irrelevant ctx ty (VType :@ p3)
      ty' <- eval ctx ty

      pure (ty, ty')
    Just (m1, ty) -> do
      -- type has already been checked earlier
      -- but we still need to check that multiplicities match
      when (unLoc mult /= unLoc m1) do
        throwError $ MultiplicityMismatch m1 mult

      (,ty) <$> quote ctx (lvl ctx) ty

  (!ex, ex', usage) <- mdo
    let ctx' = if isRec then define TAST.Unrestricted name (VThunk ex' :@ p3) ty' ctx else ctx
    (usage, ex') <-
      first (Usage.scale $ unLoc mult) <$> case unLoc mult of
        TAST.O -> check TAST.Irrelevant ctx' ex ty'
        _ -> check TAST.Present ctx' ex ty'
    checkUsage ctx' usage (getPos ex)

    when isRec do
      case (Map.lookup name usage, ty') of
        (Nothing, _) -> tell [NonRecursiveRecursiveBinding (unLoc name) p5]
        (_, VPi {} :@ _) -> pure ()
        _ -> throwError $ RecursiveValueBinding (unLoc name) p5

    ex'' <- case ty of
      TAST.EPi {} :@ _ -> eval ctx' ex'
      _ -> pure $ VThunk ex' :@ getPos ex'
    pure (ex', ex'', usage)

  pure (TAST.TopLevel [] isPublic (TAST.Let isRec mult name ty ex :@ p3) :@ p4, define (unLoc mult) name ex' ty' ctx, Map.singleton name usage)
checkToplevel ctx (AST.TopLevel isPublic (AST.Val mult name@(_ :@ p6) ty :@ p4) :@ p5) = do
  (_, ty) <- check TAST.Irrelevant ctx ty (VType :@ p4)
  ty' <- eval ctx ty

  let ctx' = define (unLoc mult) name (VUndefined :@ p6) ty' ctx
  pure (TAST.TopLevel [] isPublic (TAST.Val mult name ty :@ p4) :@ p5, ctx', mempty)

checkAlreadyBound :: forall m. MonadElab m => Located Text -> [(TAST.Multiplicity, Located Text, Origin, Located Value)] -> Environment -> Position -> m (Maybe (Located TAST.Multiplicity, Located Value))
checkAlreadyBound _ [] [] _ = pure Nothing
checkAlreadyBound x ((mult, x', origin, ty) : types) ((val :@ _) : env) p5
  | x == x' && origin == Source = case val of
    VUndefined -> pure $ Just (mult <$ x', ty)
    _ -> throwError $ IdentifierAlreadyBound (unLoc x') (getPos x') p5
  | otherwise = checkAlreadyBound x types env p5
checkAlreadyBound _ _ _ _ = error "checkAlreadyDefined: impossible"

insert' :: forall m. MonadElab m => Context -> (Usage, Located TAST.Expression, Located Value, Located TAST.Multiplicity) -> m (Usage, Located TAST.Expression, Located Value, Located TAST.Multiplicity)
insert' ctx (qs, expr, ty, usage) = do
  ty <- force ctx ty
  case ty of
    VPi imp args b :@ p | imp == implicit -> do
      ms <- flip traverse args \(mult, _, a) -> (:@ p) <$> freshMeta ctx mult a p AST.InsertedHole
      mv <- traverse (eval ctx) ms
      ty <- apply ctx b mv
      insert' ctx (qs, TAST.EApplication expr True ms :@ p, ty, usage)
    va -> pure (qs, expr, va, usage)

insert :: forall m. MonadElab m => Context -> (Usage, Located TAST.Expression, Located Value, Located TAST.Multiplicity) -> m (Usage, Located TAST.Expression, Located Value, Located TAST.Multiplicity)
insert ctx (qs, expr, ty, usage) = case (expr, ty) of
  (t@(TAST.ELam (TAST.Parameter True _ :@ _) _ :@ _), va) -> pure (qs, t, va, usage)
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
      let (m', _, ty) = indexContext ctx x
       in if mult <= m'
            then acc
            else Just (mult, m', x, ty) : acc

    quoteTypes :: forall m. MonadElab m => [(TAST.Multiplicity, TAST.Multiplicity, Located Text, Located Value)] -> m [(TAST.Multiplicity, TAST.Multiplicity, Located Text, Located TAST.Expression)]
    quoteTypes [] = pure []
    quoteTypes ((p, q, x, ty) : xs) = do
      ty <- quote ctx (lvl ctx) ty
      xs <- quoteTypes xs
      pure $ (p, q, x, ty) : xs

-- | Locally bind a variable for use in a typechecking computation, and check afterwards that its usage matches the one expected.
withLocalVar :: forall m a. MonadElab m => Located Text -> TAST.Multiplicity -> Located Value -> Context -> (Context -> m (Usage, Position, a)) -> m (Usage, a)
withLocalVar x mult ty ctx f = do
  let ctx' = bind mult x ty ctx
  (qs, pos, exp) <- f ctx'
  qs' <- checkVar ctx' x qs pos
  pure (qs', exp)
  where
    checkVar ctx x qs pos = do
      (q, qs') <- splitUsage x qs
      checkUsage ctx (Map.singleton x q) pos
      pure qs'

    splitUsage :: Located Text -> Usage -> m (TAST.Multiplicity, Usage)
    splitUsage x m =
      let m' = Map.delete x m
       in (,m') <$> case Map.lookup x m of
            Nothing -> do
              -- tell [UnusedBinding (unLoc x) (getPos x)]

              -- FIXME: `let f(x) := x` reports `x` as unused
              -- This is because of how it is desugared:
              --
              -- > let f : (ω x : _) → _ ≔ λ(ω x : _) ⇒ x
              --
              -- In such case, `x` is not used in the second hole, therefore unused when
              -- locally bound at the type-level.
              -- This function will need a bit of refinement.
              pure TAST.O
            Just m -> pure m

-- | Locally define a variable for use in a typechecking computation, and check afterwards that its usage matches the one expected.
defineLocal :: forall m. MonadElab m => Located Text -> TAST.Multiplicity -> Located Value -> Located Value -> Context -> (Context -> m (Usage, Located TAST.Expression)) -> m (Usage, Located TAST.Expression)
defineLocal x mult ex ty ctx f = do
  let ctx' = define mult x ex ty ctx
  (qs, exp) <- f ctx'
  qs' <- checkVar ctx' x qs (getPos exp)
  pure (qs', exp)
  where
    checkVar ctx x qs pos = do
      (q, qs') <- splitUsage x qs
      checkUsage ctx (Map.singleton x q) pos
      pure qs'

    splitUsage :: Located Text -> Usage -> m (TAST.Multiplicity, Usage)
    splitUsage x m =
      let m' = Map.delete x m
       in (,m') <$> case Map.lookup x m of
            Nothing -> do
              tell [UnusedBinding (unLoc x) (getPos x)]
              pure TAST.O
            Just m -> pure m

-- | @check Γ i e τ@ is the typing judgment @Γ ⊢ e ⇐ⁱ τ@.
check :: forall m. MonadElab m => TAST.Relevance -> Context -> Located AST.Expression -> Located Value -> m (Usage, Located TAST.Expression)
check rel ctx expr ty = do
  ty <- force ctx ty
  case (expr, ty) of
    (AST.ELam (AST.Parameter isImplicit args1 :@ p1) expr :@ p3, VPi imp args2 ty3 :@ p2) | isImplicit == not imp -> do
      -- m1 x ty | m2 _ ty2
      -- when (unLoc m1 /= m2) do
      --   throwError $ MultiplicityMismatch (m2 :@ p2) m1
      {-
         0Γ ⊢ Aₑ :⁰ type ℓ        Γ, xₑ :ⁱᵖ Aₑ ⊢ e ⇐ⁱ B
                 Γ, xₑ :ⁱᵖ Aₑ ⊢ xₑ₊₁ ⇐ᵖ Aₑ₊₁
        ──────────────────────────────────────────────── [⇐ λ-I]
            Γ ⊢ (λ(xₑ :ᵖ Aₑ) ⇒ e) ⇐ⁱ (xₑ :ᵖ Aₑ) → B
      -}
      when (length args1 /= length args2) do
        throwError $ IncorrectNumberOfArguments (length args1) (length args2) p3

      let go ctx [] [] = do
            ty3' <- apply ctx ty3 (indexed args1 <&> \(i, (_, x, _)) -> VVariable x (lvl ctx - fromIntegral (length args1 - i)) :@ p2)
            (qs, e) <- check rel ctx expr ty3'
            pure (qs, getPos e, ([], e))
          go ctx ((m1, x, ty) : args1) ((m2, _, ty2) : args2) = do
            when (unLoc m1 /= m2) do
              throwError $ MultiplicityMismatch (m2 :@ getPos ty2) (unLoc m1 :@ getPos ty)

            (qs1, ty) <- check TAST.Irrelevant ctx ty (VType :@ p1)
            let xMultiplicity = TAST.extend rel * unLoc m1

            ty' <- eval ctx ty
            unify ctx ty' ty2

            (qs2, (args1', e)) <- withLocalVar x xMultiplicity ty2 ctx \ctx -> go ctx args1 args2

            pure (Usage.merge qs1 qs2, p3, ((m1, x, ty) : args1', e))
          go _ _ _ = error "impossible"

      (qs, _, (args, u)) <- go ctx args1 args2

      pure (qs, TAST.ELam (TAST.Parameter isImplicit args :@ p1) u :@ p3)
    (expr@(_ :@ p1), VPi imp args ty3 :@ p2) | imp == implicit -> do
      ty' <- apply ctx ty3 (indexed args <&> \(i, (_, x, _)) -> VVariable (x :@ p2) (lvl ctx - fromIntegral (length args - i)) :@ p2)
      let ctx' = foldl (\ctx (m2, x, ty2) -> insertBinder m2 (x :@ p2) ty2 ctx) ctx args
      (qs, u) <- check TAST.Present ctx' expr ty'
      -- TODO: is @ω@ the correct multiplicity to be infered for the parameter here?

      args' <- flip traverse (indexed args) \(i, (m2, x, ty)) -> (m2 :@ p2,x :@ p2,) <$> quote ctx (lvl ctx - fromIntegral (length args - i)) ty

      pure (qs, TAST.ELam (TAST.Parameter True args' :@ p1) u :@ p1)
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
          (_, ex) <- check TAST.Irrelevant ctx ex ty'
          ex' <- eval ctx ex

          (_, u) <- defineLocal x TAST.O ex' ty' ctx \ctx ->
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

          (_, ex) <- do
            rec (qs2, ex') <- defineLocal x TAST.O (VThunk ex' :@ p1) ty' ctx \ctx ->
                  check TAST.Irrelevant ctx ex ty'
            -- let ctx' = define TAST.O x (VThunk ex' :@ p1) ty' ctx
            -- (qs2, ex') <- check TAST.Irrelevant ctx' ex ty'
            pure (qs2, ex')

          ex' <- eval ctx ex
          (_, u) <- defineLocal x TAST.O ex' ty' ctx \ctx ->
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
    (AST.EPi (AST.Parameter isImplicit args :@ p1) ty2 :@ p2, VType :@ p3) -> do
      when (rel /= TAST.Irrelevant) do
        throwError $ MultiplicityMismatch (TAST.extend rel :@ p3) (TAST.O :@ p3)
      {-
         0Γ, xₑ :⁰ Sₑ ⊢ Sₑ₊₁ ⇐⁰ type ℓₑ₊₁          0Γ, xₑ :⁰ Aₑ ⊢ B ⇐⁰ type ℓ₂
        ─────────────────────────────────────────────────────────────────────── [⇐ Π-F]
                 0Γ ⊢ (xₑ :ᵖ Sₑ) → B ⇐⁰ type (ℓₑ ⊔ ℓ₂)
      -}
      let go ctx [] = do
            (qs, e) <- check TAST.Irrelevant ctx ty2 (VType :@ p2)
            pure (qs, getPos e, ([], e))
          go ctx ((m1, x, ty) : args) = do
            (qs1, ty) <- check TAST.Irrelevant ctx ty (VType :@ p1)
            ty' <- eval ctx ty
            (qs2, (args, ty2)) <- withLocalVar x TAST.O ty' ctx \ctx -> go ctx args

            pure (Usage.concat qs1 qs2, p2, ((m1, x, ty) : args, ty2))

      (_, _, (args', ty2)) <- go ctx args
      pure (mempty, TAST.EPi (TAST.Parameter isImplicit args' :@ p1) ty2 :@ p2)
    (AST.EHole loc :@ p1, ty) -> do
      meta <- freshMeta ctx (TAST.extend rel) ty p1 loc
      pure (mempty, meta :@ p1)
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
synthetize rel ctx (AST.EInteger i suffix :@ p) = do
  {-
     n is a literal number
    ─────────────────────── [⇒ integer-I]
         Γ ⊢ n ⇒^ω uN
  -}
  let ty = typeForSuffix suffix :@ p
  tmp <- quote ctx (lvl ctx) ty
  let TAST.EBuiltin ty' :@ _ = tmp
  pure (mempty, TAST.EInteger i ty' :@ p, ty, TAST.extend rel :@ p)
  where
    typeForSuffix SuffixU64 = VBuiltinU64
    typeForSuffix SuffixU32 = VBuiltinU32
    typeForSuffix SuffixU16 = VBuiltinU16
    typeForSuffix SuffixU8 = VBuiltinU8
    typeForSuffix SuffixS64 = VBuiltinS64
    typeForSuffix SuffixS32 = VBuiltinS32
    typeForSuffix SuffixS16 = VBuiltinS16
    typeForSuffix SuffixS8 = VBuiltinS8
synthetize rel _ (AST.ECharacter c :@ p) =
  {-
     c is a literal character
    ────────────────────────── [⇒ char-I]
          Γ ⊢ c ⇒^ω char
  -}
  pure (mempty, TAST.ECharacter c :@ p, VVariable ("char" :@ p) 0 :@ p, TAST.extend rel :@ p)
synthetize rel _ (AST.EBoolean bool :@ p) =
  {-
     b is a boolean literal
    ──────────────────────── [⇒ bool-I]
         Γ ⊢ b ⇒^ω bool
  -}
  pure (mempty, TAST.EBoolean bool :@ p, VBuiltinBool :@ p, TAST.extend rel :@ p)
synthetize rel ctx (AST.EApplication e1 isImp es :@ p) = do
  {-
     Γ ⊢ f ⇒ⁱ (yₑ :ᵖ Aₑ) → B          0Γ ⊢ xₑ ⇐⁰ Aₑ          ip = 0
    ──────────────────────────────────────────────────────────────── [⇐ λ-E₀]
                         Γ ⊢ f(xₑ) ⇐ᵖ B[y\x]

     Γ₁ ⊢ f ⇒ⁱ (yₑ :ᵖ Aₑ) → B          Γ₂ ⊢ xₑ ⇐¹ Aₑ
    ───────────────────────────────────────────────── [⇐ λ-E₁]
               Γ₁ + ipΓ₂ ⊢ f(xₑ) ⇒ⁱ B[y\x]
    -}
  (icit, e1, qs1, t1, m1) <- case isImp of
    True -> do
      (qs, e1, t1, m1) <- synthetize rel ctx e1
      pure (implicit, e1, qs, t1, m1)
    False -> do
      (qs, e1, t1, m1) <- insert' ctx =<< synthetize rel ctx e1
      pure (explicit, e1, qs, t1, m1)

  t1 <- force ctx t1
  (args, b) <- case t1 of
    VPi i args b :@ p2 -- u _ a
      | i == icit -> pure (args, b)
      | otherwise -> throwError $ ImplicitMismatch icit i p2
    t1@(_ :@ p2) -> do
      -- try η-expanding
      let usage = TAST.lub (TAST.extend rel) TAST.O
      args <- forM (indexed es) \(i, _) -> do
        a <- eval ctx . (:@ p) =<< freshMeta ctx usage (VType :@ p) p AST.InsertedHole
        pure (TAST.W, Text.pack ("$" <> show i), a)
      let ctx' = foldr (\(m, x, a) ctx -> bind m (x :@ p) a ctx) ctx args

      meta <- freshMeta ctx' usage (VType :@ p) p AST.InsertedHole
      let b = Clos (env ctx) $ meta :@ p2

      unify ctx t1 (VPi explicit args b :@ p2)
      pure (args, b)

  when (length args /= length es) do
    throwError $ IncorrectNumberOfArguments (length es) (length args) p

  case any (\(m2, _, _) -> unLoc m1 * m2 == TAST.O) args of
    True -> do
      let go :: forall m. MonadElab m => [Located AST.Expression] -> [(TAST.Multiplicity, Text, Located Value)] -> m (Usage, ([Located TAST.Expression], [Located Value]))
          go [e2] [(_, _, a)] = do
            (qs2, e2) <- check TAST.Irrelevant ctx e2 a
            e2' <- eval ctx e2
            pure (qs2, ([e2], [e2']))
          go (e2 : args) (a2 : args') = do
            (qs2, (args1, args1')) <- go [e2] [a2]
            (qs2', (args2, args2')) <- go args args'
            pure (qs2 `Usage.merge` qs2', (args1 <> args2, args1' <> args2'))
          go _ _ = error "impossible"

      (qs2, (args, args')) <- go es args
      b <- apply ctx b args'

      pure (qs1 `Usage.merge` qs2, TAST.EApplication e1 (not icit) args :@ p, b, m1)
    False -> do
      let go :: forall m. MonadElab m => [Located AST.Expression] -> [(TAST.Multiplicity, Text, Located Value)] -> m (Usage, ([Located TAST.Expression], [Located Value]))
          go [e2] [(m2, _, a)] = do
            (qs2, e2) <- check TAST.Present ctx e2 a
            e2' <- eval ctx e2
            pure (Usage.scale (unLoc m1 * m2) qs2, ([e2], [e2']))
          go (e2 : args) (a2 : args') = do
            (qs2, (args1, args1')) <- go [e2] [a2]
            (qs2', (args2, args2')) <- go args args'
            pure (qs2 `Usage.merge` qs2', (args1 <> args2, args1' <> args2'))
          go _ _ = error "impossible"

      (qs2, (args, args')) <- go es args
      b <- apply ctx b args'

      pure (qs1 `Usage.concat` qs2, TAST.EApplication e1 (not icit) args :@ p, b, m1)
synthetize rel ctx (AST.EIdentifier x :@ p) = do
  {-
    ──────────────────── [⇒ var-I]
     Γ, x :ᵖ A ⊢ x ⇒ᵖ A
  -}
  (ex, ty, usage) <- go 0 (types ctx)
  case (rel, usage) of
    (TAST.Irrelevant, TAST.I) -> throwError $ RelevantVariableInIrrelevantContext (unLoc x) TAST.I p
    (TAST.Irrelevant, TAST.W) -> throwError $ RelevantVariableInIrrelevantContext (unLoc x) TAST.W p
    _ -> pure ()
  case ex of
    TAST.EBuiltin _ :@ _ -> pure (mempty, ex, ty, usage :@ p)
    _ -> pure (Map.singleton x $ TAST.extend rel, ex, ty, usage :@ p)
  where
    go _ [] = checkBuiltin
    go ix ((usage, x', origin, a) : types)
      | x == x' && origin == Source = pure (TAST.EIdentifier x' ix :@ p, a, usage)
      | otherwise = go (ix + 1) types

    checkBuiltin = case unLoc x of
      "u8" -> pure (TAST.EBuiltin TAST.TyU8 :@ p, VType :@ p, TAST.O)
      "u16" -> pure (TAST.EBuiltin TAST.TyU16 :@ p, VType :@ p, TAST.O)
      "u32" -> pure (TAST.EBuiltin TAST.TyU32 :@ p, VType :@ p, TAST.O)
      "u64" -> pure (TAST.EBuiltin TAST.TyU64 :@ p, VType :@ p, TAST.O)
      "s8" -> pure (TAST.EBuiltin TAST.TyS8 :@ p, VType :@ p, TAST.O)
      "s16" -> pure (TAST.EBuiltin TAST.TyS16 :@ p, VType :@ p, TAST.O)
      "s32" -> pure (TAST.EBuiltin TAST.TyS32 :@ p, VType :@ p, TAST.O)
      "s64" -> pure (TAST.EBuiltin TAST.TyS64 :@ p, VType :@ p, TAST.O)
      "bool" -> pure (TAST.EBuiltin TAST.TyBool :@ p, VType :@ p, TAST.O)
      name -> throwError $ BindingNotFound name p
synthetize rel _ (AST.EType :@ p) = do
  when (rel /= TAST.Irrelevant) do
    throwError $ ErasedInRelevantContext p
  {-
    ────────────────── [⇒ type-F]
     Γ ⊢ type ⇒⁰ type
  -}
  pure (mempty, TAST.EType :@ p, VType :@ p, TAST.O :@ p)
synthetize rel ctx (AST.EPi (AST.Parameter isImplicit args :@ p2) expr :@ p) = do
  when (rel /= TAST.Irrelevant) do
    throwError $ ErasedInRelevantContext p
  {-
     0Γ ⊢ A ⇐⁰ type       0Γ, xᵢ :⁰ Aᵢ ⊢ B ⇐⁰ type
              0Γ, xᵢ :⁰ Aᵢ ⊢ xᵢ₊₁ ⇐⁰ Aᵢ₊₁
    ─────────────────────────────────────────────── [⇒ Π-F]
              0Γ ⊢ (xᵢ :ᵖ Aᵢ) → B ⇒⁰ type
  -}
  (_, _, (args, b)) <- go ctx expr args
  -- (_, ty) <- check TAST.Irrelevant ctx ty (VType :@ p)
  -- ty' <- eval ctx ty
  -- (_, b) <- withLocalVar name TAST.O ty' ctx \ctx -> do
  --   (qs, e) <- check TAST.Irrelevant ctx expr (VType :@ p)
  --   pure (qs, getPos e, e)
  pure (mempty, TAST.EPi (TAST.Parameter isImplicit args :@ p2) b :@ p, VType :@ p, TAST.O :@ p)
  where
    go ctx expr [] = do
      (qs, e) <- check TAST.Irrelevant ctx expr (VType :@ p)
      pure (qs, getPos e, ([], e))
    go ctx expr ((m1, name, ty) : args) = do
      (_, ty) <- check TAST.Irrelevant ctx ty (VType :@ p)
      ty' <- eval ctx ty

      (qs, (args, b)) <- withLocalVar name TAST.O ty' ctx \ctx -> do
        go ctx expr args
      pure (qs, getPos name, ((m1, name, ty) : args, b))
synthetize rel ctx (AST.ELam (AST.Parameter isImplicit args :@ p2) ex :@ p) = do
  -- m1 name ty
  {-
     0Γ ⊢ A ⇐⁰ type ℓ       Γ, xₑ :ⁱᵖ Aₑ ⊢ e ⇒ᵖ B
    ────────────────────────────────────────────── [⇒ λ-I]
      ipΓ ⊢ (λ(xₑ :ⁱ Aₑ) ⇒ e) ⇒ᵖ (xₑ :ⁱ Aₑ) → B
  -}
  let ip = sum [TAST.extend rel * unLoc m | (m, _, _) <- args]
  (qs1, _, (args, args', ex, b, u2)) <- go ctx ex args
  -- (_, ty) <- check TAST.Irrelevant ctx ty (VType :@ p)
  -- ty' <- eval ctx ty
  -- let ip = unLoc m1 * TAST.extend rel
  -- (qs1, (ex, b, u2)) <- withLocalVar name ip ty' ctx \ctx -> do
  --   (u, ex, b, u2) <- synthetize rel ctx ex
  --   pure (u, getPos ex, (ex, b, u2))

  clos <- closeVal ctx b
  pure (Usage.scale ip qs1, TAST.ELam (TAST.Parameter isImplicit args :@ p2) ex :@ p, VPi (not isImplicit) args' clos :@ p, u2)
  where
    go ctx ex [] = do
      (u, ex, b, u2) <- synthetize rel ctx ex
      pure (u, getPos ex, ([], [], ex, b, u2))
    go ctx ex ((m1, name, ty) : args) = do
      (_, ty) <- check TAST.Irrelevant ctx ty (VType :@ p)
      ty' <- eval ctx ty
      let ip = unLoc m1 * TAST.extend rel
      (qs1, (args, args', ex, b, u2)) <- withLocalVar name ip ty' ctx \ctx -> do
        go ctx ex args
      pure (qs1, getPos name, ((m1, name, ty) : args, (unLoc m1, unLoc name, ty') : args', ex, b, u2))
synthetize rel ctx (AST.EHole loc :@ p1) = do
  meta1 <- freshMeta ctx (TAST.extend rel) (VType :@ p1) p1 loc
  a <- eval ctx (meta1 :@ p1)
  meta2 <- freshMeta ctx (TAST.extend rel) a p1 loc
  let t = meta2 :@ p1
  pure (mempty, t, a, TAST.extend rel :@ p1)
synthetize rel ctx (AST.EIfThenElse c t e :@ p) = do
  {-
     0Γ ⊢ c ⇐⁰ bool          Γ ⊢ t ⇒ᵖ A          Γ ⊢ e ⇒ᵖ B
    ──────────────────────────────────────────────────────── [⇐ bool-E₀]
          Γ ⊢ if c then t else e ⇒ᵖ if c then A else B

      Γ₀ ⊢ c ⇒ⁱ bool         Γ₁ ⊢ t ⇒¹ A            Γ₁ ⊢ e ⇒¹ A
    ───────────────────────────────────────────────────────────── [⇐ bool-E₁]
               Γ₀ + pΓ₁ ⊢ if c then t else e ⇒ᵖ A
  -}
  (qs0, c, bool, m1) <-
    do
      (qs, c) <- check TAST.Irrelevant ctx c (VBuiltinBool :@ getPos c)
      pure (qs, c, VBuiltinBool :@ getPos c, TAST.O :@ getPos c)
      `catchError` \_ -> synthetize TAST.Present ctx c
  c' <- eval ctx c

  case m1 of
    TAST.O :@ _ -> do
      -- apply [⇐ bool-E₀]
      (qs1, t, a, u1) <- synthetize rel ctx t
      (qs2, e, b, u2) <- synthetize rel ctx e

      when (unLoc u1 /= unLoc u2) do
        throwError $ MultiplicityMismatch u1 u2

      let qs1' = qs1 `Usage.merge` qs2

      pure (qs0 `Usage.concat` qs1', TAST.EIfThenElse c t e :@ p, VIfThenElse c' a b :@ p, u1)
    p' -> do
      -- apply [⇐ bool-E₁]
      unify ctx bool (VBuiltinBool :@ getPos c)

      (qs1, t, a, u1) <- synthetize TAST.Present ctx t
      (qs2, e, b, u2) <- synthetize TAST.Present ctx e

      unify ctx a b
      when (unLoc u1 /= unLoc u2) do
        throwError $ MultiplicityMismatch u1 u2

      let qs1' = qs1 `Usage.merge` qs2

      pure (qs0 `Usage.concat` Usage.scale (unLoc p') qs1', TAST.EIfThenElse c t e :@ p, a, p')
synthetize _ _ expr = error $ "not yet handled: " <> show expr

closeVal :: forall m. MonadElab m => Context -> Located Value -> m Closure
closeVal ctx ty = do
  ty <- quote ctx (lvl ctx + 1) ty
  pure $ Clos (env ctx) ty
