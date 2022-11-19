{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NoOverloadedLists #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Typecheck.Checker (checkProgram, check) where

import Control.Monad (forM, unless, void, when)
import Control.Monad.Except (catchError, throwError)
import Control.Monad.Writer (tell)
import Data.Bifunctor (Bifunctor (..), first, second)
import Data.Foldable (foldl', foldlM)
import Data.Functor ((<&>))
import qualified Data.List as List
import Data.Located (Located ((:@)), Position, getPos, unLoc)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (catMaybes)
import Data.Text (Text)
import Debug.Trace (trace, traceShow)
import qualified Language.Zilch.CLI.Flags as W (WarningFlags (..))
import Language.Zilch.Syntax.Core.AST (IntegerSuffix (..))
import qualified Language.Zilch.Syntax.Core.AST as AST
import Language.Zilch.Typecheck.Context
import qualified Language.Zilch.Typecheck.Core.AST as TAST
import Language.Zilch.Typecheck.Core.Eval (Closure (Clos), Environment, Value (..), explicit, implicit)
import qualified Language.Zilch.Typecheck.Core.Multiplicity as TAST
import {-# SOURCE #-} Language.Zilch.Typecheck.Elaborator (MonadElab)
import Language.Zilch.Typecheck.Errors (ElabError (..), ElabWarning (..))
import Language.Zilch.Typecheck.Evaluator (apply, apply', eval, force, quote)
import Language.Zilch.Typecheck.Imports (ImportCache, ModuleInterface (..), Namespace (..))
import qualified Language.Zilch.Typecheck.Imports as ImportCache
import Language.Zilch.Typecheck.Metavars (freshMeta)
import Language.Zilch.Typecheck.Simplifier (inlineMetavariables)
import Language.Zilch.Typecheck.Unification (unify)
import Language.Zilch.Typecheck.Usage (Usage)
import qualified Language.Zilch.Typecheck.Usage as Usage

checkProgram :: forall m. MonadElab m => ImportCache -> Context -> Located AST.Module -> m (Located TAST.Module, ModuleInterface)
checkProgram cache ctx mod = do
  (mod, iface, ctx, usages) <- checkProgram' cache ctx mod

  mod <- inlineMetavariables mod ctx

  checkMutuallyRecursiveValues ctx (types ctx) usages
  checkAllDefined (types ctx) (env ctx)

  pure (mod, iface)
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
      usageX <- maybe (pure mempty) (removeFunctionals ctx) (Map.lookup x usages)
      let (_, _ :@ pos, _) = indexContext ctx x
      void $ flip Map.traverseWithKey usageX \k _ -> Just <$> checkRecursivity ctx ((unLoc x :@ pos) : stack) k usages

    removeFunctionals ctx usage = flip Map.traverseWithKey usage \k mult ->
      case indexContext ctx k of
        (_, _, VPi {} :@ _) -> pure Nothing
        (_, _, _) -> pure $ Just mult

checkProgram' :: forall m. MonadElab m => ImportCache -> Context -> Located AST.Module -> m (Located TAST.Module, ModuleInterface, Context, Map (Located Text) Usage)
checkProgram' cache ctx (AST.Mod defs :@ p) = do
  case defs of
    [] -> pure (TAST.Mod [] :@ p, mempty, ctx, mempty)
    b : bs -> do
      (!b, ctx, u1) <- checkToplevel cache ctx b
      iface' <-
        mconcat
          <$> forM b \(TAST.TopLevel _ isPublic def :@ _) -> case def of
            (TAST.Let _ mult name ty ex :@ _) -> do
              let ctx' = unbind ctx
              ty <- force ctx' =<< eval ctx' ty
              ex <- eval ctx' ex
              let addNS = ((name, SingleNS mult ty ex) :)
              pure $ (if isPublic then first addNS else second addNS) ([], [])
            (TAST.Val mult name ty :@ _) -> pure ([], [])
            (TAST.External mult name ty ex _ _ :@ _) -> do
              ty <- force ctx =<< eval ctx ty
              ex <- eval ctx ex
              let addNS = ((name, SingleNS mult ty ex) :)
              pure $ (if isPublic then first addNS else second addNS) ([], [])
      let iface'' = mkInterface iface'

      (TAST.Mod defs :@ p, iface, ctx, u2) <- checkProgram' cache ctx (AST.Mod bs :@ p)

      pure (TAST.Mod (b <> defs) :@ p, iface <> iface'', ctx, u1 <> u2)
  where
    mkInterface = uncurry Iface . bimap Map.fromList Map.fromList

checkToplevel :: forall m. MonadElab m => ImportCache -> Context -> Located AST.TopLevel -> m ([Located TAST.TopLevel], Context, Map (Located Text) Usage)
checkToplevel cache ctx (AST.TopLevel isPublic metas (AST.Let isRec mult name@(_ :@ p5) ty ex :@ p3) :@ p4) = do
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
      (_, ty) <- check cache TAST.Irrelevant ctx ty (VType :@ p3)
      ty' <- eval ctx ty

      pure (ty, ty')
    Just (m1, ty) -> do
      -- type has already been checked earlier
      -- but we still need to check that multiplicities match
      when (unLoc mult /= unLoc m1) do
        throwError $ MultiplicityMismatch m1 mult

      (,ty) <$> quote ctx (lvl ctx) ty

  (ex, ex', usage) <- mdo
    let ctx' = if isRec then define TAST.Unrestricted name (VThunk ex' :@ p3) ty' ctx else ctx
    (usage, ex') <-
      first (Usage.scale $ unLoc mult) <$> case unLoc mult of
        TAST.O -> check cache TAST.Irrelevant ctx' ex ty'
        _ -> check cache TAST.Present ctx' ex ty'
    checkUsage ctx' usage (getPos ex)

    when isRec do
      case (Map.lookup name usage, ty') of
        (Nothing, _) -> when (W.recNonRec ?warnings) do
          tell [NonRecursiveRecursiveBinding (unLoc name) p5]
        (_, VPi {} :@ _) -> pure ()
        _ -> throwError $ RecursiveValueBinding (unLoc name) p5

    -- ex'' <- case ty of
    --   TAST.EPi {} :@ _ -> eval ctx' ex'
    --   TAST.ELam {} :@ _ -> eval ctx' ex'
    --   TAST.EAdditiveProduct {} :@ _ -> eval ctx' ex'
    --   TAST.EMultiplicativeProduct {} :@ _ -> eval ctx' ex'
    --   _ -> pure $ VThunk ex' :@ getPos ex'
    ex'' <- eval ctx ex'
    pure (ex', ex'', usage)

  let metas' = toTASTMetas <$> metas
  pure ([TAST.TopLevel metas' isPublic (TAST.Let isRec mult name ty ex :@ p3) :@ p4], define (unLoc mult) name ex' ty' ctx, Map.singleton name usage)
checkToplevel cache ctx (AST.TopLevel isPublic metas (AST.Val mult name@(_ :@ p6) ty :@ p4) :@ p5) = do
  (_, ty) <- check cache TAST.Irrelevant ctx ty (VType :@ p4)
  ty' <- eval ctx ty

  let val =
        if any
          ( \(m :@ _) -> case m of
              AST.Foreign {} -> True
              _ -> False
          )
          metas
          then VFFI name [] :@ p6
          else VUndefined :@ p6
  let ctx' = define (unLoc mult) name val ty' ctx

  let metas' = toTASTMetas <$> metas
  pure ([TAST.TopLevel metas' isPublic (TAST.Val mult name ty :@ p4) :@ p5], ctx', mempty)
checkToplevel cache ctx (AST.TopLevel isPublic _ (AST.Import isOpen mod access path :@ _) :@ p5) = do
  binds <- resolveImport cache isOpen mod access path p5

  let ctx' = foldl' (\ctx (m :@ _, name, ty, ex) -> define m name ex ty ctx) ctx binds
  top <- forM binds \(m, name, ty, ex) -> do
    ty <- quote ctx (lvl ctx) ty
    ex <- quote ctx (lvl ctx) ex
    pure $ TAST.TopLevel [] isPublic (TAST.External m name ty ex (mod <> access <> [name | isOpen]) path :@ p5) :@ p5
  pure (top, ctx', Map.fromList $ binds <&> \(_, name, _, _) -> (name, mempty))

toTASTMetas :: Located AST.MetaAttribute -> Located TAST.MetaAttribute
toTASTMetas (AST.Inline :@ p) = TAST.Inline :@ p
toTASTMetas (AST.Foreign conv name :@ p) = TAST.Foreign (toConv conv) name :@ p
  where
    toConv (AST.CCall :@ _) = TAST.CCall

resolveImport :: forall m. MonadElab m => ImportCache -> Bool -> [Located Text] -> [Located Text] -> FilePath -> Position -> m [(Located TAST.Multiplicity, Located Text, Located Value, Located Value)]
resolveImport cache isOpen mod access path p5 = case ImportCache.lookup (path, mod) cache of
  Nothing -> throwError $ UnresolvedModule mod p5
  Just iface@(Iface pub _) -> case access of
    [] ->
      if isOpen
        then pure $ insertName <$> Map.toList pub
        else pure [(TAST.A :@ p5, last mod, mkComposite pub :@ p5, mkRecord pub :@ p5)]
    path -> fetchFromPath path iface
  where
    fetchFromPath [] _ = undefined
    fetchFromPath [x] (Iface pub priv) =
      case Map.lookup x pub of
        Just (SingleNS mult ty ex) -> do
          -- when isOpen do
          --   tell [UselessOpenOnNonNamespace x p5]
          pure [(mult, x, ty, ex)]
        Just (MultipleNS mult val within) -> undefined
        Nothing -> case Map.lookup x priv of
          Just _ -> throwError $ PrivateModuleImport x p5
          Nothing -> throwError $ UnresolvedNamespace mod x p5
    fetchFromPath (x : xs) (Iface pub priv) = undefined

    insertName (x, SingleNS m ty ex) = (m, x, ty, ex)
    insertName (x, MultipleNS m ty (Iface pub _)) = (m, x, ty, mkRecord pub :@ getPos x)

    mkComposite fields = VModule $ Map.mapWithKey mkCompositeFieldFromNS fields
    mkCompositeFieldFromNS _ (SingleNS mult ty _) = (mult, ty)
    mkCompositeFieldFromNS _ (MultipleNS mult ty _) = (mult, ty)

    mkRecord fields = VRecord $ undefined -- TODO: Map.mapWithKey mkRecordFieldFromNS fields
    mkRecordFieldFromNS _ (SingleNS mult ty ex) = (mult, ty, ex)
    mkRecordFieldFromNS (_ :@ p) (MultipleNS mult ty (Iface pub _)) = (mult, ty, mkRecord pub :@ p)

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
    VPi mult _ imp a _ b :@ p | imp == implicit -> do
      m <- (:@ p) <$> freshMeta ctx mult a p AST.InsertedHole
      mv <- eval ctx m
      a <- quote ctx (lvl ctx) a
      ty <- apply ctx b mv
      insert' ctx (qs, TAST.EApplication expr True a m :@ p, ty, usage)
    va -> pure (qs, expr, va, usage)

insert :: forall m. MonadElab m => Context -> (Usage, Located TAST.Expression, Located Value, Located TAST.Multiplicity) -> m (Usage, Located TAST.Expression, Located Value, Located TAST.Multiplicity)
insert ctx (qs, expr, ty, usage) = case (expr, ty) of
  (t@(TAST.ELam (TAST.Parameter True _ _ _ :@ _) _ _ :@ _), va) -> pure (qs, t, va, usage)
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
              -- when (W.unusedBinding ?warnings) do
              --   tell [UnusedBinding (unLoc x) (getPos x)]

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
defineLocal :: forall m a. MonadElab m => Located Text -> TAST.Multiplicity -> Located Value -> Located Value -> Context -> (Context -> m (Usage, Position, a)) -> m (Usage, a)
defineLocal x mult ex ty ctx f = do
  let ctx' = define mult x ex ty ctx
  (qs, pos, res) <- f ctx'
  qs' <- checkVar ctx' x qs pos
  pure (qs', res)
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
              when (W.unusedBinding ?warnings) do
                tell [UnusedBinding (unLoc x) (getPos x)]
              pure TAST.O
            Just m -> pure m

-- | @check Γ i e τ@ is the typing judgment @Γ ⊢ e ⇐ⁱ τ@.
--
-- In most cases, these are introduction rules.
check :: forall m. MonadElab m => ImportCache -> TAST.Relevance -> Context -> Located AST.Expression -> Located Value -> m (Usage, Located TAST.Expression)
check cache rel ctx expr ty = do
  ty <- force ctx ty
  case (expr, ty) of
    (AST.ELam (AST.Parameter isImplicit m1 x ty :@ p1) expr :@ p3, VPi m2 _ imp ty2 _ ty3 :@ p2) | isImplicit == not imp -> do
      when (unLoc m1 /= m2) do
        throwError $ MultiplicityMismatch (m2 :@ p2) m1
      {-
         0Γ ⊢ A :⁰ type ℓ        Γ, x :ⁱᵖ A ⊢ e ⇐ⁱ B
        ───────────────────────────────────────────── [⇐ λ-I]
          Γ ⊢ (λ(x :ᵖ A) ⇒ e) ⇐ⁱ (x :ᵖ A) → B
      -}
      (qs1, ty) <- check cache TAST.Irrelevant ctx ty (VType :@ p1)
      ty3' <- apply ctx ty3 (VVariable x (lvl ctx) ty2 :@ p2)

      let xMultiplicity = TAST.extend rel * unLoc m1

      (qs2, u) <- withLocalVar x xMultiplicity ty2 ctx \ctx -> do
        (qs, e) <- check cache rel ctx expr ty3'
        pure (qs, getPos e, e)

      ty3' <- quote ctx (lvl ctx) ty3'
      ty' <- eval ctx ty
      unify ctx ty' ty2
      pure (Usage.concat qs1 qs2, TAST.ELam (TAST.Parameter isImplicit m1 x ty :@ p1) ty3' u :@ p3)
    (expr@(_ :@ p1), VPi m2 x imp ty2 ty4 ty3 :@ p2) | imp == implicit -> do
      ty' <- apply ctx ty3 (VVariable ("x?" :@ p2) (lvl ctx) ty2 :@ p2)
      (qs, u) <- check cache TAST.Present (insertBinder m2 (x :@ p2) ty2 ctx) expr ty'
      -- TODO: is @ω@ the correct multiplicity to be infered for the parameter here?

      ty2 <- quote ctx (lvl ctx) ty2
      ty4 <- quote ctx (lvl ctx) ty4

      pure (qs, TAST.ELam (TAST.Parameter True (TAST.Unrestricted :@ p1) (x :@ p1) ty2 :@ p1) ty4 u :@ p1)
    (AST.ELocal (AST.Let False m1 x ty ex :@ p1) expr :@ p2, ty2) -> do
      {-
         0Γ ⊢ A ⇐⁰ type ℓ            Γ, x :ⁱᵖ A ⊢ f ⇐ᵖ B            0Γ ⊢ e ⇐⁰ A          ip = 0
        ──────────────────────────────────────────────────────────────────────────────────────── [⇐ let-I₀]
                               Γ ⊢ (let x :ⁱ A := e; f) ⇐ᵖ B

         0Γ₁ ⊢ A ⇐⁰ type ℓ             Γ₁, x :ⁱᵖ A ⊢ f ⇐ᵖ B           Γ₂ ⊢ e ⇐¹ A
        ────────────────────────────────────────────────────────────────────────── [⇐ let-I₁]
                         Γ₁ + ipΓ₂ ⊢ (let x :ⁱ A := e; f) ⇐ᵖ B
      -}
      (qs1, ty) <- check cache TAST.Irrelevant ctx ty (VType :@ p1)
      ty' <- eval ctx ty

      case TAST.extend rel * unLoc m1 of
        TAST.O -> do
          -- apply [⇐ let-I₀]
          (_, ex) <- check cache TAST.Irrelevant ctx ex ty'
          ex' <- eval ctx ex

          (_, u) <- defineLocal x TAST.O ex' ty' ctx \ctx -> do
            (qs, e) <- check cache rel ctx expr ty2
            pure (qs, getPos e, e)

          pure (mempty, TAST.ELet (TAST.Let False m1 x ty ex :@ p1) u :@ p2)
        xMultiplicity -> do
          -- apply [⇐ let-I₁]

          (qs2, ex) <- check cache TAST.Present ctx ex ty'
          ex' <- eval ctx ex

          (qs3, u) <- defineLocal x xMultiplicity ex' ty' ctx \ctx -> do
            (qs, e) <- check cache rel ctx expr ty2
            pure (qs, getPos e, e)

          let qs1' = qs1 `Usage.merge` qs3

          pure (qs1' `Usage.concat` Usage.scale xMultiplicity qs2, TAST.ELet (TAST.Let False m1 x ty ex :@ p1) u :@ p2)
    (AST.ELocal (AST.Let True m1 x ty ex :@ p1) expr :@ p2, ty2) -> do
      {-
         0Γ ⊢ A ⇐⁰ type ℓ            Γ, x :ⁱᵖ A ⊢ f ⇐ᵖ B            0Γ, x :⁰ A ⊢ e ⇐⁰ A          ip = 0
        ──────────────────────────────────────────────────────────────────────────────────────────────── [⇐ rec-I₀]
                                     Γ ⊢ (rec x :ⁱ A := e; f) ⇐ᵖ B

         0Γ₁ ⊢ A ⇐⁰ type ℓ             Γ₁, x :ⁱᵖ A ⊢ f ⇐ᵖ B           Γ₂, x :⁻ A ⊢ e ⇐¹ A
        ────────────────────────────────────────────────────────────────────────────────── [⇐ rec-I₁]
                                Γ₁ + ipΓ₂ ⊢ (rec x :ⁱ A := e; f) ⇐ᵖ B
      -}
      (qs1, ty) <- check cache TAST.Irrelevant ctx ty (VType :@ p1)
      ty' <- eval ctx ty

      case TAST.extend rel * unLoc m1 of
        TAST.O -> do
          -- apply [⇐ rec-I₀]

          (_, ex) <- do
            rec (qs2, ex') <- defineLocal x TAST.O (VThunk ex' :@ p1) ty' ctx \ctx -> do
                  (qs, e) <- check cache TAST.Irrelevant ctx ex ty'
                  pure (qs, getPos e, e)
            pure (qs2, ex')

          ex' <- eval ctx ex
          (_, u) <- defineLocal x TAST.O ex' ty' ctx \ctx -> do
            (qs, e) <- check cache rel ctx expr ty2
            pure (qs, getPos e, e)

          pure (mempty, TAST.ELet (TAST.Let False m1 x ty ex :@ p1) u :@ p2)
        xMultiplicity -> do
          -- apply [⇐ rec-I₁]

          (qs2, ex) <- mdo
            rec (qs2, ex') <- defineLocal x TAST.W (VThunk ex' :@ p1) ty' ctx \ctx -> do
                  (qs, e) <- check cache TAST.Present ctx ex ty'
                  pure (qs, getPos e, e)
            pure (qs2, ex')

          ex' <- eval ctx ex
          (qs3, u) <- defineLocal x xMultiplicity ex' ty' ctx \ctx -> do
            (qs, e) <- check cache TAST.Present ctx expr ty2
            pure (qs, getPos e, e)

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
      (_, ty) <- check cache TAST.Irrelevant ctx ty (VType :@ p1)
      ty' <- eval ctx ty
      (_, ty2) <- withLocalVar x TAST.O ty' ctx \ctx -> do
        (qs, e) <- check cache TAST.Irrelevant ctx ty2 (VType :@ p2)
        pure (qs, getPos e, e)
      pure (mempty, TAST.EPi (TAST.Parameter isImplicit m1 x ty :@ p1) (TAST.EType :@ p2) ty2 :@ p2)
    (AST.EMultiplicativeProduct (AST.Parameter isImplicit m1 x ty :@ p1) ty2 :@ p2, VType :@ p3) -> do
      when (rel /= TAST.Irrelevant) do
        throwError $ MultiplicityMismatch (TAST.extend rel :@ p3) (TAST.O :@ p3)
      {-
         0Γ ⊢ S ⇐⁰ type ℓ₁          0Γ, x :⁰ A ⊢ B ⇐⁰ type ℓ₂
        ────────────────────────────────────────────────────── [⇐ ⊗-F]
                 0Γ ⊢ (x :ᵖ S) ⊗ T ⇐⁰ type (ℓ₁ ⊔ ℓ₂)
      -}
      (_, ty) <- check cache TAST.Irrelevant ctx ty (VType :@ p1)
      ty' <- eval ctx ty
      (_, ty2) <- withLocalVar x TAST.O ty' ctx \ctx -> do
        (qs, e) <- check cache TAST.Irrelevant ctx ty2 (VType :@ p2)
        pure (qs, getPos e, e)
      pure (mempty, TAST.EMultiplicativeProduct (TAST.Parameter isImplicit m1 x ty :@ p1) (TAST.EType :@ p2) ty2 :@ p2)
    (AST.EAdditiveProduct (AST.Parameter isImplicit m1 x ty :@ p1) ty2 :@ p2, VType :@ p3) -> do
      when (rel /= TAST.Irrelevant) do
        throwError $ MultiplicityMismatch (TAST.extend rel :@ p3) (TAST.O :@ p3)
      {-
         0Γ ⊢ S ⇐⁰ type ℓ₁          0Γ, x :⁰ A ⊢ B ⇐⁰ type ℓ₂
        ────────────────────────────────────────────────────── [⇐ &-F]
                 0Γ ⊢ (x : S) & T ⇐⁰ type (ℓ₁ ⊔ ℓ₂)
      -}
      (_, ty) <- check cache TAST.Irrelevant ctx ty (VType :@ p1)
      ty' <- eval ctx ty
      (_, ty2) <- withLocalVar x TAST.O ty' ctx \ctx -> do
        (qs, e) <- check cache TAST.Irrelevant ctx ty2 (VType :@ p2)
        pure (qs, getPos e, e)
      pure (mempty, TAST.EAdditiveProduct (TAST.Parameter isImplicit m1 x ty :@ p1) (TAST.EType :@ p2) ty2 :@ p2)
    (AST.EMultiplicativePair e1 e2 :@ p, VMultiplicativeProduct m1 x ty _ ty2 :@ p1) -> do
      {-
               0Γ ⊢ M ⇐⁰ A          Γ ⊢ N ⇐ᵖ B            ip = 0
              ─────────────────────────────────────────────────── [⇐ ⊗-I₀]
                            Γ ⊢ (M, N) ⇐ᵖ (x :ⁱ A) ⊗ B

               Γ₁ ⊢ M ⇐¹ A            Γ₂ ⊢ N ⇐ᵖ B
              ──────────────────────────────────── [⇐ ⊗-I₁]
               ipΓ₁ + Γ₂ ⊢ (M, N) ⇐ᵖ (x :ⁱ A) ⊗ B
      -}
      case TAST.extend rel * m1 of
        TAST.O -> do
          -- apply [⇐ ⊗-I₀]
          (_, e1) <- check cache TAST.Irrelevant ctx e1 ty

          ty2' <- apply ctx ty2 (VVariable (x :@ p1) (lvl ctx) ty :@ p1)
          (qs2, e2) <- check cache rel ctx e2 ty2'

          ty' <- quote ctx (lvl ctx) ty
          ty2' <- quote ctx (lvl ctx) ty2'

          pure (qs2, TAST.EMultiplicativePair e1 ty' e2 ty2' :@ p)
        xMult -> do
          -- apply [⇐ ⊗-I₁]
          (qs1, e1) <- check cache TAST.Present ctx e1 ty

          ty2' <- apply ctx ty2 (VVariable (x :@ p1) (lvl ctx) ty :@ p1)
          (qs2, e2) <- check cache rel ctx e2 ty2'

          ty' <- quote ctx (lvl ctx) ty
          ty2' <- quote ctx (lvl ctx) ty2'

          pure (Usage.scale xMult qs1 `Usage.concat` qs2, TAST.EMultiplicativePair e1 ty' e2 ty2' :@ p)
    (AST.EAdditivePair e1 e2 :@ p, VAdditiveProduct x ty _ ty2 :@ p1) -> do
      {-
         Γ ⊢ M ⇐ᵖ A           Γ ⊢ N ⇐ᵖ B
        ───────────────────────────────── [⇐ &-I]
            Γ ⊢ ⟨M, N⟩ ⇐ᵖ (x : A) & B
      -}
      (qs1, e1) <- check cache rel ctx e1 ty

      ty2' <- apply ctx ty2 (VVariable (x :@ p1) (lvl ctx) ty :@ p1)
      (qs2, e2) <- check cache rel ctx e2 ty2'

      ty' <- quote ctx (lvl ctx) ty
      ty2' <- quote ctx (lvl ctx) ty2'

      pure (qs1 `Usage.merge` qs2, TAST.EAdditivePair e1 ty' e2 ty2' :@ p)
    (AST.EOne :@ p, VType :@ _) -> do
      {-
         ─────────────── [⇐ 𝟏-F]
          Γ ⊢ 𝟏 ⇐⁰ type
      -}
      pure (mempty, TAST.EOne :@ p)
    (AST.ETop :@ p, VType :@ _) -> do
      {-
         ─────────────── [⇐ ⊤-F]
          Γ ⊢ ⊤ ⇐⁰ type
      -}
      pure (mempty, TAST.ETop :@ p)
    (AST.EMultiplicativeUnit :@ p, VOne :@ _) -> do
      {-
        ───────────── [⇒ 𝟏-I]
         Γ ⊢ () ⇐ᵖ 𝟏
      -}
      pure (mempty, TAST.EMultiplicativeUnit :@ p)
    (AST.EAdditiveUnit :@ p, VTop :@ _) -> do
      {-
        ───────────── [⇒ ⊤-I]
         Γ ⊢ ⟨⟩ ⇐ᵖ ⊤
      -}
      pure (mempty, TAST.EAdditiveUnit :@ p)
    (AST.EMultiplicativePairElim z mult x y m n :@ p, u) -> do
      {-
         0Γ₁, z :⁰ (_ :ⁱ S) ⊗ T ⊢ U ⇐⁰ type              Γ₁ ⊢ M ⇒ᵖ (_ :ⁱ S) ⊗ T
                             Γ₂, x :ⁱᵖ S, y :ᵖ T ⊢ N ⇐ᵖ U
        ──────────────────────────────────────────────────────────────────────── [⇐ ⊗-E]
                        Γ₁ + Γ₂ ⊢ let r (x, y) as z = M in N ⇐ᵖ U
      -}
      (qs1, m, ty, _) <- synthetize cache rel ctx m
      case ty of
        VMultiplicativeProduct i _ s _ t :@ _ -> do
          xVal <- eval ctx (TAST.EFst m :@ getPos m)
          yVal <- eval ctx (TAST.ESnd m :@ getPos m)

          let ipMult = pMult * i
              pMult = TAST.extend rel * unLoc mult

          (qs2, (n, t')) <- defineLocal x ipMult xVal s ctx \ctx -> do
            t <- apply ctx t xVal
            (qs, n) <- defineLocal y pMult yVal t ctx \ctx -> do
              (qs, n) <- case z of
                Nothing -> check cache rel ctx n u
                Just z -> withLocalVar z TAST.O ty ctx \ctx -> do
                  (qs, n) <- check cache rel ctx n u
                  pure (qs, getPos n, n)
              pure (qs, getPos n, n)

            t' <- quote ctx (lvl ctx) t
            pure (qs, getPos n, (n, t'))

          s' <- quote ctx (lvl ctx) s

          pure (Usage.scale (unLoc mult) qs1 `Usage.concat` qs2, TAST.EMultiplicativePairElim z mult x s' y t' m n :@ p)
        ty -> do
          ty@(_ :@ p) <- quote ctx (lvl ctx) ty
          throwError $ ExpectedMultiplicativeProduct ty p
    (AST.EMultiplicativeUnitElim z mult m n :@ p, t) -> do
      {-
          Γ₁ ⊢ M ⇐ᵖ 𝟏         Γ₁, z :⁰ 𝟏 ⊢ T ⇐⁰ type          Γ₂ ⊢ N ⇐ᵖ T
        ────────────────────────────────────────────────────────────────── [⇐ 𝟏-E]
                        Γ₁ + Γ₂ ⊢ let r () as z := M; N ⇐ᵖ T
      -}
      (qs1, m) <- check cache rel ctx m (VOne :@ p)
      (qs2, n) <- case z of
        Nothing -> check cache rel ctx n t
        Just z -> defineLocal z TAST.O (VMultiplicativeUnit :@ p) (VOne :@ p) ctx \ctx -> do
          (qs, n) <- check cache rel ctx n t
          pure (qs, getPos n, n)
      pure (qs1 `Usage.concat` qs2, TAST.EMultiplicativeUnitElim z mult m n :@ p)
    (AST.ELocal (AST.Import isOpen mod access path :@ p5) expr :@ _, ty) -> do
      (qs, _, e) <- go ctx =<< resolveImport cache isOpen mod access path p5
      pure (qs, e)
      where
        go ctx [] = do
          (qs, e) <- check cache rel ctx expr ty
          pure (qs, getPos e, e)
        go ctx ((m, x, ty, ex) : bs) = do
          (qs, e) <- defineLocal x (unLoc m) ex ty ctx \ctx -> go ctx bs
          t' <- quote ctx (lvl ctx) ty
          e' <- quote ctx (lvl ctx) ex
          pure (qs, getPos e, (TAST.ELet (TAST.External m x t' e' (mod <> access) path :@ getPos e) e :@ getPos e))
    (AST.EFieldAccess r x :@ p, ty) -> do
      {-
         Γ ⊢ r ⇒ⁱ '{ …, x :ᵖ τ, … }
        ─────────────────────────── [⇐ record-E]
              Γ ⊢ r::x ⇐ⁱᵖ τ
      -}
      (qs, r, t, _) <- synthetize cache rel ctx r
      case t of
        VComposite fields :@ _ ->
          lookup ctx x [] fields >>= \case
            (_, Nothing) -> throwError $ FieldNotFound x (getPos r)
            (subst, Just (m, _, ty1)) -> do
              ty1 <- apply' ctx ty1 subst
              unify ctx ty ty1

              ty' <- quote ctx (lvl ctx) ty
              pure (qs, TAST.ERecordAccess r ty' x :@ p)
        VModule fields :@ _ -> case Map.lookup x fields of
          Nothing -> throwError $ FieldNotFound x (getPos r)
          Just (m, ty1) -> do
            unify ctx ty ty1

            ty' <- quote ctx (lvl ctx) ty
            pure (qs, TAST.ERecordAccess r ty' x :@ p)
        _ -> do
          t <- quote ctx (lvl ctx) t
          throwError $ ExpectedRecordOrModule t (getPos r)
      where
        lookup _ _ subst [] = pure (subst, Nothing)
        lookup ctx x subst ((m, y, ty) : fs)
          | x == y = pure (subst, Just (m, y, ty))
          | otherwise = do
              ty' <- apply' ctx ty subst
              let var = VVariable x (lvl ctx) ty' :@ getPos x
              lookup (bind (unLoc m) x ty' ctx) x (var : subst) fs
    (AST.EComposite fields :@ p, VType :@ _) -> do
      when (rel /= TAST.Irrelevant) do
        throwError $ MultiplicityMismatch (TAST.extend rel :@ p) (TAST.O :@ p)
      {-
         0Γ, xₖ :⁰ τₖ ⊢ τᵢ ⇐⁰ type where k < i
        ─────────────────────────────────────── [⇐ '{}-F]
           0Γ ⊢ '{ val ρᵢ xᵢ : τᵢ } ⇐⁰ type
      -}
      (_, fields) <- foldlM checkField (ctx, mempty) fields
      pure (mempty, TAST.EComposite (reverse fields) :@ p)
      where
        checkField (ctx, fields) (mult, name, ty) = do
          (_, ty) <- check cache TAST.Irrelevant ctx ty (VType :@ getPos ty)
          ty' <- eval ctx ty
          pure (bind TAST.O name ty' ctx, (mult, name, ty) : fields)
    (AST.ERecordLiteral f1 :@ p, VComposite f2 :@ _) -> do
      {-
                             Γᵢ ⊢ eᵢ ⇐¹ τᵢ
        ──────────────────────────────────────────────────────── [⇐ @{}-I₁]
         m∑ᵢ(ρᵢΓᵢ) ⊢ @{ let ρᵢ xᵢ ≔ eᵢ } ⇐ᵐ '{ val ρᵢ xᵢ : τᵢ }
      -}
      let dom1 = domain f1
          dom2 = domain f2
      when (dom1 /= dom2) do
        let diff1 = dom1 List.\\ dom2
        unless (null diff1) do
          throwError $ RecordMissingFields diff1 p
        let diff2 = dom2 List.\\ dom1
        unless (null diff2) do
          throwError $ RecordHasTooManyFields diff2 p

      (qs, fields, _) <- checkFields (mempty, mempty, mempty) f2
      pure (Usage.scale (TAST.extend rel) qs, TAST.ERecordLiteral (reverse fields) :@ p)
      where
        checkFields (qs, fields, env) [] = pure (qs, fields, env)
        checkFields (qs, fields, env) ((mult, k, ty@(Clos _ t)) : fs) = do
          let Just (mult2, _, val) = lookup k f1
          when (mult /= mult2) do
            throwError $ MultiplicityMismatch mult2 mult

          ty <- apply' ctx ty env

          (qs', val) <- check cache rel ctx val ty
          let qs'' = Usage.scale (unLoc mult) qs'
          ty' <- quote ctx (lvl ctx) ty
          val' <- eval ctx val

          (qs, fields, env) <- checkFields (qs `Usage.concat` qs'', (mult, k, ty', val) : fields, val' : env) fs
          pure (qs, fields, env)

        domain [] = []
        domain ((_, k, _) : fs) = k : domain fs

        lookup _ [] = Nothing
        lookup x ((m, y, v) : fs)
          | x == y = Just (m, x, v)
          | otherwise = lookup x fs
    (AST.EHole loc :@ p1, ty) -> do
      meta <- freshMeta ctx (TAST.extend rel) ty p1 loc
      pure (mempty, meta :@ p1)
    (e@(_ :@ p), v) -> do
      {-
         Γ ⊢ e ⇒ⁱ A        A ≅ B       p ⩽ i
        ───────────────────────────────────── [⇐ ≅-F]
                     Γ ⊢ e ⇐ᵖ B
      -}
      (qs, e, ty, m1) <- insert ctx =<< synthetize cache rel ctx e

      if TAST.extend rel <= unLoc m1
        then do
          unify ctx v ty
          pure (qs, e)
        else throwError $ MultiplicityMismatch (TAST.extend rel :@ p) m1

-- | @Ρ, Γ ⊢ e ⇒ τ@
--
-- In most cases, these are elimination and type-formation rules.
synthetize :: forall m. MonadElab m => ImportCache -> TAST.Relevance -> Context -> Located AST.Expression -> m (Usage, Located TAST.Expression, Located Value, Located TAST.Multiplicity)
synthetize _ rel ctx (AST.EInteger i suffix :@ p) = do
  {-
     n is a literal number
    ─────────────────────── [⇒ integer-I]
          Γ ⊢ n ⇒ᵖ uN
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
synthetize _ rel _ (AST.ECharacter c :@ p) =
  {-
     c is a literal character
    ────────────────────────── [⇒ char-I]
           Γ ⊢ c ⇒ᵖ char
  -}
  pure (mempty, TAST.ECharacter c :@ p, VVariable ("char" :@ p) 0 (VType :@ p) :@ p, TAST.extend rel :@ p)
synthetize _ rel _ (AST.EBoolean bool :@ p) =
  {-
     b is a boolean literal
    ──────────────────────── [⇒ bool-I]
          Γ ⊢ b ⇒ᵖ bool
  -}
  pure (mempty, TAST.EBoolean bool :@ p, VBuiltinBool :@ p, TAST.extend rel :@ p)
synthetize _ rel _ (AST.EMultiplicativeUnit :@ p) =
  {-
    ───────────── [⇒ 𝟏-I]
     Γ ⊢ () ⇒ᵖ 𝟏
  -}
  pure (mempty, TAST.EMultiplicativeUnit :@ p, VOne :@ p, TAST.extend rel :@ p)
synthetize _ rel _ (AST.EAdditiveUnit :@ p) =
  {-
    ───────────── [⇒ ⊤-I]
     Γ ⊢ ⟨⟩ ⇒ᵖ ⊤
  -}
  pure (mempty, TAST.EAdditiveUnit :@ p, VTop :@ p, TAST.extend rel :@ p)
synthetize cache rel ctx (AST.EApplication e1 isImp e2 :@ p) = do
  {-
     Γ ⊢ f ⇒ⁱ (y :ᵖ A) → B          0Γ ⊢ x ⇐⁰ A          ip = 0
    ──────────────────────────────────────────────────────────── [⇐ λ-E₀]
                        Γ ⊢ f x ⇐ᵖ B[y\x]

     Γ₁ ⊢ f ⇒ⁱ (y :ᵖ A) → B          Γ₂ ⊢ x ⇐¹ A
    ───────────────────────────────────────────── [⇐ λ-E₁]
              Γ₁ + ipΓ₂ ⊢ f x ⇒ⁱ B[y\x]
    -}
  (icit, e1, qs1, t1, m1) <- case isImp of
    True -> do
      (qs, e1, t1, m1) <- synthetize cache rel ctx e1
      pure (implicit, e1, qs, t1, m1)
    False -> do
      (qs, e1, t1, m1) <- insert' ctx =<< synthetize cache rel ctx e1
      pure (explicit, e1, qs, t1, m1)

  t1 <- force ctx t1
  (m2, a, b) <- case t1 of
    VPi u _ i a _ b :@ p2
      | i == icit -> pure (u :@ p2, a, b)
      | otherwise -> throwError $ ImplicitMismatch icit i p2
    t1@(_ :@ p2) -> do
      -- try η-expanding
      let usage = TAST.Unrestricted
      a <- eval ctx . (:@ p) =<< freshMeta ctx usage (VType :@ p) p AST.InsertedHole
      meta <- freshMeta (bind usage ("x?" :@ p) a ctx) usage (VType :@ p) p AST.InsertedHole
      let b = Clos (env ctx) $ meta :@ p
      unify ctx t1 (VPi usage "x?" explicit a (VType :@ getPos a) b :@ p)
      pure (usage :@ p2, a, b)

  a' <- quote ctx (lvl ctx) a
  case unLoc m1 * unLoc m2 of
    TAST.O -> do
      (qs2, e2) <- check cache TAST.Irrelevant ctx e2 a

      e2' <- eval ctx e2
      b <- apply ctx b e2'

      pure (qs1 `Usage.merge` qs2, TAST.EApplication e1 (not icit) a' e2 :@ p, b, m2)
    xMultiplicity -> do
      (qs2, e2) <- check cache TAST.Present ctx e2 a

      e2' <- eval ctx e2
      b <- apply ctx b e2'

      pure (qs1 `Usage.concat` Usage.scale xMultiplicity qs2, TAST.EApplication e1 (not icit) a' e2 :@ p, b, m2)
synthetize _ rel ctx (AST.EIdentifier x :@ p) = do
  {-
    ──────────────────── [⇒ var-E]
     Γ, x :ᵖ A ⊢ x ⇒ᵖ A
  -}
  (ex, ty, usage) <- go 0 (types ctx)
  -- case (rel, usage) of
  --   (TAST.Irrelevant, TAST.I) -> throwError $ RelevantVariableInIrrelevantContext (unLoc x) TAST.I p
  --   (TAST.Irrelevant, TAST.W) -> throwError $ RelevantVariableInIrrelevantContext (unLoc x) TAST.W p
  --   _ -> pure ()
  case ex of
    TAST.EBuiltin _ :@ _ -> pure (mempty, ex, ty, TAST.extend rel :@ p)
    _ -> pure (Map.singleton x $ TAST.extend rel, ex, ty, TAST.extend rel :@ p)
  where
    go _ [] = checkBuiltin
    go ix ((usage, x', origin, a) : types)
      | x == x' && origin == Source = do
          a' <- quote ctx (lvl ctx) a
          pure (TAST.EIdentifier x' ix a' :@ p, a, usage)
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
synthetize _ rel _ (AST.EType :@ p) = do
  when (rel /= TAST.Irrelevant) do
    throwError $ ErasedInRelevantContext p
  {-
    ────────────────── [⇒ type-F]
     Γ ⊢ type ⇒⁰ type
  -}
  pure (mempty, TAST.EType :@ p, VType :@ p, TAST.O :@ p)
synthetize _ rel _ (AST.ETop :@ p) = do
  when (rel /= TAST.Irrelevant) do
    throwError $ ErasedInRelevantContext p
  {-
    ─────────────── [⇒ ⊤-F]
     Γ ⊢ ⊤ ⇒⁰ type
  -}
  pure (mempty, TAST.ETop :@ p, VType :@ p, TAST.O :@ p)
synthetize _ rel _ (AST.EOne :@ p) = do
  when (rel /= TAST.Irrelevant) do
    throwError $ ErasedInRelevantContext p
  {-
    ─────────────── [⇒ 𝟏-F]
     Γ ⊢ 𝟏 ⇒⁰ type
  -}
  pure (mempty, TAST.EOne :@ p, VType :@ p, TAST.O :@ p)
synthetize cache rel ctx (AST.EPi (AST.Parameter isImplicit m1 name ty :@ p2) expr :@ p) = do
  when (rel /= TAST.Irrelevant) do
    throwError $ ErasedInRelevantContext p
  {-
     0Γ ⊢ A ⇐⁰ type       0Γ, x :⁰ A ⊢ B ⇐⁰ type
    ───────────────────────────────────────────── [⇒ Π-F]
              0Γ ⊢ (x :ᵖ A) → B ⇒⁰ type
  -}
  (_, ty) <- check cache TAST.Irrelevant ctx ty (VType :@ p)
  ty' <- eval ctx ty
  (_, b) <- withLocalVar name TAST.O ty' ctx \ctx -> do
    (qs, e) <- check cache TAST.Irrelevant ctx expr (VType :@ p)
    pure (qs, getPos e, e)
  pure (mempty, TAST.EPi (TAST.Parameter isImplicit m1 name ty :@ p2) b (TAST.EType :@ getPos b) :@ p, VType :@ p, TAST.O :@ p)
synthetize cache rel ctx (AST.EMultiplicativeProduct (AST.Parameter isImplicit m1 name ty :@ p2) expr :@ p) = do
  when (rel /= TAST.Irrelevant) do
    throwError $ ErasedInRelevantContext p
  {-
     0Γ ⊢ A ⇐⁰ type       0Γ, x :⁰ A ⊢ B ⇐⁰ type
    ───────────────────────────────────────────── [⇒ ⊗-F]
              0Γ ⊢ (x :ᵖ A) ⊗ B ⇒⁰ type
  -}
  (_, ty) <- check cache TAST.Irrelevant ctx ty (VType :@ p)
  ty' <- eval ctx ty
  (_, b) <- withLocalVar name TAST.O ty' ctx \ctx -> do
    (qs, e) <- check cache TAST.Irrelevant ctx expr (VType :@ p)
    pure (qs, getPos e, e)
  pure (mempty, TAST.EMultiplicativeProduct (TAST.Parameter isImplicit m1 name ty :@ p2) b (TAST.EType :@ getPos b) :@ p, VType :@ p, TAST.O :@ p)
synthetize cache rel ctx (AST.EAdditiveProduct (AST.Parameter isImplicit m1 name ty :@ p2) expr :@ p) = do
  when (rel /= TAST.Irrelevant) do
    throwError $ ErasedInRelevantContext p
  {-
     0Γ ⊢ A ⇐⁰ type       0Γ, x :⁰ A ⊢ B ⇐⁰ type
    ───────────────────────────────────────────── [⇒ &-F]
              0Γ ⊢ (x :ᵖ A) & B ⇒⁰ type
  -}
  (_, ty) <- check cache TAST.Irrelevant ctx ty (VType :@ p)
  ty' <- eval ctx ty
  (_, b) <- withLocalVar name TAST.O ty' ctx \ctx -> do
    (qs, e) <- check cache TAST.Irrelevant ctx expr (VType :@ p)
    pure (qs, getPos e, e)
  pure (mempty, TAST.EAdditiveProduct (TAST.Parameter isImplicit m1 name ty :@ p2) b (TAST.EType :@ getPos b) :@ p, VType :@ p, TAST.O :@ p)
synthetize cache rel ctx (AST.ELam (AST.Parameter isImplicit m1 name ty :@ p2) ex :@ p) = do
  {-
     0Γ ⊢ A ⇐⁰ type ℓ       Γ, x :ⁱᵖ A ⊢ e ⇒ᵖ B
    ──────────────────────────────────────────── [⇒ λ-I]
       ipΓ ⊢ (λ(x :ⁱ A) ⇒ e) ⇒ᵖ (x :ⁱ A) → B
  -}
  (_, ty) <- check cache TAST.Irrelevant ctx ty (VType :@ p)
  ty' <- eval ctx ty
  let ip = unLoc m1 * TAST.extend rel
  (qs1, (ex, b, u2)) <- withLocalVar name ip ty' ctx \ctx -> do
    (u, ex, b, u2) <- synthetize cache rel ctx ex
    pure (u, getPos ex, (ex, b, u2))

  b' <- quote ctx (lvl ctx) b
  clos <- closeVal ctx b
  pure (Usage.scale ip qs1, TAST.ELam (TAST.Parameter isImplicit m1 name ty :@ p2) b' ex :@ p, VPi (unLoc m1) (unLoc name) (not isImplicit) ty' b clos :@ p, u2)
synthetize _ rel ctx (AST.EHole loc :@ p1) = do
  meta1 <- freshMeta ctx (TAST.extend rel) (VType :@ p1) p1 loc
  a <- eval ctx (meta1 :@ p1)
  meta2 <- freshMeta ctx (TAST.extend rel) a p1 loc
  let t = meta2 :@ p1
  pure (mempty, t, a, TAST.extend rel :@ p1)
synthetize cache rel ctx (AST.EIfThenElse c t e :@ p) = do
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
      (qs, c) <- check cache TAST.Irrelevant ctx c (VBuiltinBool :@ getPos c)
      pure (qs, c, VBuiltinBool :@ getPos c, TAST.O :@ getPos c)
      `catchError` \_ -> synthetize cache TAST.Present ctx c
  c' <- eval ctx c

  case m1 of
    TAST.O :@ _ -> do
      -- apply [⇐ bool-E₀]
      (qs1, t, a, u1) <- synthetize cache rel ctx t
      (qs2, e, b, u2) <- synthetize cache rel ctx e

      when (unLoc u1 /= unLoc u2) do
        throwError $ MultiplicityMismatch u1 u2

      let qs1' = qs1 `Usage.merge` qs2

      a' <- quote ctx (lvl ctx) a
      b' <- quote ctx (lvl ctx) b

      pure (qs0 `Usage.concat` qs1', TAST.EIfThenElse c t a' e b' :@ p, VIfThenElse c' a (VType :@ getPos a) b (VType :@ getPos b) :@ p, m1)
    p' -> do
      -- apply [⇐ bool-E₁]
      unify ctx bool (VBuiltinBool :@ getPos c)

      (qs1, t, a, u1) <- synthetize cache TAST.Present ctx t
      (qs2, e, b, u2) <- synthetize cache TAST.Present ctx e

      unify ctx a b
      when (unLoc u1 /= unLoc u2) do
        throwError $ MultiplicityMismatch u1 u2

      let qs1' = qs1 `Usage.merge` qs2

      a' <- quote ctx (lvl ctx) a
      b' <- quote ctx (lvl ctx) b

      pure (qs0 `Usage.concat` Usage.scale (unLoc p') qs1', TAST.EIfThenElse c t a' e b' :@ p, a, p')
synthetize cache rel ctx (AST.EAdditivePair e1 e2 :@ p) = do
  {-
     Γ ⊢ M ⇒ᵖ A           Γ ⊢ N ⇒ᵖ B
    ───────────────────────────────── [⇒ &-I]
        Γ ⊢ ⟨M, N⟩ ⇒ᵖ (x : A) & B
  -}
  (qs1, e1, a, _) <- synthetize cache rel ctx e1
  (qs2, e2, b, _) <- synthetize cache rel ctx e2

  a' <- quote ctx (lvl ctx) a
  b' <- quote ctx (lvl ctx) b

  b <- closeVal ctx b
  pure (qs1 `Usage.merge` qs2, TAST.EAdditivePair e1 a' e2 b' :@ p, VAdditiveProduct "_" a (VType :@ getPos a) b :@ p, TAST.extend rel :@ p)
synthetize cache rel ctx (AST.EAdditiveTupleAccess e n :@ _) = do
  (_, _, ty, _) <- synthetize cache rel ctx e
  ty' <- quote ctx (lvl ctx) ty
  fns <- reverse <$> mkFstSnd ty' n
  let expr = foldr mkApp e fns
  synthetize cache rel ctx expr
  where
    mkFstSnd (TAST.EAdditiveProduct _ _ _ :@ p) 1 = pure [(AST.EFst, p)]
    mkFstSnd _ 1 = pure []
    mkFstSnd (TAST.EAdditiveProduct _ _ e@(TAST.EAdditiveProduct _ _ _ :@ _) :@ p) n =
      ((AST.ESnd, p) :) <$> mkFstSnd e (n - 1)
    mkFstSnd (TAST.EAdditiveProduct _ _ _ :@ p) 2 = pure [(AST.ESnd, p)]
    mkFstSnd (TAST.EAdditiveProduct _ _ _ :@ _) _ = throwError $ CannotAccessNthElementOfAdditiveTuple n (getPos e)
    mkFstSnd e n = throwError $ CannotAccessNthElementOfNonAdditiveTuple n (getPos e)

    mkApp (f, p) e1 = f e1 :@ p
synthetize cache rel ctx (AST.EFst e :@ p) = do
  {-
     Γ ⊢ M ⇒ᵖ (x : S) & T
    ───────────────────── [⇒ &-Efst]
        Γ ⊢ fst M ⇒ᵖ S
  -}
  (qs1, e, ty, _) <- synthetize cache rel ctx e

  case ty of
    VAdditiveProduct _ s _ _ :@ _ -> pure (qs1, TAST.EFst e :@ p, s, TAST.extend rel :@ p)
    ty -> do
      ty@(_ :@ p) <- quote ctx (lvl ctx) ty
      throwError $ ExpectedAdditiveProduct ty p
synthetize cache rel ctx (AST.ESnd e :@ p) = do
  {-
     Γ ⊢ M ⇒ᵖ (x : S) & T
    ───────────────────── [⇒ &-Esnd]
        Γ ⊢ snd M ⇒ᵖ T
  -}
  (qs1, e, ty, _) <- synthetize cache rel ctx e

  case ty of
    VAdditiveProduct x s _ t :@ p1 -> do
      t <- apply ctx t (VVariable (x :@ p1) (lvl ctx) s :@ p1)
      pure (qs1, TAST.ESnd e :@ p, t, TAST.extend rel :@ p)
    ty -> do
      ty@(_ :@ p) <- quote ctx (lvl ctx) ty
      throwError $ ExpectedAdditiveProduct ty p
synthetize cache rel ctx (AST.EMultiplicativePairElim z mult x y m n :@ p) = do
  {-
     Γ₁ ⊢ M ⇒ᵖ (_ :ⁱ S) ⊗ T             Γ₂, x :ⁱᵖ S, y :ᵖ T ⊢ N ⇒ᵖ U
    ───────────────────────────────────────────────────────────────── [⇒ ⊗-E]
                Γ₁ + Γ₂ ⊢ let (x, y) as z := M; N ⇒ᵖ U
  -}
  (qs1, m, ty, _) <- synthetize cache rel ctx m
  case ty of
    VMultiplicativeProduct i _ s _ t :@ _ -> do
      xVal <- eval ctx (TAST.EFst m :@ getPos m)
      yVal <- eval ctx (TAST.ESnd m :@ getPos m)

      let ipMult = pMult * i
          pMult = TAST.extend rel * unLoc mult

      (qs2, (n, u, t')) <- defineLocal x ipMult xVal s ctx \ctx -> do
        t <- apply ctx t xVal
        (qs, (n, u)) <- defineLocal y pMult yVal t ctx \ctx -> do
          (qs, n, ty2, _) <- synthetize cache rel ctx n
          pure (qs, getPos n, (n, ty2))

        t' <- quote ctx (lvl ctx) t
        pure (qs, getPos n, (n, u, t'))

      s' <- quote ctx (lvl ctx) s
      pure (Usage.scale (unLoc mult) qs1 `Usage.concat` qs2, TAST.EMultiplicativePairElim z mult x s' y t' m n :@ p, u, TAST.extend rel :@ p)
    ty -> do
      ty@(_ :@ p) <- quote ctx (lvl ctx) ty
      throwError $ ExpectedMultiplicativeProduct ty p
synthetize cache rel ctx (AST.EMultiplicativeUnitElim z mult m n :@ p) = do
  {-
      Γ₁ ⊢ M ⇐ᵖ 𝟏          Γ₂ ⊢ N ⇒ᵖ T
    ──────────────────────────────────── [⇒ 𝟏-E]
     Γ₁ + Γ₂ ⊢ let () as z := M; N ⇒ᵖ T
  -}
  (qs1, m) <- check cache rel ctx m (VOne :@ p)
  (qs2, n, t, _) <- synthetize cache rel ctx n
  pure (qs1 `Usage.concat` qs2, TAST.EMultiplicativeUnitElim z mult m n :@ p, t, TAST.extend rel :@ p)
synthetize cache rel ctx (AST.ELocal (AST.Import isOpen mod access path :@ p4) expr :@ p) = do
  (qs, _, (e, t)) <- go ctx =<< resolveImport cache isOpen mod access path p4
  pure (qs, e, t, TAST.extend rel :@ p)
  where
    go ctx [] = do
      (qs, e, t, _) <- synthetize cache rel ctx expr
      pure (qs, getPos e, (e, t))
    go ctx ((m, x, ty, ex) : bs) = do
      (qs, (e, t)) <- defineLocal x (unLoc m) ex ty ctx \ctx -> go ctx bs
      t' <- quote ctx (lvl ctx) ty
      e' <- quote ctx (lvl ctx) ex
      pure (qs, getPos e, (TAST.ELet (TAST.External m x t' e' (mod <> access) path :@ getPos e) e :@ getPos e, t))
synthetize cache rel ctx (AST.EFieldAccess r x :@ p) = do
  {-
     Γ ⊢ r ⇒ⁱ '{ …, x :ᵖ τ, … }
    ─────────────────────────── [⇒ record-E]
          Γ ⊢ r::x ⇒ⁱᵖ τ
  -}
  (qs, r, t, u) <- synthetize cache rel ctx r
  t' <- quote ctx (lvl ctx) t
  case t of
    VComposite fields :@ _ ->
      lookup ctx x [] fields >>= \case
        (_, Nothing) -> throwError $ FieldNotFound x (getPos r)
        (subst, Just (m, x, ty)) -> do
          ty <- apply' ctx ty subst
          pure (qs, TAST.ERecordAccess r t' x :@ p, ty, (* unLoc m) <$> u)
    VModule fields :@ _ -> case Map.lookup x fields of
      Nothing -> throwError $ FieldNotFound x (getPos r)
      Just (m, ty) -> pure (qs, TAST.ERecordAccess r t' x :@ p, ty, (* unLoc m) <$> u)
    _ -> do
      t <- quote ctx (lvl ctx) t
      throwError $ ExpectedRecordOrModule t (getPos r)
  where
    lookup _ _ subst [] = pure (subst, Nothing)
    lookup ctx x subst ((m, y, ty) : fs)
      | x == y = pure (subst, Just (m, y, ty))
      | otherwise = do
          ty' <- apply' ctx ty subst
          let var = VVariable x (lvl ctx) ty' :@ getPos x
          lookup (bind (unLoc m) x ty' ctx) x (var : subst) fs
synthetize _ _ _ (_ :@ p) = throwError $ CannotInferType p

closeVal :: forall m. MonadElab m => Context -> Located Value -> m Closure
closeVal ctx ty = do
  ty <- quote ctx (lvl ctx + 1) ty
  pure $ Clos (env ctx) ty
