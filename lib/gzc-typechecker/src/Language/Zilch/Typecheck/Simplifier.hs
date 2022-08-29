{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoOverloadedLists #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Typecheck.Simplifier where

import Control.Monad (forM, forM_, (<=<), (>=>))
import Control.Monad.Except (throwError)
import Control.Monad.State (gets)
import Data.Foldable (foldlM)
import Data.Located (Located ((:@)), unLoc)
import Language.Zilch.Typecheck.Context (Context, bind, define, emptyContext, env, lvl)
import qualified Language.Zilch.Typecheck.Core.AST as TAST
import Language.Zilch.Typecheck.Core.Eval (Closure (..), MetaEntry (..), Value (..))
import Language.Zilch.Typecheck.Core.Multiplicity (Multiplicity (..))
import {-# SOURCE #-} Language.Zilch.Typecheck.Elaborator (MonadElab)
import Language.Zilch.Typecheck.Errors (ElabError (..))
import Language.Zilch.Typecheck.Evaluator (apply, eval, force, quote)

inlineMetavariables :: forall m. MonadElab m => Located TAST.Module -> Context -> m (Located TAST.Module)
inlineMetavariables (TAST.Mod binds :@ p) ctx = do
  metas <- gets snd
  forM_ metas \case
    (Unsolved _ _, path, p, loc) -> do
      let go TAST.Here = pure []
          go (TAST.Bind path mult x ty) = do
            ty' <- quote ctx (lvl ctx) ty
            ((unLoc x, mult, ty') :) <$> go path
          go (TAST.Define path _ _ _ _) = go path

      path' <- go path
      throwError $ CannotSolveHole path' p loc
    _ -> pure ()

  binds <- simplify binds
  pure $ TAST.Mod (reverse binds) :@ p

simplify :: forall m. MonadElab m => [Located TAST.TopLevel] -> m [Located TAST.TopLevel]
simplify = fmap snd . foldlM simp (emptyContext, [])
  where
    simp (ctx, ts) (TAST.TopLevel attrs isOpen def :@ p) = do
      (ctx, def) <- case def of
        TAST.Let isRec mult name ty val :@ p -> do
          ty <- simplify' ctx ty
          val <- simplify' ctx val
          pure (ctx, TAST.Let isRec mult name ty val :@ p)
        TAST.Val mult name ty :@ p -> do
          ty <- simplify' ctx ty
          pure (ctx, TAST.Val mult name ty :@ p)
        TAST.External mult name ty val mod path :@ p -> do
          ty <- simplify' ctx ty
          val <- simplify' ctx val
          let ctx' = define (unLoc mult) name (VVariable name (lvl ctx) :@ p) (VVariable name (lvl ctx) :@ p) ctx
          pure (ctx', TAST.External mult name ty val mod path :@ p)
      pure (ctx, (TAST.TopLevel attrs isOpen def :@ p) : ts)

    simplify' ctx = eval ctx >=> resimplify' ctx >=> quote ctx (lvl ctx)

    resimplify' ctx =
      force ctx >=> \case
        VPi mult x imp ty clos :@ p -> do
          ty <- resimplify' ctx ty
          let ctx' = bind mult (x :@ p) ty ctx
          val <- apply ctx clos (VVariable (x :@ p) (lvl ctx) :@ p) >>= resimplify' ctx' >>= quote ctx' (lvl ctx')
          pure $ VPi mult x imp ty (Clos (env ctx) val) :@ p
        VLam mult x imp ty clos :@ p -> do
          ty <- resimplify' ctx ty
          let ctx' = bind mult (x :@ p) ty ctx
          val <- apply ctx clos (VVariable (x :@ p) (lvl ctx) :@ p) >>= resimplify' ctx' >>= quote ctx' (lvl ctx')
          pure $ VLam mult x imp ty (Clos (env ctx) val) :@ p
        VMultiplicativeProduct mult x ty clos :@ p -> do
          ty <- resimplify' ctx ty
          let ctx' = bind mult (x :@ p) ty ctx
          val <- apply ctx clos (VVariable (x :@ p) (lvl ctx) :@ p) >>= resimplify' ctx' >>= quote ctx' (lvl ctx')
          pure $ VMultiplicativeProduct mult x ty (Clos (env ctx) val) :@ p
        VAdditiveProduct x ty clos :@ p -> do
          ty <- resimplify' ctx ty
          let ctx' = bind W (x :@ p) ty ctx
          val <- apply ctx clos (VVariable (x :@ p) (lvl ctx) :@ p) >>= resimplify' ctx' >>= quote ctx' (lvl ctx')
          pure $ VAdditiveProduct x ty (Clos (env ctx) val) :@ p
        v -> pure v
