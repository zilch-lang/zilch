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
import Data.Located (Located ((:@)), getPos, unLoc)
import Debug.Trace (trace)
import Language.Zilch.Typecheck.Context (Context, bind, define, emptyContext, env, lvl)
import qualified Language.Zilch.Typecheck.Core.AST as TAST
import Language.Zilch.Typecheck.Core.Eval (Closure (..), MetaEntry (..), Value (..), explicit)
import Language.Zilch.Typecheck.Core.Multiplicity (Multiplicity (..))
import {-# SOURCE #-} Language.Zilch.Typecheck.Elaborator (MonadElab)
import Language.Zilch.Typecheck.Errors (ElabError (..))
import Language.Zilch.Typecheck.Evaluator (apply, applyVal, eval, force, quote)

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
      (ctx, def) <- simplifyDef ctx def
      pure (ctx, (TAST.TopLevel attrs isOpen def :@ p) : ts)

    simplifyDef ctx def = case def of
      TAST.Let isRec mult name ty val :@ p -> do
        ty' <- eval ctx ty
        let var = VVariable name (lvl ctx) ty' :@ p
        let ctx' = define (unLoc mult) name var var ctx
        ty <- simplify' (if isRec then ctx' else ctx) ty
        val <- simplify' (if isRec then ctx' else ctx) val
        pure (ctx', TAST.Let isRec mult name ty val :@ p)
      TAST.Val mult name ty :@ p -> do
        ty' <- eval ctx ty
        let var = VVariable name (lvl ctx) ty' :@ p
        let ctx' = define (unLoc mult) name var var ctx
        ty <- simplify' ctx ty
        pure (ctx', TAST.Val mult name ty :@ p)
      TAST.External mult name ty val mod path :@ p -> do
        ty' <- eval ctx ty
        let var = VVariable name (lvl ctx) ty' :@ p
        let ctx' = define (unLoc mult) name var var ctx
        ty <- simplify' ctx ty
        val <- simplify' ctx val
        pure (ctx', TAST.External mult name ty val mod path :@ p)

    simplify' ctx (TAST.ELet def val :@ p) = do
      (ctx, def) <- simplifyDef ctx def
      val <- simplify' ctx val
      pure (TAST.ELet def val :@ p)
    simplify' ctx expr = eval ctx expr >>= resimplify' ctx >>= quote ctx (lvl ctx)

    resimplify' ctx =
      force ctx >=> \case
        VPi mult x imp ty ty2 clos :@ p -> do
          ty <- resimplify' ctx ty
          let ctx' = bind mult (x :@ p) ty ctx
              var = VVariable (x :@ p) (lvl ctx) ty :@ p
          ty2 <- resimplify' ctx' ty2
          val <- apply ctx clos var >>= resimplify' ctx' >>= quote ctx' (lvl ctx')
          pure $ VPi mult x imp ty ty2 (Clos (env ctx) val) :@ p
        VLam mult x imp ty ty2 clos :@ p -> do
          ty <- resimplify' ctx ty
          ty2 <- resimplify' ctx ty2
          let ctx' = bind mult (x :@ p) ty ctx
              var = VVariable (x :@ p) (lvl ctx) ty :@ p
          ty2 <- resimplify' ctx' ty2
          val <- apply ctx clos var >>= resimplify' ctx' >>= quote ctx' (lvl ctx')
          pure $ VLam mult x imp ty ty2 (Clos (env ctx) val) :@ p
        VMultiplicativeProduct mult x ty ty2 clos :@ p -> do
          ty <- resimplify' ctx ty
          ty2 <- resimplify' ctx ty2
          let ctx' = bind mult (x :@ p) ty ctx
              var = VVariable (x :@ p) (lvl ctx) ty :@ p
          ty2 <- resimplify' ctx' ty2
          val <- apply ctx clos var >>= resimplify' ctx' >>= quote ctx' (lvl ctx')
          pure $ VMultiplicativeProduct mult x ty ty2 (Clos (env ctx) val) :@ p
        VAdditiveProduct x ty ty2 clos :@ p -> do
          ty <- resimplify' ctx ty
          ty2 <- resimplify' ctx ty2
          let ctx' = bind W (x :@ p) ty ctx
              var = VVariable (x :@ p) (lvl ctx) ty :@ p
          ty2 <- resimplify' ctx' ty2
          val <- apply ctx clos var >>= resimplify' ctx' >>= quote ctx' (lvl ctx')
          pure $ VAdditiveProduct x ty ty2 (Clos (env ctx) val) :@ p
        v -> pure v
