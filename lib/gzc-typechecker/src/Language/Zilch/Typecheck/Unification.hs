{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Zilch.Typecheck.Unification where

import Control.Monad.Except (catchError, throwError)
import Data.IORef (modifyIORef', readIORef, writeIORef)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Located (Located ((:@)))
import qualified Data.Text as Text
import Language.Zilch.Typecheck.Context (Context, bds, emptyContext, lvl)
import qualified Language.Zilch.Typecheck.Core.AST as TAST
import Language.Zilch.Typecheck.Core.Eval (DeBruijnLvl (Lvl), MetaEntry (Solved, Unsolved), Spine, Value (..))
import qualified Language.Zilch.Typecheck.Core.Usage as TAST
import {-# SOURCE #-} Language.Zilch.Typecheck.Elaborator (MonadElab)
import Language.Zilch.Typecheck.Errors (ElabError (CannotUnify, UnificationError, UsageMismatch))
import Language.Zilch.Typecheck.Evaluator (apply, applyVal, debruijnLevelToIndex, eval, force, quote)
import Language.Zilch.Typecheck.Metavariables (mcxt, nextMeta)
import System.IO.Unsafe (unsafeDupablePerformIO)

-- | Generate new fresh metavariables from the context.
freshMeta :: Context -> TAST.Expression
freshMeta ctx = unsafeDupablePerformIO do
  m <- readIORef nextMeta
  writeIORef nextMeta (m + 1)
  modifyIORef' mcxt (IntMap.insert m Unsolved)
  pure $ TAST.EInsertedMeta m (bds ctx)

data PartialRenaming = Renaming DeBruijnLvl DeBruijnLvl (IntMap DeBruijnLvl)

lift :: PartialRenaming -> PartialRenaming
lift (Renaming dom cod@(Lvl cod') ren) =
  Renaming (dom + 1) (cod + 1) (IntMap.insert cod' dom ren)

invert :: forall m. MonadElab m => Context -> DeBruijnLvl -> Spine -> m PartialRenaming
invert ctx gamma sp = do
  (dom, ren) <- go sp
  pure $ Renaming dom gamma ren
  where
    go [] = pure (0, mempty)
    go ((t, _) : sp) = do
      (dom, ren) <- go sp
      t' <- force ctx t
      case t' of
        VVariable _ (Lvl x) :@ _ | IntMap.notMember x ren -> pure (dom + 1, IntMap.insert x dom ren)
        _ -> throwError UnificationError

rename :: forall m. MonadElab m => Context -> Int -> PartialRenaming -> Located Value -> m (Located TAST.Expression)
rename ctx m ren v = go ren v
  where
    go :: PartialRenaming -> Located Value -> m (Located TAST.Expression)
    go ren@(Renaming dom cod env) t =
      force ctx t >>= \case
        VFlexible m' sp :@ p
          | m == m' -> throwError UnificationError
          | otherwise -> goSpine ren (TAST.EMeta m' :@ p) sp
        VRigid name (Lvl x) sp :@ p -> case IntMap.lookup x env of
          Nothing -> throwError UnificationError
          Just x' -> goSpine ren (TAST.EIdentifier name (debruijnLevelToIndex dom x') :@ p) sp
        VLam usage x isExplicit a t :@ p -> do
          a' <- go ren a
          t' <- go (lift ren) =<< apply ctx t (VVariable ("?" :@ p) cod :@ p)
          pure $ TAST.ELam (TAST.Parameter (not isExplicit) (usage :@ p) (x :@ p) a' :@ p) t' :@ p
        VPi usage x isExplicit a t :@ p -> do
          a' <- go ren a
          t' <- go (lift ren) =<< apply ctx t (VVariable ("?" :@ p) cod :@ p)
          pure $ TAST.EPi (TAST.Parameter (not isExplicit) (usage :@ p) (x :@ p) a' :@ p) t' :@ p
        VType :@ p -> pure $ TAST.EType :@ p
        VBuiltinU64 :@ p -> pure $ TAST.EBuiltin TAST.TyU64 :@ p
        VBuiltinU32 :@ p -> pure $ TAST.EBuiltin TAST.TyU32 :@ p
        VBuiltinU16 :@ p -> pure $ TAST.EBuiltin TAST.TyU16 :@ p
        VBuiltinU8 :@ p -> pure $ TAST.EBuiltin TAST.TyU8 :@ p
        VBuiltinS64 :@ p -> pure $ TAST.EBuiltin TAST.TyS64 :@ p
        VBuiltinS32 :@ p -> pure $ TAST.EBuiltin TAST.TyS32 :@ p
        VBuiltinS16 :@ p -> pure $ TAST.EBuiltin TAST.TyS16 :@ p
        VBuiltinS8 :@ p -> pure $ TAST.EBuiltin TAST.TyS8 :@ p
        t :@ p -> error "TODO: rename base terms"

    goSpine ren t [] = pure t
    goSpine ren t@(_ :@ p) ((u, i) : sp) = do
      v1 <- goSpine ren t sp
      v2 <- go ren u
      pure $ TAST.EApplication v1 (not i) v2 :@ p

solve :: forall m. MonadElab m => DeBruijnLvl -> Int -> Spine -> Located Value -> m ()
solve gamma m sp val = do
  let ctx = emptyContext
  ren@(Renaming dom _ _) <- invert ctx gamma sp
  val'@(_ :@ p) <- rename ctx m ren val
  solution :@ _ <- eval ctx $ lams (reverse $ snd <$> sp) val' p
  let !_ = unsafeDupablePerformIO $ modifyIORef' mcxt $ IntMap.insert m (Solved solution)
  pure ()
  where
    lams = go 0

    go x [] t _ = t
    go x (i : is) t p =
      TAST.ELam
        (TAST.Parameter (not i) (TAST.Unrestricted :@ p) (("$" <> Text.pack (show (x + 1))) :@ p) (TAST.EUnknown :@ p) :@ p)
        (go (x + 1) is t p)
        :@ p

unifySpine :: forall m. MonadElab m => Context -> DeBruijnLvl -> Spine -> Spine -> m ()
unifySpine _ _ [] [] = pure ()
unifySpine ctx lvl ((t, _) : sp) ((t', _) : sp') = do
  unifySpine ctx lvl sp sp'
  unify' ctx lvl t t'
unifySpine _ _ _ _ = throwError UnificationError

unify' :: forall m. MonadElab m => Context -> DeBruijnLvl -> Located Value -> Located Value -> m ()
unify' ctx lvl t u = do
  t <- force ctx t
  u <- force ctx u
  case (t, u) of
    (VLam u1 _ _ a1 t1 :@ p1, VLam u2 _ _ a2 t2 :@ p2) -> do
      -- unifyUsage (u1 :@ p1) (u2 :@ p2)
      unify' ctx lvl a1 a2
      (v1, v2) <-
        (,)
          <$> apply ctx t1 (VVariable ("x?" :@ p1) lvl :@ p1)
          <*> apply ctx t2 (VVariable ("x?" :@ p2) lvl :@ p2)
      unify' ctx (lvl + 1) v1 v2
    (t1 :@ p1, VLam _ _ i _ t2 :@ p2) -> do
      (v1, v2) <-
        (,)
          <$> applyVal ctx (t1 :@ p1) (VVariable ("x?" :@ p1) lvl :@ p1) i
          <*> apply ctx t2 (VVariable ("x?" :@ p2) lvl :@ p2)
      unify' ctx (lvl + 1) v1 v2
    (VLam _ _ i _ t1 :@ p1, t2 :@ p2) -> do
      (v2, v1) <-
        (,)
          <$> applyVal ctx (t2 :@ p2) (VVariable ("x?" :@ p2) lvl :@ p2) i
          <*> apply ctx t1 (VVariable ("x?" :@ p1) lvl :@ p1)
      unify' ctx (lvl + 1) v1 v2
    (VPi u1 _ i1 a1 t1 :@ p1, VPi u2 _ i2 a2 t2 :@ p2) | i1 == i2 -> do
      -- unifyUsage (u1 :@ p1) (u2 :@ p2)
      unify' ctx lvl a1 a2
      (v1, v2) <-
        (,)
          <$> apply ctx t1 (VVariable ("x?" :@ p1) lvl :@ p1)
          <*> apply ctx t2 (VVariable ("x?" :@ p2) lvl :@ p2)
      unify' ctx (lvl + 1) v1 v2
    (VRigid _ l1 sp1 :@ p1, VRigid _ l2 sp2 :@ p2)
      | l1 == l2 -> unifySpine ctx lvl sp1 sp2
    (VFlexible m1 sp1 :@ p1, VFlexible m2 sp2 :@ p2)
      | m1 == m2 -> unifySpine ctx lvl sp1 sp2
    (VFlexible m sp :@ p1, t) -> solve lvl m sp t
    (t, VFlexible m sp :@ p2) -> solve lvl m sp t
    (VType :@ _, VType :@ _) -> pure ()
    _ -> throwError UnificationError

unify :: forall m. MonadElab m => Context -> Located Value -> Located Value -> m ()
unify ctx v1 v2 =
  unify' ctx (lvl ctx) v1 v2
    `catchError` \UnificationError -> do
      (v1, v2) <-
        (,)
          <$> quote ctx (lvl ctx) v1
          <*> quote ctx (lvl ctx) v2
      throwError $ CannotUnify v1 v2
