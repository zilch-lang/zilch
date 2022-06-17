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
import Language.Zilch.Typecheck.Core.Eval (DeBruijnLvl (Lvl), MetaEntry (Solved, Unsolved), Spine, Value (VFlexible, VLam, VPi, VRigid, VType, VVariable))
import {-# SOURCE #-} Language.Zilch.Typecheck.Elaborator (MonadElab)
import Language.Zilch.Typecheck.Errors (ElabError (CannotUnify, UnificationError, UsageMismatch))
import Language.Zilch.Typecheck.Evaluator (apply, applyVal, debruijnLevelToIndex, eval, force, plugNormalisation, quote)
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
    go (t : sp) = do
      (dom, ren) <- go sp
      t' <- plugNormalisation $ force ctx t
      case t' of
        VVariable _ (Lvl x) :@ _ | IntMap.notMember x ren -> pure (dom + 1, IntMap.insert x dom ren)
        _ -> throwError UnificationError

rename :: forall m. MonadElab m => Context -> Int -> PartialRenaming -> Located Value -> m (Located TAST.Expression)
rename ctx m ren v = go ren v
  where
    go :: PartialRenaming -> Located Value -> m (Located TAST.Expression)
    go ren@(Renaming dom cod env) t =
      plugNormalisation (force ctx t) >>= \case
        VFlexible m' sp :@ p
          | m == m' -> throwError UnificationError
          | otherwise -> goSpine ren (TAST.EMeta m' :@ p) sp
        VRigid name (Lvl x) sp :@ p -> case IntMap.lookup x env of
          Nothing -> throwError UnificationError
          Just x' -> goSpine ren (TAST.EIdentifier name (debruijnLevelToIndex dom x') :@ p) sp
        VLam usage x a t :@ p -> do
          a' <- go ren a
          t' <- go (lift ren) =<< plugNormalisation (apply ctx t (VVariable ("?" :@ p) cod :@ p))
          pure $ TAST.ELam (TAST.Parameter True (usage :@ p) (x :@ p) a' :@ p) t' :@ p
        VPi usage x a t :@ p -> do
          a' <- go ren a
          t' <- go (lift ren) =<< plugNormalisation (apply ctx t (VVariable ("?" :@ p) cod :@ p))
          pure $ TAST.EPi (TAST.Parameter True (usage :@ p) (x :@ p) a' :@ p) t' :@ p
        VType :@ p -> pure $ TAST.EType :@ p
        t :@ p -> error "TODO: rename base terms"

    goSpine ren t [] = pure t
    goSpine ren t@(_ :@ p) (u : sp) = do
      v1 <- goSpine ren t sp
      v2 <- go ren u
      pure $ TAST.EApplication v1 v2 :@ p

solve :: forall m. MonadElab m => DeBruijnLvl -> Int -> Spine -> Located Value -> m ()
solve gamma m sp val = do
  let ctx = emptyContext
  ren@(Renaming dom _ _) <- invert ctx gamma sp
  val'@(_ :@ p) <- rename ctx m ren val
  solution :@ _ <- plugNormalisation do eval ctx $ lams dom val' p
  let !_ = unsafeDupablePerformIO $ modifyIORef' mcxt $ IntMap.insert m (Solved solution)
  pure ()
  where
    lams = go 0

    go x lvl t _ | x == lvl = t
    go x lvl t p =
      TAST.ELam
        (TAST.Parameter True (TAST.Unrestricted :@ p) (("$" <> Text.pack (show (x + 1))) :@ p) (TAST.EUnknown :@ p) :@ p)
        (go (x + 1) lvl t p)
        :@ p

unifySpine :: forall m. MonadElab m => Context -> DeBruijnLvl -> Spine -> Spine -> m ()
unifySpine _ _ [] [] = pure ()
unifySpine ctx lvl (t : sp) (t' : sp') = do
  unifySpine ctx lvl sp sp'
  unify' ctx lvl t t'
unifySpine _ _ _ _ = throwError UnificationError

unify' :: forall m. MonadElab m => Context -> DeBruijnLvl -> Located Value -> Located Value -> m ()
unify' ctx lvl t u = do
  t <- plugNormalisation $ force ctx t
  u <- plugNormalisation $ force ctx u
  case (t, u) of
    (VLam u1 _ a1 t1 :@ p1, VLam u2 _ a2 t2 :@ p2) -> do
      unifyUsage (u1 :@ p1) (u2 :@ p2)
      unify' ctx lvl a1 a2
      (v1, v2) <- plugNormalisation do
        (,)
          <$> apply ctx t1 (VVariable ("x?" :@ p1) lvl :@ p1)
          <*> apply ctx t2 (VVariable ("x?" :@ p2) lvl :@ p2)
      unify' ctx (lvl + 1) v1 v2
    (t1 :@ p1, VLam _ _ _ t2 :@ p2) -> do
      (v1, v2) <- plugNormalisation do
        (,)
          <$> applyVal ctx (t1 :@ p1) (VVariable ("x?" :@ p1) lvl :@ p1)
          <*> apply ctx t2 (VVariable ("x?" :@ p2) lvl :@ p2)
      unify' ctx (lvl + 1) v1 v2
    (VLam _ _ _ t1 :@ p1, t2 :@ p2) -> do
      (v2, v1) <- plugNormalisation do
        (,)
          <$> applyVal ctx (t2 :@ p2) (VVariable ("x?" :@ p2) lvl :@ p2)
          <*> apply ctx t1 (VVariable ("x?" :@ p1) lvl :@ p1)
      unify' ctx (lvl + 1) v1 v2
    (VPi u1 _ a1 t1 :@ p1, VPi u2 _ a2 t2 :@ p2) -> do
      unifyUsage (u1 :@ p1) (u2 :@ p2)
      unify' ctx lvl a1 a2
      (v1, v2) <- plugNormalisation do
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
      (v1, v2) <- plugNormalisation do
        (,)
          <$> quote ctx (lvl ctx) v1
          <*> quote ctx (lvl ctx) v2
      throwError $ CannotUnify v1 v2

unifyUsage :: forall m. MonadElab m => Located TAST.Usage -> Located TAST.Usage -> m ()
-- unifyUsage expected actual
unifyUsage (TAST.Unrestricted :@ _) _ = pure ()
unifyUsage (TAST.Linear :@ _) (TAST.Linear :@ _) = pure ()
unifyUsage (TAST.Erased :@ _) (TAST.Erased :@ _) = pure ()
unifyUsage u1 u2 = throwError $ UsageMismatch u1 u2
