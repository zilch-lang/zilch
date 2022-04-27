{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Typecheck.Unification (unify) where

import Control.Monad.Except (catchError, throwError)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Located (Located ((:@)), unLoc)
import qualified Data.Text as Text
import Language.Zilch.Typecheck.Context (Context (lvl), emptyContext, setMeta)
import Language.Zilch.Typecheck.Core.AST (Expression (..), Parameter (Parameter))
import Language.Zilch.Typecheck.Core.Eval (DeBruijnLvl (Lvl), MetaEntry (Solved), Spine, Value (..))
import Language.Zilch.Typecheck.Elaborator (MonadElab)
import Language.Zilch.Typecheck.Errors (ElabError (TypesAreNotEqual, UnificationError))
import Language.Zilch.Typecheck.Evaluator (apply, applyVal, debruijnLevelToIndex, eval, force, plugNormalisation, quote)

data PartialRenaming = Rename
  { -- | Size of domain of meta
    dom :: DeBruijnLvl,
    -- | Size of codomain of meta
    codom :: DeBruijnLvl,
    -- | Mapping from codomain to domain
    ren :: IntMap DeBruijnLvl
  }

-- | Insert a new bound variable in partial renaming.
lift :: PartialRenaming -> PartialRenaming
lift (Rename dom cod@(Lvl ix) ren) =
  Rename (dom + 1) (cod + 1) (IntMap.insert ix dom ren)

invert :: forall m. MonadElab m => Context -> DeBruijnLvl -> Spine -> m PartialRenaming
invert ctx g sp = do
  (dom, ren) <- generateRenaming sp
  pure $ Rename dom g ren
  where
    generateRenaming :: Spine -> m (DeBruijnLvl, IntMap DeBruijnLvl)
    generateRenaming [] = pure (0, mempty)
    generateRenaming (t : sp) = do
      (dom, ren) <- generateRenaming sp
      plugNormalisation (force ctx t) >>= \case
        VIdentifier (Lvl x) [] :@ _ | IntMap.notMember x ren -> pure (dom + 1, IntMap.insert x dom ren)
        _ -> throwError UnificationError

rename :: forall m. MonadElab m => Context -> Located Int -> PartialRenaming -> Located Value -> m (Located Expression)
rename ctx m = go
  where
    goSpine _ t [] = pure t
    goSpine ren t@(_ :@ p) (u : sp) = do
      t1 <- goSpine ren t sp
      t2 <- go ren u
      pure $ EApplication t1 t2 :@ p

    go pren t =
      plugNormalisation (force ctx t) >>= \case
        VFlexible m' sp :@ p
          | m == m' -> throwError UnificationError -- occurs check, maybe put a better error?
          | otherwise -> goSpine pren (EMeta m' :@ p) sp
        VIdentifier (Lvl x) sp :@ p -> case IntMap.lookup x (ren pren) of
          Nothing -> throwError UnificationError -- variable escaping scope
          Just x -> goSpine pren (EIdentifier (debruijnLevelToIndex (dom pren) x :@ p) :@ p) sp
        VLam ty :@ p -> do
          ty <- go (lift pren) =<< plugNormalisation do apply ctx ty (VIdentifier (codom pren) [] :@ p)
          pure $ ELam ty :@ p -- TODO: what to put here
        VPi x ty1 ty2 :@ p -> do
          ty1 <- go pren ty1
          ty2 <- go (lift pren) =<< plugNormalisation do apply ctx ty2 (VIdentifier (codom pren) [] :@ p)
          pure $ EPi (Parameter False (x :@ p) ty1 :@ p) ty2 :@ p
        VType :@ p -> pure $ EType :@ p
        VInteger i :@ p -> pure $ EInteger (Text.pack (show i) :@ p) :@ p
        VCharacter c :@ p -> pure $ ECharacter (Text.singleton c :@ p) :@ p
        VApplication v1 v2 :@ p -> undefined -- TODO: what to do here?

solve :: forall m. MonadElab m => Context -> Located Int -> Spine -> Located Value -> m ()
solve ctx m sp rhs@(_ :@ p) = do
  let g = lvl ctx
  pren <- invert ctx g sp
  rhs <- rename ctx m pren rhs
  solution <- plugNormalisation $ eval emptyContext (toLambdas (dom pren) rhs)
  let !() = setMeta (unLoc m) (Solved solution)
  pure ()
  where
    toLambdas :: DeBruijnLvl -> Located Expression -> Located Expression
    toLambdas (Lvl l) t = go 0 l t

    go :: Int -> Int -> Located Expression -> Located Expression
    go x lvl t
      | x == lvl = t
      | otherwise = ELam (go (x + 1) lvl t) :@ p

unify :: forall m. MonadElab m => Context -> Located Value -> Located Value -> m ()
unify ctx t@(_ :@ p) u = do
  (t', u') <- plugNormalisation do
    (,) <$> quote ctx (lvl ctx) t <*> quote ctx (lvl ctx) u
  unify' ctx t u `catchError` \UnificationError -> throwError $ TypesAreNotEqual t' u' p
  where
    unify' :: Context -> Located Value -> Located Value -> m ()
    unify' ctx t@(_ :@ p1) u@(_ :@ p2) =
      let lvl' = lvl ctx
       in plugNormalisation ((,) <$> force ctx t <*> force ctx u) >>= \case
            (VLam t :@ _, VLam t' :@ _) -> do
              t1 <- plugNormalisation $ apply ctx t (VIdentifier lvl' [] :@ p1)
              t2 <- plugNormalisation $ apply ctx t' (VIdentifier lvl' [] :@ p2)
              unify' (ctx {lvl = lvl ctx + 1}) t1 t2
            (t, VLam t' :@ _) -> do
              t1 <- plugNormalisation $ applyVal ctx t (VIdentifier lvl' [] :@ p1)
              t2 <- plugNormalisation $ apply ctx t' (VIdentifier lvl' [] :@ p2)
              unify' (ctx {lvl = lvl ctx + 1}) t1 t2
            (VLam t :@ _, t') -> do
              t1 <- plugNormalisation $ apply ctx t (VIdentifier lvl' [] :@ p1)
              t2 <- plugNormalisation $ applyVal ctx t' (VIdentifier lvl' [] :@ p2)
              unify' (ctx {lvl = lvl ctx + 1}) t1 t2
            (VType :@ _, VType :@ _) -> pure ()
            (VPi _ a b :@ _, VPi _ a' b' :@ _) -> do
              unify' ctx a a'
              t1 <- plugNormalisation $ apply ctx b (VIdentifier lvl' [] :@ p1)
              t2 <- plugNormalisation $ apply ctx b' (VIdentifier lvl' [] :@ p2)
              unify' (ctx {lvl = lvl ctx + 1}) t1 t2
            (VIdentifier x sp :@ _, VIdentifier x' sp' :@ _) | x == x' -> unifySpine ctx sp sp'
            (VFlexible m sp :@ _, VFlexible m' sp' :@ _) | m == m' -> unifySpine ctx sp sp'
            (VFlexible m sp :@ _, t') -> solve ctx m sp t'
            (t, VFlexible m' sp' :@ _) -> solve ctx m' sp' t
            (_, _) -> throwError UnificationError

unifySpine :: forall m. MonadElab m => Context -> Spine -> Spine -> m ()
unifySpine ctx [] [] = pure ()
unifySpine ctx (t : sp) (t' : sp') = do
  unifySpine ctx sp sp'
  unify ctx t t'
unifySpine _ _ _ = throwError UnificationError
