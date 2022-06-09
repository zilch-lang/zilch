{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Typecheck.Evaluator (normalize, normalize0, eval, apply, quote, plugNormalisation, applyVal, debruijnLevelToIndex, force) where

import Control.Monad ((<=<))
import Control.Monad.Except (Except, MonadError, runExcept, throwError)
import Data.Bifunctor (first)
import Data.Located (Located ((:@)), Position, unLoc)
import Data.Text (Text)
import qualified Data.Text as Text
import Debug.Trace (trace)
import Error.Diagnose (Diagnostic, addReport, def)
import Language.Zilch.Typecheck.Context (Context (env, lvl), emptyContext)
import qualified Language.Zilch.Typecheck.Core.AST as TAST
import Language.Zilch.Typecheck.Core.Eval
import Language.Zilch.Typecheck.Defaults (defaultContext)
import {-# SOURCE #-} Language.Zilch.Typecheck.Elaborator (MonadElab)
import Language.Zilch.Typecheck.Environment (lookup)
import qualified Language.Zilch.Typecheck.Environment as Env
import Language.Zilch.Typecheck.Errors
import Language.Zilch.Typecheck.Metavariables (lookupMeta)
import Prelude hiding (lookup, read)
import qualified Prelude (read)

type MonadEval m = (MonadError EvalError m)

------------

-- | Evaluate the given expression in normal form, where normal form is either:
--
-- * A lambda
-- * An application @(e1 e2)@ where @e1@ is /not/ a lambda
-- * An integer
-- * The pi type
eval :: forall m. MonadEval m => Context -> Located TAST.Expression -> m (Located Value)
eval _ (TAST.EInteger e :@ p) = pure $ VInteger (read $ unLoc e) :@ p
eval _ (TAST.ECharacter (c :@ _) :@ p) = pure $ VCharacter (Text.head c) :@ p
eval ctx (TAST.EIdentifier (name :@ _) (TAST.Idx i) :@ _) = pure $ lookup (env ctx) i
eval ctx (TAST.EApplication e1 e2 :@ _) = do
  v1 <- eval ctx e1
  v2 <- eval ctx e2

  applyVal ctx v1 v2
eval _ (TAST.ELet (TAST.Let True _ _ _ :@ _) _ :@ p) = throwError $ RecursiveBindingNormalisation p
eval ctx (TAST.ELet (TAST.Let False _ _ val :@ _) u :@ _) = do
  val' <- eval ctx val
  let env' = Env.extend (env ctx) val'
  eval (ctx {env = env'}) u
eval ctx (TAST.EPi (TAST.Parameter _ name ty1 :@ _) ty2 :@ p) = do
  ty1' <- eval ctx ty1
  pure $ VPi (unLoc name) ty1' (Clos (env ctx) ty2) :@ p
eval ctx (TAST.ELam (TAST.Parameter _ (x :@ _) _ :@ _) ex :@ p) = pure $ VLam x (Clos (env ctx) ex) :@ p
eval _ (TAST.EType :@ p) = pure $ VType :@ p
eval _ (TAST.EMeta m :@ p) = pure $ metaValue m p
eval ctx (TAST.EInsertedMeta m bds :@ p) = applyBDs ctx (env ctx) (metaValue m p) bds
eval _ e = error $ "unhandled case " <> show e

apply :: forall m. MonadEval m => Context -> Closure -> Located Value -> m (Located Value)
apply ctx (Clos env expr) val =
  let env' = Env.extend env val
   in eval (emptyContext {env = env'}) expr

applyVal :: forall m. MonadEval m => Context -> Located Value -> Located Value -> m (Located Value)
applyVal ctx (VLam _ t :@ _) u = apply ctx t u
applyVal ctx (VFlexible x sp :@ p) u = pure $ VFlexible x (u : sp) :@ p
applyVal ctx (VRigid x name sp :@ p) u = pure $ VRigid x name (u : sp) :@ p
applyVal ctx t@(_ :@ p) u = pure $ VApplication t u :@ p -- TODO: remove

applySpine :: forall m. MonadEval m => Context -> Located Value -> Spine -> m (Located Value)
applySpine ctx t [] = pure t
applySpine ctx t (u : sp) = do
  v1 <- applySpine ctx t sp
  applyVal ctx v1 t

applyBDs :: forall m. MonadEval m => Context -> Environment -> Located Value -> [TAST.Binding] -> m (Located Value)
applyBDs _ [] v [] = pure v
applyBDs ctx (t : env) v (TAST.Bound _ : bds) = do
  v1 <- applyBDs ctx env v bds
  applyVal ctx v1 t
applyBDs ctx (t : env) v (TAST.Defined _ : bds) = applyBDs ctx env v bds
applyBDs _ _ _ _ = error "impossible"

metaValue :: Int -> Position -> Located Value
metaValue m pos = case lookupMeta m of
  Solved v -> v :@ pos
  Unsolved -> VMeta m :@ pos

force :: forall m. MonadEval m => Context -> Located Value -> m (Located Value)
force ctx (VFlexible m sp :@ p) | Solved t <- lookupMeta m = do
  v1 <- applySpine ctx (t :@ p) sp
  force ctx v1
force ctx t = pure t

debruijnLevelToIndex :: DeBruijnLvl -> DeBruijnLvl -> TAST.DeBruijnIdx
debruijnLevelToIndex (Lvl l) (Lvl x) = TAST.Idx $! l - x - 1

quote :: forall m. MonadEval m => Context -> DeBruijnLvl -> Located Value -> m (Located TAST.Expression)
quote ctx level val = do
  v <- force ctx val
  case v of
    -- (VIdentifier name n :@ p) -> pure $ TAST.EIdentifier name (debruijnLevelToIndex level n) :@ p
    VFlexible m sp :@ p -> quoteSpine ctx level (TAST.EMeta m :@ p) sp p
    VRigid name m sp :@ p -> quoteSpine ctx level (TAST.EIdentifier name (debruijnLevelToIndex level m) :@ p) sp p
    (VCharacter c :@ p) -> pure $ TAST.ECharacter (Text.singleton c :@ p) :@ p
    (VInteger n :@ p) -> pure $ TAST.EInteger (Text.pack (show n) :@ p) :@ p
    (VLam name clos :@ p) -> do
      x' <- apply ctx clos (VVariable (name :@ p) level :@ p)
      x' <- quote ctx (level + 1) x'
      pure $
        TAST.ELam
          (TAST.Parameter False (name :@ p) (TAST.EIdentifier ("?" :@ p) (debruijnLevelToIndex level 0) :@ p) :@ p)
          x'
          :@ p
    (VPi y val clos :@ p) -> do
      x' <- apply ctx clos (VVariable (y :@ p) level :@ p)
      val' <- quote ctx level val
      x' <- quote ctx (level + 1) x'
      pure $
        TAST.EPi
          (TAST.Parameter False (y :@ p) val' :@ p)
          x'
          :@ p
    (VType :@ p) -> pure $ TAST.EType :@ p
    v -> error $ "not yet handled " <> show v

quoteSpine :: forall m. MonadEval m => Context -> DeBruijnLvl -> Located TAST.Expression -> Spine -> Position -> m (Located TAST.Expression)
quoteSpine ctx lvl term [] _ = pure term
quoteSpine ctx lvl term (u : sp) pos = do
  t1 <- quote ctx lvl u
  t2 <- quoteSpine ctx lvl term sp pos
  pure $ TAST.EApplication t1 t2 :@ pos

toNF :: Context -> Located TAST.Expression -> Either (Diagnostic String) (Located TAST.Expression)
toNF ctx =
  first toDiagnostic
    . runExcept
    . (quote ctx (Lvl . Env.length $ env ctx) <=< eval ctx)
  where
    toDiagnostic = addReport def . fromEvalError

normalize :: Context -> Located TAST.Expression -> Either (Diagnostic String) (Located TAST.Expression)
normalize = toNF
{-# INLINE normalize #-}

normalize0 :: Located TAST.Expression -> Either (Diagnostic String) (Located TAST.Expression)
normalize0 = normalize defaultContext
{-# INLINE normalize0 #-}

plugNormalisation :: forall m1 a. MonadElab m1 => Except EvalError a {- MonadEval m => m a -} -> m1 a
plugNormalisation m =
  case runExcept m of
    Left err -> throwError $ FromEvalError err
    Right res -> pure res

------------

read :: Read a => Text -> a
read = Prelude.read . Text.unpack
