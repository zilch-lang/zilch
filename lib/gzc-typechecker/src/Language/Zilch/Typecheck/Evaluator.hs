{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Typecheck.Evaluator (normalize, normalize0, eval, apply, quote, plugNormalisation, force, applyVal, debruijnLevelToIndex) where

import Control.Monad ((<=<))
import Control.Monad.Except (Except, MonadError, runExcept, throwError)
import Data.Bifunctor (first)
import Data.Located (Located ((:@)), unLoc)
import Data.Text (Text)
import qualified Data.Text as Text
import Debug.Trace (trace)
import Error.Diagnose (Diagnostic, addReport, def)
import Language.Zilch.Typecheck.Context (Context (env, lvl), emptyContext, lookupMeta)
import qualified Language.Zilch.Typecheck.Core.AST as TAST
import Language.Zilch.Typecheck.Core.Eval
import Language.Zilch.Typecheck.Defaults (defaultContext)
import {-# SOURCE #-} Language.Zilch.Typecheck.Elaborator (MonadElab)
import Language.Zilch.Typecheck.Environment (lookup)
import qualified Language.Zilch.Typecheck.Environment as Env
import Language.Zilch.Typecheck.Errors
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
eval ctx (TAST.EIdentifier (TAST.Idx i :@ _) :@ _) = pure $ lookup (env ctx) i
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
eval ctx (TAST.ELam ex :@ p) = pure $ VLam (Clos (env ctx) ex) :@ p
eval _ (TAST.EType :@ p) = pure $ VType :@ p
eval ctx (TAST.EMeta m :@ _) = pure $ evalMeta m
eval ctx (TAST.EInsertedMeta m status :@ p) = do
  let meta = evalMeta m
  trace ("Creating inserted meta " <> show m <> " " <> show status <> " " <> show (env ctx)) $ pure ()
  applyInsertedMeta ctx meta status
eval _ e = error $ "unhandled case " <> show e

evalMeta :: Located Int -> Located Value
evalMeta (m :@ p) = case lookupMeta m of
  Solved v -> v
  Unsolved -> VFlexible (m :@ p) [] :@ p

apply :: forall m. MonadEval m => Context -> Closure -> Located Value -> m (Located Value)
apply ctx (Clos env expr) val =
  let env' = Env.extend env val
   in eval (emptyContext {env = env'}) expr

applyVal :: forall m. MonadEval m => Context -> Located Value -> Located Value -> m (Located Value)
applyVal ctx (VLam t :@ _) u = apply ctx t u
applyVal _ (VFlexible m sp :@ p) u = pure $ VFlexible m (u : sp) :@ p
applyVal _ (VIdentifier x sp :@ p) u = pure $ VIdentifier x (u : sp) :@ p
applyVal _ v u = error $ "applyVal (" <> show v <> ") (" <> show u <> ")"

applySpine :: forall m. MonadEval m => Context -> Located Value -> Spine -> m (Located Value)
applySpine _ v [] = pure v
applySpine ctx v (s : sp) = do
  t <- applySpine ctx v sp
  applyVal ctx t s

applyInsertedMeta :: forall m. MonadEval m => Context -> Located Value -> [TAST.MetaStatus] -> m (Located Value)
applyInsertedMeta ctx v status =
  case (Env.toList $ env ctx, status) of
    ([], []) -> pure v
    (k : ks, TAST.Bound : ss) -> do
      val' <- applyInsertedMeta (ctx {env = ks}) v ss
      applyVal ctx val' k
    (_ : ks, TAST.Defined : ss) -> do
      applyInsertedMeta (ctx {env = ks}) v ss
    (ks, ss) -> error $ "applyInsertedMeta (" <> show ks <> ") (" <> show ss <> ")"

force :: forall m. MonadEval m => Context -> Located Value -> m (Located Value)
force ctx u@(VFlexible (m :@ _) sp :@ _) = case lookupMeta m of
  Solved t -> trace ("Found solved meta " <> show m <> " " <> show sp <> " = " <> show t) $ applySpine ctx t sp >>= force ctx
  _ -> pure u
force _ u = pure u

quoteSpine :: forall m. MonadEval m => Context -> DeBruijnLvl -> Located TAST.Expression -> Spine -> m (Located TAST.Expression)
quoteSpine _ _ term [] = pure term
quoteSpine ctx level term@(_ :@ p) (u : sp) = do
  e1 <- quoteSpine ctx level term sp
  e2 <- quote ctx level u
  pure $ TAST.EApplication e1 e2 :@ p

debruijnLevelToIndex :: DeBruijnLvl -> DeBruijnLvl -> TAST.DeBruijnIdx
debruijnLevelToIndex (Lvl l) (Lvl x) = TAST.Idx $! l - x - 1

quote :: forall m. MonadEval m => Context -> DeBruijnLvl -> Located Value -> m (Located TAST.Expression)
quote ctx level val =
  force ctx val >>= \case
    (VIdentifier n sp :@ p) ->
      quoteSpine ctx level (TAST.EIdentifier (debruijnLevelToIndex (lvl ctx) n :@ p) :@ p) sp
    (VFlexible m sp :@ p) -> quoteSpine ctx level (TAST.EMeta m :@ p) sp
    (VCharacter c :@ p) -> pure $ TAST.ECharacter (Text.singleton c :@ p) :@ p
    (VInteger n :@ p) -> pure $ TAST.EInteger (Text.pack (show n) :@ p) :@ p
    (VLam clos :@ p) -> do
      x' <- apply ctx clos (VIdentifier level [] :@ p)
      x'' <- quote ctx (level + 1) x'
      pure $
        TAST.ELam
          x''
          :@ p
    (VPi y val clos :@ p) -> do
      x' <- apply ctx clos (VIdentifier level [] :@ p)
      val' <- quote ctx level val
      x'' <- quote ctx (level + 1) x'
      pure $
        TAST.EPi
          (TAST.Parameter False (y :@ p) val' :@ p)
          x''
          :@ p
    (VType :@ p) -> pure $ TAST.EType :@ p
    v -> error $ "not yet handled " <> show v

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
