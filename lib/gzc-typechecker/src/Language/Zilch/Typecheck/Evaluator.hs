{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Typecheck.Evaluator (normalize, normalize0, eval, apply, quote, plugNormalisation, applyVal, debruijnLevelToIndex) where

import Control.Monad ((<=<))
import Control.Monad.Except (Except, MonadError, runExcept, throwError)
import Data.Bifunctor (first)
import Data.Located (Located ((:@)), unLoc)
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
eval _ e = error $ "unhandled case " <> show e

apply :: forall m. MonadEval m => Context -> Closure -> Located Value -> m (Located Value)
apply ctx (Clos env expr) val =
  let env' = Env.extend env val
   in eval (emptyContext {env = env'}) expr

applyVal :: forall m. MonadEval m => Context -> Located Value -> Located Value -> m (Located Value)
applyVal ctx (VLam t :@ _) u = apply ctx t u
applyVal ctx t@(_ :@ p) u = pure $ VApplication t u :@ p

debruijnLevelToIndex :: DeBruijnLvl -> DeBruijnLvl -> TAST.DeBruijnIdx
debruijnLevelToIndex (Lvl l) (Lvl x) = TAST.Idx $! l - x - 1

quote :: forall m. MonadEval m => Context -> DeBruijnLvl -> Located Value -> m (Located TAST.Expression)
quote ctx level val =
  case val of
    (VIdentifier n :@ p) -> pure $ TAST.EIdentifier (debruijnLevelToIndex (lvl ctx) n :@ p) :@ p
    (VCharacter c :@ p) -> pure $ TAST.ECharacter (Text.singleton c :@ p) :@ p
    (VInteger n :@ p) -> pure $ TAST.EInteger (Text.pack (show n) :@ p) :@ p
    (VLam clos :@ p) -> do
      x' <- apply ctx clos (VIdentifier level :@ p)
      x' <- quote ctx (level + 1) x'
      pure $
        TAST.ELam
          x'
          :@ p
    (VPi y val clos :@ p) -> do
      x' <- apply ctx clos (VIdentifier level :@ p)
      val' <- quote ctx level val
      x' <- quote ctx (level + 1) x'
      pure $
        TAST.EPi
          (TAST.Parameter False (y :@ p) val' :@ p)
          x'
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
