{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Zilch.Typecheck.Evaluator (normalize, normalize0, eval, apply, quote, plugNormalisation) where

import Control.Monad ((<=<))
import Control.Monad.Except (Except, MonadError, runExcept, throwError)
import Data.Bifunctor (first)
import Data.Located (Located ((:@)), unLoc)
import Data.Text (Text)
import qualified Data.Text as Text
import Error.Diagnose (Diagnostic, addReport, def)
import Language.Zilch.Syntax.Core.AST (Definition (..), Expression (..), Parameter (..))
import Language.Zilch.Typecheck.Core.Eval
import Language.Zilch.Typecheck.Defaults (defaultEnv)
import {-# SOURCE #-} Language.Zilch.Typecheck.Elaborator (MonadElab)
import Language.Zilch.Typecheck.Environment (extend, lookup)
import Language.Zilch.Typecheck.Errors
import Language.Zilch.Typecheck.Fresh (fresh)
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
eval :: forall m. MonadEval m => Environment -> Located Expression -> m (Located Value)
eval _ (EInteger e :@ p) = pure $ VInteger (read $ unLoc e) :@ p
eval _ (ECharacter (c :@ _) :@ p) = pure $ VCharacter (Text.head c) :@ p
eval env (EIdentifier n :@ p) =
  maybe (throwError $ NoSuchBinding (unLoc n) p) pure $ lookup env (unLoc n)
eval env (EApplication e1 e2 :@ p) = do
  v1 <- eval env e1
  v2 <- eval env e2

  case (v1, v2) of
    (VLam x clos :@ _, u) -> apply clos x u
    (t, u) -> pure $ VApplication t u :@ p
eval _ (ELet (Let True _ _ _ :@ _) _ :@ p) = throwError $ RecursiveBindingNormalisation p
eval env (ELet (Let False name _ val :@ _) u :@ _) = do
  val' <- eval env val
  eval (extend env (unLoc name) val') u
eval env (EPi (Parameter _ name ty1 :@ _) ty2 :@ p) = do
  ty1' <- eval env ty1
  pure $ VPi (unLoc name) ty1' (Clos env ty2) :@ p
eval env (ELam (Parameter _ name _ :@ _) ex :@ p) = pure $ VLam (unLoc name) (Clos env ex) :@ p
eval env (EType :@ p) = pure $ VType :@ p
eval env (EHole :@ p) = pure $ VHole :@ p
eval _ e = error $ "unhandled case " <> show e

apply :: forall m. MonadEval m => Closure -> Name -> Located Value -> m (Located Value)
apply (Clos env expr) name val = eval (extend env name val) expr

quote :: forall m. MonadEval m => Environment -> Located Value -> m (Located Expression)
quote _ (VIdentifier n :@ p) = pure $ EIdentifier (n :@ p) :@ p
quote _ (VCharacter c :@ p) = pure $ ECharacter (Text.singleton c :@ p) :@ p
quote _ (VInteger n :@ p) = pure $ EInteger (Text.pack (show n) :@ p) :@ p
quote env (VApplication v1 v2 :@ p) = do
  v1' <- quote env v1
  v2' <- quote env v2
  pure $ EApplication v1' v2' :@ p
quote env (VLam y clos :@ p) = do
  let x = fresh env y
  x' <- apply clos y (VIdentifier x :@ p)
  x'' <- quote (extend env x (VIdentifier x :@ p)) x'
  pure $
    ELam
      (Parameter False (x :@ p) (EHole :@ p) :@ p)
      x''
      :@ p
quote env (VPi y val clos :@ p) = do
  let x = fresh env y
  x' <- apply clos y (VIdentifier x :@ p)
  val' <- quote env val
  x'' <- quote (extend env x (VIdentifier x :@ p)) x'
  pure $
    EPi
      (Parameter False (x :@ p) val' :@ p)
      x''
      :@ p
quote _ (VType :@ p) = pure $ EType :@ p
quote _ (VHole :@ p) = pure $ EHole :@ p
quote _ v = error $ "not yet handled " <> show v

toNF :: Environment -> Located Expression -> Either (Diagnostic String) (Located Expression)
toNF env = first toDiagnostic . runExcept . (quote env <=< eval env)
  where
    toDiagnostic = addReport def . fromEvalError

normalize :: Environment -> Located Expression -> Either (Diagnostic String) (Located Expression)
normalize = toNF
{-# INLINE normalize #-}

normalize0 :: Located Expression -> Either (Diagnostic String) (Located Expression)
normalize0 = normalize defaultEnv
{-# INLINE normalize0 #-}

plugNormalisation :: forall m1 a. MonadElab m1 => Except EvalError a {- MonadEval m => m a -} -> m1 a
plugNormalisation m =
  case runExcept m of
    Left err -> throwError $ FromEvalError err
    Right res -> pure res

------------

read :: Read a => Text -> a
read = Prelude.read . Text.unpack
