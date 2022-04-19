{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Zilch.Typecheck.Evaluator (normalize, normalize0) where

import Control.Monad ((<=<))
import Control.Monad.Except (MonadError, runExcept, throwError)
import Data.Bifunctor (first)
import qualified Data.HashMap as Hash
import Data.Located (Located ((:@)), unLoc)
import Data.Text (Text)
import qualified Data.Text as Text
import Error.Diagnose (Diagnostic, addReport, def)
import Language.Zilch.Syntax.Core.AST (Definition (..), Expression (..), Parameter (..))
import Language.Zilch.Typecheck.Core.Eval
import Language.Zilch.Typecheck.Errors
import Language.Zilch.Typecheck.Fresh (fresh)
import Prelude hiding (read)
import qualified Prelude (read)

type MonadEval m = (MonadError EvalError m)

------------

-- | Extend the given environment by one entry.
extend :: Environment -> Name -> Located Value -> Environment
extend env name val = Hash.insert name val env

-- | Evaluate the given expression in normal form, where normal form is either:
--
-- * A lambda
-- * An application @(e1 e2)@ where @e1@ is /not/ a lambda
-- * An integer
-- * The pi type
eval :: forall m. MonadEval m => Environment -> Located Expression -> m (Located Value)
eval _ (EInteger e :@ p) = pure $ VInteger (read $ unLoc e) :@ p
eval env (EIdentifier n :@ p) =
  maybe (throwError $ NoSuchBinding (unLoc n) p) pure $ Hash.lookup (unLoc n) env
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
eval _ e = error $ "unhandled case " <> show e

apply :: forall m. MonadEval m => Closure -> Name -> Located Value -> m (Located Value)
apply (Clos env expr) name val = eval (extend env name val) expr

quote :: forall m. MonadEval m => Environment -> Located Value -> m (Located Expression)
quote _ (VIdentifier n :@ p) = pure $ EIdentifier (n :@ p) :@ p
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
quote _ v = error $ "not yet handled " <> show v

toNF :: Environment -> Located Expression -> Either (Diagnostic String) (Located Expression)
toNF env = first toDiagnostic . runExcept . (quote env <=< eval env)
  where
    toDiagnostic = addReport def . fromEvalError

normalize :: Environment -> Located Expression -> Either (Diagnostic String) (Located Expression)
normalize = toNF

normalize0 :: Located Expression -> Either (Diagnostic String) (Located Expression)
normalize0 = toNF mempty

------------

read :: Read a => Text -> a
read = Prelude.read . Text.unpack
