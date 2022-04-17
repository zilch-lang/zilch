{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Syntax.Desugarer where

import Control.Monad (unless)
import Control.Monad.Except (MonadError, runExcept, throwError)
import Control.Monad.State (MonadState, evalStateT)
import Control.Monad.Writer (MonadWriter, runWriterT)
import Data.Bifunctor (bimap, second)
import Data.Foldable (foldlM)
import Data.List (foldl')
import Data.Located (Located ((:@)))
import Error.Diagnose (Diagnostic, addReport, def)
import qualified Language.Zilch.Syntax.Core.AST as AST
import qualified Language.Zilch.Syntax.Core.CST as CST
import Language.Zilch.Syntax.Errors

type MonadDesugar m = (MonadError DesugarError m, MonadWriter [DesugarWarning] m, MonadState () m)

desugarCST :: Located CST.Module -> Either (Diagnostic String) (Located AST.Module, Diagnostic String)
desugarCST mod =
  bimap toErrorDiagnostic (second toWarningDiagnostic) $
    runExcept $
      runWriterT $
        evalStateT (desugarModule mod) ()
  where
    toErrorDiagnostic err = addReport def (fromDesugarerError err)
    toWarningDiagnostic warns = foldl' addReport def (fromDesugarerWarning <$> warns)

-----------------

desugarModule :: forall m. MonadDesugar m => Located CST.Module -> m (Located AST.Module)
desugarModule (CST.Mod _ defs :@ p) = do
  defs' <- traverse desugarToplevel defs
  pure $ AST.Mod [] defs' :@ p

desugarToplevel :: forall m. MonadDesugar m => Located CST.TopLevelDefinition -> m (Located AST.TopLevel)
desugarToplevel (CST.TopLevel _ isPublic def :@ p) = do
  def' <- desugarDefinition def
  pure $ AST.TopLevel isPublic def' :@ p

desugarDefinition :: forall m. MonadDesugar m => Located CST.Definition -> m (Located AST.Definition)
desugarDefinition (CST.Let name params retTy ret :@ p) = do
  (implicits, explicits) <- separateParameters params
  retTy' <- traverse desugarExpression retTy
  ret' <- desugarExpression ret
  pure $ AST.Let False name implicits explicits retTy' ret' :@ p
desugarDefinition (CST.Rec name params retTy ret :@ p) = do
  (implicits, explicits) <- separateParameters params
  retTy' <- traverse desugarExpression retTy
  ret' <- desugarExpression ret
  pure $ AST.Let True name implicits explicits retTy' ret' :@ p

separateParameters :: forall m. MonadDesugar m => [Located CST.Parameter] -> m ([Located AST.Parameter], [Located AST.Parameter])
separateParameters ps = bimap reverse reverse . snd <$> foldlM separate (True, ([], [])) ps
  where
    separate (wasImplicit, (implicits, explicits)) (CST.Implicit name ty :@ p) = do
      unless wasImplicit do
        throwError (ImplicitAfterExplicit name p)

      ty' <- traverse desugarExpression ty
      pure (True, ((AST.Parameter True name ty' :@ p) : implicits, explicits))
    separate (_, (implicits, explicits)) (CST.Explicit name ty :@ p) = do
      ty' <- traverse desugarExpression ty
      pure (False, (implicits, (AST.Parameter False name ty' :@ p) : explicits))

desugarExpression :: forall m. MonadDesugar m => Located CST.Expression -> m (Located AST.Expression)
desugarExpression = undefined
