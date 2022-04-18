{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Syntax.Desugarer where

import Control.Monad.Except (MonadError, runExcept)
import Control.Monad.State (MonadState, evalStateT)
import Control.Monad.Writer (MonadWriter, runWriterT)
import Data.Bifunctor (bimap, second)
import Data.List (foldl')
import Data.Located (Located ((:@)))
import Data.Maybe (fromMaybe)
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
desugarDefinition (CST.Let name params retTy ret@(_ :@ p1) :@ p) = do
  params' <- traverse desugarParameter params
  retTy' <- traverse desugarExpression retTy

  let ty = foldr mkPi (fromMaybe (AST.EHole :@ p) retTy') params'
  val <- desugarExpression (CST.ELam params ret :@ p1)

  pure $ AST.Let False name ty val :@ p
  where
    mkPi param expr = AST.EPi param expr :@ p
desugarDefinition (CST.Rec name params retTy ret@(_ :@ p1) :@ p) = do
  params' <- traverse desugarParameter params
  retTy' <- traverse desugarExpression retTy

  let ty = foldr mkPi (fromMaybe (AST.EHole :@ p) retTy') params'
  val <- desugarExpression (CST.ELam params ret :@ p1)

  pure $ AST.Let True name ty val :@ p
  where
    mkPi param expr = AST.EPi param expr :@ p

desugarParameter :: forall m. MonadDesugar m => Located CST.Parameter -> m (Located AST.Parameter)
desugarParameter (CST.Implicit name ty :@ p) = do
  ty' <- maybe (pure $ AST.EHole :@ p) desugarExpression ty
  pure $ AST.Parameter True name ty' :@ p
desugarParameter (CST.Explicit name ty :@ p) = do
  ty' <- maybe (pure $ AST.EHole :@ p) desugarExpression ty
  pure $ AST.Parameter False name ty' :@ p

desugarExpression :: forall m. MonadDesugar m => Located CST.Expression -> m (Located AST.Expression)
desugarExpression (CST.EType :@ p) = pure $ AST.EType :@ p
desugarExpression (CST.EId i :@ p) = pure $ AST.EIdentifier i :@ p
desugarExpression (CST.EHole :@ p) = pure $ AST.EHole :@ p
desugarExpression (CST.EInt i :@ p) = pure $ AST.EInteger (i :@ p) :@ p
desugarExpression (CST.EChar c :@ p) = pure $ AST.ECharacter (c :@ p) :@ p
desugarExpression (CST.EImplicit expr :@ p) = do
  expr' <- desugarExpression expr
  pure $ AST.EImplicit expr' :@ p
desugarExpression (CST.ELam params expr :@ p) = do
  params' <- traverse desugarParameter params
  expr' <- desugarExpression expr

  pure $ foldr mkLam expr' params'
  where
    mkLam param expr = AST.ELam param expr :@ p
desugarExpression (CST.EDo expr :@ p) = do
  expr' <- desugarExpression expr
  pure $ AST.EDo expr' :@ p
desugarExpression (CST.ELet def ret :@ p) = do
  def' <- desugarDefinition def
  ret' <- desugarExpression ret
  pure $ AST.ELet def' ret' :@ p
desugarExpression (CST.EApplication [e] :@ _) = desugarExpression e
desugarExpression (CST.EParens e :@ _) = desugarExpression e
desugarExpression (CST.EApplication (e : es) :@ p) = do
  e' <- desugarExpression e
  es' <- traverse desugarExpression es
  pure $ foldl' mkApp e' es'
  where
    mkApp e1 e2 = AST.EApplication e1 e2 :@ p
desugarExpression (CST.EPi param ret :@ p) = do
  param' <- desugarParameter param
  ret' <- desugarExpression ret
  pure $ AST.EPi param' ret' :@ p
desugarExpression _ = error "todo"
