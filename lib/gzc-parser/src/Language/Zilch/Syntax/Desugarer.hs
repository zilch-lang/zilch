{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Syntax.Desugarer (desugarCST) where

import Control.Monad (forM)
import Control.Monad.Except (MonadError, runExcept, throwError)
import Control.Monad.State (MonadState, evalStateT, get, modify)
import Control.Monad.Writer (MonadWriter, runWriterT)
import Data.Bifunctor (bimap, second)
import Data.List (foldl')
import Data.Located (Located ((:@)), Position)
import Data.Maybe (catMaybes, fromJust, fromMaybe)
import Data.Text (Text)
import Error.Diagnose (Diagnostic, addReport, def)
import Language.Zilch.Syntax.Core.AST (IntegerSuffix (..))
import qualified Language.Zilch.Syntax.Core.AST as AST
import qualified Language.Zilch.Syntax.Core.CST as CST
import Language.Zilch.Syntax.Errors
import Language.Zilch.Typecheck.Core.Multiplicity (Multiplicity (..))

type MonadDesugar m = (MonadError DesugarError m, MonadWriter [DesugarWarning] m, MonadState ([Located CST.Parameter], [Located AST.Parameter]) m)

desugarCST :: Located CST.Module -> Either (Diagnostic String) (Located AST.Module, Diagnostic String)
desugarCST mod =
  bimap toErrorDiagnostic (second toWarningDiagnostic) $
    runExcept $
      runWriterT $
        evalStateT (desugarModule mod) ([], [])
  where
    toErrorDiagnostic err = addReport def (fromDesugarerError err)
    toWarningDiagnostic warns = foldl' addReport def (fromDesugarerWarning <$> warns)

-----------------

desugarModule :: forall m. MonadDesugar m => Located CST.Module -> m (Located AST.Module)
desugarModule (CST.Mod _ defs :@ p) = do
  defs' <- catMaybes <$> traverse desugarToplevel defs
  pure $ AST.Mod [] defs' :@ p

desugarToplevel :: forall m. MonadDesugar m => Located CST.TopLevelDefinition -> m (Maybe (Located AST.TopLevel))
desugarToplevel (CST.TopLevel _ True (CST.Assume _ :@ _) :@ p) = throwError $ PublicAssumptions p
desugarToplevel (CST.TopLevel _ isPublic def :@ p) = do
  def' <- desugarDefinition def

  -- we forbid top-level linear definitions
  case def' of
    Just (AST.Let _ (I :@ _) (name :@ _) _ _ :@ pos) -> throwError $ LinearTopLevelBinding name pos
    Nothing -> pure Nothing
    Just def' -> pure . Just $ AST.TopLevel isPublic def' :@ p

desugarDefinition :: forall m. MonadDesugar m => Located CST.Definition -> m (Maybe (Located AST.Definition))
desugarDefinition (CST.Let usage name@(_ :@ p2) params retTy ret@(_ :@ p1) :@ p) = do
  usage' <- desugarMultiplicity usage p2
  (cParams, aParams) <- get
  params' <- (<>) aParams <$> traverse desugarParameter params
  retTy' <- traverse desugarExpression retTy

  let ty = foldr mkPi (fromMaybe (AST.EHole :@ p2) retTy') params'
  val <- desugarExpression (CST.ELam (cParams <> params) ret :@ p1)

  pure . Just $ AST.Let False usage' name ty val :@ p
  where
    mkPi param expr = AST.EPi param expr :@ p
desugarDefinition (CST.Rec usage name@(_ :@ p2) params retTy ret@(_ :@ p1) :@ p) = do
  usage' <- desugarMultiplicity usage p2
  (cParams, aParams) <- get
  params' <- (<>) aParams <$> traverse desugarParameter params
  retTy' <- traverse desugarExpression retTy

  let ty = foldr mkPi (fromMaybe (AST.EHole :@ p2) retTy') params'
  val <- desugarExpression (CST.ELam (cParams <> params) ret :@ p1)

  pure . Just $ AST.Let True usage' name ty val :@ p
  where
    mkPi param expr = AST.EPi param expr :@ p
desugarDefinition (CST.Assume params :@ _) = do
  params' <- forM params \param -> do
    case param of
      CST.Implicit _ (name :@ _) Nothing :@ p -> throwError $ TypelessAssumption name p
      CST.Explicit _ (name :@ _) Nothing :@ p -> throwError $ TypelessAssumption name p
      param -> desugarParameter param
  modify $ bimap (<> params) (<> params')
  pure Nothing

desugarParameter :: forall m. MonadDesugar m => Located CST.Parameter -> m (Located AST.Parameter)
desugarParameter (CST.Implicit usage name@(_ :@ p1) ty :@ p) = do
  ty' <- maybe (pure $ AST.EHole :@ p1) desugarExpression ty
  usage' <- desugarMultiplicity usage p1
  pure $ AST.Parameter True usage' name ty' :@ p
desugarParameter (CST.Explicit usage name@(_ :@ p1) ty :@ p) = do
  ty' <- maybe (pure $ AST.EHole :@ p1) desugarExpression ty
  usage' <- desugarMultiplicity usage p1
  pure $ AST.Parameter False usage' name ty' :@ p

desugarMultiplicity :: forall m. MonadDesugar m => Maybe (Located Integer) -> Position -> m (Located Multiplicity)
desugarMultiplicity Nothing p = pure (Unrestricted :@ p)
desugarMultiplicity (Just (u :@ p)) _ = pure (fromInteger u :@ p)

desugarExpression :: forall m. MonadDesugar m => Located CST.Expression -> m (Located AST.Expression)
desugarExpression (CST.EType :@ p) = pure $ AST.EType :@ p
desugarExpression (CST.EId i :@ p) = pure $ AST.EIdentifier i :@ p
desugarExpression (CST.EHole :@ p) = pure $ AST.EHole :@ p
desugarExpression (CST.EInt i suffix :@ p) = do
  suffix' <- maybe (pure SuffixU64) (desugarIntegerSuffix p) suffix
  pure $ AST.EInteger (i :@ p) suffix' :@ p
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
  def' <- fromJust <$> desugarDefinition def
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

desugarIntegerSuffix :: forall m. MonadDesugar m => Position -> Text -> m IntegerSuffix
desugarIntegerSuffix _ "u8" = pure SuffixU8
desugarIntegerSuffix _ "u16" = pure SuffixU16
desugarIntegerSuffix _ "u32" = pure SuffixU32
desugarIntegerSuffix _ "u64" = pure SuffixU64
desugarIntegerSuffix _ "s8" = pure SuffixS8
desugarIntegerSuffix _ "s16" = pure SuffixS16
desugarIntegerSuffix _ "s32" = pure SuffixS32
desugarIntegerSuffix _ "s64" = pure SuffixS64
desugarIntegerSuffix p suffix = throwError $ InvalidIntegerSuffix suffix p
