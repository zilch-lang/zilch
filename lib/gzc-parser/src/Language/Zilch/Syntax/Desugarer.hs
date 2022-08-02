{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Syntax.Desugarer (desugarCST) where

import Control.Applicative ((<|>))
import Control.Monad (forM, forM_)
import Control.Monad.Except (MonadError, runExcept, throwError)
import Control.Monad.State (MonadState, evalStateT, get, modify)
import Control.Monad.Writer (MonadWriter, runWriterT, tell)
import Data.Bifunctor (bimap, second)
import Data.Foldable (fold, foldrM)
import Data.List (foldl')
import Data.Located (Located ((:@)), Position, getPos, spanOf)
import Data.Maybe (fromJust, fromMaybe)
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
  defs' <- mconcat <$> traverse desugarToplevel defs
  pure $ AST.Mod [] defs' :@ p

desugarToplevel :: forall m. MonadDesugar m => Located CST.TopLevelDefinition -> m [Located AST.TopLevel]
desugarToplevel (CST.TopLevel _ True (CST.Assume _ :@ _) :@ p) = throwError $ PublicAssumptions p
desugarToplevel (CST.TopLevel _ isPublic def :@ p) = do
  def' <- desugarDefinition def

  -- we forbid top-level linear definitions
  case def' of
    Just (AST.Let _ (I :@ _) (name :@ _) _ _ :@ pos) -> throwError $ LinearTopLevelBinding name pos
    Just (AST.Val (I :@ _) (name :@ _) _ :@ pos) -> throwError $ LinearTopLevelBinding name pos
    Nothing -> pure []
    Just (AST.Val _ _ ty :@ p1) | Just (loc, p) <- holes ty -> throwError $ HoleInValType loc p p1
    Just def' -> pure [AST.TopLevel isPublic def' :@ p]
desugarToplevel (CST.Mutual defs :@ _) = do
  defs' <- desugarToplevel' defs
  defs'' <- generateSignatures [] defs'
  pure $ defs'' <> defs'
  where
    generateSignatures :: forall m. MonadDesugar m => [Text] -> [Located AST.TopLevel] -> m [Located AST.TopLevel]
    generateSignatures _ [] = pure []
    generateSignatures withSig ((AST.TopLevel _ (AST.Val _ (name :@ _) _ :@ _) :@ _) : ts) = generateSignatures (name : withSig) ts
    generateSignatures withSig ((AST.TopLevel _ (AST.Let _ usage name@(n :@ _) ty _ :@ p) :@ _) : ts)
      | n `elem` withSig = generateSignatures withSig ts
      | Just (loc, p1) <- holes ty = throwError $ HoleInValType loc p1 p
      | otherwise = ((AST.TopLevel False (AST.Val usage name ty :@ p) :@ p) :) <$> generateSignatures withSig ts

    desugarToplevel' :: forall m. MonadDesugar m => [Located CST.TopLevelDefinition] -> m [Located AST.TopLevel]
    desugarToplevel' [] = pure []
    desugarToplevel' ((CST.TopLevel _ _ (CST.Assume _ :@ p) :@ _) : _) = throwError $ AssumptionsInMutualBlock p
    desugarToplevel' (t : ts) = (<>) <$> desugarToplevel t <*> desugarToplevel' ts

holes :: Located AST.Expression -> Maybe (AST.HoleLocation, Position)
holes (AST.EHole loc :@ p) = Just (loc, p)
holes (AST.EType :@ _) = Nothing
holes (AST.EInteger _ _ :@ _) = Nothing
holes (AST.ECharacter _ :@ _) = Nothing
holes (AST.EIdentifier _ :@ _) = Nothing
holes (AST.EDo e :@ _) = holes e
holes (AST.ELam (AST.Parameter _ _ _ e1 :@ _) e2 :@ _) = holes e1 <|> holes e2
holes (AST.ELet (AST.Let _ _ _ e1 e2 :@ _) e3 :@ _) = holes e1 <|> holes e2 <|> holes e3
holes (AST.ELet (AST.Val {} :@ _) _ :@ _) = error "cannot bind 'val' in 'val'"
holes (AST.EApplication e1 _ e2 :@ _) = holes e1 <|> holes e2
holes (AST.EPi (AST.Parameter _ _ _ e1 :@ _) e2 :@ _) = holes e1 <|> holes e2
holes (AST.EBoolean _ :@ _) = Nothing
holes (AST.EIfThenElse e1 e2 e3 :@ _) = holes e1 <|> holes e2 <|> holes e3
holes (AST.EAdditivePair e1 e2 :@ _) = holes e1 <|> holes e2
holes (AST.EMultiplicativePair e1 e2 :@ _) = holes e1 <|> holes e2
holes (AST.EMultiplicativeProduct (AST.Parameter _ _ _ e1 :@ _) e2 :@ _) = holes e1 <|> holes e2
holes (AST.EAdditiveProduct (AST.Parameter _ _ _ e1 :@ _) e2 :@ _) = holes e1 <|> holes e2

desugarDefinition :: forall m. MonadDesugar m => Located CST.Definition -> m (Maybe (Located AST.Definition))
desugarDefinition (CST.Let usage name@(_ :@ p2) params retTy ret@(_ :@ p1) :@ p) = do
  usage' <- desugarMultiplicity usage p2
  (cParams, aParams) <- get
  params' <- (<>) aParams . fold <$> traverse desugarParameter params
  retTy' <- traverse desugarExpression retTy

  let ty = foldr mkPi (fromMaybe (AST.EHole AST.InsertedHole :@ spanOf p2 (maybe p2 getPos retTy)) retTy') params'
  val <- desugarExpression (CST.ELam (cParams <> params) ret :@ p1)

  pure . Just $ AST.Let False usage' name ty val :@ p
  where
    mkPi param expr = AST.EPi param expr :@ spanOf (getPos param) (getPos expr)
desugarDefinition (CST.Rec usage name@(_ :@ p2) params retTy ret@(_ :@ p1) :@ p) = do
  usage' <- desugarMultiplicity usage p2
  (cParams, aParams) <- get
  params' <- (<>) aParams . fold <$> traverse desugarParameter params
  retTy' <- traverse desugarExpression retTy

  let ty = foldr mkPi (fromMaybe (AST.EHole AST.InsertedHole :@ spanOf p2 (maybe p2 getPos retTy)) retTy') params'
  val <- desugarExpression (CST.ELam (cParams <> params) ret :@ p1)

  pure . Just $ AST.Let True usage' name ty val :@ p
  where
    mkPi param expr = AST.EPi param expr :@ spanOf (getPos param) (getPos expr)
desugarDefinition (CST.Assume params :@ _) = do
  params' <-
    fold <$> forM params \param -> do
      param' <- desugarParameter param
      forM_ param' \case
        AST.Parameter _ _ (name :@ _) ty :@ p | Just _ <- holes ty -> throwError $ TypelessAssumption name p
        _ -> pure ()
      pure param'
  modify $ bimap (<> params) (<> params')
  pure Nothing
desugarDefinition (CST.Val usage name@(_ :@ p2) ty :@ p) = do
  usage' <- desugarMultiplicity usage p2
  (_, aParams) <- get
  ty' <- desugarExpression ty
  let ty'' = foldr mkPi ty' aParams
  pure . Just $ AST.Val usage' name ty'' :@ p
  where
    mkPi param expr = AST.EPi param expr :@ spanOf (getPos param) (getPos expr)

desugarParameter :: forall m. MonadDesugar m => Located CST.Parameter -> m [Located AST.Parameter]
desugarParameter (CST.Implicit args :@ p) = do
  args' <- flip traverse args \(usage, name@(_ :@ p1), ty) -> do
    ty' <- maybe (pure $ AST.EHole AST.InsertedHole :@ p1) desugarExpression ty
    usage' <- desugarMultiplicity usage p1
    pure $ AST.Parameter True usage' name ty' :@ p
  pure args'
desugarParameter (CST.Explicit args :@ p) = do
  args' <- flip traverse args \(usage, name@(_ :@ p1), ty) -> do
    ty' <- maybe (pure $ AST.EHole AST.InsertedHole :@ p1) desugarExpression ty
    usage' <- desugarMultiplicity usage p1
    pure $ AST.Parameter False usage' name ty' :@ p
  pure args'

desugarMultiplicity :: forall m. MonadDesugar m => Maybe (Located Integer) -> Position -> m (Located Multiplicity)
desugarMultiplicity Nothing p = pure (Unrestricted :@ p)
desugarMultiplicity (Just (u :@ p)) _ = pure (fromInteger u :@ p)

desugarExpression :: forall m. MonadDesugar m => Located CST.Expression -> m (Located AST.Expression)
desugarExpression (CST.EType :@ p) = pure $ AST.EType :@ p
desugarExpression (CST.EId i :@ p) = pure $ AST.EIdentifier i :@ p
desugarExpression (CST.EHole :@ p) = pure $ AST.EHole AST.SourceHole :@ p
desugarExpression (CST.EInt i suffix :@ p) = do
  suffix' <- maybe (pure SuffixU64) (desugarIntegerSuffix p) suffix
  pure $ AST.EInteger (i :@ p) suffix' :@ p
desugarExpression (CST.EChar c :@ p) = pure $ AST.ECharacter (c :@ p) :@ p
desugarExpression (CST.ELam params expr :@ _) = do
  params' <- fold <$> traverse desugarParameter params
  expr' <- desugarExpression expr

  pure $ foldr mkLam expr' params'
  where
    mkLam param expr = AST.ELam param expr :@ spanOf (getPos param) (getPos expr)
desugarExpression (CST.EDo expr :@ p) = do
  expr' <- desugarExpression expr
  pure $ AST.EDo expr' :@ p
desugarExpression (CST.ELet def ret :@ p) = do
  def' <- fromJust <$> desugarDefinition def
  ret' <- desugarExpression ret
  pure $ AST.ELet def' ret' :@ p
desugarExpression (CST.EParens e :@ _) = desugarExpression e
desugarExpression (CST.EApplication e es :@ _) = do
  e' <- desugarExpression e
  args <- go es
  pure $ foldl' mkApp e' args
  where
    mkApp e1 (isImp, e2) = AST.EApplication e1 isImp e2 :@ spanOf (getPos e1) (getPos e2)

    go [] = pure []
    go (((isImp, es) :@ _) : es') = do
      es1 <- traverse (fmap (isImp,) . desugarExpression) es
      es2 <- go es'
      pure $ es1 <> es2
desugarExpression (CST.EPi params ret :@ _) = do
  param' <- desugarParameter params
  ret' <- desugarExpression ret
  pure $ foldr mkPi ret' param'
  where
    mkPi param expr = AST.EPi param expr :@ spanOf (getPos param) (getPos expr)
desugarExpression (CST.ETrue :@ p) = pure $ AST.EBoolean True :@ p
desugarExpression (CST.EFalse :@ p) = pure $ AST.EBoolean False :@ p
desugarExpression (CST.EIfThenElse c t e :@ p) = do
  c' <- desugarExpression c
  t' <- desugarExpression t
  e' <- desugarExpression e
  pure $ AST.EIfThenElse c' t' e' :@ p
desugarExpression (CST.EMultiplicativeProduct params ty :@ _) = do
  params' <- desugarParameter params
  ty' <- desugarExpression ty
  foldrM mkProd ty' params'
  where
    mkProd (AST.Parameter True _ _ _ :@ p) _ = throwError $ ImplicitProductType p
    mkProd param ret = pure $ AST.EMultiplicativeProduct param ret :@ spanOf (getPos param) (getPos ret)
desugarExpression (CST.EAdditiveProduct params ty :@ _) = do
  params' <- desugarParameter params
  ty' <- desugarExpression ty
  foldrM mkProd ty' params'
  where
    mkProd (AST.Parameter True _ _ _ :@ p) _ = throwError $ ImplicitProductType p
    mkProd (AST.Parameter _ (mult :@ _) (x :@ _) _ :@ p) _
      | mult /= Unrestricted = throwError $ AdditiveProductWithMultiplicity x p
    mkProd param ret = pure $ AST.EAdditiveProduct param ret :@ spanOf (getPos param) (getPos ret)
desugarExpression (CST.EMultiplicativeTuple es :@ _) = do
  es' <- traverse desugarExpression es
  pure $ foldr1 mkPair es'
  where
    mkPair e1 e2 = AST.EMultiplicativePair e1 e2 :@ spanOf (getPos e1) (getPos e2)
desugarExpression (CST.EAdditiveTuple [e] :@ p) = do
  tell [SingletonAdditivePair p]
  desugarExpression e
desugarExpression (CST.EAdditiveTuple es :@ _) = do
  es' <- traverse desugarExpression es
  pure $ foldr1 mkPair es'
  where
    mkPair e1 e2 = AST.EAdditivePair e1 e2 :@ spanOf (getPos e1) (getPos e2)
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
