{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Typecheck.Internal.IR2ANF where

import Control.Monad.Cont (ContT, MonadCont, mapContT, runContT)
import Control.Monad.State (MonadState, evalState, get, put)
import Data.Located (Located ((:@)), Position, getPos)
import Data.Maybe (catMaybes)
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Traversable (for)
import Debug.Trace (traceShow)
import qualified Language.Zilch.Typecheck.ANF as ANF
import Language.Zilch.Typecheck.IR (Multiplicity (..))
import qualified Language.Zilch.Typecheck.IR as IR

type MonadNormalizer m = MonadState Integer m

normalizeModule :: Located IR.Module -> Located ANF.Module
normalizeModule mod = evalState (normalizeModule' mod) 1

normalizeModule' :: MonadNormalizer m => Located IR.Module -> m (Located ANF.Module)
normalizeModule' (IR.Module binds :@ p) = do
  binds <- catMaybes <$> traverse normalizeTopLevel binds
  pure $ ANF.Module binds :@ p

normalizeTopLevel :: MonadNormalizer m => Located IR.TopLevel -> m (Maybe (Located ANF.TopLevel))
normalizeTopLevel (IR.TopLevel attrs _ def :@ p) =
  normalizeDefinition def >>= \case
    Nothing -> pure Nothing
    Just def -> pure $ Just $ ANF.TopLevel attrs def :@ p

normalizeDefinition :: MonadNormalizer m => Located IR.Definition -> m (Maybe (Located ANF.Definition))
normalizeDefinition (IR.Val _ _ _ :@ _) = pure Nothing
normalizeDefinition (IR.Let isRec mult name ty val :@ p) = do
  ty <- rawExpr ty
  val <- normalizeTerm val
  pure $ Just $ ANF.Let isRec mult name ty val :@ p

normalizeTerm :: MonadNormalizer m => Located IR.Expression -> m (Located ANF.Expression)
normalizeTerm t = runContT (normalizeExpression t) pure

normalizeExpression :: MonadNormalizer m => Located IR.Expression -> ContT (Located ANF.Expression) m (Located ANF.Expression)
normalizeExpression (IR.EType :@ p) = pure (ANF.EType :@ p)
normalizeExpression (IR.ELam param _ val :@ p) = do
  param <- normalizeParameter param
  val <- normalizeTerm val
  pure (ANF.ELam [param] val :@ p)
normalizeExpression (IR.EPi param _ ty :@ p) = do
  param <- normalizeParameter param
  ty <- normalizeTerm ty
  pure (ANF.EPi [param] ty :@ p)
normalizeExpression (IR.EAdditiveProduct param _ ty :@ p) = do
  param <- normalizeParameter param
  ty <- normalizeTerm ty
  pure (ANF.EAdditiveProduct [param] ty :@ p)
normalizeExpression (IR.EMultiplicativeProduct param _ ty :@ p) = do
  param <- normalizeParameter param
  ty <- normalizeTerm ty
  pure (ANF.EMultiplicativeProduct [param] ty :@ p)
normalizeExpression (IR.ELet def val :@ p) = do
  normalizeDefinition def >>= \case
    Nothing -> normalizeTerm val
    Just def -> do
      val <- normalizeTerm val
      pure $ ANF.ELet def val :@ p
normalizeExpression (IR.EApplication tf f tx x :@ p) = do
  f <- normalizeName f tf
  x <- normalizeName x tx
  pure (ANF.EApplication f [x] :@ p)
normalizeExpression (IR.EIdentifier i :@ p) = pure (ANF.EIdentifier i :@ p)
normalizeExpression (IR.EInteger i ty :@ p) = pure (ANF.EInteger i ty :@ p)
normalizeExpression (IR.ECharacter c :@ p) = pure (ANF.ECharacter c :@ p)
normalizeExpression (IR.EBuiltin bt :@ p) = pure (ANF.EBuiltin bt :@ p)
normalizeExpression (IR.EBoolean b :@ p) = pure (ANF.EBoolean b :@ p)
normalizeExpression (IR.EIfThenElse c t _ e _ :@ p) = do
  c <- normalizeName c (IR.EBuiltin IR.TyBool :@ getPos c)
  t <- normalizeTerm t
  e <- normalizeTerm e
  pure (ANF.EIfThenElse c t e :@ p)
normalizeExpression (IR.EAdditivePair x tx y ty :@ p) = do
  x <- normalizeName x tx
  y <- normalizeName y ty
  pure (ANF.EAdditivePair [x, y] :@ p)
normalizeExpression (IR.EMultiplicativePair x tx y ty :@ p) = do
  x <- normalizeName x tx
  y <- normalizeName y ty
  pure (ANF.EMultiplicativePair [x, y] :@ p)
normalizeExpression (IR.EMultiplicativeUnit :@ p) = pure (ANF.EMultiplicativePair [] :@ p)
normalizeExpression (IR.EAdditiveUnit :@ p) = pure (ANF.EAdditivePair [] :@ p)
normalizeExpression (IR.EOne :@ p) = pure (ANF.EOne :@ p)
normalizeExpression (IR.ETop :@ p) = pure (ANF.ETop :@ p)
normalizeExpression (IR.EFst ty x :@ p) = do
  x <- normalizeName x ty
  pure (ANF.EFst x :@ p)
normalizeExpression (IR.ESnd ty x :@ p) = do
  x <- normalizeName x ty
  pure (ANF.ESnd x :@ p)
normalizeExpression (IR.EMultiplicativePairElim z mult x tx y ty e f :@ p) = do
  e <- normalizeName e (IR.EMultiplicativeProduct (IR.Parameter mult ("_" :@ getPos tx) tx :@ getPos e) (IR.EType :@ getPos ty) ty :@ getPos e)
  f <- normalizeTerm f
  pure (ANF.EMultiplicativePairElim z mult [x, y] e f :@ p)
normalizeExpression (IR.EMultiplicativeUnitElim z mult e f :@ p) = do
  e <- normalizeName e (IR.EMultiplicativeUnit :@ getPos e)
  f <- normalizeTerm f
  pure (ANF.EMultiplicativePairElim z mult [] e f :@ p)
normalizeExpression (IR.EComposite fields :@ p) = do
  fields <- for fields \(mult, name, ty) -> do
    ty <- rawExpr ty
    pure (mult, name, ty)
  pure (ANF.EComposite fields :@ p)
normalizeExpression (IR.ERecordLiteral fields :@ p) = do
  fields <- for fields \(mult, name, ty, val) -> do
    val <- normalizeName val ty
    ty <- rawExpr ty
    pure (mult, name, ty, val)
  pure (ANF.ERecordLiteral fields :@ p)
normalizeExpression (IR.ERecordAccess r ty x :@ p) = do
  r <- normalizeName r ty
  pure (ANF.ERecordAccess r x :@ p)
normalizeExpression _ = undefined

normalizeParameter :: MonadNormalizer m => Located IR.Parameter -> ContT (Located ANF.Expression) m (Located ANF.Parameter)
normalizeParameter (IR.Parameter mult name ty :@ p) = do
  ty <- rawExpr ty
  pure $ ANF.Parameter mult name ty :@ p

normalizeName :: MonadNormalizer m => Located IR.Expression -> Located IR.Expression -> ContT (Located ANF.Expression) m (Located ANF.Expression)
normalizeName expr ty = do
  let f expr = do
        let pos = getPos expr

        name <- gensym pos
        let ident = ANF.EIdentifier [name] :@ pos

        flip mapContT (pure ident) \e -> do
          e <- e
          ty <- rawExpr ty
          pure $ ANF.ELet (ANF.Let False (I :@ pos) name ty expr :@ pos) e :@ pos

  expr <- normalizeExpression expr
  case expr of
    ANF.EFst _ :@ _ -> f expr
    ANF.ESnd _ :@ _ -> f expr
    ANF.EIfThenElse _ _ _ :@ _ -> f expr
    ANF.EApplication _ _ :@ _ -> f expr
    ANF.ELam _ _ :@ _ -> f expr
    ANF.EPi _ _ :@ _ -> f expr
    ANF.EAdditiveProduct _ _ :@ _ -> f expr
    ANF.EMultiplicativeProduct _ _ :@ _ -> f expr
    ANF.ELet _ _ :@ _ -> f expr
    ANF.EMultiplicativePairElim _ _ _ _ _ :@ _ -> f expr
    ANF.EComposite _ :@ _ -> f expr
    ANF.ERecordLiteral _ :@ _ -> f expr
    ANF.ERecordAccess _ _ :@ _ -> f expr
    ANF.EAdditivePair _ :@ _ -> f expr
    ANF.EMultiplicativePair _ :@ _ -> f expr
    ---------------------------
    _ -> pure expr

--------------------------------

rawDefinition :: MonadNormalizer m => Located IR.Definition -> m (Located ANF.Definition)
rawDefinition (IR.Let isRec mult name ty val :@ p) = do
  ty <- rawExpr ty
  val <- rawExpr val
  pure $ ANF.Let isRec mult name ty val :@ p
rawDefinition (IR.Val _ _ _ :@ _) = undefined

rawExpr :: MonadNormalizer m => Located IR.Expression -> m (Located ANF.Expression)
rawExpr (IR.EType :@ p) = pure (ANF.EType :@ p)
rawExpr (IR.ELam (IR.Parameter mult name ty :@ p1) _ ex :@ p) = do
  ty <- rawExpr ty
  ex <- rawExpr ex
  pure $ ANF.ELam [ANF.Parameter mult name ty :@ p1] ex :@ p
rawExpr (IR.EPi (IR.Parameter mult name ty :@ p1) _ ty2 :@ p) = do
  ty <- rawExpr ty
  ty2 <- rawExpr ty2
  pure $ ANF.EPi [ANF.Parameter mult name ty :@ p1] ty2 :@ p
rawExpr (IR.EAdditiveProduct (IR.Parameter mult name ty :@ p1) _ ty2 :@ p) = do
  ty <- rawExpr ty
  ty2 <- rawExpr ty2
  pure $ ANF.EAdditiveProduct [ANF.Parameter mult name ty :@ p1] ty2 :@ p
rawExpr (IR.EMultiplicativeProduct (IR.Parameter mult name ty :@ p1) _ ty2 :@ p) = do
  ty <- rawExpr ty
  ty2 <- rawExpr ty2
  pure $ ANF.EPi [ANF.Parameter mult name ty :@ p1] ty2 :@ p
rawExpr (IR.ELet def ex :@ p) = do
  def <- rawDefinition def
  ex <- rawExpr ex
  pure $ ANF.ELet def ex :@ p
rawExpr (IR.EApplication _ f _ x :@ p) = do
  f <- rawExpr f
  x <- rawExpr x
  pure $ ANF.EApplication f [x] :@ p
rawExpr (IR.EIdentifier i :@ p) = pure (ANF.EIdentifier i :@ p)
rawExpr (IR.EInteger i ty :@ p) = pure (ANF.EInteger i ty :@ p)
rawExpr (IR.ECharacter c :@ p) = pure (ANF.ECharacter c :@ p)
rawExpr (IR.EBuiltin bt :@ p) = pure (ANF.EBuiltin bt :@ p)
rawExpr (IR.EBoolean b :@ p) = pure (ANF.EBoolean b :@ p)
rawExpr (IR.EIfThenElse c t _ e _ :@ p) = do
  c <- rawExpr c
  t <- rawExpr t
  e <- rawExpr e
  pure $ ANF.EIfThenElse c t e :@ p
rawExpr (IR.EAdditivePair x _ y _ :@ p) = do
  x <- rawExpr x
  y <- rawExpr y
  pure $ ANF.EAdditivePair [x, y] :@ p
rawExpr (IR.EMultiplicativePair x _ y _ :@ p) = do
  x <- rawExpr x
  y <- rawExpr y
  pure $ ANF.EMultiplicativePair [x, y] :@ p
rawExpr (IR.EMultiplicativeUnit :@ p) = pure (ANF.EMultiplicativePair [] :@ p)
rawExpr (IR.EAdditiveUnit :@ p) = pure (ANF.EAdditivePair [] :@ p)
rawExpr (IR.EOne :@ p) = pure (ANF.EOne :@ p)
rawExpr (IR.ETop :@ p) = pure (ANF.ETop :@ p)
rawExpr (IR.EFst _ x :@ p) = do
  x <- rawExpr x
  pure (ANF.EFst x :@ p)
rawExpr (IR.ESnd _ x :@ p) = do
  x <- rawExpr x
  pure (ANF.ESnd x :@ p)
rawExpr (IR.EMultiplicativePairElim z mult x _ y _ e f :@ p) = do
  e <- rawExpr e
  f <- rawExpr f
  pure $ ANF.EMultiplicativePairElim z mult [x, y] e f :@ p
rawExpr (IR.EMultiplicativeUnitElim z mult e f :@ p) = do
  e <- rawExpr e
  f <- rawExpr f
  pure $ ANF.EMultiplicativePairElim z mult [] e f :@ p
rawExpr (IR.EComposite fields :@ p) = do
  fields <- for fields \(mult, x, ty) -> do
    ty <- rawExpr ty
    pure (mult, x, ty)
  pure $ ANF.EComposite fields :@ p
rawExpr (IR.ERecordLiteral fields :@ p) = do
  fields <- for fields \(mult, x, ty, val) -> do
    ty <- rawExpr ty
    val <- rawExpr val
    pure (mult, x, ty, val)
  pure $ ANF.ERecordLiteral fields :@ p
rawExpr (IR.ERecordAccess r _ x :@ p) = do
  r <- rawExpr r
  pure $ ANF.ERecordAccess r x :@ p
rawExpr _ = undefined

gensym :: MonadNormalizer m => Position -> m (Located Text)
gensym p = do
  n <- get
  put (n + 1)
  pure $ ("$" <> Text.pack (show n)) :@ p
