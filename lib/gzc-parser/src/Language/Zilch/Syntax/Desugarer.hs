{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NoOverloadedLists #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

module Language.Zilch.Syntax.Desugarer (desugarCST) where

import Control.Applicative ((<|>))
import Control.Monad (forM, forM_, when)
import Control.Monad.Except (MonadError, runExcept, runExceptT, throwError)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.State (MonadState, get, modify, runStateT)
import Control.Monad.Writer (MonadWriter, runWriterT, tell)
import Data.Bifunctor (first, second)
import Data.Foldable (fold, foldlM, foldrM)
import Data.Functor ((<&>))
import Data.List (foldl', nub)
import Data.Located (Located ((:@)), Position, getPos, spanOf)
import qualified Data.Map as Map
import Data.Maybe (catMaybes, fromMaybe)
import Data.Text (Text)
import qualified Data.Text as Text
import Debug.Trace (trace, traceShow)
import Error.Diagnose (Diagnostic, addReport, def)
import GHC.Stack (HasCallStack)
import Language.Zilch.CLI.Flags (WarningFlags)
import qualified Language.Zilch.CLI.Flags as W (WarningFlags (..))
import Language.Zilch.Syntax.Core.AST (IntegerSuffix (..))
import qualified Language.Zilch.Syntax.Core.AST as AST
import qualified Language.Zilch.Syntax.Core.CST as CST
import Language.Zilch.Syntax.Errors
import Language.Zilch.Typecheck.Core.Multiplicity (Multiplicity (..))

type MonadDesugar m = (?warnings :: WarningFlags, ?includeDirs :: [FilePath], MonadError DesugarError m, MonadWriter [DesugarWarning] m, MonadState ([Located CST.Parameter], [Located AST.Parameter], [[Located Text]]) m, HasCallStack)

desugarCST :: (?warnings :: WarningFlags, ?includeDirs :: [FilePath]) => Located CST.Module -> Either (Diagnostic String) (Located AST.Module, [[Located Text]], Diagnostic String)
desugarCST mod = adapt $ runExcept $ runWriterT $ runStateT (desugarModule mod) ([], [], [])
  where
    toErrorDiagnostic err = addReport def (fromDesugarerError err)
    toWarningDiagnostic warns = foldl' addReport def (fromDesugarerWarning <$> warns)

    adapt (Left e) = Left $ toErrorDiagnostic e
    adapt (Right ((mod, (_, _, graph)), warns)) = Right (mod, graph, toWarningDiagnostic warns)

-----------------

desugarModule :: forall m. MonadDesugar m => Located CST.Module -> m (Located AST.Module)
desugarModule (CST.Mod defs :@ p) = do
  defs' <- mconcat <$> traverse desugarToplevel defs
  pure $ AST.Mod defs' :@ p

checkConsistencyOfMetaAttributes :: forall m. MonadDesugar m => [Located CST.MetaAttribute] -> Position -> m ()
checkConsistencyOfMetaAttributes l p = do
  let (inlines, imports) = groupMetaAttrs l
  when (length inlines > 1) do
    -- when (... ?warnings) do
    --   tell [RedundantMetaAttribute $ getPos <$> inlines]
    pure ()
  when (length imports > 1) do
    -- when there are multiple of the same calling convention, error out
    let (c, other) = groupByConv imports
    when (null c) do
      throwError $ NoSupportedImportCallingConventions p (getPos . getCallConv <$> imports)

    case nub c of
      [] -> undefined
      [_] ->
        -- when (length c > 1) do
        --   tell [RedundantMetaAttribute $ getPos <$> c]
        pure ()
      cs -> throwError $ ClashingForeignImports p cs

    pure ()

  pure ()
  where
    groupMetaAttrs [] = ([], [])
    groupMetaAttrs (attr@(CST.Inline {} :@ _) : ls) = first (attr :) (groupMetaAttrs ls)
    groupMetaAttrs (attr@(CST.Foreign {} :@ _) : ls) = second (attr :) (groupMetaAttrs ls)

    groupByConv [] = ([], [])
    groupByConv ((CST.Foreign (CST.CCall :@ _) name :@ _) : ls) = first (name :) (groupByConv ls)
    groupByConv ((CST.Foreign (CST.UnknownCall _ :@ _) name :@ _) : ls) = second (name :) (groupByConv ls)
    groupByConv _ = undefined

    getCallConv (CST.Foreign conv _ :@ _) = conv
    getCallConv _ = undefined

desugarToplevel :: forall m. MonadDesugar m => Located CST.TopLevelDefinition -> m [Located AST.TopLevel]
desugarToplevel (CST.TopLevel _ True (CST.Assume _ :@ _) :@ p) = throwError $ PublicAssumptions p
desugarToplevel (CST.TopLevel metas _ (CST.Assume _ :@ _) :@ p)
  | not (null metas) = throwError $ AssumptionWithMetaAttributes p
desugarToplevel (CST.TopLevel metas isPublic def :@ p) = do
  checkConsistencyOfMetaAttributes metas (getPos def)

  metas' <- catMaybes <$> traverse desugarMetaAttribute metas
  def' <- desugarDefinition True def

  case def' of
    [] -> pure []
    defs -> forM defs \case
      -- we forbid top-level linear definitions
      (AST.Let _ (I :@ _) (name :@ _) _ _ :@ pos, _) -> throwError $ LinearTopLevelBinding name pos
      (AST.Val (I :@ _) (name :@ _) _ :@ pos, _) -> throwError $ LinearTopLevelBinding name pos
      (AST.Val _ _ ty :@ p1, _) | Just (loc, p) <- holes ty -> throwError $ HoleInValType loc p p1
      -- check that @inline@ does not appear on a @val@
      (AST.Val {} :@ p1, _) | Just p <- hasInline metas' -> throwError $ InlineAttributeOnVal p1 p
      -- check that @import@ only happens on @val@
      (AST.Let {} :@ p1, _) | Just p <- hasImport metas' -> throwError $ ImportAttributeOnlyAllowedOnVal p1 p
      (AST.Import {} :@ p1, _) | Just p <- hasImport metas' -> throwError $ ImportAttributeOnlyAllowedOnVal p1 p
      (def, _) -> pure $ AST.TopLevel isPublic metas' def :@ p
  where
    hasInline [] = Nothing
    hasInline ((AST.Inline {} :@ p) : _) = Just p
    hasInline (_ : ms) = hasInline ms

    hasImport [] = Nothing
    hasImport ((AST.Foreign {} :@ p) : _) = Just p
    hasImport (_ : ms) = hasImport ms
desugarToplevel (CST.Mutual defs :@ _) = do
  defs' <- desugarToplevel' defs
  defs'' <- generateSignatures [] defs'
  pure $ defs'' <> defs'
  where
    generateSignatures :: forall m. MonadDesugar m => [Text] -> [Located AST.TopLevel] -> m [Located AST.TopLevel]
    generateSignatures _ [] = pure []
    generateSignatures withSig ((AST.TopLevel _ _ (AST.Val _ (name :@ _) _ :@ _) :@ _) : ts) = generateSignatures (name : withSig) ts
    generateSignatures withSig ((AST.TopLevel _ metas (AST.Let _ usage name@(n :@ _) ty _ :@ p) :@ _) : ts)
      | n `elem` withSig = generateSignatures withSig ts
      | Just (loc, p1) <- holes ty = throwError $ HoleInValType loc p1 p
      | otherwise = ((AST.TopLevel False metas (AST.Val usage name ty :@ p) :@ p) :) <$> generateSignatures withSig ts
    generateSignatures withSig ((AST.TopLevel _ _ (AST.Import {} :@ _) :@ _) : ts) = generateSignatures withSig ts

    desugarToplevel' :: forall m. MonadDesugar m => [Located CST.TopLevelDefinition] -> m [Located AST.TopLevel]
    desugarToplevel' [] = pure []
    desugarToplevel' ((CST.TopLevel _ _ (CST.Assume _ :@ p) :@ _) : _) = throwError $ AssumptionsInMutualBlock p
    desugarToplevel' (t : ts) = (<>) <$> desugarToplevel t <*> desugarToplevel' ts

desugarMetaAttribute :: forall m. MonadDesugar m => Located CST.MetaAttribute -> m (Maybe (Located AST.MetaAttribute))
desugarMetaAttribute (CST.Inline :@ p) = pure . Just $ AST.Inline :@ p
desugarMetaAttribute (CST.Foreign conv name :@ p) = do
  pure $ desugarCallingConvention conv <&> \c -> AST.Foreign c name :@ p
  where
    desugarCallingConvention (CST.CCall :@ p) = Just $ AST.CCall :@ p
    desugarCallingConvention (CST.UnknownCall _ :@ _) = Nothing

holes :: Located AST.Expression -> Maybe (AST.HoleLocation, Position)
holes (AST.EHole loc :@ p) = Just (loc, p)
holes (AST.EType :@ _) = Nothing
holes (AST.EInteger _ _ :@ _) = Nothing
holes (AST.ECharacter _ :@ _) = Nothing
holes (AST.EIdentifier _ :@ _) = Nothing
holes (AST.ELam (AST.Parameter _ _ _ e1 :@ _) e2 :@ _) = holes e1 <|> holes e2
holes (AST.ELocal (AST.Let _ _ _ e1 e2 :@ _) e3 :@ _) = holes e1 <|> holes e2 <|> holes e3
holes (AST.ELocal (AST.Val {} :@ _) _ :@ _) = error "cannot bind 'val' in 'val'"
holes (AST.ELocal (AST.Import {} :@ _) e2 :@ _) = holes e2
holes (AST.EApplication e1 _ e2 :@ _) = holes e1 <|> holes e2
holes (AST.EPi (AST.Parameter _ _ _ e1 :@ _) e2 :@ _) = holes e1 <|> holes e2
holes (AST.EBoolean _ :@ _) = Nothing
holes (AST.EIfThenElse e1 e2 e3 :@ _) = holes e1 <|> holes e2 <|> holes e3
holes (AST.EAdditivePair e1 e2 :@ _) = holes e1 <|> holes e2
holes (AST.EMultiplicativePair e1 e2 :@ _) = holes e1 <|> holes e2
holes (AST.EMultiplicativeProduct (AST.Parameter _ _ _ e1 :@ _) e2 :@ _) = holes e1 <|> holes e2
holes (AST.EAdditiveProduct (AST.Parameter _ _ _ e1 :@ _) e2 :@ _) = holes e1 <|> holes e2
holes (AST.EAdditiveUnit :@ _) = Nothing
holes (AST.EMultiplicativeUnit :@ _) = Nothing
holes (AST.EOne :@ _) = Nothing
holes (AST.ETop :@ _) = Nothing
holes (AST.EFst e :@ _) = holes e
holes (AST.ESnd e :@ _) = holes e
holes (AST.EAdditiveTupleAccess e _ :@ _) = holes e
holes (AST.EMultiplicativePairElim _ _ _ _ m n :@ _) = holes m <|> holes n
holes (AST.EMultiplicativeUnitElim _ _ m n :@ _) = holes m <|> holes n
holes (AST.EFieldAccess e _ :@ _) = holes e
holes (AST.ERecordLiteral fields :@ _) = head <$> traverse (\(_, _, e) -> holes e) fields

desugarDefinition :: forall m. MonadDesugar m => Bool -> Located CST.Definition -> m [(Located AST.Definition, [Located Text])]
desugarDefinition isTopLevel (CST.Let usage name@(_ :@ p2) params retTy ret@(_ :@ p1) :@ p) = do
  usage' <- desugarMultiplicity usage (if isTopLevel then Unrestricted else Linear) p2
  (cParams, aParams, _) <- get
  params' <- (if isTopLevel then (<>) aParams else id) . fold <$> traverse desugarParameter params
  retTy' <- traverse desugarExpression retTy

  let ty = foldr mkPi (fromMaybe (AST.EHole AST.InsertedHole :@ spanOf p2 (maybe p2 getPos retTy)) retTy') params'
  let par = cParams <> params
  (val, binds) <-
    if
        | null par && not isTopLevel -> desugarExpression' ret
        | null par -> (,[]) <$> desugarExpression ret
        | otherwise -> (,[]) <$> desugarExpression (CST.ELam par ret :@ p1)

  pure [(AST.Let False usage' name ty val :@ p, binds)]
  where
    mkPi param expr = AST.EPi param expr :@ spanOf (getPos param) (getPos expr)
desugarDefinition isTopLevel (CST.Rec usage name@(_ :@ p2) params retTy ret@(_ :@ p1) :@ p) = do
  usage' <- desugarMultiplicity usage Unrestricted p2
  (cParams, aParams, _) <- get
  params' <- (if isTopLevel then (<>) aParams else id) . fold <$> traverse desugarParameter params
  retTy' <- traverse desugarExpression retTy

  let ty = foldr mkPi (fromMaybe (AST.EHole AST.InsertedHole :@ spanOf p2 (maybe p2 getPos retTy)) retTy') params'
  let par = cParams <> params
  val <- if null par then desugarExpression ret else desugarExpression (CST.ELam par ret :@ p1)

  pure [(AST.Let True usage' name ty val :@ p, [])]
  where
    mkPi param expr = AST.EPi param expr :@ spanOf (getPos param) (getPos expr)
desugarDefinition _ (CST.Assume params :@ _) = do
  params' <-
    fold <$> forM params \param -> do
      param' <- desugarParameter param
      forM_ param' \case
        AST.Parameter _ _ (name :@ _) ty :@ p | Just _ <- holes ty -> throwError $ TypelessAssumption name p
        _ -> pure ()
      pure param'
  modify $ trimap (<> params) (<> params') id
  pure []
desugarDefinition _ (CST.Val usage name@(_ :@ p2) ty :@ p) = do
  usage' <- desugarMultiplicity usage Unrestricted p2
  (_, aParams, _) <- get
  ty' <- desugarExpression ty
  let ty'' = foldr mkPi ty' aParams
  pure [(AST.Val usage' name ty'' :@ p, [])]
  where
    mkPi param expr = AST.EPi param expr :@ spanOf (getPos param) (getPos expr)
desugarDefinition _ (CST.Import opened spine :@ p) = do
  let spines = flattenBranches spine
  modify $ third3 (<> spines)
  pure $ (,[]) . (:@ p) . (\m -> AST.Import opened m [] "") <$> spines
  where
    flattenBranches :: Located CST.ImportSpine -> [[Located Text]]
    flattenBranches (CST.Empty :@ _) = []
    flattenBranches (CST.Base mod p :@ _) = case flattenBranches p of
      [] -> [[mod]]
      mods -> ([mod] <>) <$> mods
    flattenBranches (CST.Branch mods :@ _) = mods >>= flattenBranches
desugarDefinition _ (CST.Record name params ty ctor fields :@ p1) = do
  (cParams, aParams, _) <- get
  params' <- (aParams <>) . fold <$> traverse desugarParameter params
  fields' <- fold <$> traverse desugarToplevel fields
  let fields'' = flip map fields' \case
        AST.TopLevel _ _ (AST.Val mult name ty :@ _) :@ _ -> (mult, name, ty)
        _ -> undefined

  -- TODO: check that no field is duplicated

  ty <- desugarExpression ty
  case ty of
    AST.EType :@ _ -> pure ()
    _ :@ p -> throwError $ NotASort p

  ctor' <-
    maybe [] pure <$> flip traverse ctor \(isPublic, name2@(_ :@ p)) -> do
      -- TODO: pass multiplicity within constructor with 'constructor ρ name' instead of just 'constructor name'
      mult <- desugarMultiplicity Nothing W p

      let params = fmap toImplicit params' <> fmap mkParam fields''

      let ty' = foldl' mkApp (AST.EIdentifier name :@ getPos name) params'
      let ty'' = foldr mkPi ty' params

      let reclit = AST.ERecordLiteral (toValue <$> fields'') :@ p
      let val = foldr mkLam reclit params
      pure (AST.Let False mult name2 ty'' val :@ p, [])
  -- undefined

  let ty' = foldr mkPi ty params'
      complit = AST.EComposite fields'' :@ p1
      val' = foldr mkLam complit params'

  -- TODO: generate eliminator
  pure $ (AST.Let False (O :@ getPos name) name ty' val' :@ p1, []) : ctor'
  where
    mkApp ty@(_ :@ p1) (AST.Parameter isImp _ name _ :@ p2) = AST.EApplication ty isImp (AST.EIdentifier name :@ p2) :@ spanOf p1 p2

    toImplicit (AST.Parameter _ mult name ty :@ p) = AST.Parameter True mult name ty :@ p

    mkParam (mult, name@(_ :@ p), ty@(_ :@ p2)) = AST.Parameter False mult name ty :@ spanOf p p2

    mkPi param expr = AST.EPi param expr :@ spanOf (getPos param) (getPos expr)
    mkLam param expr = AST.ELam param expr :@ spanOf (getPos param) (getPos expr)

    toValue (mult, name@(_ :@ p), _) = (mult, name, AST.EIdentifier name :@ p)

desugarParameter :: forall m. MonadDesugar m => Located CST.Parameter -> m [Located AST.Parameter]
desugarParameter (CST.Implicit args :@ p) = do
  args' <- flip traverse args \(usage, name@(_ :@ p1), ty) -> do
    ty' <- maybe (pure $ AST.EHole AST.InsertedHole :@ p1) desugarExpression ty
    usage' <- desugarMultiplicity usage Unrestricted p1
    pure $ AST.Parameter True usage' name ty' :@ p
  pure args'
desugarParameter (CST.Explicit [] :@ p) = pure [AST.Parameter False (Unrestricted :@ p) ("_" :@ p) (AST.EOne :@ p) :@ p]
desugarParameter (CST.Explicit args :@ p) = do
  args' <- flip traverse args \(usage, name@(_ :@ p1), ty) -> do
    ty' <- maybe (pure $ AST.EHole AST.InsertedHole :@ p1) desugarExpression ty
    usage' <- desugarMultiplicity usage Unrestricted p1
    pure $ AST.Parameter False usage' name ty' :@ p
  pure args'

desugarMultiplicity :: forall m. MonadDesugar m => Maybe (Located Integer) -> Multiplicity -> Position -> m (Located Multiplicity)
desugarMultiplicity may m p = pure $ maybe (m :@ p) (fromInteger <$>) may

desugarExpression :: forall m. MonadDesugar m => Located CST.Expression -> m (Located AST.Expression)
desugarExpression expr = do
  (expr, byrefs) <- desugarExpression' expr
  case byrefs of
    (x :@ p) : _ -> throwError $ InvalidUseOfByRef x p
    _ -> pure expr

desugarExpression' :: forall m. MonadDesugar m => Located CST.Expression -> m (Located AST.Expression, [Located Text])
desugarExpression' (CST.EType :@ p) = pure (AST.EType :@ p, [])
desugarExpression' (CST.EId i :@ p) = pure (AST.EIdentifier i :@ p, [])
desugarExpression' (CST.EHole :@ p) = pure (AST.EHole AST.SourceHole :@ p, [])
desugarExpression' (CST.EInt i suffix :@ p) = do
  suffix' <- maybe (pure SuffixU64) (desugarIntegerSuffix p) suffix
  pure (AST.EInteger (i :@ p) suffix' :@ p, [])
desugarExpression' (CST.EChar c :@ p) = pure (AST.ECharacter (c :@ p) :@ p, [])
desugarExpression' (CST.ELam [] expr :@ p) = do
  expr' <- desugarExpression expr

  pure (AST.ELam (AST.Parameter False (Unrestricted :@ p) ("_" :@ p) (AST.EOne :@ p) :@ p) expr' :@ p, [])
desugarExpression' (CST.ELam params expr :@ _) = do
  params' <- fold <$> traverse desugarParameter params
  expr' <- desugarExpression expr

  pure (foldr mkLam expr' params', [])
  where
    mkLam param expr = AST.ELam param expr :@ spanOf (getPos param) (getPos expr)
desugarExpression' (CST.EDo expr :@ p) = desugarExpression' (CST.ELam [] expr :@ p)
desugarExpression' (CST.ELet def ret :@ p) = do
  defs' <- desugarDefinition False def
  ret' <- desugarExpression ret
  (,[]) <$> foldrM mkLocal ret' defs'
  where
    mkLocal (d, []) r = pure $ AST.ELocal d r :@ p
    mkLocal (d, binds) r = do
      let AST.Let _ mult name _ m :@ _ = d
      elims <- mkMultiplicativeElims (binds <> [name]) mult m p
      pure (foldr mkLet r elims)

    mkLet (z, m, x, y, e) f = AST.EMultiplicativePairElim z m x y e f :@ p
desugarExpression' (CST.EImport imp ret :@ p) = do
  imps' <- desugarDefinition False imp
  ret' <- desugarExpression ret
  pure (foldr (\(i, _) r -> AST.ELocal i r :@ p) ret' imps', [])
desugarExpression' (CST.EParens e :@ _) = desugarExpression' e
desugarExpression' (CST.EApplication e es :@ _) = do
  e' <- desugarExpression' e
  args <- go es
  pure $ foldl' mkApp e' args
  where
    mkApp (e1, byrefs1) (isImp, (e2, byrefs2)) = (AST.EApplication e1 isImp e2 :@ spanOf (getPos e1) (getPos e2), byrefs1 <> byrefs2)

    go [] = pure []
    go (((isImp, es) :@ _) : es') = do
      es1 <- traverse (fmap (isImp,) . desugarExpression'') es
      es2 <- go es'
      pure $ es1 <> es2

    desugarExpression'' e@(CST.EByRef _ :@ _) = desugarExpression' e
    desugarExpression'' e = (,[]) <$> desugarExpression e
desugarExpression' (CST.EPi params ret :@ _) = do
  param' <- desugarParameter params
  ret' <- desugarExpression ret
  pure (foldr mkPi ret' param', [])
  where
    mkPi param expr = AST.EPi param expr :@ spanOf (getPos param) (getPos expr)
desugarExpression' (CST.ETrue :@ p) = pure (AST.EBoolean True :@ p, [])
desugarExpression' (CST.EFalse :@ p) = pure (AST.EBoolean False :@ p, [])
desugarExpression' (CST.EIfThenElse c t e :@ p) = do
  c' <- desugarExpression c
  t' <- desugarExpression t
  e' <- desugarExpression e
  pure (AST.EIfThenElse c' t' e' :@ p, [])
desugarExpression' (CST.EMultiplicativeProduct params ty :@ _) = do
  params' <- desugarParameter params
  ty' <- desugarExpression ty
  (,[]) <$> foldrM mkProd ty' params'
  where
    mkProd (AST.Parameter True _ _ _ :@ p) _ = throwError $ ImplicitProductType p
    mkProd param ret = pure $ AST.EMultiplicativeProduct param ret :@ spanOf (getPos param) (getPos ret)
desugarExpression' (CST.EAdditiveProduct params ty :@ _) = do
  params' <- desugarParameter params
  ty' <- desugarExpression ty
  (,[]) <$> foldrM mkProd ty' params'
  where
    mkProd (AST.Parameter True _ _ _ :@ p) _ = throwError $ ImplicitProductType p
    mkProd (AST.Parameter _ (mult :@ _) (x :@ _) _ :@ p) _
      | mult /= Unrestricted = throwError $ AdditiveProductWithMultiplicity x p
    mkProd param ret = pure $ AST.EAdditiveProduct param ret :@ spanOf (getPos param) (getPos ret)
desugarExpression' (CST.EMultiplicativeTuple es :@ _) = do
  es' <- traverse desugarExpression es
  pure (foldr1 mkPair es', [])
  where
    mkPair e1 e2 = AST.EMultiplicativePair e1 e2 :@ spanOf (getPos e1) (getPos e2)
desugarExpression' (CST.EAdditiveTuple [e] :@ p) = do
  when (W.additiveSingleton ?warnings) do
    tell [SingletonAdditivePair p]
  desugarExpression' e
desugarExpression' (CST.EAdditiveTuple es :@ _) = do
  es' <- traverse desugarExpression es
  pure (foldr1 mkPair es', [])
  where
    mkPair e1 e2 = AST.EAdditivePair e1 e2 :@ spanOf (getPos e1) (getPos e2)
desugarExpression' (CST.EAdditiveUnit :@ p) = pure (AST.EAdditiveUnit :@ p, [])
desugarExpression' (CST.EMultiplicativeUnit :@ p) = pure (AST.EMultiplicativeUnit :@ p, [])
desugarExpression' (CST.EOne :@ p) = pure (AST.EOne :@ p, [])
desugarExpression' (CST.ETop :@ p) = pure (AST.ETop :@ p, [])
desugarExpression' (CST.EAccess e args :@ _) = do
  e' <- desugarExpression e
  (,[]) <$> foldlM mkAccess e' args
  where
    mkAccess _ (CST.EInt _ (Just _) :@ p) = throwError $ NumberSuffixInAccess p
    mkAccess e1 (CST.EInt x Nothing :@ p) =
      pure $ AST.EAdditiveTupleAccess e1 (Language.Zilch.Syntax.Desugarer.read x) :@ spanOf (getPos e1) p
    mkAccess e1 (CST.EId x :@ p) = pure $ AST.EFieldAccess e1 x :@ spanOf (getPos e1) p
    mkAccess (_ :@ p1) (_ :@ p2) = throwError $ UnsupportedAccessKind (spanOf p1 p2)
desugarExpression' (CST.EMultiplicativeTupleElim bind mult [] m n :@ p) = do
  mult' <- desugarMultiplicity mult Linear p
  (m', byrefs) <- desugarExpression' m
  n' <- desugarExpression n

  case byrefs of
    [] -> pure (AST.EMultiplicativeUnitElim bind mult' m' n' :@ p, [])
    byrefs -> do
      let name = "?unit" :@ getPos m
          unit = AST.EIdentifier name :@ getPos m
      elims <- mkMultiplicativeElims (byrefs <> [name]) mult' m' p
      let ret = AST.EMultiplicativeUnitElim bind mult' unit n' :@ p
      pure (foldr mkLet ret elims, [])
  where
    mkLet (z, m, x, y, e) f = AST.EMultiplicativePairElim z m x y e f :@ p
desugarExpression' (CST.EMultiplicativeTupleElim _ _ [_ :@ p] _ _ :@ _) =
  throwError $ SingletonMultiplicativeTupleElim p
desugarExpression' (CST.EMultiplicativeTupleElim bind mult ids m n :@ p) = do
  mult' <- desugarMultiplicity mult Linear p
  (m', byrefs) <- desugarExpression' m
  n' <- desugarExpression n

  elims <- mkMultiplicativeElims (byrefs <> maybe [] pure bind <> ids) mult' m' p
  let ((_, mult, x, y, m) : tuples) = elims

  pure (foldr mkLet n' ((bind, mult, x, y, m) : tuples), [])
  where
    mkLet (z, m, x, y, e) f = AST.EMultiplicativePairElim z m x y e f :@ p
desugarExpression' (CST.EByRef id :@ p) = pure (AST.EIdentifier id :@ p, [id])

mkMultiplicativeElims :: forall m. MonadDesugar m => [Located Text] -> Located Multiplicity -> Located AST.Expression -> Position -> m [(Maybe (Located Text), Located Multiplicity, Located Text, Located Text, Located AST.Expression)]
mkMultiplicativeElims binds mult m' p = do
  checkBindings binds
  let tuples = go mult binds m' 0
  pure tuples
  where
    go _ [] _ _ = undefined
    go mult [x, y] m _ = [(Nothing, mult, x, y, m)]
    go mult (x : xs) m n =
      let tmp = Text.pack ("?" <> show n) :@ p
       in (Nothing, mult, x, tmp, m) : go mult xs (AST.EIdentifier tmp :@ p) (n + 1)

    checkBindings l = case dups l of
      [] -> pure ()
      y@(x :@ p) : _ ->
        let ps = getPos <$> filter (== y) l
         in throwError $ DuplicateBindingInMultiplicativeTuplesEliminator x (spans p l) ps

    -- highly inefficient but we'll do better later
    dups [] = []
    dups (x : xs) = if x `elem` xs then x : dups xs else dups xs

    spans p = foldr spanOf p . fmap getPos

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

---------------------------------

read :: Read a => Text -> a
read = Prelude.read . Text.unpack

trimap :: (a -> d) -> (b -> e) -> (c -> f) -> (a, b, c) -> (d, e, f)
trimap f g h (x, y, z) = (f x, g y, h z)

third3 :: (c -> d) -> (a, b, c) -> (a, b, d)
third3 = trimap id id
