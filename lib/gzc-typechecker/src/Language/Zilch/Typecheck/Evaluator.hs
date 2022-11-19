{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Typecheck.Evaluator (eval, apply, apply', quote, applyVal, debruijnLevelToIndex, force, destroyClosure, metaType) where

import Data.Functor ((<&>))
import Data.List (foldl')
import Data.Located (Located ((:@)), Position, getPos, unLoc)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Debug.Trace (trace, traceShow)
import Language.Zilch.Typecheck.Context (Context (env, lvl), emptyContext)
import qualified Language.Zilch.Typecheck.Core.AST as TAST
import Language.Zilch.Typecheck.Core.Eval
import qualified Language.Zilch.Typecheck.Core.Multiplicity as TAST
import {-# SOURCE #-} Language.Zilch.Typecheck.Elaborator (MonadElab)
import Language.Zilch.Typecheck.Environment (lookup)
import qualified Language.Zilch.Typecheck.Environment as Env
import Language.Zilch.Typecheck.Metavars (lookupMeta)
import Prelude hiding (lookup, read)
import qualified Prelude (read)

-- | Evaluate the given expression in normal form, where normal form is either:
--
-- - A lambda
-- - An application @(e1 e2)@ where @e1@ is /not/ a lambda
-- - An integer
-- - The pi type
eval :: forall m. MonadElab m => Context -> Located TAST.Expression -> m (Located Value)
eval ctx (TAST.EInteger e ty :@ p) = do
  ty :@ _ <- eval ctx (TAST.EBuiltin ty :@ p)
  pure $ VInteger (read $ unLoc e) ty :@ p
eval _ (TAST.ECharacter (c :@ _) :@ p) = pure $ VCharacter (Text.head c) :@ p
eval _ (TAST.EBoolean bool :@ p) = pure $ (if bool then VTrue else VFalse) :@ p
eval ctx (TAST.EIdentifier _ (TAST.Idx i) ty :@ _) = do
  case lookup (env ctx) i of
    VThunk (expr :@ p) :@ _ -> eval ctx (expr :@ p)
    val -> pure val
eval ctx (TAST.EApplication _ e1 isImplicit ty2 e2 :@ _) = do
  v1 <- eval ctx e1
  ty2 <- eval ctx ty2
  v2 <- eval ctx e2

  applyVal ctx v1 ty2 v2 (not isImplicit)
eval ctx (TAST.ELet (TAST.Let True _ _ _ val :@ _) u :@ _) = mdo
  let ctx' = ctx {env = Env.extend (env ctx) val'}
  val' <- eval ctx' val
  eval ctx' u
eval ctx (TAST.ELet (TAST.Let False _ _ _ val :@ _) u :@ _) = do
  val' <- eval ctx val
  let env' = Env.extend (env ctx) val'
  eval (ctx {env = env'}) u
eval ctx (TAST.ELet (TAST.External _ _ _ val _ _ :@ _) u :@ _) = do
  val' <- eval ctx val
  let env' = Env.extend (env ctx) val'
  eval (ctx {env = env'}) u
eval ctx (TAST.EPi (TAST.Parameter isImplicit usage name ty1 :@ _) ty3 ty2 :@ p) = do
  ty1' <- eval ctx ty1
  ty3' <- eval ctx ty3
  pure $ VPi (unLoc usage) (unLoc name) (not isImplicit) ty1' ty3' (Clos (env ctx) ty2) :@ p
eval ctx (TAST.EMultiplicativeProduct (TAST.Parameter _ usage name ty1 :@ _) ty3 ty2 :@ p) = do
  ty1' <- eval ctx ty1
  ty3' <- eval ctx ty3
  pure $ VMultiplicativeProduct (unLoc usage) (unLoc name) ty1' ty3' (Clos (env ctx) ty2) :@ p
eval ctx (TAST.EAdditiveProduct (TAST.Parameter _ _ name ty1 :@ _) ty3 ty2 :@ p) = do
  ty1' <- eval ctx ty1
  ty3' <- eval ctx ty3
  pure $ VAdditiveProduct (unLoc name) ty1' ty3' (Clos (env ctx) ty2) :@ p
eval ctx (TAST.ELam (TAST.Parameter isImplicit usage (x :@ _) ty1 :@ _) ty2 ex :@ p) = do
  ty1' <- eval ctx ty1
  ty2' <- eval ctx ty2
  pure $ VLam (unLoc usage) x (not isImplicit) ty1' ty2' (Clos (env ctx) ex) :@ p
eval _ (TAST.EType :@ p) = pure $ VType :@ p
eval _ (TAST.EMeta m :@ p) = metaValue m p
eval ctx (TAST.EInsertedMeta m bds :@ p) = do
  meta <- metaValue m p
  applyBDs ctx (env ctx) meta bds
eval _ (TAST.EBuiltin TAST.TyU64 :@ p) = pure $ VBuiltinU64 :@ p
eval _ (TAST.EBuiltin TAST.TyU32 :@ p) = pure $ VBuiltinU32 :@ p
eval _ (TAST.EBuiltin TAST.TyU16 :@ p) = pure $ VBuiltinU16 :@ p
eval _ (TAST.EBuiltin TAST.TyU8 :@ p) = pure $ VBuiltinU8 :@ p
eval _ (TAST.EBuiltin TAST.TyS64 :@ p) = pure $ VBuiltinS64 :@ p
eval _ (TAST.EBuiltin TAST.TyS32 :@ p) = pure $ VBuiltinS32 :@ p
eval _ (TAST.EBuiltin TAST.TyS16 :@ p) = pure $ VBuiltinS16 :@ p
eval _ (TAST.EBuiltin TAST.TyS8 :@ p) = pure $ VBuiltinS8 :@ p
eval _ (TAST.EBuiltin TAST.TyBool :@ p) = pure $ VBuiltinBool :@ p
eval ctx (TAST.EIfThenElse c t tyt e tye :@ p) = do
  c' <- eval ctx c
  t' <- eval ctx t
  tyt' <- eval ctx tyt
  e' <- eval ctx e
  tye' <- eval ctx tye
  pure (VIfThenElse c' t' tyt' e' tye' :@ p)
eval ctx (TAST.EMultiplicativePair e1 ty1 e2 ty2 :@ p) = do
  e1' <- eval ctx e1
  ty1' <- eval ctx ty1
  e2' <- eval ctx e2
  ty2' <- eval ctx ty2
  pure $ VMultiplicativePair e1' ty1' e2' ty2' :@ p
eval ctx (TAST.EAdditivePair e1 ty1 e2 ty2 :@ p) = do
  e1' <- eval ctx e1
  ty1' <- eval ctx ty1
  e2' <- eval ctx e2
  ty2' <- eval ctx ty2
  pure $ VAdditivePair e1' ty1' e2' ty2' :@ p
eval _ (TAST.EMultiplicativeUnit :@ p) = pure $ VMultiplicativeUnit :@ p
eval _ (TAST.EAdditiveUnit :@ p) = pure $ VAdditiveUnit :@ p
eval _ (TAST.EOne :@ p) = pure $ VOne :@ p
eval _ (TAST.ETop :@ p) = pure $ VTop :@ p
eval ctx (TAST.EFst ty e :@ p) = do
  ty' <- eval ctx ty
  eval ctx e >>= \case
    VAdditivePair a _ _ _ :@ _ -> pure a
    VMultiplicativePair a _ _ _ :@ _ -> pure a
    e -> pure $ VFst ty' e :@ p
eval ctx (TAST.ESnd ty e :@ p) = do
  ty' <- eval ctx ty
  eval ctx e >>= \case
    VAdditivePair _ _ b _ :@ _ -> pure b
    VMultiplicativePair _ _ b _ :@ _ -> pure b
    e -> pure $ VSnd ty' e :@ p
eval ctx (TAST.EMultiplicativePairElim _ mult _ tx _ ty m n :@ _) = do
  m' <- eval ctx m
  tx' <- eval ctx tx
  let typ = VMultiplicativeProduct (unLoc mult) "_" tx' (VType :@ getPos ty) (Clos (env ctx) ty) :@ getPos m
  let env' = Env.extend (Env.extend (env ctx) (VFst typ m' :@ getPos m')) (VSnd typ m' :@ getPos m')
  eval (ctx {env = env'}) n
eval ctx (TAST.EMultiplicativeUnitElim _ _ m n :@ _) = do
  eval ctx m -- << this will not be evaluated
  eval ctx n
eval ctx (TAST.EComposite fields :@ p) = do
  let fields' = fields <&> \(m, name, ty) -> (m, name, Clos (env ctx) ty)
  pure $ VComposite fields' :@ p
eval ctx (TAST.EModule fields :@ p) = do
  fields' <- traverse (\(m, ty) -> (m,) <$> eval ctx ty) fields
  pure $ VModule fields' :@ p
eval ctx (TAST.ERecordLiteral fields :@ p) = do
  fields' <- traverse (\(m, k, ty, ex) -> (m,k,,) <$> eval ctx ty <*> eval ctx ex) fields
  pure $ VRecord fields' :@ p
eval ctx (TAST.ERecordAccess r tyr x :@ p) = do
  tyr' <- eval ctx tyr
  eval ctx r >>= \case
    VRecord fields :@ _ -> case lookup x fields of
      Nothing -> undefined
      Just (_, _, _, ex) -> pure ex
    r -> pure $ VRecordAccess r tyr' x :@ p
  where
    lookup _ [] = Nothing
    lookup x ((m, y, ty, ex) : fs)
      | x == y = Just (m, x, ty, ex)
      | otherwise = lookup x fs
eval _ e = error $ "unhandled case " <> show e

apply :: forall m. MonadElab m => Context -> Closure -> Located Value -> m (Located Value)
apply ctx clos val = apply' ctx clos [val]

apply' :: forall m. MonadElab m => Context -> Closure -> [Located Value] -> m (Located Value)
apply' _ (Clos env expr) vals = do
  let env' = foldl' Env.extend env vals
  eval (emptyContext {env = env'}) expr

destroyClosure :: forall m. MonadElab m => Closure -> m (Located Value)
destroyClosure (Clos env expr) = eval (emptyContext {env}) expr

applyVal :: forall m. MonadElab m => Context -> Located Value -> Located Value -> Located Value -> Implicitness -> m (Located Value)
applyVal ctx (VLam _ _ _ _ _ t :@ _) _ u _ = apply ctx t u
applyVal _ (VFlexible x sp :@ p) ty u i = pure $ VFlexible x ((u, ty, i) : sp) :@ p
applyVal _ (VRigid x name ty1 sp :@ p) ty u i = pure $ VRigid x name ty1 ((u, ty, i) : sp) :@ p
applyVal _ (VFFI name sp :@ p) ty u i = pure $ VFFI name ((u, ty, i) : sp) :@ p
applyVal _ _ _ _ _ = undefined

applySpine :: forall m. MonadElab m => Context -> Located Value -> Spine -> m (Located Value)
applySpine _ t [] = pure t
applySpine ctx t ((u, t2, i) : sp) = do
  v1 <- applySpine ctx t sp
  applyVal ctx v1 t2 u i

applyBDs :: forall m. MonadElab m => Context -> Environment -> Located Value -> TAST.Path -> m (Located Value)
applyBDs _ [] v TAST.Here = pure v
applyBDs ctx (t : env) v (TAST.Bind bds _ _ ty) = do
  v1 <- applyBDs ctx env v bds
  applyVal ctx v1 ty t explicit
applyBDs ctx (_ : env) v (TAST.Define bds _ _ _ _) = applyBDs ctx env v bds
applyBDs _ _ _ _ = error "impossible"

metaValue :: forall m. MonadElab m => Int -> Position -> m (Located Value)
metaValue m pos =
  lookupMeta m >>= \case
    (Solved v _ _, _, _, _) -> pure $ v :@ pos
    (Unsolved _ _, _, _, _) -> pure $ VMeta m :@ pos

metaType :: forall m. MonadElab m => Int -> m (Located Value)
metaType m =
  lookupMeta m >>= \case
    (Solved _ _ ty, _, _, _) -> pure ty
    (Unsolved _ ty, _, _, _) -> pure ty

force :: forall m. MonadElab m => Context -> Located Value -> m (Located Value)
force ctx t@(VFlexible m sp :@ p) = do
  lookupMeta m >>= \case
    (Solved t _ _, _, _, _) -> do
      v1 <- applySpine ctx (t :@ p) sp
      force ctx v1
    _ -> pure t
force _ t = pure t

debruijnLevelToIndex :: DeBruijnLvl -> DeBruijnLvl -> TAST.DeBruijnIdx
debruijnLevelToIndex (Lvl l) (Lvl x) = TAST.Idx $! l - x - 1

quote :: forall m. MonadElab m => Context -> DeBruijnLvl -> Located Value -> m (Located TAST.Expression)
quote ctx level val = do
  v <- force ctx val
  case v of
    -- (VIdentifier name n :@ p) -> pure $ TAST.EIdentifier name (debruijnLevelToIndex level n) :@ p
    VFlexible m sp :@ p -> do
      ty <- quote ctx (lvl ctx) =<< metaType m
      fst <$> quoteSpine ctx level (TAST.EMeta m :@ p) ty sp p
    VRigid name m ty sp :@ p -> do
      ty' <- quote ctx level ty
      fst <$> quoteSpine ctx level (TAST.EIdentifier name (debruijnLevelToIndex level m) ty' :@ p) ty' sp p
    (VCharacter c :@ p) -> pure $ TAST.ECharacter (Text.singleton c :@ p) :@ p
    (VInteger n ty :@ p) -> do
      tmp <- quote ctx level (ty :@ p)
      let TAST.EBuiltin ty :@ _ = tmp
      pure $ TAST.EInteger (Text.pack (show n) :@ p) ty :@ p
    VTrue :@ p -> pure $ TAST.EBoolean True :@ p
    VFalse :@ p -> pure $ TAST.EBoolean False :@ p
    (VLam usage name isExplicit ty1 ty2 clos :@ p) -> do
      x' <- apply ctx clos (VVariable (name :@ p) level ty1 :@ p)
      x' <- quote ctx (level + 1) x'
      ty1' <- quote ctx level ty1
      ty2' <- quote ctx (level + 1) ty2
      pure $ TAST.ELam (TAST.Parameter (not isExplicit) (usage :@ p) (name :@ p) ty1' :@ p) ty2' x' :@ p
    (VPi usage y isExplicit val ty clos :@ p) -> do
      x' <- apply ctx clos (VVariable (y :@ p) level ty :@ p)
      val' <- quote ctx level val
      ty' <- quote ctx (level + 1) ty
      x' <- quote ctx (level + 1) x'
      pure $ TAST.EPi (TAST.Parameter (not isExplicit) (usage :@ p) (y :@ p) val' :@ p) ty' x' :@ p
    (VMultiplicativeProduct usage y val ty clos :@ p) -> do
      x' <- apply ctx clos (VVariable (y :@ p) level ty :@ p)
      val' <- quote ctx level val
      x' <- quote ctx (level + 1) x'
      ty' <- quote ctx (level + 1) ty
      pure $ TAST.EMultiplicativeProduct (TAST.Parameter (not explicit) (usage :@ p) (y :@ p) val' :@ p) ty' x' :@ p
    (VAdditiveProduct y val ty clos :@ p) -> do
      x' <- apply ctx clos (VVariable (y :@ p) level ty :@ p)
      val' <- quote ctx level val
      x' <- quote ctx (level + 1) x'
      ty' <- quote ctx (level + 1) ty
      pure $ TAST.EAdditiveProduct (TAST.Parameter (not explicit) (TAST.W :@ p) (y :@ p) val' :@ p) ty' x' :@ p
    (VMultiplicativePair e1 t1 e2 t2 :@ p) -> do
      e1' <- quote ctx level e1
      e2' <- quote ctx level e2
      t1' <- quote ctx level t1
      t2' <- quote ctx level t2
      pure $ TAST.EMultiplicativePair e1' t1' e2' t2' :@ p
    (VAdditivePair e1 t1 e2 t2 :@ p) -> do
      e1' <- quote ctx level e1
      e2' <- quote ctx level e2
      t1' <- quote ctx level t1
      t2' <- quote ctx level t2
      pure $ TAST.EAdditivePair e1' t1' e2' t2' :@ p
    (VIfThenElse c t tt e te :@ p) -> do
      c' <- quote ctx level c
      t' <- quote ctx level t
      tt' <- quote ctx level tt
      e' <- quote ctx level e
      te' <- quote ctx level te
      pure $ TAST.EIfThenElse c' t' tt' e' te' :@ p
    (VType :@ p) -> pure $ TAST.EType :@ p
    VBuiltinU64 :@ p -> pure $ TAST.EBuiltin TAST.TyU64 :@ p
    VBuiltinU32 :@ p -> pure $ TAST.EBuiltin TAST.TyU32 :@ p
    VBuiltinU16 :@ p -> pure $ TAST.EBuiltin TAST.TyU16 :@ p
    VBuiltinU8 :@ p -> pure $ TAST.EBuiltin TAST.TyU8 :@ p
    VBuiltinS64 :@ p -> pure $ TAST.EBuiltin TAST.TyS64 :@ p
    VBuiltinS32 :@ p -> pure $ TAST.EBuiltin TAST.TyS32 :@ p
    VBuiltinS16 :@ p -> pure $ TAST.EBuiltin TAST.TyS16 :@ p
    VBuiltinS8 :@ p -> pure $ TAST.EBuiltin TAST.TyS8 :@ p
    VBuiltinBool :@ p -> pure $ TAST.EBuiltin TAST.TyBool :@ p
    VOne :@ p -> pure $ TAST.EOne :@ p
    VTop :@ p -> pure $ TAST.ETop :@ p
    VAdditiveUnit :@ p -> pure $ TAST.EAdditiveUnit :@ p
    VMultiplicativeUnit :@ p -> pure $ TAST.EMultiplicativeUnit :@ p
    VFst ty e :@ p -> do
      e' <- quote ctx level e
      ty' <- quote ctx (lvl ctx) ty
      pure $ TAST.EFst ty' e' :@ p
    VSnd ty e :@ p -> do
      e' <- quote ctx level e
      ty' <- quote ctx (lvl ctx) ty
      pure $ TAST.ESnd ty' e' :@ p
    VComposite fields :@ p -> do
      fields' <- quoteFields (level, mempty, mempty) fields -- traverse (\(m, ty) -> (m,) <$> quote ctx level ty) fields
      pure $ TAST.EComposite (reverse $ fields' <&> \(m, k, _, t) -> (m, k, t)) :@ p
      where
        quoteFields (_, fields, _) [] = pure fields
        quoteFields (level, fields, fields') ((m, k, clos) : fs) = do
          ty <- apply' ctx clos fields' -- (fields <&> \(_, k, lvl, ty) -> VVariable k lvl ty :@ p)
          ty' <- quote ctx level ty
          quoteFields (level + 1, (m, k, level, ty') : fields, (VVariable k level ty :@ p) : fields') fs
    VModule fields :@ p -> do
      fields' <- traverse (\(m, ty) -> (m,) <$> quote ctx level ty) fields
      pure $ TAST.EModule fields' :@ p
    VRecord fields :@ p -> do
      fields' <- traverse (\(m, k, ty, ex) -> (m,k,,) <$> quote ctx level ty <*> quote ctx level ex) fields
      pure $ TAST.ERecordLiteral fields' :@ p
    VRecordAccess r tr x :@ p -> do
      r' <- quote ctx level r
      tr' <- quote ctx level tr
      pure $ TAST.ERecordAccess r' tr' x :@ p
    -- VThunk expr :@ _ -> pure expr
    v -> error $ "not yet handled " <> show v

quoteSpine :: forall m. MonadElab m => Context -> DeBruijnLvl -> Located TAST.Expression -> Located TAST.Expression -> Spine -> Position -> m (Located TAST.Expression, Located TAST.Expression)
quoteSpine _ _ term ty [] _ = pure (term, ty)
quoteSpine ctx lvl term ty ((u, t, i) : sp) pos = do
  t1 <- quote ctx lvl u
  (t2, ty) <- quoteSpine ctx lvl term ty sp pos
  t3 <- quote ctx lvl t

  let TAST.EPi _ _ ty2 :@ _ = ty
  pure (TAST.EApplication ty t2 (not i) t3 t1 :@ pos, ty2)

------------

read :: Read a => Text -> a
read = Prelude.read . Text.unpack
