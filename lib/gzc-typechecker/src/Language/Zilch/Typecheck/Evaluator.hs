{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecursiveDo #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Typecheck.Evaluator (eval, apply, quote, applyVal, debruijnLevelToIndex, force) where

import Data.Located (Located ((:@)), Position, unLoc)
import Data.Text (Text)
import qualified Data.Text as Text
import Language.Zilch.Typecheck.Context (Context (env), emptyContext)
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
eval ctx (TAST.EIdentifier _ (TAST.Idx i) :@ _) =
  case lookup (env ctx) i of
    VThunk (expr :@ p) :@ _ -> eval ctx (expr :@ p)
    val -> pure val
eval ctx (TAST.EApplication e1 isImplicit e2 :@ _) = do
  v1 <- eval ctx e1
  v2 <- eval ctx e2

  applyVal ctx v1 v2 (not isImplicit)
eval ctx (TAST.ELet (TAST.Let True _ _ _ val :@ _) u :@ _) = mdo
  let ctx' = ctx {env = Env.extend (env ctx) val'}
  val' <- eval ctx' val
  eval ctx' u
eval ctx (TAST.ELet (TAST.Let False _ _ _ val :@ _) u :@ _) = do
  val' <- eval ctx val
  let env' = Env.extend (env ctx) val'
  eval (ctx {env = env'}) u
eval ctx (TAST.EPi (TAST.Parameter isImplicit usage name ty1 :@ _) ty2 :@ p) = do
  ty1' <- eval ctx ty1
  pure $ VPi (unLoc usage) (unLoc name) (not isImplicit) ty1' (Clos (env ctx) ty2) :@ p
eval ctx (TAST.EMultiplicativeProduct (TAST.Parameter _ usage name ty1 :@ _) ty2 :@ p) = do
  ty1' <- eval ctx ty1
  pure $ VMultiplicativeProduct (unLoc usage) (unLoc name) ty1' (Clos (env ctx) ty2) :@ p
eval ctx (TAST.EAdditiveProduct (TAST.Parameter _ _ name ty1 :@ _) ty2 :@ p) = do
  ty1' <- eval ctx ty1
  pure $ VAdditiveProduct (unLoc name) ty1' (Clos (env ctx) ty2) :@ p
eval ctx (TAST.ELam (TAST.Parameter isImplicit usage (x :@ _) ty1 :@ _) ex :@ p) = do
  ty1' <- eval ctx ty1
  pure $ VLam (unLoc usage) x (not isImplicit) ty1' (Clos (env ctx) ex) :@ p
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
eval ctx (TAST.EIfThenElse c t e :@ p) = do
  c' <- eval ctx c
  t' <- eval ctx t
  e' <- eval ctx e
  pure (VIfThenElse c' t' e' :@ p)
eval ctx (TAST.EMultiplicativePair e1 e2 :@ p) = do
  e1' <- eval ctx e1
  e2' <- eval ctx e2
  pure $ VMultiplicativePair e1' e2' :@ p
eval ctx (TAST.EAdditivePair e1 e2 :@ p) = do
  e1' <- eval ctx e1
  e2' <- eval ctx e2
  pure $ VAdditivePair e1' e2' :@ p
eval _ (TAST.EMultiplicativeUnit :@ p) = pure $ VMultiplicativeUnit :@ p
eval _ (TAST.EAdditiveUnit :@ p) = pure $ VAdditiveUnit :@ p
eval _ (TAST.EOne :@ p) = pure $ VOne :@ p
eval _ (TAST.ETop :@ p) = pure $ VTop :@ p
eval _ e = error $ "unhandled case " <> show e

apply :: forall m. MonadElab m => Context -> Closure -> Located Value -> m (Located Value)
apply _ (Clos env expr) val =
  let env' = Env.extend env val
   in eval (emptyContext {env = env'}) expr

applyVal :: forall m. MonadElab m => Context -> Located Value -> Located Value -> Implicitness -> m (Located Value)
applyVal ctx (VLam _ _ _ _ t :@ _) u _ = apply ctx t u
applyVal _ (VFlexible x sp :@ p) u i = pure $ VFlexible x ((u, i) : sp) :@ p
applyVal _ (VRigid x name sp :@ p) u i = pure $ VRigid x name ((u, i) : sp) :@ p
applyVal _ _ _ _ = undefined

applySpine :: forall m. MonadElab m => Context -> Located Value -> Spine -> m (Located Value)
applySpine _ t [] = pure t
applySpine ctx t ((u, i) : sp) = do
  v1 <- applySpine ctx t sp
  applyVal ctx v1 u i

applyBDs :: forall m. MonadElab m => Context -> Environment -> Located Value -> TAST.Path -> m (Located Value)
applyBDs _ [] v TAST.Here = pure v
applyBDs ctx (t : env) v (TAST.Bind bds _ _ _) = do
  v1 <- applyBDs ctx env v bds
  applyVal ctx v1 t explicit
applyBDs ctx (_ : env) v (TAST.Define bds _ _ _ _) = applyBDs ctx env v bds
applyBDs _ _ _ _ = error "impossible"

metaValue :: forall m. MonadElab m => Int -> Position -> m (Located Value)
metaValue m pos =
  lookupMeta m >>= \case
    (Solved v _ _, _, _, _) -> pure $ v :@ pos
    (Unsolved _ _, _, _, _) -> pure $ VMeta m :@ pos

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
    VFlexible m sp :@ p -> quoteSpine ctx level (TAST.EMeta m :@ p) sp p
    VRigid name m sp :@ p -> quoteSpine ctx level (TAST.EIdentifier name (debruijnLevelToIndex level m) :@ p) sp p
    (VCharacter c :@ p) -> pure $ TAST.ECharacter (Text.singleton c :@ p) :@ p
    (VInteger n ty :@ p) -> do
      tmp <- quote ctx level (ty :@ p)
      let TAST.EBuiltin ty :@ _ = tmp
      pure $ TAST.EInteger (Text.pack (show n) :@ p) ty :@ p
    VTrue :@ p -> pure $ TAST.EBoolean True :@ p
    VFalse :@ p -> pure $ TAST.EBoolean False :@ p
    (VLam usage name isExplicit ty1 clos :@ p) -> do
      x' <- apply ctx clos (VVariable (name :@ p) level :@ p)
      x' <- quote ctx (level + 1) x'
      ty1 <- quote ctx level ty1
      pure $ TAST.ELam (TAST.Parameter (not isExplicit) (usage :@ p) (name :@ p) ty1 :@ p) x' :@ p
    (VPi usage y isExplicit val clos :@ p) -> do
      x' <- apply ctx clos (VVariable (y :@ p) level :@ p)
      val' <- quote ctx level val
      x' <- quote ctx (level + 1) x'
      pure $ TAST.EPi (TAST.Parameter (not isExplicit) (usage :@ p) (y :@ p) val' :@ p) x' :@ p
    (VMultiplicativeProduct usage y val clos :@ p) -> do
      x' <- apply ctx clos (VVariable (y :@ p) level :@ p)
      val' <- quote ctx level val
      x' <- quote ctx (level + 1) x'
      pure $ TAST.EMultiplicativeProduct (TAST.Parameter (not explicit) (usage :@ p) (y :@ p) val' :@ p) x' :@ p
    (VAdditiveProduct y val clos :@ p) -> do
      x' <- apply ctx clos (VVariable (y :@ p) level :@ p)
      val' <- quote ctx level val
      x' <- quote ctx (level + 1) x'
      pure $ TAST.EAdditiveProduct (TAST.Parameter (not explicit) (TAST.W :@ p) (y :@ p) val' :@ p) x' :@ p
    (VMultiplicativePair e1 e2 :@ p) -> do
      e1' <- quote ctx level e1
      e2' <- quote ctx level e2
      pure $ TAST.EMultiplicativePair e1' e2' :@ p
    (VAdditivePair e1 e2 :@ p) -> do
      e1' <- quote ctx level e1
      e2' <- quote ctx level e2
      pure $ TAST.EAdditivePair e1' e2' :@ p
    (VIfThenElse c t e :@ p) -> do
      c' <- quote ctx level c
      t' <- quote ctx level t
      e' <- quote ctx level e
      pure $ TAST.EIfThenElse c' t' e' :@ p
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
    v -> error $ "not yet handled " <> show v

quoteSpine :: forall m. MonadElab m => Context -> DeBruijnLvl -> Located TAST.Expression -> Spine -> Position -> m (Located TAST.Expression)
quoteSpine _ _ term [] _ = pure term
quoteSpine ctx lvl term ((u, i) : sp) pos = do
  t1 <- quote ctx lvl u
  t2 <- quoteSpine ctx lvl term sp pos
  pure $ TAST.EApplication t2 (not i) t1 :@ pos

------------

read :: Read a => Text -> a
read = Prelude.read . Text.unpack
