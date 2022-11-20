{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Typecheck.Internal.TAST2IR where

import Control.Monad (forM, when)
import Control.Monad.State (MonadState, evalState, get, gets, modify, put)
import Data.Functor ((<&>))
import Data.Located (Located (..), getPos)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (catMaybes)
import Data.Text (Text)
import Debug.Trace (traceShow)
import qualified Language.Zilch.Typecheck.Core.AST as TAST
import qualified Language.Zilch.Typecheck.IR as IR

type MonadTranslator m = MonadState (Map (Located Text) [Located Text]) m

locally :: MonadState s m => (s -> s) -> m a -> m a
locally f act = do
  s <- get <* modify f
  act <* put s

translateModules :: [(FilePath, [Located Text], Located TAST.Module)] -> [(FilePath, [Located Text], Located IR.Module)]
translateModules [] = []
translateModules ((path, modName, mod) : mods) =
  (path, modName, evalState (translateMod modName mod) mempty) : translateModules mods

translateMod :: MonadTranslator m => [Located Text] -> Located TAST.Module -> m (Located IR.Module)
translateMod _ (TAST.Mod [] :@ p) = pure $ IR.Module [] :@ p
translateMod modName (TAST.Mod bs :@ p) = do
  bs <-
    catMaybes <$> forM bs \b -> do
      translateToplevel modName b >>= \case
        b@(Just (IR.TopLevel _ isPub def :@ _)) -> do
          case def of
            IR.Let _ _ name _ _ :@ _ ->
              let modName' = if isPub then modName else modName <> ["/priv" :@ getPos name]
               in modify (Map.insert name modName')
            IR.Val _ name _ :@ _ ->
              let modName' = if isPub then modName else modName <> ["/priv" :@ getPos name]
               in modify (Map.insert name modName')
          pure b
        Nothing -> pure Nothing

  pure $ IR.Module bs :@ p

translateToplevel :: MonadTranslator m => [Located Text] -> Located TAST.TopLevel -> m (Maybe (Located IR.TopLevel))
translateToplevel modName (TAST.TopLevel attrs isPublic def :@ p) = do
  def <- translateDefinition modName isPublic True def
  pure $ def <&> \def -> IR.TopLevel attrs isPublic def :@ p

translateDefinition :: MonadTranslator m => [Located Text] -> Bool -> Bool -> Located TAST.Definition -> m (Maybe (Located IR.Definition))
translateDefinition modName isPub isTop (TAST.Let isRec mult name ty ex :@ p) = do
  ty <- locally id (translateExpression modName ty)
  let modName' = if not isPub && isTop then modName <> ["/priv" :@ getPos name] else modName
  ex <- (if isRec then locally (Map.insert name modName') else id) do
    -- this has as effect to scope any new `external` definitions
    translateExpression (modName' <> [name]) ex
  modify (Map.insert name modName')
  pure $ Just (IR.Let isRec mult name ty ex :@ p)
translateDefinition modName _ _ (TAST.Val mult name ty :@ p) = do
  ty <- locally id (translateExpression modName ty)
  pure $ Just (IR.Val mult name ty :@ p)
translateDefinition _ _ _ (TAST.External _ name _ _ (init -> mod) _ :@ _) = do
  modify (Map.insert name mod)
  pure Nothing

translateParameter :: MonadTranslator m => [Located Text] -> Located TAST.Parameter -> m (Located IR.Parameter)
translateParameter modName (TAST.Parameter _ mult name ty :@ p) = do
  ty <- locally id (translateExpression modName ty)
  modify (Map.insert name [])
  -- parameter must not be qualified
  -- or we could also add the qualification to the parameter name
  -- but this would mess up the original names
  pure $ IR.Parameter mult name ty :@ p

translateExpression :: MonadTranslator m => [Located Text] -> Located TAST.Expression -> m (Located IR.Expression)
translateExpression _ (TAST.EType :@ p) = pure $ IR.EType :@ p
translateExpression modName (TAST.ELam param ty ex :@ p) = locally id do
  param <- translateParameter modName param
  ty <- locally id (translateExpression modName ty)
  ex <- translateExpression modName ex
  pure $ IR.ELam param ty ex :@ p
translateExpression modName (TAST.EPi param ty ex :@ p) = locally id do
  param <- translateParameter modName param
  ty <- locally id (translateExpression modName ty)
  ex <- translateExpression modName ex
  pure $ IR.EPi param ty ex :@ p
translateExpression modName (TAST.EAdditiveProduct param ty ex :@ p) = locally id do
  param <- translateParameter modName param
  ty <- locally id (translateExpression modName ty)
  ex <- translateExpression modName ex
  pure $ IR.EAdditiveProduct param ty ex :@ p
translateExpression modName (TAST.EMultiplicativeProduct param ty ex :@ p) = locally id do
  param <- translateParameter modName param
  ty <- locally id (translateExpression modName ty)
  ex <- translateExpression modName ex
  pure $ IR.EMultiplicativeProduct param ty ex :@ p
translateExpression modName (TAST.ELet def ex :@ p) = do
  def <- translateDefinition modName False False def
  ex <- locally id (translateExpression modName ex)
  pure case def of
    Nothing -> ex
    Just def -> IR.ELet def ex :@ p
translateExpression modName (TAST.EApplication ty1 f _ ty2 x :@ p) = do
  ty1 <- locally id (translateExpression modName ty1)
  f <- locally id (translateExpression modName f)
  ty2 <- locally id (translateExpression modName ty2)
  x <- locally id (translateExpression modName x)
  pure $ IR.EApplication ty1 f ty2 x :@ p
translateExpression _ (TAST.EIdentifier name _ _ :@ p) = do
  -- traceShow name $ pure ()
  mod <- gets (Map.! name)
  pure $ IR.EIdentifier (mod <> [name]) :@ p
translateExpression _ (TAST.EInteger i ty :@ p) = pure $ IR.EInteger i ty :@ p
translateExpression _ (TAST.ECharacter c :@ p) = pure $ IR.ECharacter c :@ p
translateExpression _ (TAST.EMeta _ :@ _) = undefined
translateExpression _ (TAST.EInsertedMeta _ _ :@ _) = undefined
translateExpression _ (TAST.EBuiltin ty :@ p) = pure $ IR.EBuiltin ty :@ p
translateExpression _ (TAST.EBoolean b :@ p) = pure $ IR.EBoolean b :@ p
translateExpression modName (TAST.EIfThenElse c t tt e te :@ p) = do
  c <- locally id (translateExpression modName c)
  t <- locally id (translateExpression modName t)
  tt <- locally id (translateExpression modName tt)
  e <- locally id (translateExpression modName e)
  te <- locally id (translateExpression modName te)
  pure $ IR.EIfThenElse c t tt e te :@ p
translateExpression modName (TAST.EAdditivePair e1 t1 e2 t2 :@ p) = do
  e1 <- locally id (translateExpression modName e1)
  t1 <- locally id (translateExpression modName t1)
  e2 <- locally id (translateExpression modName e2)
  t2 <- locally id (translateExpression modName t2)
  pure $ IR.EAdditivePair e1 t1 e2 t2 :@ p
translateExpression modName (TAST.EMultiplicativePair e1 t1 e2 t2 :@ p) = do
  e1 <- locally id (translateExpression modName e1)
  t1 <- locally id (translateExpression modName t1)
  e2 <- locally id (translateExpression modName e2)
  t2 <- locally id (translateExpression modName t2)
  pure $ IR.EMultiplicativePair e1 t1 e2 t2 :@ p
translateExpression _ (TAST.EMultiplicativeUnit :@ p) = pure $ IR.EMultiplicativeUnit :@ p
translateExpression _ (TAST.EAdditiveUnit :@ p) = pure $ IR.EAdditiveUnit :@ p
translateExpression _ (TAST.EOne :@ p) = pure $ IR.EOne :@ p
translateExpression _ (TAST.ETop :@ p) = pure $ IR.ETop :@ p
translateExpression modName (TAST.EFst ty ex :@ p) = do
  ex <- locally id (translateExpression modName ex)
  ty <- locally id (translateExpression modName ty)
  pure $ IR.EFst ty ex :@ p
translateExpression modName (TAST.ESnd ty ex :@ p) = do
  ex <- locally id (translateExpression modName ex)
  ty <- locally id (translateExpression modName ty)
  pure $ IR.ESnd ty ex :@ p
translateExpression modName (TAST.EMultiplicativePairElim z m x tx y ty e1 e2 :@ p) = locally id do
  tx <- locally id (translateExpression modName tx)
  ty <- locally id (translateExpression modName ty)
  e1 <- locally id (translateExpression modName e1)
  modify (Map.insert x modName . Map.insert y modName)
  case z of
    Just z -> modify (Map.insert z modName)
    Nothing -> pure ()
  e2 <- translateExpression modName e2
  pure $ IR.EMultiplicativePairElim z m x tx y ty e1 e2 :@ p
translateExpression modName (TAST.EMultiplicativeUnitElim z m e1 e2 :@ p) = locally id do
  e1 <- locally id (translateExpression modName e1)
  case z of
    Just z -> modify (Map.insert z modName)
    Nothing -> pure ()
  e2 <- translateExpression modName e2
  pure $ IR.EMultiplicativeUnitElim z m e1 e2 :@ p
translateExpression modName (TAST.EComposite fields :@ p) = do
  fields <- forM fields \(mult, name, ex) -> (mult,name,) <$> locally id (translateExpression modName ex)
  pure $ IR.EComposite fields :@ p
translateExpression _ (TAST.EModule _ :@ _) = undefined
translateExpression modName (TAST.ERecordLiteral fields :@ p) = do
  fields <- forM fields \(mult, name, ty, ex) -> do
    ty <- locally id (translateExpression modName ty)
    ex <- locally id (translateExpression modName ex)
    pure (mult, name, ty, ex)
  pure $ IR.ERecordLiteral fields :@ p
translateExpression modName (TAST.ERecordAccess r ty x :@ p) = do
  r <- locally id (translateExpression modName r)
  ty <- locally id (translateExpression modName ty)
  pure $ IR.ERecordAccess r ty x :@ p
