{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoOverloadedLists #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Optimize.ArgumentTuplingAnalysis where

import Control.Applicative (liftA2)
import Control.Monad (forM, forM_)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.State (MonadState, evalStateT, gets, modify)
import Data.Located (Located (..))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Traversable (for)
import Debug.Trace (traceShow)
import Language.Zilch.CLI.Flags (Flags, debug, doDump', dumpArities)
import Language.Zilch.Optimize.Internal.PrettyArityTable ()
import Language.Zilch.Optimize.Internal.Type
import Language.Zilch.Typecheck.ANF
import Prettyprinter (pretty)

tupleArguments :: Optimizer
tupleArguments flags (path, name, mod) = do
  mod <- evalStateT (optimize flags mod) mempty
  pure (path, name, mod)

type MonadOptimizer m = (MonadState (Map [Located Text] Integer) m, MonadIO m)

optimize :: MonadOptimizer m => Flags -> Located Module -> m (Located Module)
optimize flags mod = do
  gatherAllIdentifiers mod

  let Module defs :@ _ = mod
  partialArities <-
    Map.fromListWith min
      . mconcat
      <$> for defs \(TopLevel _ (Let _ _ _ _ e :@ _) :@ _) -> analyseArities e
  liftIO $ doDumpArities flags partialArities

  undefined

analyseArities :: MonadOptimizer m => Located Expression -> m [([Located Text], Integer)]
analyseArities ex = do
  ids <- gets Map.keys

  forM ids \i -> do
    arityI <- gets (Map.! i)
    minArity <- fmap (max 0 . min arityI) <$> nbCalls i ex

    pure (i, fromMaybe arityI minArity)

nbCalls :: MonadOptimizer m => [Located Text] -> Located Expression -> m (Maybe Integer)
nbCalls _ (EType :@ _) = pure Nothing
nbCalls f (EIdentifier g :@ _)
  | f == g = pure $ Just 0
  | otherwise = pure Nothing
nbCalls _ (EInteger _ _ :@ _) = pure Nothing
nbCalls _ (ECharacter _ :@ _) = pure Nothing
nbCalls _ (EBuiltin _ :@ _) = pure Nothing
nbCalls _ (EBoolean _ :@ _) = pure Nothing
nbCalls _ (EOne :@ _) = pure Nothing
nbCalls _ (ETop :@ _) = pure Nothing
nbCalls _ (EFst _ :@ _) = pure Nothing
nbCalls _ (ESnd _ :@ _) = pure Nothing
nbCalls f (EIfThenElse _ t e :@ _) = do
  nbCallsT <- nbCalls f t
  nbCallsE <- nbCalls f e
  case (nbCallsT, nbCallsE) of
    (Nothing, Nothing) -> pure Nothing
    (Just a, Nothing) -> pure $ Just a
    (Nothing, Just a) -> pure $ Just a
    (Just a1, Just a2) -> pure $ Just $ min a1 a2
nbCalls f (EApplication (EIdentifier g :@ _) args :@ _)
  | f == g = pure . Just . toInteger $ length args
nbCalls _ (EApplication _ _ :@ _) = pure Nothing
nbCalls _ (EAdditivePair _ :@ _) = pure Nothing
nbCalls _ (EMultiplicativePair _ :@ _) = pure Nothing
nbCalls f (ELam _ e :@ _) = nbCalls f e
nbCalls f (EPi _ e :@ _) = nbCalls f e
nbCalls _ (EAdditiveProduct _ _ :@ _) = pure Nothing
nbCalls _ (EMultiplicativeProduct _ _ :@ _) = pure Nothing
nbCalls f (ELet (Let _ _ h _ (EApplication (EIdentifier g :@ _) args :@ _) :@ _) e :@ _)
  | f == g = do
      nbCallsHE <- fmap (+ toInteger (length args)) <$> nbCalls h e
      nbCallsFE <- nbCalls f e
      case (nbCallsHE, nbCallsFE) of
        (Nothing, Nothing) -> pure Nothing
        (Just a, Nothing) -> pure $ Just a
        (Nothing, Just a) -> pure $ Just a
        (Just a1, Just a2) -> pure $ Just $ min a1 a2
nbCalls f (ELet (Let _ _ _ _ e1 :@ _) e2 :@ _) = do
  nbCallsE1 <- nbCalls f e1
  nbCallsE2 <- nbCalls f e2
  case (nbCallsE1, nbCallsE2) of
    (Nothing, Nothing) -> pure Nothing
    (Just a, Nothing) -> pure $ Just a
    (Nothing, Just a) -> pure $ Just a
    (Just a1, Just a2) -> pure $ Just $ min a1 a2
nbCalls f (EMultiplicativePairElim _ _ _ (EApplication (EIdentifier g :@ _) args :@ _) e :@ _)
  | f == g = fmap (min (toInteger $ length args)) <$> nbCalls f e
nbCalls f (EMultiplicativePairElim _ _ _ _ e :@ _) = nbCalls f e
nbCalls _ (EComposite _ :@ _) = pure Nothing
nbCalls _ (ERecordLiteral _ :@ _) = pure Nothing
nbCalls _ (ERecordAccess _ _ :@ _) = pure Nothing

gatherAllIdentifiers :: MonadOptimizer m => Located Module -> m ()
gatherAllIdentifiers (Module defs :@ _) = forM_ defs \(TopLevel _ (Let _ _ name ty e :@ _) :@ _) -> do
  let arity = deriveArityFromType ty
  modify (Map.insert name arity)

  insertLocalArity e
  where
    insertLocalArity :: MonadOptimizer m => Located Expression -> m ()
    insertLocalArity (EType :@ _) = pure ()
    insertLocalArity (EIdentifier _ :@ _) = pure ()
    insertLocalArity (EInteger _ _ :@ _) = pure ()
    insertLocalArity (ECharacter _ :@ _) = pure ()
    insertLocalArity (EBuiltin _ :@ _) = pure ()
    insertLocalArity (EBoolean _ :@ _) = pure ()
    insertLocalArity (EOne :@ _) = pure ()
    insertLocalArity (ETop :@ _) = pure ()
    insertLocalArity (EFst _ :@ _) = pure ()
    insertLocalArity (ESnd _ :@ _) = pure ()
    insertLocalArity (EIfThenElse _ t e :@ _) = do
      insertLocalArity t
      insertLocalArity e
    insertLocalArity (EApplication _ _ :@ _) = pure ()
    insertLocalArity (EAdditivePair _ :@ _) = pure ()
    insertLocalArity (EMultiplicativePair _ :@ _) = pure ()
    insertLocalArity (ELam _ e :@ _) = insertLocalArity e
    insertLocalArity (EPi _ e :@ _) = insertLocalArity e
    insertLocalArity (EAdditiveProduct _ _ :@ _) = pure ()
    insertLocalArity (EMultiplicativeProduct _ _ :@ _) = pure ()
    insertLocalArity (ELet (Let _ _ name ty _ :@ _) e :@ _) = do
      let arity = deriveArityFromType ty
      modify (Map.insert name arity)

      insertLocalArity e
    insertLocalArity (EMultiplicativePairElim _ _ _ _ e :@ _) = insertLocalArity e
    insertLocalArity (EComposite _ :@ _) = pure ()
    insertLocalArity (ERecordLiteral _ :@ _) = pure ()
    insertLocalArity (ERecordAccess _ _ :@ _) = pure ()

deriveArityFromType :: Located Expression -> Integer
deriveArityFromType (EType :@ _) = 0
deriveArityFromType (EIdentifier _ :@ _) = 0
deriveArityFromType (EInteger _ _ :@ _) = 0
deriveArityFromType (ECharacter _ :@ _) = 0
deriveArityFromType (EBuiltin _ :@ _) = 0
deriveArityFromType (EBoolean _ :@ _) = 0
deriveArityFromType (EOne :@ _) = 0
deriveArityFromType (ETop :@ _) = 0
deriveArityFromType (EFst _ :@ _) = 0
deriveArityFromType (ESnd _ :@ _) = 0
deriveArityFromType (EIfThenElse _ t e :@ _) = min (deriveArityFromType t) (deriveArityFromType e)
deriveArityFromType (EApplication _ _ :@ _) = 0
deriveArityFromType (EAdditivePair _ :@ _) = 0
deriveArityFromType (EMultiplicativePair _ :@ _) = 0
deriveArityFromType (ELam _ e :@ _) = 1 + deriveArityFromType e
deriveArityFromType (EPi _ e :@ _) = 1 + deriveArityFromType e
deriveArityFromType (EAdditiveProduct _ _ :@ _) = 0
deriveArityFromType (EMultiplicativeProduct _ _ :@ _) = 0
deriveArityFromType (ELet _ e :@ _) = deriveArityFromType e
deriveArityFromType (EMultiplicativePairElim _ _ _ _ e :@ _) = deriveArityFromType e
deriveArityFromType (EComposite _ :@ _) = 0
deriveArityFromType (ERecordLiteral _ :@ _) = 0
deriveArityFromType (ERecordAccess _ _ :@ _) = 0

doDumpArities :: Flags -> Map [Located Text] Integer -> IO ()
doDumpArities flags arityTable = doDump' flags "arities.tbl" (dumpArities . debug) (pretty arityTable)
