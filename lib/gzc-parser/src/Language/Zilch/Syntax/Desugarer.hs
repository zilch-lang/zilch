{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}

module Language.Zilch.Syntax.Desugarer (runDesugarer) where

import Control.Monad.State.Strict (MonadState, evalStateT, modify, get)
import Data.HashMap.Strict (HashMap)
import Data.Text (Text)
import qualified Language.Zilch.Core.ConcreteSyntaxTree as CST
import qualified Language.Zilch.Core.AbstractSyntaxTree as AST
import Text.Diagnose (Diagnostic, (<++>), diagnostic)
import Control.Monad.Except (MonadError, runExcept, throwError)
import Language.Zilch.Syntax.Errors (DesugarerError (ConflictingFixitySpecifiers, AliasedOperatorInImport), fromDesugarerError)
import Data.Bifunctor (first)
import qualified Data.HashMap.Strict as H
import Control.Monad (void, forM, when)
import Data.Located (Located((:@)), unwrapLocated)
import Data.Maybe (catMaybes)
import Data.Functor ((<&>))
import Data.Foldable (foldl')
import Language.Zilch.Syntax.Internal (qualIdentToModuleName)
import qualified Data.Text as Text
import Data.Char (isSymbol, isPunctuation)
import Debug.Trace (trace, traceShow)
import Control.Applicative (liftA2)

type Desugarer m = (MonadState DesugarerState m, MonadError DesugarerError m)

data DesugarerState
  = DesugarerState
      (HashMap Text (HashMap CST.Identifier CST.Fixity))  -- ^ Operator fixities per module

instance Semigroup DesugarerState where
  DesugarerState m1 <> DesugarerState m2 = DesugarerState (m1 <> m2)

instance Monoid DesugarerState where
  mempty = DesugarerState mempty


runDesugarer :: [Text] -> HashMap Text CST.Module -> Either (Diagnostic [] String Char) (HashMap Text AST.Module)
runDesugarer topsort mods = first toDiagnostic . runExcept $ evalStateT (exploreModules mods *> desugarModules topsort mods) mempty
  where
    toDiagnostic = (<++>) diagnostic . fromDesugarerError

exploreModules :: Desugarer m => HashMap Text CST.Module -> m ()
exploreModules = void . H.traverseWithKey exploreModule

-- | Registers the fixity of all defined operators in the module.
exploreModule :: Desugarer m => Text -> CST.Module -> m ()
exploreModule modName (CST.Module _ _ decls) = do
  fixs <- H.fromList . catMaybes <$> forM decls \ ((!specs, !decl) :@ _) -> case decl of
    CST.Def (CST.Decl _ (name :@ _) _ _ _) _ _ :@ _ ->
      case extractFixity <$> filter isFixitySpec specs of
        []  -> pure Nothing
        [f] -> pure $ Just (name, unwrapLocated f)
        fs  -> throwError (ConflictingFixitySpecifiers $ fs <&> \ (f :@ p) -> (p, f))
    _                                               -> pure Nothing
  modify \ (DesugarerState m) -> DesugarerState (H.insert modName fixs m)
  where
    isFixitySpec (CST.OpFix _ :@ _) = True
    isFixitySpec _                  = False

    extractFixity (CST.OpFix f :@ p) = f :@ p
    extractFixity _                  = undefined

desugarModules :: Desugarer m => [Text] -> HashMap Text CST.Module -> m (HashMap Text AST.Module)
desugarModules ms mods = foldMapM (\ m -> H.singleton m <$> desugarModule (mods H.! m)) ms
  where
    foldMapM :: (Traversable t, Applicative f, Monoid m) => (a -> f m) -> t a -> f m
    foldMapM f l = foldl' (<>) mempty <$> traverse f l

desugarModule :: Desugarer m => CST.Module -> m AST.Module
desugarModule (CST.Module exportList imports declarations) = do
  -- TODO:
  -- 3. desugar all top-level bindings

  (modImports, operatorFixities) <- unzip <$> forM imports \ (CST.Import open m@(modName :@ p1) qual importedDefs :@ p) -> do
    DesugarerState st <- get
    let modN = qualIdentToModuleName modName :@ p1

    ops <- case importedDefs of
      Nothing -> pure mempty
      Just ds -> H.fromList <$> flip mapMaybeM ds \ (CST.ImportList _(d :@ p) a :@ _) -> do
        case a of
          Nothing        -> pure ()
          Just (op :@ _) -> when (isOperator d && isOperator op) do
            throwError (AliasedOperatorInImport (qualIdentToModuleName d) (qualIdentToModuleName op) p)

        pure $ (d, ) <$> st H.! unwrapLocated modN H.!? d

    pure (AST.Import open m qual (desugarImportList <$> importedDefs) {- TODO -} :@ p, ops)

  let modHeader = AST.ModHead (desugarExportList <$> exportList) modImports

  pure (AST.Module modHeader mempty)
  where
    mapMaybeM f l = catMaybes <$> traverse f l
    {-# INLINE mapMaybeM #-}

    desugarExportList = fmap \ (CST.Export iety name :@ _) -> (desugarIEType <$> iety, name)

    desugarImportList = fmap \ (CST.ImportList iety modN alias :@ _) -> (desugarIEType <$> iety, modN, alias)

    desugarIEType CST.ModuleIE = AST.ModuleIE
    desugarIEType CST.TypeIE   = AST.TypeIE
    desugarIEType CST.EffectIE = AST.EffectIE

isOperator :: CST.Identifier -> Bool
isOperator (_, ident) = Text.any (liftA2 (||) isSymbol isPunctuation) ident
