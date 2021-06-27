{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Zilch.Syntax.Desugarer (runDesugarer) where

import Control.Monad.State.Strict (MonadState, evalStateT)
import Data.HashMap.Strict (HashMap)
import Data.Text (Text)
import qualified Language.Zilch.Core.ConcreteSyntaxTree as CST
import qualified Language.Zilch.Core.AbstractSyntaxTree as AST
import Text.Diagnose (Diagnostic, (<++>), diagnostic)
import Control.Monad.Except (MonadError, runExcept)
import Language.Zilch.Syntax.Errors (DesugarerError, fromDesugarerError)
import Data.Bifunctor (first)

type Desugarer m = (MonadState DesugarerState m, MonadError DesugarerError m)

data DesugarerState
  = DesugarerState
      (HashMap Text (HashMap Text CST.Fixity))  -- ^ Operator fixities per module

instance Semigroup DesugarerState where
  DesugarerState m1 <> DesugarerState m2 = DesugarerState (m1 <> m2)

instance Monoid DesugarerState where
  mempty = DesugarerState mempty


runDesugarer :: [Text] -> HashMap Text CST.Module -> Either (Diagnostic [] String Char) (HashMap Text AST.Module)
runDesugarer topsort mods = first toDiagnostic . runExcept $ evalStateT (desugarModules topsort mods) mempty
  where
    toDiagnostic = (<++>) diagnostic . fromDesugarerError

desugarModules :: Desugarer m => [Text] -> HashMap Text CST.Module -> m (HashMap Text AST.Module)
desugarModules _ _ = pure mempty
