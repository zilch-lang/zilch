{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module Language.Zilch.Syntax.Desugarer where

import Control.Monad.Except (MonadError, runExcept)
import Control.Monad.State (MonadState, evalStateT)
import Control.Monad.Writer (MonadWriter, runWriterT)
import Data.Bifunctor (bimap, second)
import Data.List (foldl')
import Data.Located (Located ((:@)))
import Error.Diagnose (Diagnostic, addReport, def)
import qualified Language.Zilch.Syntax.Core.AST as AST
import qualified Language.Zilch.Syntax.Core.CST as CST
import Language.Zilch.Syntax.Errors

type MonadDesugar m = (MonadError DesugarError m, MonadWriter [DesugarWarning] m, MonadState () m)

desugarCST :: Located CST.Module -> Either (Diagnostic String) (Located AST.Module, Diagnostic String)
desugarCST mod =
  bimap toErrorDiagnostic (second toWarningDiagnostic) $
    runExcept $
      runWriterT $
        evalStateT (desugarModule mod) ()
  where
    toErrorDiagnostic err = addReport def (fromDesugarerError err)
    toWarningDiagnostic warns = foldl' addReport def (fromDesugarerWarning <$> warns)

-----------------

desugarModule :: forall m. MonadDesugar m => Located CST.Module -> m (Located AST.Module)
desugarModule (CST.Mod _ _ :@ p) = do
  pure $ AST.Mod [] [] :@ p
