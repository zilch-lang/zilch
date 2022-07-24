{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Zilch.Typecheck.Elaborator where

import Control.Monad.Except (MonadError)
import Control.Monad.Fix (MonadFix)
import Data.Located (Located)
import Error.Diagnose (Diagnostic)
import GHC.Stack (HasCallStack)
import qualified Language.Zilch.Syntax.Core.AST as AST
import qualified Language.Zilch.Typecheck.Core.AST as TAST
import Language.Zilch.Typecheck.Errors (ElabError, ElabWarning)
import Control.Monad.Writer (MonadWriter)

type MonadElab m = (HasCallStack, MonadError ElabError m, MonadFix m, MonadWriter [ElabWarning] m)

elabProgram :: Located AST.Module -> Either (Diagnostic String) (Located TAST.Module, Diagnostic String)
