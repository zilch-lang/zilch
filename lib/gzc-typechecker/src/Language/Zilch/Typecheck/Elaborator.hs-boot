{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Typecheck.Elaborator (elabProgram, MonadElab) where

import Control.Monad.Except (MonadError)
import Control.Monad.Fix (MonadFix)
import Control.Monad.State (MonadState)
import Control.Monad.Writer (MonadWriter)
import Data.IntMap (IntMap)
import Data.Located (Located, Position)
import Error.Diagnose (Diagnostic)
import GHC.Stack (HasCallStack)
import qualified Language.Zilch.Syntax.Core.AST as AST
import qualified Language.Zilch.Typecheck.Core.AST as TAST
import Language.Zilch.Typecheck.Core.Eval (MetaEntry)
import Language.Zilch.Typecheck.Errors

type MetaContext = (Int, IntMap (MetaEntry, TAST.Path, Position, AST.HoleLocation))
type MonadElab m = (HasCallStack, MonadError ElabError m, MonadFix m, MonadWriter [ElabWarning] m, MonadState MetaContext m)

-------------

elabProgram :: Located AST.Module -> Either (Diagnostic String) (Located TAST.Module, Diagnostic String)
