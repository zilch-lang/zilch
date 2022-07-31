{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Typecheck.Elaborator (elabProgram, MonadElab) where

import Control.Monad.Except (MonadError, runExcept)
import Control.Monad.Fix (MonadFix)
import Control.Monad.State (MonadState, evalStateT)
import Control.Monad.Writer (MonadWriter, runWriterT)
import Data.Bifunctor (bimap, second)
import Data.IntMap (IntMap)
import Data.List (foldl', nub)
import Data.Located (Located, Position)
import Error.Diagnose (Diagnostic, addReport, def)
import GHC.Stack (HasCallStack)
import qualified Language.Zilch.Syntax.Core.AST as AST
import Language.Zilch.Typecheck.Checker (checkProgram)
import qualified Language.Zilch.Typecheck.Core.AST as TAST
import Language.Zilch.Typecheck.Core.Eval (MetaEntry)
import Language.Zilch.Typecheck.Defaults
import Language.Zilch.Typecheck.Errors

type MetaContext = (Int, IntMap (MetaEntry, TAST.Path, Position, AST.HoleLocation))

type MonadElab m = (HasCallStack, MonadError ElabError m, MonadFix m, MonadWriter [ElabWarning] m, MonadState MetaContext m)

-------------

elabProgram :: Located AST.Module -> Either (Diagnostic String) (Located TAST.Module, Diagnostic String)
elabProgram mod = bimap errToDiagnostic warnToDiagnostic . runExcept . flip evalStateT (0, mempty) . runWriterT $ checkProgram defaultContext mod

errToDiagnostic :: ElabError -> Diagnostic String
errToDiagnostic = addReport def . fromElabError

warnToDiagnostic :: (Located TAST.Module, [ElabWarning]) -> (Located TAST.Module, Diagnostic String)
warnToDiagnostic = second toDiag
  where
    toDiag = foldl' addReport def . fmap fromElabWarning . nub
