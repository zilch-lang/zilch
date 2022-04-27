{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Typecheck.Elaborator (elabProgram, MonadElab) where

import Control.Monad.Except (MonadError, runExcept)
import Data.Bifunctor (first)
import Data.Located (Located)
import Error.Diagnose (Diagnostic, addReport, def)
import qualified Language.Zilch.Syntax.Core.AST as AST
import Language.Zilch.Typecheck.Checker (checkProgram)
import qualified Language.Zilch.Typecheck.Core.AST as TAST
import Language.Zilch.Typecheck.Defaults
import Language.Zilch.Typecheck.Errors

type MonadElab m = (MonadError ElabError m)

-------------

elabProgram :: Located AST.Module -> Either (Diagnostic String) (Located TAST.Module)
elabProgram mod = first toDiagnostic . runExcept $ checkProgram defaultContext mod

toDiagnostic :: ElabError -> Diagnostic String
toDiagnostic = addReport def . fromElabError
