{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Zilch.Typecheck.Elaborator (elab, elab0, MonadElab) where

import Control.Monad.Except (MonadError, runExcept)
import Data.Bifunctor (first)
import Data.Located (Located ((:@)))
import Error.Diagnose (Diagnostic, addReport, def)
import Language.Zilch.Syntax.Core.AST (Expression)
import Language.Zilch.Typecheck.Context
import Language.Zilch.Typecheck.Core.Eval (Environment)
import Language.Zilch.Typecheck.Defaults
import Language.Zilch.Typecheck.Errors
import Language.Zilch.Typecheck.Evaluator (plugNormalisation, quote)
import {-# SOURCE #-} Language.Zilch.Typecheck.Synthetizer (synthetize)

type MonadElab m = (MonadError ElabError m)

-------------

elab :: Environment -> Context -> Located Expression -> Either (Diagnostic String) (Located Expression)
elab env ctx expr = first toDiagnostic $ runExcept do
  ty <- synthetize env ctx expr
  plugNormalisation $ quote env ty
  where
    toDiagnostic = addReport def . fromElabError

elab0 :: Located Expression -> Either (Diagnostic String) (Located Expression)
elab0 = elab defaultEnv defaultCtx
{-# INLINE elab0 #-}
