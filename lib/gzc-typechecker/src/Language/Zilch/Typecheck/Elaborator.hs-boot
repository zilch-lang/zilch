{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Zilch.Typecheck.Elaborator where

import Control.Monad.Except (MonadError)
import Data.Located (Located)
import Error.Diagnose (Diagnostic)
import Language.Zilch.Syntax.Core.AST (Expression, Module)
import Language.Zilch.Typecheck.Context (Context)
import Language.Zilch.Typecheck.Core.Eval (Environment)
import Language.Zilch.Typecheck.Errors (ElabError)

type MonadElab m = (MonadError ElabError m)

elabProgram :: Located Module -> Either (Diagnostic String) (Located Module)
elab :: Environment -> Context -> Located Expression -> Either (Diagnostic String) (Located Expression)
elab0 :: Located Expression -> Either (Diagnostic String) (Located Expression)
