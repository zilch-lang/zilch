{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Zilch.Typecheck.Checker where

import Data.Located (Located)
import Language.Zilch.Syntax.Core.AST (Expression, Module)
import Language.Zilch.Typecheck.Context (Context)
import Language.Zilch.Typecheck.Core.Eval (Environment, Value)
import {-# SOURCE #-} Language.Zilch.Typecheck.Elaborator (MonadElab)

checkProgram :: forall m. MonadElab m => Environment -> Context -> Located Module -> m ()
check :: forall m. MonadElab m => Environment -> Context -> Located Expression -> Located Value -> m ()
