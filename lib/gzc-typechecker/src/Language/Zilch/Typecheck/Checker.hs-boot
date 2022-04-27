{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Zilch.Typecheck.Checker where

import Data.Located (Located)
import qualified Language.Zilch.Syntax.Core.AST as AST (Expression, Module)
import Language.Zilch.Typecheck.Context (Context)
import qualified Language.Zilch.Typecheck.Core.AST as TAST (Expression, Module)
import Language.Zilch.Typecheck.Core.Eval (Environment, Value)
import {-# SOURCE #-} Language.Zilch.Typecheck.Elaborator (MonadElab)

checkProgram :: forall m. MonadElab m => Context -> Located AST.Module -> m (Located TAST.Module)
check :: forall m. MonadElab m => Context -> Located AST.Expression -> Located Value -> m (Located TAST.Expression)
