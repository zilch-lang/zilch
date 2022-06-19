{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Zilch.Typecheck.Synthetizer where

import Data.Located (Located)
import qualified Language.Zilch.Syntax.Core.AST as AST (Expression)
import qualified Language.Zilch.Typecheck.Core.AST as TAST (Expression)
import qualified Language.Zilch.Typecheck.Core.Usage as TAST (Usage)
import Language.Zilch.Typecheck.Context (Context)
import Language.Zilch.Typecheck.Core.Eval (Value)
import {-# SOURCE #-} Language.Zilch.Typecheck.Elaborator (MonadElab)

synthetize :: forall m. MonadElab m => Context -> Located AST.Expression -> m (Context, Located TAST.Expression, Located Value, Located TAST.Usage)
