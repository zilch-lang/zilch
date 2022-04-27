{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Zilch.Typecheck.Unification where

import Data.Located (Located)
import Language.Zilch.Typecheck.Context (Context)
import Language.Zilch.Typecheck.Core.Eval (Value)
import {-# SOURCE #-} Language.Zilch.Typecheck.Elaborator (MonadElab)

unify :: forall m. MonadElab m => Context -> Located Value -> Located Value -> m ()
