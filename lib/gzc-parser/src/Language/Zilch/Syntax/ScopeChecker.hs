{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Syntax.ScopeChecker where

import Control.Monad.IO.Class (MonadIO)
import qualified Language.Zilch.Core.ConcreteSyntaxTree as CST
import Control.Monad.State.Strict (MonadState, evalStateT)
import Data.HashMap.Strict (HashMap)


type ScopeChecker m = (MonadIO m, MonadState (HashMap String CST.Module) m)


runScopeChecker :: MonadIO m => CST.Module -> m CST.Module
runScopeChecker mod = evalStateT (checkModule mod) iState
  where iState = mempty

checkModule :: ScopeChecker m => CST.Module -> m CST.Module
checkModule = pure
