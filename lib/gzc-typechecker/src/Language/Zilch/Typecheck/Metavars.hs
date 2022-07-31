{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Zilch.Typecheck.Metavars where

import Control.Monad.State (gets, modify')
import Data.Bifunctor (bimap)
import qualified Data.IntMap as IntMap
import Data.Located (Located, Position)
import qualified Language.Zilch.Syntax.Core.AST as AST
import Language.Zilch.Typecheck.Context (Context, path)
import qualified Language.Zilch.Typecheck.Core.AST as TAST
import Language.Zilch.Typecheck.Core.Eval (MetaEntry (..), Value)
import qualified Language.Zilch.Typecheck.Core.Multiplicity as TAST
import {-# SOURCE #-} Language.Zilch.Typecheck.Elaborator (MonadElab)

-- | Generate new fresh metavariables from the context.
freshMeta :: forall m. MonadElab m => Context -> TAST.Multiplicity -> Located Value -> Position -> AST.HoleLocation -> m TAST.Expression
freshMeta ctx mult ty p loc = do
  m <- gets fst
  modify' $ bimap (+ 1) (IntMap.insert m (Unsolved mult ty, path ctx, p, loc))
  pure $ TAST.EInsertedMeta m (path ctx)

lookupMeta :: forall m. MonadElab m => Int -> m (MetaEntry, TAST.Path, Position, AST.HoleLocation)
lookupMeta m = do
  ms <- gets snd
  case IntMap.lookup m ms of
    Just e -> pure e
    Nothing -> error "impossible"
