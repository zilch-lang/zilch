{-# LANGUAGE RankNTypes #-}

module Language.Zilch.Optimize.Internal.Type where

import Control.Monad.IO.Class (MonadIO)
import Data.Located (Located)
import Data.Text (Text)
import Language.Zilch.CLI.Flags (Flags)
import Language.Zilch.Typecheck.ANF (Module)

type Optimizer = forall m. MonadIO m => Flags -> (FilePath, [Located Text], Located Module) -> m (FilePath, [Located Text], Located Module)
