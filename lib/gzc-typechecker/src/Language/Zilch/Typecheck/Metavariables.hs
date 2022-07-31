module Language.Zilch.Typecheck.Metavariables where

import Data.IORef (IORef, newIORef, readIORef)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Located (Position)
import Language.Zilch.Syntax.Core.AST (HoleLocation)
import Language.Zilch.Typecheck.Core.AST (Path)
import Language.Zilch.Typecheck.Core.Eval (MetaEntry)
import System.IO.Unsafe (unsafeDupablePerformIO)

nextMeta :: IORef Int
nextMeta = unsafeDupablePerformIO $ newIORef 0
{-# NOINLINE nextMeta #-}

mcxt :: IORef (IntMap (MetaEntry, Path, Position, HoleLocation))
mcxt = unsafeDupablePerformIO $ newIORef mempty
{-# NOINLINE mcxt #-}

lookupMeta :: Int -> (MetaEntry, Path, Position, HoleLocation)
lookupMeta m = unsafeDupablePerformIO $ do
  ms <- readIORef mcxt
  case IntMap.lookup m ms of
    Just e -> pure e
    Nothing -> error "impossible"
