module Language.Zilch.Typecheck.Metavariables where

import Data.IORef (IORef, newIORef, readIORef)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Language.Zilch.Typecheck.Core.Eval (MetaEntry)
import System.IO.Unsafe (unsafeDupablePerformIO)

nextMeta :: IORef Int
nextMeta = unsafeDupablePerformIO $ newIORef 0 -- alternative: ReaderT IO (reader has metacontext)
{-# NOINLINE nextMeta #-}

mcxt :: IORef (IntMap MetaEntry) -- in "production", we'd have mutable array instead of IntMap
mcxt = unsafeDupablePerformIO $ newIORef mempty
{-# NOINLINE mcxt #-}

lookupMeta :: Int -> MetaEntry
lookupMeta m = unsafeDupablePerformIO $ do
  ms <- readIORef mcxt
  case IntMap.lookup m ms of
    Just e -> pure e
    Nothing -> error "impossible"
