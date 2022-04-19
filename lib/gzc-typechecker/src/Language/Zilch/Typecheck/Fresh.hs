module Language.Zilch.Typecheck.Fresh (fresh) where

import qualified Data.HashMap as Hash
import Data.IORef (IORef, modifyIORef', newIORef, readIORef)
import Data.Text (Text)
import qualified Data.Text as Text
import Language.Zilch.Typecheck.Core.Eval
import System.IO.Unsafe (unsafeDupablePerformIO)

-- | An internal counter for generating fresh names.
counter :: IORef Integer
counter = unsafeDupablePerformIO $ newIORef 0
{-# NOINLINE counter #-}

-- | Generate a new name from a given prefix, which does not occur in the list of known names.
fresh :: Environment -> Text -> Text
fresh names prefix =
  let newName = mappend prefix . Text.pack . show $ unsafeDupablePerformIO do
        val <- readIORef counter
        modifyIORef' counter (+ 1)
        pure val
   in if newName `Hash.member` names
        then fresh names prefix
        else newName
