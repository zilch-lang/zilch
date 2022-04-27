{-# LANGUAGE BangPatterns #-}

module Language.Zilch.Typecheck.Context where

import qualified Data.HashMap as Hash
import Data.IORef (IORef, modifyIORef', newIORef, readIORef, writeIORef)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Located (Located ((:@)), Position, unLoc)
import Data.Text (Text)
import qualified Data.Text as Text
import Debug.Trace (trace)
import Language.Zilch.Typecheck.Core.AST (Expression (EInsertedMeta), MetaStatus (Bound, Defined))
import Language.Zilch.Typecheck.Core.Eval (DeBruijnLvl (Lvl), Environment, MetaEntry (Unsolved), Name, Value (VIdentifier))
import qualified Language.Zilch.Typecheck.Environment as Env
import System.IO.Unsafe (unsafeDupablePerformIO)

data Context = Context
  { -- | The evaluation environment
    env :: Environment,
    -- | Known types for name lookup
    types :: [(Text, Located Value)],
    -- | Current DeBruijn level for unification
    lvl :: DeBruijnLvl,
    -- | Creation of fresh meta variable
    bds :: [MetaStatus]
  }

-- | The current meta context
mctx :: IORef (IntMap MetaEntry)
mctx = unsafeDupablePerformIO $ newIORef mempty

emptyContext :: Context
emptyContext = Context mempty mempty (Lvl 0) mempty

-- | Extend the context with a bound variable (that is, a variable found next to a @lam@).
bind :: Located Name -> Located Value -> Context -> Context
bind (x :@ p) ty ctx =
  let level = lvl ctx
   in ctx
        { env = Env.extend (env ctx) (VIdentifier level [] :@ p),
          types = (x, ty) : types ctx,
          lvl = level + 1,
          bds = Bound : bds ctx
        }

-- | Extend the context with a new value definition.
define :: Located Name -> Located Value -> Located Value -> Context -> Context
define (f :@ _) val ty ctx =
  ctx
    { env = Env.extend (env ctx) val,
      types = (f, ty) : types ctx,
      lvl = lvl ctx + 1,
      bds = Defined : bds ctx
    }

lookupMeta :: Int -> MetaEntry
lookupMeta name = unsafeDupablePerformIO $ (IntMap.! name) <$> readIORef mctx

-- | An internal counter for generating fresh names.
counter :: IORef Int
counter = unsafeDupablePerformIO $ newIORef 0
{-# NOINLINE counter #-}

-- | Generate a new name for a new metavariable.
freshMeta :: Context -> Position -> Located Expression
freshMeta ctx p =
  let idx = unsafeDupablePerformIO do
        val <- readIORef counter
        writeIORef counter $! val + 1
        pure val

      !() = unsafeDupablePerformIO $ modifyIORef' mctx (IntMap.insert idx Unsolved)
   in EInsertedMeta (idx :@ p) (bds ctx) :@ p

setMeta :: Int -> MetaEntry -> ()
setMeta idx entry = unsafeDupablePerformIO $ modifyIORef' mctx (IntMap.insert idx entry)

metas :: () -> [(Int, MetaEntry)]
metas () = unsafeDupablePerformIO $ IntMap.toList <$> readIORef mctx
