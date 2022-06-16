{-# LANGUAGE BangPatterns #-}

module Language.Zilch.Typecheck.Context where

import Data.Located (Located ((:@)))
import Data.Text (Text)
import Language.Zilch.Typecheck.Core.AST (Binding (Bound, Defined))
import Language.Zilch.Typecheck.Core.Eval (DeBruijnLvl (Lvl), Environment, Name, Value (VVariable))
import qualified Language.Zilch.Typecheck.Environment as Env

data Context = Context
  { -- | The evaluation environment
    env :: Environment,
    -- | Known types for name lookup
    types :: [(Text, Located Value)],
    -- | Current DeBruijn level for unification
    lvl :: DeBruijnLvl,
    -- | Bindings
    bds :: [Binding]
  }

emptyContext :: Context
emptyContext = Context mempty mempty (Lvl 0) []

-- | Extend the context with a bound variable (that is, a variable found next to a @lam@).
bind :: Located Name -> Located Value -> Context -> Context
bind (x :@ p) ty ctx =
  let level = lvl ctx
   in ctx
        { env = Env.extend (env ctx) (VVariable (x :@ p) level :@ p),
          types = (x, ty) : types ctx,
          lvl = level + 1,
          bds = Bound x : bds ctx
        }

-- | Extend the context with a new value definition.
define :: Located Name -> Located Value -> Located Value -> Context -> Context
define (f :@ _) val ty ctx =
  ctx
    { env = Env.extend (env ctx) val,
      types = (f, ty) : types ctx,
      lvl = lvl ctx + 1,
      bds = Defined f : bds ctx
    }