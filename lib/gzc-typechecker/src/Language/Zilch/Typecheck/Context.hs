{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Typecheck.Context where

import Data.Located (Located ((:@)), unLoc)
import Data.Text (Text)
import qualified Data.Text as Text
import GHC.Stack (HasCallStack)
import Language.Zilch.Typecheck.Core.AST (Binding (Bound, Defined))
import Language.Zilch.Typecheck.Core.Eval (DeBruijnLvl (Lvl), Environment, Name, Value (VVariable))
import Language.Zilch.Typecheck.Core.Multiplicity (Multiplicity)
import qualified Language.Zilch.Typecheck.Environment as Env

data Origin = Source | Inserted
  deriving (Show, Eq)

data Context = Context
  { -- | The evaluation environment
    env :: Environment,
    -- | Known types for name lookup
    types :: [(Multiplicity, Located Text, Origin, Located Value)],
    -- | Current DeBruijn level for unification
    lvl :: DeBruijnLvl,
    -- | Bindings
    bds :: [Binding]
  }

emptyContext :: Context
emptyContext = Context mempty mempty (Lvl 0) []

indexContext :: HasCallStack => Context -> Located Name -> (Multiplicity, Located Text, Located Value)
indexContext ctx x = go (types ctx)
  where
    go [] = error $ "impossible: cannot access variable named " <> Text.unpack (unLoc x) <> " in context"
    go ((usage, y, _, ty) : _) | y == x = (usage, y, ty)
    go (_ : ts) = go ts

setContext :: Context -> Located Name -> Multiplicity -> Context
setContext ctx x usage = Context (env ctx) (go (types ctx)) (lvl ctx) (bds ctx)
  where
    go [] = []
    go ((u, y, origin, ty) : tys)
      | x == y = (usage, y, origin, ty) : go tys
      | otherwise = (u, y, origin, ty) : go tys

-- | Extend the context with a bound variable (that is, a variable found next to a @lam@).
bind :: Multiplicity -> Located Name -> Located Value -> Context -> Context
bind usage x@(_ :@ p) ty ctx =
  let level = lvl ctx
   in ctx
        { env = Env.extend (env ctx) (VVariable x level :@ p),
          types = (usage, x, Source, ty) : types ctx,
          lvl = level + 1,
          bds = Bound (unLoc x) : bds ctx
        }

insertBinder :: Multiplicity -> Located Name -> Located Value -> Context -> Context
insertBinder usage x@(_ :@ p) typ ctx =
  let level = lvl ctx
   in ctx
        { env = Env.extend (env ctx) (VVariable x level :@ p),
          types = (usage, x, Inserted, typ) : types ctx,
          lvl = level + 1,
          bds = Bound (unLoc x) : bds ctx
        }

-- | Extend the context with a new value definition.
define :: Multiplicity -> Located Name -> Located Value -> Located Value -> Context -> Context
define usage f val ty ctx =
  ctx
    { env = Env.extend (env ctx) val,
      types = (usage, f, Source, ty) : types ctx,
      lvl = lvl ctx + 1,
      bds = Defined (unLoc f) : bds ctx
    }
