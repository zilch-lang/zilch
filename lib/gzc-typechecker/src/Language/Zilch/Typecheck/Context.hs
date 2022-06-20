{-# LANGUAGE BangPatterns #-}

module Language.Zilch.Typecheck.Context where

import Data.Functor ((<&>))
import Data.Located (Located ((:@)))
import Data.Text (Text)
import Language.Zilch.Typecheck.Core.AST (Binding (Bound, Defined))
import Language.Zilch.Typecheck.Core.Eval (DeBruijnLvl (Lvl), Environment, Name, Value (VVariable))
import Language.Zilch.Typecheck.Core.Usage (Usage)
import qualified Language.Zilch.Typecheck.Environment as Env

data Origin = Source | Inserted
  deriving (Show, Eq)

data Context = Context
  { -- | The evaluation environment
    env :: Environment,
    -- | Known types for name lookup
    types :: [(Usage, Text, Origin, Located Value)],
    -- | Current DeBruijn level for unification
    lvl :: DeBruijnLvl,
    -- | Bindings
    bds :: [Binding]
  }

emptyContext :: Context
emptyContext = Context mempty mempty (Lvl 0) []

indexContext :: Context -> Located Name -> Usage
indexContext ctx (x :@ _) = go (types ctx)
  where
    go [] = error "impossible"
    go ((usage, y, _, _) : _) | y == x = usage
    go (_ : ts) = go ts

setContext :: Context -> Name -> Usage -> Context
setContext ctx x usage = Context (env ctx) (go (types ctx)) (lvl ctx) (bds ctx)
  where
    go [] = []
    go ((u, y, origin, ty) : tys)
      | x == y = (usage, y, origin, ty) : go tys
      | otherwise = (u, y, origin, ty) : go tys

unbind :: Context -> Context
unbind (Context (_ : env) (_ : tys) lvl (_ : bds)) = Context env tys (lvl - 1) bds

-- | Extend the context with a bound variable (that is, a variable found next to a @lam@).
bind :: Usage -> Located Name -> Located Value -> Context -> Context
bind usage (x :@ p) ty ctx =
  let level = lvl ctx
   in ctx
        { env = Env.extend (env ctx) (VVariable (x :@ p) level :@ p),
          types = (usage, x, Source, ty) : types ctx,
          lvl = level + 1,
          bds = Bound x : bds ctx
        }

insertBinder :: Usage -> Located Name -> Located Value -> Context -> Context
insertBinder usage (x :@ p) typ ctx =
  let level = lvl ctx
   in ctx
        { env = Env.extend (env ctx) (VVariable (x :@ p) level :@ p),
          types = (usage, x, Inserted, typ) : types ctx,
          lvl = level + 1,
          bds = Bound x : bds ctx
        }

-- | Extend the context with a new value definition.
define :: Usage -> Located Name -> Located Value -> Located Value -> Context -> Context
define usage (f :@ _) val ty ctx =
  ctx
    { env = Env.extend (env ctx) val,
      types = (usage, f, Source, ty) : types ctx,
      lvl = lvl ctx + 1,
      bds = Defined f : bds ctx
    }

scale :: Context -> Usage -> Context
scale (Context env types lvl bds) pi = Context env types' lvl bds
  where
    types' = types <&> \(usage, name, origin, ty) -> (pi * usage, name, origin, ty)

union :: Context -> Context -> Context
union (Context env1 tys1 lvl1 bds1) (Context env2 tys2 lvl2 bds2)
  | length env1 == length env2 && length tys1 == length tys2 && lvl1 == lvl2 && bds1 == bds2 =
    let tys = go tys1 tys2
     in Context env1 tys lvl1 bds1
  where
    go :: [(Usage, Text, Origin, Located Value)] -> [(Usage, Text, Origin, Located Value)] -> [(Usage, Text, Origin, Located Value)]
    go [] [] = []
    go ((u1, name1, origin1, ty1) : env1) ((u2, name2, origin2, ty2) : env2)
      | name1 == name2 =
        let tys = go env1 env2
         in (u1 + u2, name1, origin1, ty1) : tys
    go _ _ = error "inconsistent contexts"
union _ _ = error "inconsistent contexts"
