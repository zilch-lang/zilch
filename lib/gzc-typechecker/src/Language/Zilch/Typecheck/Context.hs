{-# LANGUAGE BangPatterns #-}

module Language.Zilch.Typecheck.Context where

import Data.Functor ((<&>))
import Data.Located (Located ((:@)))
import Data.Text (Text)
import Language.Zilch.Typecheck.Core.AST (Binding (Bound, Defined), Usage)
import Language.Zilch.Typecheck.Core.Eval (DeBruijnLvl (Lvl), Environment, Name, Value (VVariable))
import qualified Language.Zilch.Typecheck.Environment as Env

data Context = Context
  { -- | The evaluation environment
    env :: Environment,
    -- | Known types for name lookup
    types :: [(Usage, Text, Located Value)],
    -- | Current DeBruijn level for unification
    lvl :: DeBruijnLvl,
    -- | Bindings
    bds :: [Binding]
  }

emptyContext :: Context
emptyContext = Context mempty mempty (Lvl 0) []

-- | Extend the context with a bound variable (that is, a variable found next to a @lam@).
bind :: Usage -> Located Name -> Located Value -> Context -> Context
bind usage (x :@ p) ty ctx =
  let level = lvl ctx
   in ctx
        { env = Env.extend (env ctx) (VVariable (x :@ p) level :@ p),
          types = (usage, x, ty) : types ctx,
          lvl = level + 1,
          bds = Bound x : bds ctx
        }

-- | Extend the context with a new value definition.
define :: Usage -> Located Name -> Located Value -> Located Value -> Context -> Context
define usage (f :@ _) val ty ctx =
  ctx
    { env = Env.extend (env ctx) val,
      types = (usage, f, ty) : types ctx,
      lvl = lvl ctx + 1,
      bds = Defined f : bds ctx
    }

scale :: Context -> Usage -> Context
scale (Context env types lvl bds) pi = Context env types' lvl bds
  where
    types' = types <&> \(usage, name, ty) -> (pi * usage, name, ty)

union :: Context -> Context -> Context
union (Context env1 tys1 lvl1 bds1) (Context env2 tys2 lvl2 bds2)
  | length env1 == length env2 && length tys1 == length tys2 && lvl1 == lvl2 && bds1 == bds2 =
    let tys = go tys1 tys2
     in Context env1 tys lvl1 bds1
  where
    go :: [(Usage, Text, Located Value)] -> [(Usage, Text, Located Value)] -> [(Usage, Text, Located Value)]
    go [] [] = []
    go ((u1, name1, ty1) : env1) ((u2, name2, ty2) : env2)
      | name1 == name2 =
        let tys = go env1 env2
         in (u1 + u2, name1, ty1) : tys
    go _ _ = error "inconsistent contexts"
union _ _ = error "inconsistent contexts"
