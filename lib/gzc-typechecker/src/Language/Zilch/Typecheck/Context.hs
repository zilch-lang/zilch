{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Typecheck.Context where

import Data.Functor ((<&>))
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

scale :: Context -> Multiplicity -> Context
scale (Context env types lvl bds) pi = Context env types' lvl bds
  where
    types' = types <&> \(usage, name, origin, ty) -> (pi * usage, name, origin, ty)

union :: Context -> Context -> Context
union (Context env1 tys1 lvl1 bds1) (Context env2 tys2 lvl2 bds2)
  | length env1 == length env2 && length tys1 == length tys2 && lvl1 == lvl2 && bds1 == bds2 =
    let tys = go tys1 tys2
     in Context env1 tys lvl1 bds1
  where
    go :: [(Multiplicity, Located Text, Origin, Located Value)] -> [(Multiplicity, Located Text, Origin, Located Value)] -> [(Multiplicity, Located Text, Origin, Located Value)]
    go [] [] = []
    go ((u1, name1, origin1, ty1) : env1) ((u2, name2, origin2, ty2) : env2)
      | name1 == name2 =
        let tys = go env1 env2
         in (u1 + u2, name1, origin1, ty1) : tys
    go _ _ = error "inconsistent contexts"
union _ _ = error "inconsistent contexts"
