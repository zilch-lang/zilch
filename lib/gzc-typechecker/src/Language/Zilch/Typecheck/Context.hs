{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Typecheck.Context where

import Data.Located (Located ((:@)), unLoc)
import Data.Text (Text)
import qualified Data.Text as Text
import GHC.Stack (HasCallStack)
import Language.Zilch.Typecheck.Core.AST (Path (..))
import Language.Zilch.Typecheck.Core.Eval (DeBruijnLvl (Lvl), Environment, Name, Value (VUndefined, VVariable))
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
    path :: Path
  }
  deriving (Show)

emptyContext :: Context
emptyContext = Context mempty mempty (Lvl 0) Here

indexContext :: HasCallStack => Context -> Located Name -> (Multiplicity, Located Text, Located Value)
indexContext ctx x = go (types ctx)
  where
    go [] = error $ "impossible: cannot access variable named " <> Text.unpack (unLoc x) <> " in context"
    go ((usage, y, _, ty) : _) | y == x = (usage, y, ty)
    go (_ : ts) = go ts

unbind :: Context -> Context
unbind (Context (_ : env) types lvl path') = case (types, path') of
  (_, Here {}) -> undefined
  (_ : types, Bind path _ _ _) -> Context {env, types, lvl = lvl - 1, path}
  (_ : types, Define path _ _ _ _) -> Context {env, types, lvl = lvl - 1, path}

setContext :: Context -> Located Name -> Multiplicity -> Context
setContext ctx x usage = Context (env ctx) (go (types ctx)) (lvl ctx) (path ctx)
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
        { env = Env.extend (env ctx) (VVariable x level ty :@ p),
          types = (usage, x, Source, ty) : types ctx,
          lvl = level + 1,
          path = Bind (path ctx) usage x ty
        }

insertBinder :: Multiplicity -> Located Name -> Located Value -> Context -> Context
insertBinder usage x@(_ :@ p) typ ctx =
  let level = lvl ctx
   in ctx
        { env = Env.extend (env ctx) (VVariable x level typ :@ p),
          types = (usage, x, Inserted, typ) : types ctx,
          lvl = level + 1,
          path = Bind (path ctx) usage x typ
        }

-- | Extend the context with a new value definition.
define :: Multiplicity -> Located Name -> Located Value -> Located Value -> Context -> Context
define usage f val ty ctx =
  -- we need to check if @f@ is already in the context with a value of @VUndefined@
  -- if yes: replace its value
  -- if no: insert in the context as a new binding
  let index = indexOfUndefined (lvl ctx) (env ctx) (types ctx)
   in case index of
        Nothing ->
          ctx
            { env = Env.extend (env ctx) val,
              types = (usage, f, Source, ty) : types ctx,
              lvl = lvl ctx + 1,
              path = Define (path ctx) usage f ty val
            }
        Just idx -> ctx {env = replaceAt (lvl ctx) idx (env ctx) val}
  where
    indexOfUndefined _ [] [] = Nothing
    indexOfUndefined lvl ((VUndefined :@ _) : env) ((_, g, _, _) : types)
      | f == g = Just lvl
      | otherwise = indexOfUndefined (lvl - 1) env types
    indexOfUndefined lvl (_ : env) (_ : types) = indexOfUndefined (lvl - 1) env types
    indexOfUndefined _ _ _ = error "indexOfUndefined: incoherent context"

    replaceAt _ _ [] _ = error "replaceAt: index too large"
    replaceAt lvl idx (e : env) val
      | lvl < idx = e : env
      | lvl == idx = val : env
      | otherwise =
          let env' = replaceAt (lvl - 1) idx env val
           in e : env'
