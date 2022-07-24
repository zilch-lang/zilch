{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Language.Zilch.Typecheck.Defaults (defaultContext) where

import Data.Located (Position (Position))
import Language.Zilch.Typecheck.Context

defaultContext :: Context
defaultContext =
  -- define Erased ("u64" :@ p) (VBuiltinU64 :@ p) (VType :@ p) $
  --   define Erased ("char" :@ p) (VVariable ("char" :@ p) 0 :@ p) (VType :@ p) $
  emptyContext

----------------------------

p :: Position
p = Position (0, 0) (0, 0) "builtin"
