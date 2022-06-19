module Language.Zilch.Typecheck.Defaults (defaultContext) where

import Data.Located (Located ((:@)), Position (Position))
import Language.Zilch.Typecheck.Context
import Language.Zilch.Typecheck.Core.Eval (Value (..))
import Language.Zilch.Typecheck.Core.Usage (Usage (..))

defaultContext :: Context
defaultContext =
  -- define Erased ("u64" :@ p) (VBuiltinU64 :@ p) (VType :@ p) $
  --   define Erased ("char" :@ p) (VVariable ("char" :@ p) 0 :@ p) (VType :@ p) $
  emptyContext

----------------------------

p :: Position
p = Position (0, 0) (0, 0) "builtin"
