module Language.Zilch.Typecheck.Defaults (defaultContext) where

import Data.Located (Located ((:@)), Position (Position))
import Language.Zilch.Typecheck.Context
import Language.Zilch.Typecheck.Core.AST (Usage (..))
import Language.Zilch.Typecheck.Core.Eval (Value (VType, VVariable))

defaultContext :: Context
defaultContext =
  define Erased ("nat" :@ p) (VVariable ("nat" :@ p) 1 :@ p) (VType :@ p) $
    define Erased ("char" :@ p) (VVariable ("char" :@ p) 0 :@ p) (VType :@ p) $
      emptyContext

----------------------------

p :: Position
p = Position (0, 0) (0, 0) "builtin"
