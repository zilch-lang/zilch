module Language.Zilch.Typecheck.Defaults (defaultContext) where

import Data.Located (Located ((:@)), Position (Position))
import Language.Zilch.Typecheck.Context
import Language.Zilch.Typecheck.Core.Eval (Value (VIdentifier, VType))

defaultContext :: Context
defaultContext =
  Context
    { env =
        -- Is it necessary? Or should we add special rules when unifying?
        [ -- nat is builtin
          VIdentifier ("nat" :@ p) 1 :@ p,
          -- char is builtin
          VIdentifier ("char" :@ p) 0 :@ p
        ],
      types =
        [ -- nat : type 0
          ("nat", VType :@ p),
          -- char : type 0
          ("char", VType :@ p)
        ],
      lvl = 2
    }

----------------------------

p :: Position
p = Position (0, 0) (0, 0) "builtin"
