module Language.Zilch.Typecheck.Defaults (defaultContext) where

import Data.Located (Located ((:@)), Position (Position))
import Language.Zilch.Typecheck.Context
import Language.Zilch.Typecheck.Core.AST (MetaStatus (Defined))
import Language.Zilch.Typecheck.Core.Eval (Value (VIdentifier, VType))

defaultContext :: Context
defaultContext =
  Context
    { env =
        -- Is it necessary? Or should we add special rules when unifying?
        [ -- nat is builtin
          VIdentifier 1 mempty :@ p,
          -- char is builtin
          VIdentifier 0 mempty :@ p
        ],
      types =
        [ -- nat : type 0
          ("nat", VType :@ p),
          -- char : type 0
          ("char", VType :@ p)
        ],
      lvl = 2,
      bds = [Defined, Defined]
    }

----------------------------

p :: Position
p = Position (0, 0) (0, 0) "builtin"
