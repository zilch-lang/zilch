module Language.Zilch.Typecheck.Defaults (defaultEnv, defaultCtx) where

import Data.Located (Located ((:@)), Position (Position))
import Language.Zilch.Typecheck.Context
import qualified Language.Zilch.Typecheck.Context as Ctx
import Language.Zilch.Typecheck.Core.Eval (Environment, Value (VIdentifier, VType))
import qualified Language.Zilch.Typecheck.Environment as Env

defaultEnv :: Environment
defaultEnv =
  Env.fromList
    [ -- nat is builtin
      ("nat", VIdentifier "nat" :@ p),
      -- char is builtin
      ("char", VIdentifier "char" :@ p)
    ]

defaultCtx :: Context
defaultCtx =
  Ctx.fromList
    [ -- nat : type 0
      ("nat", VType :@ p),
      -- char : type 0
      ("char", VType :@ p)
    ]

----------------------------

p :: Position
p = Position (0, 0) (0, 0) "builtin"
