module Language.Zilch.Typecheck.Environment where

import Data.Located (Located)
import Language.Zilch.Typecheck.Core.Eval (Environment, Value)

-- | Extend the given environment by one entry.
extend :: Environment -> Located Value -> Environment
extend env val = val : env

lookup :: Environment -> Int -> Located Value
lookup env name = env !! name

length :: Environment -> Int
length = Prelude.length

-- | Returns a list of values ordered in increasing order on the keys.
toList :: Environment -> [Located Value]
toList = id
