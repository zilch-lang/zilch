module Language.Zilch.Typecheck.Environment where

import Data.Located (Located)
import GHC.Stack (HasCallStack)
import Language.Zilch.Typecheck.Core.Eval (Environment, Value)

-- | Extend the given environment by one entry.
extend :: Environment -> Located Value -> Environment
extend env val = val : env

lookup :: HasCallStack => Environment -> Int -> Located Value
lookup env name = env !! name

length :: Environment -> Int
length = Prelude.length

set :: Environment -> Int -> Located Value -> Environment
set env idx val = go idx env
  where
    go _ [] = []
    go 0 (x : xs) = val : xs
    go n (x : xs) = x : go (n - 1) xs

-- | Returns a list of values ordered in increasing order on the keys.
toList :: Environment -> [Located Value]
toList = id
