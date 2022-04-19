module Language.Zilch.Typecheck.Environment where

import qualified Data.HashMap as Hash
import Data.Located (Located)
import Language.Zilch.Typecheck.Core.Eval (Environment, Name, Value)

-- | Extend the given environment by one entry.
extend :: Environment -> Name -> Located Value -> Environment
extend env name val = Hash.insert name val env

lookup :: Environment -> Name -> Maybe (Located Value)
lookup env name = Hash.lookup name env

fromList :: [(Name, Located Value)] -> Environment
fromList = Hash.fromList
