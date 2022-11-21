module Language.Zilch.Optimize.Internal.Type where

import Data.Located (Located)
import Data.Text (Text)
import Language.Zilch.Typecheck.ANF (Module)

type Optimizer = (FilePath, [Located Text], Located Module) -> (FilePath, [Located Text], Located Module)
