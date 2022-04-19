module Language.Zilch.Typecheck.Context where

import qualified Data.HashMap as Hash
import Data.Located (Located)
import Data.Text (Text)
import Language.Zilch.Typecheck.Core.Eval (Value)

type Context = Hash.Map Text (Located Value)

extend :: Context -> Text -> Located Value -> Context
extend ctx name expr = Hash.insert name expr ctx

lookup :: Context -> Text -> Maybe (Located Value)
lookup ctx name = Hash.lookup name ctx

fromList :: [(Text, Located Value)] -> Context
fromList = Hash.fromList
