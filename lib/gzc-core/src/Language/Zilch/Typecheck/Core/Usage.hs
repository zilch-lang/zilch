module Language.Zilch.Typecheck.Core.Usage where

data Usage
  = Erased
  | Linear
  | Unrestricted
  deriving (Show, Eq)

instance Num Usage where
  Erased + u = u
  _ + Unrestricted = Unrestricted
  Linear + _ = Linear
  Unrestricted + u = u

  Erased * _ = Erased
  _ * Erased = Erased
  Linear * _ = Linear
  _ * Linear = Linear
  Unrestricted * Unrestricted = Unrestricted

  fromInteger 0 = Erased
  fromInteger 1 = Linear
  fromInteger i = error $ "Unknown usage kind " <> show i

