{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module Language.Zilch.Typecheck.Core.Usage (Usage (O, I, W, Erased, Linear, Unrestricted)) where

data Usage
  = Erased
  | Linear
  | Unrestricted
  deriving (Show, Eq)

pattern O, I, W :: Usage
pattern O = Erased
pattern I = Linear
pattern W = Unrestricted

{-# COMPLETE O, I, W #-}

instance Num Usage where
  x + O = x
  O + x = x
  I + I = W
  _ + W = W
  W + _ = W

  O * _ = O
  _ * O = O
  I * x = x
  x * I = x
  W * _ = W
  _ * W = W

  fromInteger 0 = Erased
  fromInteger 1 = Linear
  fromInteger i = error $ "Unknown usage kind " <> show i

instance Ord Usage where
  O <= W = True
  I <= W = True
  I <= I = True
  O <= O = True
  _ <= _ = False
