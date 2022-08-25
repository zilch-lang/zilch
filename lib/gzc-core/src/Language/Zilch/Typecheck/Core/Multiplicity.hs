{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module Language.Zilch.Typecheck.Core.Multiplicity (Multiplicity (O, I, W, A, Erased, Linear, Unrestricted, Any), extend, lub, relevance, Relevance (..)) where

data Multiplicity
  = Erased
  | Linear
  | Unrestricted
  | Any
  deriving (Show, Eq)

pattern O, I, W, A :: Multiplicity
pattern O = Erased
pattern I = Linear
pattern W = Unrestricted
pattern A = Any

{-# COMPLETE O, I, W, A #-}

instance Num Multiplicity where
  A + _ = A
  _ + A = A
  x + O = x
  O + x = x
  I + I = W
  _ + W = W
  W + _ = W

  A * x = x
  x * A = x
  O * _ = O
  _ * O = O
  I * x = x
  x * I = x
  W * _ = W
  _ * W = W

  fromInteger 0 = Erased
  fromInteger 1 = Linear
  fromInteger i = error $ "Unknown usage kind " <> show i

instance Ord Multiplicity where
  A <= _ = True
  _ <= A = True
  W <= W = True
  O <= W = True
  I <= W = True
  I <= I = True
  O <= O = True
  _ <= _ = False

data Relevance
  = -- | What's being checked has no computational relevance.
    --   It is used only in the formation of types.
    Irrelevant
  | -- | What's being checked is present at runtime.
    Present
  deriving (Eq)

-- | Determines how to extend variable multiplicities given whether the are used within the formation of types or not.
--
-- Extending basically returns @0@ if we are currently checking a computationally irrelevant term, and @1@ otherwise.
extend :: Relevance -> Multiplicity
extend Irrelevant = O
extend Present = I

-- | Returns the relevance associated with a given multiplicity.
--
-- @0@ is considered to be irrelevant, while all other multiplicities are present.
relevance :: Multiplicity -> Relevance
relevance O = Irrelevant
relevance I = Present
relevance W = Present
relevance A = undefined

-- | The least upper bound of two multiplicities.
lub :: Multiplicity -> Multiplicity -> Multiplicity
O `lub` O = O
I `lub` I = I
A `lub` _ = A
_ `lub` A = A
_ `lub` _ = W
