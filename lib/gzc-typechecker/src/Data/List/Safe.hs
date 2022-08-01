{-# LANGUAGE MagicHash #-}

module Data.List.Safe where

import GHC.Base (Int (I#), (+#))

-- |
-- 'indexed' pairs each element with its index.

-- >>> indexed "hello"
-- [(0,'h'),(1,'e'),(2,'l'),(3,'l'),(4,'o')]

-- /Subject to fusion./
indexed :: [a] -> [(Int, a)]
indexed xs = go 0# xs
  where
    go i (a : as) = (I# i, a) : go (i +# 1#) as
    go _ _ = []
{-# NOINLINE [1] indexed #-}
