module Language.Zilch.Typecheck.Usage where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Map.Internal as Map (mapMissing, zipWithMatched, merge)
import Language.Zilch.Typecheck.Core.Multiplicity (Multiplicity(..), lub)

type Usage = Map Text Multiplicity

merge :: Usage -> Usage -> Usage
merge = Map.merge
  -- if a key is in the first and not the second, compute the upper bound with 0
  (Map.mapMissing (const $ lub O))
  -- if a key is in the second and not the first, compute the upper bound with 0
  (Map.mapMissing (const $ lub O))
  -- if a key is in both, compute their upper bound
  (Map.zipWithMatched (const lub))

-- | Scale a usage by multiplying each of the multiplicities by the given multiplicity.
scale :: Multiplicity -> Usage -> Usage
scale mult = fmap (mult *)

-- | Concatenates two usages by adding the multiplicities together.
concat :: Usage -> Usage -> Usage
concat = Map.unionWith (+)
