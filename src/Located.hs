{-# LANGUAGE PackageImports #-}

module Located (module Export, spanOf) where

import "nsc-core" Data.Located as Export (Located (..), Position (..), getPos, unLoc)

-- | Computes the effective span between two positions.
spanOf :: Position -> Position -> Position
spanOf p1 p2 = Position b e (file p1)
  where
    b = min (begin p1) (begin p2)
    e = max (end p1) (end p2)
