{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Zilch.Optimize.Internal.PrettyArityTable where

import Data.List (intersperse)
import Data.Located (Located, unLoc)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Prettyprinter (Pretty (..), fill, hardline, pipe, (<+>))

instance Pretty (Map [Located Text] Integer) where
  pretty m =
    let maxKeyLength = maximum $ 10 : fmap lengthOfId (Map.keys m)
     in fill maxKeyLength "Identifier"
          <+> "┃"
          <+> fill 5 "Arity"
            <> hardline
            <> pretty (replicate (maxKeyLength + 1) '━')
            <> "╋"
            <> pretty (replicate (5 + 1) '━')
            <> hardline
            <> mconcat (intersperse hardline $ renderLine maxKeyLength <$> Map.toList m)
            <> hardline
    where
      lengthOfId i = length i - 1 + sum (Text.length . unLoc <$> i)

      renderLine size (id, nb) = fill size (renderId id) <+> "┃" <+> pretty nb

      renderId id = pretty $ mconcat $ intersperse "∷" $ unLoc <$> id
