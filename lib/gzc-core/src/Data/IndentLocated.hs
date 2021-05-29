module Data.IndentLocated
( Position
, IndentLocated(..), Located
, indentLevel, position, unwrapLocated
) where

import Text.Diagnose (Position)
import Data.Function (on)

type Located a = IndentLocated a

data IndentLocated a
  = ILocated
        Position   -- ^ The beginning and end position within a file
        Integer    -- ^ The indentation level of the current line
        a          -- ^ The located data
  deriving (Show)

indentLevel :: IndentLocated a -> Integer
indentLevel (ILocated _ i _) = i

position :: IndentLocated a -> Position
position (ILocated p _ _) = p

unwrapLocated :: IndentLocated a -> a
unwrapLocated (ILocated _ _ x) = x


instance Eq a => Eq (IndentLocated a) where
  ILocated _ _ x1 == ILocated _ _ x2 = x1 == x2

instance Eq a => Ord (IndentLocated a) where
  compare = compare `on` position
