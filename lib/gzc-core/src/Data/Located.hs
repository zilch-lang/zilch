{-# LANGUAGE PackageImports #-}

module Data.Located
( Position
, IndentLocated(..)
, indentLevel, position, unwrapLocated
) where

import Text.Diagnose (Position)

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
