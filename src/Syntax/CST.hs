{-# LANGUAGE EmptyDataDeriving #-}

module Syntax.CST where

import Data.Text (Text)
import Located (Located)

-- | The type containing a whole compilation unit.
data Module
  = Mod [Located TopLevel]
  deriving (Show)

-- | Top-level bindings and type declarations.
data TopLevel
  = Binding
      Bool
      (Located Definition)
  deriving (Show)

data Definition
  = Let
      (Maybe (Located Multiplicity))
      (Located String)
      [[Located Parameter]]
      (Maybe (Located Expression))
      (Located Expression)
  | Rec
      (Maybe (Located Multiplicity))
      (Located String)
      [[Located Parameter]]
      (Maybe (Located Expression))
      (Located Expression)
  | Val
      (Maybe (Located Multiplicity))
      (Located String)
      [[Located Parameter]]
      (Located Expression)
  | Assume
      [[Located Parameter]]
  | Mutual
      [Located TopLevel]
  deriving (Show)

-- | Multiplicities are certain kinds of expressions.
type Multiplicity = Expression

data Implicitness
  = Implicit
  | Explicit
  deriving (Show)

data Parameter
  = Parameter
      Implicitness
      (Maybe (Located Multiplicity))
      (Located String)
      (Located Expression)
  deriving (Show)

data Expression
  = Identifier String
  | Integer
      (Located String)
      (Maybe (Located Expression))
  | ProductType
      [Located Parameter]
      (Located Expression)
  | Lambda
      [[Located Parameter]]
      (Located Expression)
  | MultiplicativeSigmaType
      [Located Parameter]
      (Located Expression)
  | AdditiveSigmaType
      [Located Parameter]
      (Located Expression)
  | MultiplicativeUnitType
  | MultiplicativeUnit
  | Local
      (Located Definition)
      (Located Expression)
  | Application
      (Located Expression)
      [(Implicitness, [Located Expression])]
  | Parenthesized
      (Located Expression)
  | Hole
  deriving (Show)
