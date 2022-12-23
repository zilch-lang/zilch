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
      (Located Expression)
      (Located Expression)
  | Rec
      (Maybe (Located Multiplicity))
      (Located String)
      [[Located Parameter]]
      (Located Expression)
      (Located Expression)
  | Val
      (Maybe (Located Multiplicity))
      (Located String)
      [[Located Parameter]]
      (Located Expression)
  | Assume
      (Maybe (Located Multiplicity))
      (Located String)
      [[Located Parameter]]
      (Located Expression)
  | Mutual
      [Located TopLevel]
  deriving (Show)

-- | Multiplicities are certain kinds of expressions.
type Multiplicity = Expression

data Parameter
  = Parameter
      (Maybe (Located Multiplicity))
      (Located String)
      (Located Expression)
  deriving (Show)

data Expression
  = Identifier String
  | Integer
      (Located String)
      (Located Expression)
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
      [Located Expression]
  | Parenthesized
      (Located Expression)
  deriving (Show)
