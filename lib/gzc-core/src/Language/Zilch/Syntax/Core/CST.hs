module Language.Zilch.Syntax.Core.CST where

import Data.Located (Located)
import Data.Text (Text)

data Module
  = Mod
      [Located Import]
      [Located TopLevelDefinition]
  deriving (Show)

data Import
  = Import
      Bool
      -- ^ Is the import @public@?
      Bool
      -- ^ Is the import @open@ed?
      () -- TODO
  deriving (Show)

data TopLevelDefinition
  = TopLevel
      [Located MetaAttribute]
      Bool
      -- ^ Is the definition @public@?
      (Located Definition)
  | Mutual
      [Located TopLevelDefinition]
  deriving (Show)

data MetaAttribute
  = Inline
  deriving (Show)

data Definition
  = -- | A non-recursive value definition
    Let
      (Maybe (Located Integer))
      (Located Text)
      [Located Parameter]
      (Maybe (Located Expression))
      (Located Expression)
  | -- | A (potentially) recursive value definition
    Rec
      (Maybe (Located Integer))
      (Located Text)
      [Located Parameter]
      (Maybe (Located Expression))
      (Located Expression)
  | -- | Assumption (as parameters) introduced at the top-level
    Assume
      [Located Parameter]
  | -- | Forward declaration
    Val
      (Maybe (Located Integer))
      (Located Text)
      (Located Expression)
  deriving (Show)

data Parameter
  = Implicit
      [(Maybe (Located Integer), Located Text, Maybe (Located Expression))]
  | Explicit
      [(Maybe (Located Integer), Located Text, Maybe (Located Expression))]
  deriving (Show)

data Expression
  = EId (Located Text)
  | EType
  | EInt
      Text
      -- ^ Integer content
      (Maybe Text)
      -- ^ Optional integer suffix (e.g. @u64@)
  | EChar Text
  | -- | A specific case of 'EStringConcat' with only one string
    EString Text
  | EStringConcat [Text]
  | EApplication
      (Located Expression)
      [Located (Bool, [Located Expression])]
  | ELam
      [Located Parameter]
      (Located Expression)
  | EDo
      (Located Expression)
  | ELet
      (Located Definition)
      -- ^ Local definition
      (Located Expression)
  | EParens (Located Expression)
  | EHole
  | ETypedHole
  | EPi
      (Located Parameter)
      (Located Expression)
  | ETrue
  | EFalse
  | EIfThenElse
      (Located Expression)
      (Located Expression)
      (Located Expression)
  deriving (Show)
