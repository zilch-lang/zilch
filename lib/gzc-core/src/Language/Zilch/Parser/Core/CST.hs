module Language.Zilch.Parser.Core.CST where

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
  deriving (Show)

data MetaAttribute
  = Inline
  deriving (Show)

data Definition
  = Let
      (Located Text)
      [Located Parameter]
      (Maybe (Located Expression))
      (Located Expression)
  deriving (Show)

data Parameter
  = Implicit
      (Located Text)
      (Maybe (Located Expression))
  | Explicit
      (Located Text)
      (Maybe (Located Expression))
  deriving (Show)

data Expression
  = EId (Located Text)
  | EType
  | EInt Text
  | EChar Text
  | -- | A specific case of 'EStringConcat' with only one string
    EString Text
  | EStringConcat [Text]
  | EApplication
      (Located Expression)
      [Located Expression]
      -- ^ Implicit arguments, whenever they are made explicit
      [Located Expression]
      -- ^ Explicit arguments
  | EInfix
      (Located Expression)
      Text
      (Located Expression)
  | ELam
      (Located Parameter)
      (Located Expression)
  | EDo
      (Located Expression)
  | ELet
      (Located Definition)
      -- ^ Local definition
      (Located Expression)
  | EForall
      [Located Parameter]
      (Located Expression)
  | EExists
      [Located Parameter]
      (Located Expression)
  deriving (Show)
