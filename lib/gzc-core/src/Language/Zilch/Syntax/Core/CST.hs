module Language.Zilch.Syntax.Core.CST where

import Data.Located (Located)
import Data.Text (Text)

data Module
  = Mod
      [Located TopLevelDefinition]
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
  | Foreign
      (Located CallingConvention)
      (Located Text)
  deriving (Show)

data CallingConvention
  = CCall
  | UnknownCall (Located Text)
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
  | Import
      Bool
      -- ^ Is the import @open@ed
      (Located ImportSpine)
      -- ^ Import list
  deriving (Show)

data ImportSpine
  = Empty
  | Base
      (Located Text)
      (Located ImportSpine)
  | Branch
      [Located ImportSpine]
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
  | EImport
      (Located Definition)
      (Located Expression)
  | EParens (Located Expression)
  | EHole
  | ETypedHole
  | EPi
      (Located Parameter)
      (Located Expression)
  | EMultiplicativeProduct
      (Located Parameter)
      (Located Expression)
  | EAdditiveProduct
      (Located Parameter)
      (Located Expression)
  | EMultiplicativeTuple
      [Located Expression]
  | EAdditiveTuple
      [Located Expression]
  | EMultiplicativeUnit
  | EAdditiveUnit
  | ETrue
  | EFalse
  | EIfThenElse
      (Located Expression)
      (Located Expression)
      (Located Expression)
  | EOne
  | ETop
  | EAccess
      (Located Expression)
      [Located Expression]
  | EMultiplicativeTupleElim
      (Maybe (Located Text))
      (Maybe (Located Integer))
      [Located Text]
      (Located Expression)
      (Located Expression)
  | EByRef
      (Located Text)
  deriving (Show)
