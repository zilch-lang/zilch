module Language.Zilch.Typecheck.ANF where

import Data.Located (Located)
import Data.Text (Text)
import Language.Zilch.Typecheck.IR (BuiltinType, MetaAttribute, Multiplicity)

data Module
  = Module [Located TopLevel]
  deriving (Show)

data TopLevel
  = TopLevel
      [Located MetaAttribute]
      (Located Definition)
  deriving (Show)

data Definition
  = Let
      Bool
      (Located Multiplicity)
      (Located Text)
      (Located Expression)
      (Located Expression)
  deriving (Show)

data Parameter
  = Parameter
      (Located Multiplicity)
      (Located Text)
      (Located Expression)
  deriving (Show)

data Expression
  = EType
  | EIdentifier
      [Located Text]
  | EInteger
      (Located Text)
      BuiltinType
  | ECharacter
      (Located Text)
  | EBuiltin
      BuiltinType
  | EBoolean
      Bool
  | EOne
  | ETop
  | EFst
      (Located Expression)
  | ESnd
      (Located Expression)
  | EIfThenElse
      (Located Expression)
      (Located Expression)
      (Located Expression)
  | EApplication
      (Located Expression)
      [Located Expression]
  | EAdditivePair
      [Located Expression]
  | EMultiplicativePair
      [Located Expression]
  | ELam
      [Located Parameter]
      (Located Expression)
  | EPi
      [Located Parameter]
      (Located Expression)
  | EAdditiveProduct
      [Located Parameter]
      (Located Expression)
  | EMultiplicativeProduct
      [Located Parameter]
      (Located Expression)
  | ELet
      (Located Definition)
      (Located Expression)
  | EMultiplicativePairElim
      (Maybe (Located Text))
      (Located Multiplicity)
      [Located Text]
      (Located Expression)
      (Located Expression)
  | EComposite
      [(Located Multiplicity, Located Text, Located Expression)]
  | ERecordLiteral
      [(Located Multiplicity, Located Text, Located Expression, Located Expression)]
  | ERecordAccess
      (Located Expression)
      (Located Text)
  deriving (Show)
