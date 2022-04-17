module Language.Zilch.Syntax.Core.AST where

import Data.Located (Located)
import Data.Text (Text)

-------

data Module
  = Mod
      [()]
      [Located TopLevel]
  deriving (Show)

data TopLevel
  = TopLevel
      Bool
      -- ^ Is the toplevel binding public?
      (Located Definition)
  deriving (Show)

data Definition
  = -- | A value binding
    Let
      Bool
      -- ^ Is the binding a recursive one?
      (Located Text)
      -- ^ Binding name
      [Located Parameter]
      -- ^ Implicit parameters
      [Located Parameter]
      -- ^ Explicit parameters
      (Maybe (Located Expression))
      -- ^ Optional return type
      (Located Expression)
      -- ^ Value
  deriving (Show)

data Parameter
  = Parameter
      Bool
      -- ^ Is it implicit?
      (Located Text)
      -- ^ The name of the parameter
      (Maybe (Located Expression))
      -- ^ Optional explicit type
  deriving (Show)

data Expression
  = EForall
      [Located Parameter]
      -- ^ Implicit parameters
      [Located Parameter]
      -- ^ Explicit parameters
      (Located Expression)
      -- ^ Quantified expression (type)
  | EExists
      [Located Parameter]
      -- ^ Implicit parameters
      [Located Parameter]
      -- ^ Explicit parameters
      (Located Expression)
      -- ^ Quantified expression (type)
  | EInteger
      (Located Text)
  | ECharacter
      (Located Text)
  | EIdentifier
      (Located Text)
  | EDo (Located Expression)
  | ELam
      [Located Parameter]
      -- ^ Explicit parameters
      (Located Expression)
      -- ^ Return expression
  | ELet
      (Located Definition)
      -- ^ Additional binding
      (Located Expression)
      -- ^ Return expression
  | EApplication
      (Located Expression)
      -- ^ The expression which has arguments applied to it
      [Located Expression]
      -- ^ Implicit parameters made explicit
      [Located Expression]
      -- ^ Explicit parameters
  | -- | The @type@ builtin type
    EType
  | EHole
  deriving (Show)
