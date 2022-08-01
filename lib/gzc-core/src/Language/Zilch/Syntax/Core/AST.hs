module Language.Zilch.Syntax.Core.AST where

import Data.Located (Located)
import Data.Text (Text)
import Language.Zilch.Typecheck.Core.Multiplicity (Multiplicity)

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
      (Located Multiplicity)
      -- ^ An optional resource usage annotation for the defined binding
      (Located Text)
      -- ^ Binding name
      (Located Expression)
      -- ^ The type of the binding, where unknown types are filled by holes
      (Located Expression)
      -- ^ Value
  | -- | A type hypothesis
    Val
      (Located Multiplicity)
      -- ^ An optional resource usage
      (Located Text)
      -- ^ The name of the binding
      (Located Expression)
      -- ^ The type assumed
  deriving (Show)

data Parameter
  = Parameter
      Bool
      -- ^ Is it implicit?
      [(Located Multiplicity, Located Text, Located Expression)]
      -- ^ Multiplicities, names and types of parameters
  deriving (Show)

data Expression
  = EInteger
      (Located Text)
      IntegerSuffix
  | ECharacter
      (Located Text)
  | EIdentifier
      (Located Text)
  | EDo (Located Expression)
  | ELam
      (Located Parameter)
      -- ^ Explicit or implicit parameters
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
      Bool
      -- ^ Is the application implicit?
      [Located Expression]
      -- ^ The first parameter
  | -- | The @type@ builtin type
    EType
  | EHole
      HoleLocation
  | -- | The dependent function type
    EPi
      (Located Parameter)
      (Located Expression)
  | EBoolean
      Bool
  | EIfThenElse
      (Located Expression)
      (Located Expression)
      (Located Expression)
  deriving (Show)

data HoleLocation = SourceHole | InsertedHole
  deriving (Show)

data IntegerSuffix
  = SuffixU8
  | SuffixU16
  | SuffixU32
  | SuffixU64
  | SuffixS8
  | SuffixS16
  | SuffixS32
  | SuffixS64
  deriving (Show, Eq)
