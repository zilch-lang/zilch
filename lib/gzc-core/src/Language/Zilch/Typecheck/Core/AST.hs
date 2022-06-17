{-# LANGUAGE DerivingVia #-}

module Language.Zilch.Typecheck.Core.AST where

import Data.Located (Located)
import Data.Text (Text)

data Module
  = Mod [Located TopLevel]
  deriving (Show)

data TopLevel
  = TopLevel
      [()]
      -- ^ For future use (maybe)
      Bool
      -- ^ Is it public?
      (Located Definition)
  deriving (Show)

data Definition
  = Let
      Bool
      -- ^ Is it recursive?
      (Located Text)
      -- ^ The name of the binding
      (Located Expression)
      -- ^ The return type
      (Located Expression)
      -- ^ The value bound
  | LetMeta
      Int
      (Maybe (Located Expression))
  deriving (Show)

data Parameter
  = Parameter
      Bool
      -- ^ Is it implicit?
      (Located Usage)
      -- ^ Resource usage
      (Located Text)
      -- ^ The name of the parameter
      (Located Expression)
      -- ^ Its type
  deriving (Show)

newtype DeBruijnIdx = Idx Int
  deriving (Show, Eq, Ord, Num, Integral, Enum, Real) via Int

data Expression
  = -- | The @type@ builtin universe constructor (@type X@ is the universe at level @X@ where @X : nat@)
    EType
  | -- | An unapplied lambda abstraction
    ELam
      (Located Parameter)
      (Located Expression)
  | -- | The function type @(_ x : A) → B@ or @{_ x : A} → B@
    EPi
      (Located Parameter)
      (Located Expression)
  | ELet
      (Located Definition)
      (Located Expression)
  | EApplication
      (Located Expression)
      (Located Expression)
  | EIdentifier
      (Located Text)
      DeBruijnIdx
  | EInteger
      (Located Text)
  | ECharacter
      (Located Text)
  | EMeta
      Int
  | EInsertedMeta
      Int
      [Binding]
  | EUnknown
  deriving (Show)

data Binding = Bound Text | Defined Text
  deriving (Show, Eq)

data Usage
  = Erased
  | Linear
  | Unrestricted
  deriving (Show, Eq)

instance Num Usage where
  Erased + u = u
  _ + Unrestricted = Unrestricted
  Linear + _ = Linear
  Unrestricted + u = u

  Erased * _ = Erased
  _ * Erased = Erased
  Linear * u = u
  u * Linear = u
  Unrestricted * Unrestricted = Unrestricted

  fromInteger 0 = Erased
  fromInteger 1 = Linear
  fromInteger i = error $ "Unknown usage kind " <> show i
