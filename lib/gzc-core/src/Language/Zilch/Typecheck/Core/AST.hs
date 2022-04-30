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
  deriving (Show)

data Parameter
  = Parameter
      Bool
      -- ^ Is it implicit?
      (Located Text)
      -- ^ The name of the parameter
      (Located Expression)
      -- ^ Its type
  deriving (Show)

newtype DeBruijnIdx = Idx Int
  deriving (Show, Eq, Ord, Num, Integral, Enum, Real) via Int

data Expression
  = -- | The @type@ builtin universe constructor (@type X@ is the universe at level @X@ where @X :: nat@)
    EType
  | -- | An unapplied lambda abstraction
    ELam
      (Located Expression)
  | -- | The function type @(x : A) → B@ or @{x : A} → B@
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
      (Located DeBruijnIdx)
  | EInteger
      (Located Text)
  | ECharacter
      (Located Text)
  deriving (Show)
