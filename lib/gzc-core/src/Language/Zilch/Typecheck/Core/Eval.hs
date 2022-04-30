{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}

module Language.Zilch.Typecheck.Core.Eval where

import Data.Located (Located)
import Data.Text (Text)
import Language.Zilch.Typecheck.Core.AST (Expression)

type Name = Text

type Environment = [Located Value]

data Closure = Clos Environment (Located Expression)

newtype DeBruijnLvl = Lvl Int
  deriving (Show, Eq, Ord, Num, Integral, Enum, Real) via Int

instance Show Closure where
  show _ = "<<clos>>"

data Value
  = -- | A bound variable
    VIdentifier
      (Located Text)
      DeBruijnLvl
  | -- | The application of a value to another one
    VApplication
      (Located Value)
      (Located Value)
  | -- | An un-applied lambda abstraction with a given closure
    VLam
      Name
      Closure
  | -- | A pi-type with an explicit argument (denoted @(x : A) → B@)
    VPi
      Name
      (Located Value)
      Closure
  | -- | Universes (of the given level)
    VType
  | -- | Basic integers
    VInteger
      Integer
  | -- | Basic characters
    VCharacter
      Char
  deriving (Show)
