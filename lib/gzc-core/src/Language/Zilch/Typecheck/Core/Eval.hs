{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}

module Language.Zilch.Typecheck.Core.Eval where

import qualified Data.HashMap as Hash
import Data.Located (Located)
import Data.Text (Text)
import Language.Zilch.Syntax.Core.AST (Expression)

type Name = Text

type Environment = Hash.Map Name (Located Value)

data Closure = Clos Environment (Located Expression)

instance Show Closure where
  show _ = "<<clos>>"

data Value
  = -- | A given identifier
    VIdentifier
      Name
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
  | -- | A hole
    VHole
  deriving (Show)
