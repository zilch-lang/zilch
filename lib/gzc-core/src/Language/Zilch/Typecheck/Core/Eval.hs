{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Language.Zilch.Typecheck.Core.Eval where

import qualified Data.HashMap as Hash
import Data.Text (Text)

type Name = Text

type Environment = Hash.Map Name Value

type Closure = Value -> Value

instance Show Closure where
  show _ = "<<clos>>"

data Value
  = -- | A given identifier
    VIdentifier
      Name
  | -- | The application of a value to another one
    VApplication
      Value
      Value
  | -- | An un-applied lambda abstraction with a given closure
    VLam
      Closure
  | -- | A pi-type with an explicit argument (denoted @(x : A) → B@)
    VPi
      Name
      Value
      Closure
  | -- | Universes (of the given level)
    VType
      Value
  | -- | Basic integers
    VInteger
      Integer
  deriving (Show)
