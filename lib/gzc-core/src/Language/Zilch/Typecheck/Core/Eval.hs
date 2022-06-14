{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}

module Language.Zilch.Typecheck.Core.Eval (Value (.., VVariable, VMeta), Name, Environment, Closure (..), DeBruijnLvl (..), Spine, MetaEntry (..)) where

import Data.Located (Located ((:@)))
import Data.Text (Text)
import Language.Zilch.Typecheck.Core.AST (Expression)

type Name = Text

type Environment = [Located Value]

data Closure = Clos Environment (Located Expression)

newtype DeBruijnLvl = Lvl Int
  deriving (Show, Eq, Ord, Num, Integral, Enum, Real) via Int

instance Show Closure where
  show _ = "<<clos>>"

type Spine = [Located Value]

data Value
  = -- | A bound variable
    VRigid
      (Located Text)
      DeBruijnLvl
      Spine
  | VFlexible
      Int
      Spine
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
  | -- | An unevaluated piece of code
    VThunk
      (Located Expression)
  deriving (Show)

data MetaEntry
  = Solved Value
  | Unsolved

pattern VVariable :: Located Text -> DeBruijnLvl -> Value
pattern VVariable x lvl <-
  VRigid x lvl []
  where
    VVariable x lvl = VRigid x lvl []

pattern VMeta :: Int -> Value
pattern VMeta m <-
  VFlexible m []
  where
    VMeta m = VFlexible m []
