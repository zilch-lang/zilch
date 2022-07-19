{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}

module Language.Zilch.Typecheck.Core.Eval (Value (.., VVariable, VMeta), Name, Environment, Closure (..), DeBruijnLvl (..), Spine, MetaEntry (..), Implicitness, implicit, explicit) where

import Data.Located (Located ((:@)))
import Data.Text (Text)
import Language.Zilch.Typecheck.Core.AST (Expression)
import Language.Zilch.Typecheck.Core.Multiplicity (Multiplicity)

type Name = Text

type Environment = [Located Value]

data Closure = Clos Environment (Located Expression)

newtype DeBruijnLvl = Lvl Int
  deriving (Show, Eq, Ord, Num, Integral, Enum, Real) via Int

instance Show Closure where
  show _ = "<<clos>>"

type Implicitness = Bool

explicit, implicit :: Implicitness
explicit = True
implicit = False

type Spine = [(Located Value, Implicitness)]

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
      Multiplicity
      Name
      Implicitness
      (Located Value)
      Closure
  | -- | A pi-type with an explicit argument (denoted @(x : A) → B@)
    VPi
      Multiplicity
      Name
      Implicitness
      (Located Value)
      Closure
  | -- | Universes (of the given level)
    VType
  | -- | Basic integers
    VInteger
      Integer
      Value
      -- ^ The type of integer
  | -- | Basic characters
    VCharacter
      Char
  | -- | An unevaluated piece of code
    VThunk
      (Located Expression)
  | -- builtin types
    VBuiltinU64
  | VBuiltinU32
  | VBuiltinU16
  | VBuiltinU8
  | VBuiltinS64
  | VBuiltinS32
  | VBuiltinS16
  | VBuiltinS8
  | VUnknown
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
