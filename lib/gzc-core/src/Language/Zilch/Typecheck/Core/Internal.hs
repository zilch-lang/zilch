{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.Zilch.Typecheck.Core.Internal (Value (.., VMeta, VVariable), module Language.Zilch.Typecheck.Core.Internal) where

import Data.Located (Located)
import Data.Map (Map)
import Data.Text (Text)
import Language.Zilch.Typecheck.Core.Multiplicity (Multiplicity)

data Definition
  = Let
      Bool
      -- ^ Is it recursive?
      (Located Multiplicity)
      -- ^ Multiplicity information
      (Located Text)
      -- ^ The name of the binding
      (Located Expression)
      -- ^ The return type
      (Located Expression)
      -- ^ The value bound
  | Val
      (Located Multiplicity)
      (Located Text)
      (Located Expression)
  | External
      (Located Multiplicity)
      (Located Text)
      (Located Expression)
      (Located Expression)
      [Located Text]
      FilePath
  deriving (Show)

data Parameter
  = Parameter
      Bool
      -- ^ Is it implicit?
      (Located Multiplicity)
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
  | -- | The dependent additive product type @(_ x : A) & B@
    EAdditiveProduct
      (Located Parameter)
      (Located Expression)
  | -- | The dependent multiplicative product type @(_ x : A) ⊗ B@
    EMultiplicativeProduct
      (Located Parameter)
      (Located Expression)
  | ELet
      (Located Definition)
      (Located Expression)
  | EApplication
      (Located Expression)
      Bool
      -- ^ Is it implicit
      (Located Expression)
  | EIdentifier
      (Located Text)
      DeBruijnIdx
  | EInteger
      (Located Text)
      BuiltinType
  | ECharacter
      (Located Text)
  | EMeta
      Int
  | EInsertedMeta
      Int
      Path
  | -- | Builtin types
    EBuiltin BuiltinType
  | EBoolean Bool
  | EIfThenElse
      (Located Expression)
      (Located Expression)
      (Located Expression)
  | EAdditivePair
      (Located Expression)
      (Located Expression)
  | EMultiplicativePair
      (Located Expression)
      (Located Expression)
  | EMultiplicativeUnit
  | EAdditiveUnit
  | EOne
  | ETop
  | -- | @FST e@
    EFst
      (Located Expression)
  | -- | @SND e@
    ESnd
      (Located Expression)
  | -- | @let p (x, y) as z := M; N@
    EMultiplicativePairElim
      (Maybe (Located Text))
      -- ^ @z@
      (Located Multiplicity)
      -- ^ @p@
      (Located Text)
      -- ^ @x@
      (Located Text)
      -- ^ @y@
      (Located Expression)
      -- ^ @M@
      (Located Expression)
      -- ^ @N@
  | -- | @let p () as z := M; N@
    EMultiplicativeUnitElim
      (Maybe (Located Text))
      -- ^ @z@
      (Located Multiplicity)
      -- ^ @p@
      (Located Expression)
      -- ^ @M@
      (Located Expression)
      -- ^ @N@
  | -- | @'{ p x : τ }@
    EComposite
      (Map (Located Text) (Located Multiplicity, Located Expression))
  | -- | @\@{p x : t := e }@
    ERecord
      (Map (Located Text) (Located Multiplicity, Located Expression, Located Expression))
  | ERecordAccess
      (Located Expression)
      (Located Text)
  deriving (Show)

data BuiltinType
  = TyU64
  | TyU32
  | TyU16
  | TyU8
  | TyS64
  | TyS32
  | TyS16
  | TyS8
  | TyBool
  deriving (Show)

---------------------------------------------

data Path
  = Here
  | Bind Path Multiplicity (Located Text) (Located Value)
  | Define Path Multiplicity (Located Text) (Located Value) (Located Value)
  deriving (Show)

---------------------------------------------

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
  | -- | A pi-type with an explicit argument (denoted @(p x : A) → B@)
    VPi
      Multiplicity
      Name
      Implicitness
      (Located Value)
      Closure
  | -- | A ⊗-type with an explicit argument (denoted @(p x : A) ⊗ B@)
    VMultiplicativeProduct
      Multiplicity
      Name
      (Located Value)
      Closure
  | -- | A &-type with an explicit argument (denoted @(x : A) & B@)
    VAdditiveProduct
      Name
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
  | -- | A conditional expression
    VIfThenElse
      (Located Value)
      (Located Value)
      (Located Value)
  | VTrue
  | VFalse
  | VMultiplicativePair
      (Located Value)
      (Located Value)
  | VAdditivePair
      (Located Value)
      (Located Value)
  | VMultiplicativeUnit
  | VAdditiveUnit
  | VOne
  | VTop
  | VFst
      (Located Value)
  | VSnd
      (Located Value)
  | -- builtin types
    VBuiltinU64
  | VBuiltinU32
  | VBuiltinU16
  | VBuiltinU8
  | VBuiltinS64
  | VBuiltinS32
  | VBuiltinS16
  | VBuiltinS8
  | VBuiltinBool
  | VUndefined
  | -- | @'{ p x : τ }@
    VComposite
      (Map (Located Text) (Located Multiplicity, Located Value))
  | -- | @\@{p x : t := e }@
    VRecord
      (Map (Located Text) (Located Multiplicity, Located Value, Located Value))
  | VRecordAccess
      (Located Value)
      (Located Text)
  deriving (Show)

data MetaEntry
  = Solved Value Multiplicity (Located Value)
  | Unsolved Multiplicity (Located Value)
  deriving (Show)

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

type Name = Text

type Environment = [Located Value]

data Closure = Clos Environment (Located Expression)

newtype DeBruijnLvl = Lvl Int
  deriving (Show, Eq, Ord, Num, Integral, Enum, Real) via Int

instance Show Closure where
  show _ = "<<clos>>"

type Implicitness = Bool
