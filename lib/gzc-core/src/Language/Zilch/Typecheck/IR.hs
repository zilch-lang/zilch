module Language.Zilch.Typecheck.IR
  ( Module (..),
    TopLevel (..),
    MetaAttribute (..),
    Definition (..),
    Parameter (..),
    Expression (..),
    BuiltinType (..),
    Multiplicity (..),
  )
where

import Data.Located (Located)
import Data.Map (Map)
import Data.Text (Text)
import Language.Zilch.Typecheck.Core.AST (BuiltinType (..), MetaAttribute (..))
import Language.Zilch.Typecheck.Core.Multiplicity (Multiplicity (..))

data Module
  = Module [Located TopLevel]
  deriving (Show)

data TopLevel
  = TopLevel
      [Located MetaAttribute]
      Bool
      (Located Definition)
  deriving (Show)

data Definition
  = Let
      Bool
      (Located Multiplicity)
      [Located Text]
      (Located Expression)
      (Located Expression)
  | Val
      (Located Multiplicity)
      [Located Text]
      (Located Expression)
  deriving (Show, Eq, Ord)

data Parameter
  = Parameter
      (Located Multiplicity)
      -- ^ Resource usage
      (Located Text)
      -- ^ The name of the parameter
      (Located Expression)
      -- ^ Its type
  deriving (Show, Eq, Ord)

data Expression
  = -- | The @type@ builtin universe constructor (@type X@ is the universe at level @X@ where @X : nat@)
    EType
  | -- | An unapplied lambda abstraction
    ELam
      (Located Parameter)
      (Located Expression)
      (Located Expression)
  | -- | The function type @(_ x : A) → B@ or @{_ x : A} → B@
    EPi
      (Located Parameter)
      (Located Expression)
      (Located Expression)
  | -- | The dependent additive product type @(_ x : A) & B@
    EAdditiveProduct
      (Located Parameter)
      (Located Expression)
      (Located Expression)
  | -- | The dependent multiplicative product type @(_ x : A) ⊗ B@
    EMultiplicativeProduct
      (Located Parameter)
      (Located Expression)
      (Located Expression)
  | ELet
      (Located Definition)
      (Located Expression)
  | EApplication
      (Located Expression)
      (Located Expression)
      (Located Expression)
      (Located Expression)
  | -- | Represents the fully qualified identifier from within a module
    EIdentifier
      [Located Text]
  | EInteger
      (Located Text)
      BuiltinType
  | ECharacter
      (Located Text)
  | -- | Builtin types
    EBuiltin BuiltinType
  | EBoolean Bool
  | EIfThenElse
      (Located Expression)
      (Located Expression)
      (Located Expression)
      (Located Expression)
      (Located Expression)
  | EAdditivePair
      (Located Expression)
      (Located Expression)
      (Located Expression)
      (Located Expression)
  | EMultiplicativePair
      (Located Expression)
      (Located Expression)
      (Located Expression)
      (Located Expression)
  | EMultiplicativeUnit
  | EAdditiveUnit
  | EOne
  | ETop
  | -- | @FST e@
    EFst
      (Located Expression)
      (Located Expression)
  | -- | @SND e@
    ESnd
      (Located Expression)
      (Located Expression)
  | -- | @let p (x, y) as z := M; N@
    EMultiplicativePairElim
      (Maybe (Located Text))
      -- ^ @z@
      (Located Multiplicity)
      -- ^ @p@
      (Located Text)
      -- ^ @x@
      (Located Expression)
      (Located Text)
      -- ^ @y@
      (Located Expression)
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
      [(Located Multiplicity, Located Text, Located Expression)]
  | -- | @MODULE { p x : τ }@
    EModule
      (Map (Located Text) (Located Multiplicity, Located Expression))
  | -- | @\@{p x : t := e }@
    ERecordLiteral
      [(Located Multiplicity, Located Text, Located Expression, Located Expression)]
  | ERecordAccess
      (Located Expression)
      (Located Expression)
      (Located Text)
  deriving (Show, Eq, Ord)
