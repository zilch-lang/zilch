{-- Contains the typed AST

-}
module Language.Zilch.Typecheck.Core where

import Data.Located (Located)
import Data.Text (Text)

data Module
  = Mod [Located TopLevel]

data TopLevel
  = TopLevel
      [()]
      -- ^ For future use (maybe)
      Bool
      -- ^ Is it public?
      (Located Definition)

data Definition
  = Let
      Bool
      -- ^ Is it recursive?
      (Located Text)
      -- ^ The name of the binding
      [Located Parameter]
      -- ^ Parameters (implicit & explicit)
      (Located Expression)
      -- ^ The return type
      (Located Expression)
      -- ^ The value bound

data Parameter
  = Parameter
      Bool
      -- ^ Is it implicit?
      (Located Text)
      -- ^ The name of the parameter
      (Located Expression)
      -- ^ Its type

data Expression
  = -- | The @type@ builtin universe constructor (@type X@ is the universe at level @X@ where @X :: nat@)
    EType
  | -- | An unapplied lambda abstraction
    ELam
      [Located Parameter]
      (Located Expression)
  | -- | The function type @(x : A) → B@ or @{x : A} → B@
    EFun
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
  | EInteger
      (Located Text)
