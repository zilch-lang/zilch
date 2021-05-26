module Language.Zilch.Core.Lexer where

import Data.Located (IndentLocated)
import Data.Text (Text)

-- | A simple type alias for located tokens (tokens with an additional position information).
type LToken = IndentLocated Token

-- | The datatype containing all possible tokens in Zilch.
data Token
-------- Keywords
  = -- | Forall type-variable binder (@forall@)
    Forall
    -- | Forall type-variable binder (@∀@ unicode variant)
  | UniForall
    -- | Function definition (@def@)
  | Def
    -- | Enumeration definition (@enum@)
  | Enum
    -- | Record definition (@record@)
  | Record
    -- | Type class definition (@class@)
  | Class
    -- | Type class implementation (@impl@)
  | Impl
    -- | Additional variable binders in function definition (@where@)
  | Where
    -- | Do-expression
  | Do
    -- | Type alias definition and type kind (@type@)
  | Type
    -- | Pattern matching beginning delimiter (@case@)
  | Case
    -- | Pattern matching middle delimiter (@of@)
  | Of
    -- | Module definition (@module@)
  | Module
    -- | Anonymous function definition (@fn@)
  | Fn
    -- | FFI specifier on imports/exports (@foreign@)
  | Foreign
    -- | Alias creation (@as@)
  | As
    -- | Open import (@open@)
  | Open
    -- | Module/FFI import (@import@)
  | Import
    -- | Midule/FFI export (@export@)
  | Export
    -- | Permission declaration (@perm@)
  | Perm
    -- | Conditional beginning delimiter (@if@)
  | If
    -- | Conditional middle delimiter (@then@)
  | Then
    -- | Conditional end delimiter (@else@)
  | Else
    -- | Pattern alias definition (@pattern@)
  | Pattern
    -- | Definition symbol (@:=@)
  | ColonEquals
    -- | Definition symbol (@≔@ unicode variant)
  | UniColonEquals
    -- | Assignment in do-expression (@<-@)
  | LeftArrow
    -- | Assignment in do-expression (@←@ unicode variant)
  | UniLeftArrow
    -- | Function type/case delimiter in pattern matching (@->@)
  | RightArrow
    -- | Function type/case delimiter in pattern matching (@→@ unicode variant)
  | UniRightArrow
    -- | Sub-permission declaration (@<:@)
  | LessColon
    -- | Wildcard (@_@)
  | Underscore
    -- | Wildcard (@·@ unicode variant)
  | UniUnderscore
    -- | Dot record access (@.@)
  | Dot
    -- | Typed hole (@?@)
  | Question
    -- | Left parenthesis (@(@)
  | LParen
    -- | Right parenthesis (@)@)
  | RParen
    -- | Left square bracket (@[@)
  | LBrack
    -- | Right square bracket (@]@)
  | RBrack
    -- | Left curly bracket (@{@)
  | LBrace
    -- | Right curly bracket (@}@)
  | RBrace
    -- | Comma (@,@)
  | Comma
    -- | Type specifier (@:@)
  | Colon
    -- | Identifier or mixfix backbone part
  | Identifier Text
    -- | Inline comments (@-- ...@)
  | InlineComment Text
    -- | Integral numbers
  | Integer Text
    -- | Floating point numbers
  | Float Text
    -- | String
  | String Text
    -- | Character
  | Character Text
  deriving (Show)
