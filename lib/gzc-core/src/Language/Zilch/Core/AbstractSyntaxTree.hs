module Language.Zilch.Core.AbstractSyntaxTree where

import Data.Located (Located)
import Data.Text (Text)

data Module
  = Module
      ModuleHeader           -- ^ The header of the module, containing the export and import list
      [Located Declaration]  -- ^ The list of declarations in the module
  deriving (Show, Eq)

data ModuleHeader
  = ModHead
      (Maybe [(Maybe IEType, Located Identifier)])
      [Located Import]
  deriving (Show, Eq)

-- | An @import@ statement at the top of a module.
data Import
  = Import
      Bool                                                                      -- ^ Is the import opened/unqualified?
      (Located Identifier)                                                      -- ^ The module imported
      (Maybe (Located Identifier))                                              -- ^ An optional alias for the imported module
      (Maybe [(Maybe IEType, Located Identifier, Maybe (Located Identifier))])  -- ^ An optional import list with optional aliasing
  deriving (Show, Eq)

data IEType
  = ModuleIE
  | TypeIE
  | EffectIE
  deriving (Show, Eq)

data Declaration
  = -- | Function definition
    Def
        (Located FunctionDeclaration)  -- ^ The head of the function declaration
        (Located Expression)           -- ^ The value of the function
  | -- | Type alias
    Type
        (Located Identifier)        -- ^ The name of the alias
        [Located (Parameter Kind)]  -- ^ The type parameters with optional kind annotations
        (Located Type)              -- ^ The type aliased
  | -- | Enum definition
    Enum
        (Located Identifier)                    -- ^ The name of the enumeration
        [Located (Parameter Kind)]              -- ^ The type parameters with optional kind annotations
        [(Located Identifier, [Located Type])]  -- ^ Enumeration constructors
  | -- | Record definition
    Record
        (Located Identifier)                  -- ^ The name of the record
        [Located (Parameter Kind)]            -- ^ The type parameters with optional kind annotations
        [(Located Identifier, Located Type)]  -- ^ Record fields
  | -- | Type class declaration
    Class
        (Located Identifier)                  -- ^ Class name
        [Located (Parameter Kind)]            -- ^ Optionally kind-annotated type parameters
        [Located Type]                        -- ^ Type constraints on class head
        [(Located Identifier, Located Type)]  -- ^ Type class member functions
  | -- | Type class implementation
    Impl
        (Located Identifier)        -- ^ The name of the type class implemented
        [Located (Parameter Kind)]  -- ^ Universally quantified type variables in the head of the implementation, optionally kind-annotated
        [Located Type]              -- ^ The types whose implementation is defined for
        [Located Declaration]       -- ^ The definition of the function members
  deriving (Show, Eq)

-- | The head of a function declaration/definition.
data FunctionDeclaration
  = FunDecl
        (Located Identifier)        -- ^ The name of the function
        [Located (Parameter Kind)]  -- ^ Type parameters with optional kind annotations
        [Located Type]              -- ^ Type constraints on function head
  deriving (Show, Eq)

-- | A qualified identifier
type Identifier = ([Text], Text)

-- | An optionally @t@-annotated parameter.
type Parameter t = (Located Identifier, Maybe (Located t))

-- | Types at the type-level
data Type
  = -- | An anonymous function at the type-level
    LambdaT
        [Located (Parameter Kind)]  -- ^ The parameter of the lambda
        (Located Type)              -- ^ The return type of the lambda
  | -- | A function application at the type-level
    ApplicationT
        (Located Type)  -- ^ The function type
        [Located Type]  -- ^ The arguments to the function call
  | -- | A universally quantified type
    ForallT
        [Located (Parameter Kind)]  -- ^ The universally bound type variables with optional kind annotations
        [Located Type]              -- ^ Optional constraints on the universally bound variables
        (Located Type)              -- ^ The quantified type
  | -- | A type identified by its name
    NameT
        (Located Identifier) -- ^ The name of the type
--------- Builtin types
  | -- | The pointer type
    PtrT
  | -- | The reference type
    RefT
  | -- | The type of unsigned integers
    UnsignedT
        Integer -- ^ The width of the integer
  | -- | The type of signed integers
    SignedT
        Integer
  | -- | The type of characters
    CharT
  deriving (Show, Eq)

-- | Types at the kind-level
data Kind
  = -- | The kind of fully applied types
    TypeK
  | -- | The kind of type-level functions
    FunctionK
        [Located Kind]  -- ^ The parameters of the function
        (Located Kind)  -- ^ The result kind
  deriving (Show, Eq)

-- | An expression
data Expression
  = -- | A lambda abstraction
    LambdaE
        [Located (Parameter Type)]  -- ^ The parameters of the lambda with optional type annotations
        (Located Expression)        -- ^ The return expression
  | -- | A conditional expression
    IfE
      (Located Expression)  -- ^ The condition
      (Located Expression)  -- ^ The expression returned if the condition is true
      (Located Expression)  -- ^ The expression returned if the condition is false
  | -- | A @let@-@in@ expression
    LetE
      [Located Declaration]  -- ^ The variables bound in the @let@ expression
      (Located Expression)   -- ^ The result of the @let@ expression
  | -- | A pattern-matching expression
    CaseE
      (Located Expression)                    -- ^ The expression whose value is to match
      [(Located Pattern, Located Expression)] -- ^ The branches of the pattern matching
  | -- | A record literal
    RecordE
      [(Located Identifier, Located Expression)] -- ^ The fields of the record
  | -- | A variable
    IdentifierE
      (Located Identifier)  -- ^ The name of the identifier
  | -- | A typed hole
    TypedHoleE
  | -- | A record access
    RecordAccessE
      (Located Expression)  -- ^ The record to access
      (Located Identifier)  -- ^ The name of the fields to access
  | -- | Function application
    ApplicationE
      (Located Expression)  -- ^ The function to apply
      [Located Expression]  -- ^ The arguments of the application
  | -- | An integral number
    IntegerE
      (Located Text)
  | -- | A string
    StringE
      (Located Text)
  | -- | A character
    CharE
      (Located Text)
  deriving (Show, Eq)

data Pattern
  = -- | The wildcard pattern
    WildcardP
  | -- | An enumeration constructor
    ConstructorP
      [Located Pattern]  -- ^ The constructor parameters
  | -- | An integral number
    IntegerP
      (Located Text)
  | -- | A variable binding
    VariableP
      (Located Identifier)  -- ^ The name of the variable
  deriving (Show, Eq)
