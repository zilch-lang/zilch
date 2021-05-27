module Language.Zilch.Core.ConcreteSyntaxTree where

import Data.Located (Located)
import Data.Text (Text)

-- | A Zilch program is composed of many located declarations.
data Program
  = Program [Located TopLevelDeclaration]

-- | A top-level declaration with meta-attributes introduced in the @#[...]@ construct.
type TopLevelDeclaration = ([Located MetaSpecifier], Declaration)

-- | Any Zilch declaration
data Declaration
  = -- | A function definition
    Def
        FunctionDeclaration         -- ^ The head of the function
        (Located Expression)        -- ^ The value of the function
        [Located Declaration]       -- ^ @where@-bound functions
  | -- | An enumeration definition
    Enum
      (Located Identifier)                    -- ^ The name of the enumeration
      [Located (Parameter Kind)]              -- ^ The type parameters with optional kind annotations
      [(Located Identifier, [Located Type])]  -- ^ The constructors with their parameters
  | -- | A record definition
    Record
      (Located Identifier)                  -- ^ The name of the record
      [Located (Parameter Kind)]            -- ^ The type parameters with optional kind annotations
      [(Located Identifier, Located Type)]  -- ^ The fields of the record
  | -- | A type alias
    Type
      (Located Identifier)        -- ^ The name of the type alias
      [Located (Parameter Kind)]  -- ^ The type parameters with optional kind annotations
      (Located Type)              -- ^ The type aliased
  | -- | A type class declaration
    Class
      (Located Identifier)           -- ^ The name of the type class
      [Located (Parameter Kind)]     -- ^ The parameters with optional kind annotations
      [Located Type]                 -- ^ The constraints on the type class head
      [Located FunctionDeclaration]  -- ^ The members of the type class
  | -- | A type class implementation
    Impl
      ()

data FunctionDeclaration
  = Decl
      (Located Identifier)        -- ^ The name of the declared function
      [Located (Parameter Kind)]  -- ^ A list of type parameters with optional kind annotations
      [Located (Parameter Type)]  -- ^ A list of parameters with optional types
      (Maybe (Located Type))      -- ^ The optional return type

-- | A parameter is an identifier whose type may be specified (or not).
type Parameter t = (Located Identifier, Maybe (Located t))

-- | The type of identifiers.
type Identifier = Text

-- | The associativity of an infix operator
data Associativity
  = L | R | N

-- | Meta-specifiers for top-level bindings.
data MetaSpecifier
  = -- | > infix  N
    --   > infixl N
    --   > infixr N
    Infix Associativity Integer
  | -- | > prefix N
    Prefix Integer
  | -- | > postfix N
    Postfix Integer
  | -- | > default
    DefaultImpl

-- | An expression is a list of atoms.
type Expression = [Located ExpressionAtom]

-- | A type is a list of atoms.
type Type = [Located TypeAtom]

data ExpressionAtom
  = -- | A lambda abstraction
    FnE
      [Located (Parameter Type)]  -- ^ The parameters of the lambda with optional type annotations
      (Located Expression)        -- ^ The return expression
  | -- | A conditional expression
    IfE
      (Located Expression)  -- ^ The condition
      (Located Expression)  -- ^ The expression returned if the condition is true
      (Located Expression)  -- ^ The expression returned if the condition is false
  | -- | A do-block
    DoE
      [Located DoStatement] -- ^ The statements in the do-block
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
  | -- | A parenthesized expression
    ParensE
      (Located Expression)

data DoStatement
  = -- | A function binding
    BindingD
      (Located Identifier)  -- ^ The name of the function
      (Located Expression)  -- ^ The value of the function
  | -- | A single expression
    ExprD
      (Located Expression)

-- | A pattern is a list of atoms.
type Pattern = [Located PatternAtom]

data PatternAtom
  = -- | The wildcard pattern
    WildcardP
  | -- | An enumeration constructor
    ConstructorP
      [Located Pattern]  -- ^ The constructor parameters
  | -- | An integral number
    IntegerP
      (Located Text)
  | -- | A parenthesized pattern
    ParensP
      (Located Pattern)

data TypeAtom
  = -- | A universally quantified type
    ForallT
      [Located (Parameter Kind)]   -- ^ The list of universally quantified type variables with optional kind quantification
      (Located Type)               -- ^ The universally quantified type
  | -- | A contrained type
    ConstrainedT
      [Located Type]  -- ^ The type constraints
      (Located Type)  -- ^ The constrained type
  | -- | A type-level function
    FunctionT
      [Located (Parameter Kind)]  -- ^ The function parameters
      (Located Type)              -- ^ The function return type
  | -- | A type-level function application
    ApplicationT
      (Located Type)  -- ^ The type-level function
      [Located Type]  -- ^ The parameters
  | -- | The wildcard type for anonymous type-level function construction
    WildcardT
  | -- | A type identified by its name
    IdentifierT
      (Located Text)  -- ^ The name of the type
  | -- | A parenthesized type
    ParensT
      (Located Type)
-------- Builtin type
  | -- | Pointer type
    PtrT
  | -- | Reference type
    RefT
  | -- | An unsigned integer
    UnsignedT
      Integer  -- ^ The width of the integer
  | -- | A signed integer
    SignedT
      Integer  -- ^ The width of the integer

-- | The type of types
data Kind
  = -- | The kind of fully applied (concrete) types
    TypeK
  | -- | The kind of type-level functions
    FunctionK
      [Located Kind]  -- ^ The parameters
      (Located Kind)  -- ^ The result
  | -- | A parenthesized kind
    ParensK
      (Located Kind)
