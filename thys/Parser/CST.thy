theory CST
  imports
    Main
    ExternalLibrary.Located
begin

section \<open>Haskell definition of the Concrete Syntax Tree\<close>

code_printing
  code_module Syntax_CST \<rightharpoonup> (Haskell) \<open>
{-# LANGUAGE EmptyDataDeriving #-}

module Syntax_CST where

import Data.Text (Text)
import ExternalLibrary_Located (Located)

-- | The type containing a whole compilation unit.
data Module
  = Mod [Located TopLevel]
  deriving (Show)

-- | Top-level bindings and type declarations.
data TopLevel
  = Binding
      Bool
      (Located Definition)
  deriving (Show)

data Definition
  = Let
      (Maybe (Located Multiplicity))
      (Located String)
      [[Located Parameter]]
      (Maybe (Located Expression))
      (Located Expression)
  | Rec
      (Maybe (Located Multiplicity))
      (Located String)
      [[Located Parameter]]
      (Maybe (Located Expression))
      (Located Expression)
  | Val
      (Maybe (Located Multiplicity))
      (Located String)
      [[Located Parameter]]
      (Located Expression)
  | Assume
      [[Located Parameter]]
  | Mutual
      [Located Definition]
  deriving (Show)

-- | Multiplicities are certain kinds of expressions.
type Multiplicity = Expression

data Implicitness
  = Implicit
  | Explicit
  deriving (Show)

data Parameter
  = Parameter
      Implicitness
      (Maybe (Located Multiplicity))
      (Maybe (Located String))
      (Maybe (Located Expression))
  deriving (Show)

data Expression
  = Identifier String
  | Integer
      (Located String)
      (Maybe (Located Expression))
  | ProductType
      [Located Parameter]
      (Located Expression)
  | Lambda
      [[Located Parameter]]
      (Located Expression)
  | MultiplicativeSigmaType
      [Located Parameter]
      (Located Expression)
  | AdditiveSigmaType
      [Located Parameter]
      (Located Expression)
  | MultiplicativeUnitType
  | MultiplicativeUnit
  | Local
      (Located Definition)
      (Located Expression)
  | Application
      (Located Expression)
      [(Implicitness, [Located Expression])]
  | Parenthesized
      (Located Expression)
  | Do
      (Located Expression)
  deriving (Show)
\<close>

section \<open>Isabelle definition of the Concrete Syntax Tree\<close>

datatype implicitness =
  Explicit
| Implicit

datatype expr =
  Identifier string
| Integer
    \<open>string located\<close>
    \<open>expr located option\<close>
| ProductType
    \<open>parameter located list\<close>
    \<open>expr located\<close>
| Lambda
    \<open>parameter located list list\<close>
    \<open>expr located\<close>
| MultiplicativeSigmaType
    \<open>parameter located list\<close>
    \<open>expr located\<close>
| AdditiveSigmaType
    \<open>parameter located list\<close>
    \<open>expr located\<close>
| MultiplicativeUnitType
| MultiplicativeUnit
| Local
    \<open>def' located\<close>
    \<open>expr located\<close>
| Application
    \<open>expr located\<close>
    \<open>(implicitness \<times> expr located list) list\<close>
| Parenthesized
    \<open>expr located\<close>
| Do
    \<open>expr located\<close>

and parameter =
  Parameter
    \<open>implicitness\<close>
    \<open>expr located option\<close>
    \<open>string located option\<close>
    \<open>expr located option\<close>

and def' =
  Let
    \<open>expr located option\<close>
    \<open>string located\<close>
    \<open>parameter located list list\<close>
    \<open>expr located option\<close>
    \<open>expr located\<close>
| Rec
    \<open>expr located option\<close>
    \<open>string located\<close>
    \<open>parameter located list list\<close>
    \<open>expr located option\<close>
    \<open>expr located\<close>
| Val
    \<open>expr located option\<close>
    \<open>string located\<close>
    \<open>parameter located list list\<close>
    \<open>expr located\<close>
| Assume
    \<open>parameter located list list\<close>
| Mutual
    \<open>def' located list\<close>

datatype toplevel =
  Binding bool \<open>def' located\<close>

datatype module =
  Mod \<open>toplevel located list\<close>

type_synonym multiplicity = expr

lemma [measure_function]: \<open>is_measure size_expr\<close> ..
lemma [measure_function]: \<open>is_measure size_def'\<close> ..
lemma [measure_function]: \<open>is_measure size_parameter\<close> ..

text \<open>
  Disallow using unqualified constructors, because we will surely have some other constructors
  with the same name for other abstract trees.
\<close>

hide_type (open) implicitness expr parameter def' toplevel module
hide_const (open) Explicit Implicit Identifier Integer ProductType Lambda
  MultiplicativeSigmaType AdditiveSigmaType MultiplicativeUnitType
  MultiplicativeUnit Local Application Parenthesized Do
  Let Rec Val Mutual Binding Mod

section \<open>Code generator setup\<close>

text \<open>
  Now we setup the code generator so that both definitions are linked together.
\<close>

code_printing
  type_constructor CST.expr \<rightharpoonup> (Haskell) "Syntax'_CST.Expression"
| constant CST.Identifier \<rightharpoonup> (Haskell) "Syntax'_CST.Identifier"
| constant CST.Integer \<rightharpoonup> (Haskell) "Syntax'_CST.Integer"
| constant CST.ProductType \<rightharpoonup> (Haskell) "Syntax'_CST.ProductType"
| constant CST.Lambda \<rightharpoonup> (Haskell) "Syntax'_CST.Lambda"
| constant CST.MultiplicativeSigmaType \<rightharpoonup> (Haskell) "Syntax'_CST.MultiplicativeSigmaType"
| constant CST.AdditiveSigmaType \<rightharpoonup> (Haskell) "Syntax'_CST.AdditiveSigmaType"
| constant CST.MultiplicativeUnitType \<rightharpoonup> (Haskell) "Syntax'_CST.MultiplicativeUnitType"
| constant CST.MultiplicativeUnit \<rightharpoonup> (Haskell) "Syntax'_CST.MultiplicativeUnit"
| constant CST.Local \<rightharpoonup> (Haskell) "Syntax'_CST.Local"
| constant CST.Application \<rightharpoonup> (Haskell) "Syntax'_CST.Application"
| constant CST.Parenthesized \<rightharpoonup> (Haskell) "Syntax'_CST.Parenthesized"
| constant CST.Do \<rightharpoonup> (Haskell) "Syntax'_CST.Do"

| type_constructor CST.parameter \<rightharpoonup> (Haskell) "Syntax'_CST.Parameter"
| constant CST.Parameter \<rightharpoonup> (Haskell) "Syntax'_CST.Parameter"

| type_constructor CST.def' \<rightharpoonup> (Haskell) "Syntax'_CST.Definition"
| constant CST.Let \<rightharpoonup> (Haskell) "Syntax'_CST.Let"
| constant CST.Rec \<rightharpoonup> (Haskell) "Syntax'_CST.Rec"
| constant CST.Val \<rightharpoonup> (Haskell) "Syntax'_CST.Val"
| constant CST.Assume \<rightharpoonup> (Haskell) "Syntax'_CST.Assume"
| constant CST.Mutual \<rightharpoonup> (Haskell) "Syntax'_CST.Mutual"

| type_constructor CST.toplevel \<rightharpoonup> (Haskell) "Syntax'_CST.TopLevel"
| constant CST.Binding \<rightharpoonup> (Haskell) "Syntax'_CST.Binding"

| type_constructor CST.module \<rightharpoonup> (Haskell) "Syntax'_CST.Module"
| constant CST.Mod \<rightharpoonup> (Haskell) "Syntax'_CST.Mod"

| type_constructor CST.implicitness \<rightharpoonup> (Haskell) "Syntax'_CST.Implicitness"
| constant CST.Implicit \<rightharpoonup> (Haskell) "Syntax'_CST.Implicit"
| constant CST.Explicit \<rightharpoonup> (Haskell) "Syntax'_CST.Explicit"

end
