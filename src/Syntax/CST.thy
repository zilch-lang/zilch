theory CST
  imports
    Main
    Located.At
begin

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

hide_type (open) implicitness expr parameter def' toplevel module
hide_const (open) Explicit Implicit Identifier Integer ProductType Lambda
                  MultiplicativeSigmaType AdditiveSigmaType MultiplicativeUnitType
                  MultiplicativeUnit Local Application Parenthesized Do
                  Let Rec Val Mutual Binding Mod

(************************************************)

(* code_reserved Haskell Expression Definition Parameter Module TopLevel
                      Mod Binding Let Rec Val Assume Mutual Identifier ProductType
                      Lambda MultiplicativeSigmaType AdditiveSigmaType MultiplicativeUnitType
                      MultiplicativeUnit Local Application Parenthesized Do *)

code_printing
  type_constructor CST.expr \<rightharpoonup> (Haskell) "Syntax.CST.Expression"
| constant CST.Identifier \<rightharpoonup> (Haskell) "Syntax.CST.Identifier"
| constant CST.Integer \<rightharpoonup> (Haskell) "Syntax.CST.Integer"
| constant CST.ProductType \<rightharpoonup> (Haskell) "Syntax.CST.ProductType"
| constant CST.Lambda \<rightharpoonup> (Haskell) "Syntax.CST.Lambda"
| constant CST.MultiplicativeSigmaType \<rightharpoonup> (Haskell) "Syntax.CST.MultiplicativeSigmaType"
| constant CST.AdditiveSigmaType \<rightharpoonup> (Haskell) "Syntax.CST.AdditiveSigmaType"
| constant CST.MultiplicativeUnitType \<rightharpoonup> (Haskell) "Syntax.CST.MultiplicativeUnitType"
| constant CST.MultiplicativeUnit \<rightharpoonup> (Haskell) "Syntax.CST.MultiplicativeUnit"
| constant CST.Local \<rightharpoonup> (Haskell) "Syntax.CST.Local"
| constant CST.Application \<rightharpoonup> (Haskell) "Syntax.CST.Application"
| constant CST.Parenthesized \<rightharpoonup> (Haskell) "Syntax.CST.Parenthesized"
| constant CST.Do \<rightharpoonup> (Haskell) "Syntax.CST.Do"

| type_constructor CST.parameter \<rightharpoonup> (Haskell) "Syntax.CST.Parameter"
| constant CST.Parameter \<rightharpoonup> (Haskell) "Syntax.CST.Parameter"

| type_constructor CST.def' \<rightharpoonup> (Haskell) "Syntax.CST.Definition"
| constant CST.Let \<rightharpoonup> (Haskell) "Syntax.CST.Let"
| constant CST.Rec \<rightharpoonup> (Haskell) "Syntax.CST.Rec"
| constant CST.Val \<rightharpoonup> (Haskell) "Syntax.CST.Val"
| constant CST.Assume \<rightharpoonup> (Haskell) "Syntax.CST.Assume"
| constant CST.Mutual \<rightharpoonup> (Haskell) "Syntax.CST.Mutual"

| type_constructor CST.toplevel \<rightharpoonup> (Haskell) "Syntax.CST.TopLevel"
| constant CST.Binding \<rightharpoonup> (Haskell) "Syntax.CST.Binding"

| type_constructor CST.module \<rightharpoonup> (Haskell) "Syntax.CST.Module"
| constant CST.Mod \<rightharpoonup> (Haskell) "Syntax.CST.Mod"

| type_constructor CST.implicitness \<rightharpoonup> (Haskell) "Syntax.CST.Implicitness"
| constant CST.Implicit \<rightharpoonup> (Haskell) "Syntax.CST.Implicit"
| constant CST.Explicit \<rightharpoonup> (Haskell) "Syntax.CST.Explicit"

end
