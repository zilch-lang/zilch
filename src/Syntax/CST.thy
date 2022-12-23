theory CST
  imports
    Main
    Located.At
begin

datatype expr =
  Identifier string
| Integer
    \<open>string located\<close>
    \<open>expr located\<close>
| ProductType
    \<open>parameter located list\<close>
    \<open>expr located\<close>
| Lambda
    \<open>parameter located list\<close>
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
    \<open>expr located list\<close>
| Parenthesized
    \<open>expr located\<close>

and parameter =
  Parameter
    \<open>expr located option\<close>
    \<open>string located\<close>
    \<open>expr located\<close>

and def' =
  Let
    \<open>expr located option\<close>
    \<open>string located\<close>
    \<open>parameter located list list\<close>
    \<open>expr located\<close>
    \<open>expr located\<close>
| Rec
    \<open>expr located option\<close>
    \<open>string located\<close>
    \<open>parameter located list list\<close>
    \<open>expr located\<close>
    \<open>expr located\<close>
| Val
    \<open>expr located option\<close>
    \<open>string located\<close>
    \<open>parameter located list list\<close>
    \<open>expr located\<close>
| Assume
    \<open>expr located option\<close>
    \<open>string located\<close>
    \<open>parameter located list list\<close>
    \<open>expr located\<close>
| Mutual
    \<open>toplevel located list\<close>

and toplevel =
  Binding bool \<open>def' located\<close>

datatype module =
  Mod \<open>toplevel located list\<close>

(************************************************)

code_reserved Haskell Expression Definition Parameter Module TopLevel
                      Mod Binding Let Rec Val Assume Mutual Identifier ProductType
                      Lambda MultiplicativeSigmaType AdditiveSigmaType MultiplicativeUnitType
                      MultiplicativeUnit Local Application Parenthesized

code_printing
  type_constructor expr \<rightharpoonup> (Haskell) "Syntax.CST.Expression"
| constant Identifier \<rightharpoonup> (Haskell) "Syntax.CST.Identifier"
| constant Integer \<rightharpoonup> (Haskell) "Syntax.CST.Integer"
| constant ProductType \<rightharpoonup> (Haskell) "Syntax.CST.ProductType"
| constant Lambda \<rightharpoonup> (Haskell) "Syntax.CST.Lambda"
| constant MultiplicativeSigmaType \<rightharpoonup> (Haskell) "Syntax.CST.MultiplicativeSigmaType"
| constant AdditiveSigmaType \<rightharpoonup> (Haskell) "Syntax.CST.AdditiveSigmaType"
| constant MultiplicativeUnitType \<rightharpoonup> (Haskell) "Syntax.CST.MultiplicativeUnitType"
| constant MultiplicativeUnit \<rightharpoonup> (Haskell) "Syntax.CST.MultiplicativeUnit"
| constant Local \<rightharpoonup> (Haskell) "Syntax.CST.Local"
| constant Application \<rightharpoonup> (Haskell) "Syntax.CST.Application"
| constant Parenthesized \<rightharpoonup> (Haskell) "Syntax.CST.Parenthesized"

| type_constructor parameter \<rightharpoonup> (Haskell) "Syntax.CST.Parameter"
| constant Parameter \<rightharpoonup> (Haskell) "Syntax.CST.Parameter"

| type_constructor def' \<rightharpoonup> (Haskell) "Syntax.CST.Definition"
| constant Let \<rightharpoonup> (Haskell) "Syntax.CST.Let"
| constant Rec \<rightharpoonup> (Haskell) "Syntax.CST.Rec"
| constant Val \<rightharpoonup> (Haskell) "Syntax.CST.Val"
| constant Assume \<rightharpoonup> (Haskell) "Syntax.CST.Assume"
| constant Mutual \<rightharpoonup> (Haskell) "Syntax.CST.Mutual"

| type_constructor toplevel \<rightharpoonup> (Haskell) "Syntax.CST.TopLevel"
| constant Binding \<rightharpoonup> (Haskell) "Syntax.CST.Binding"

| type_constructor module \<rightharpoonup> (Haskell) "Syntax.CST.Module"
| constant Mod \<rightharpoonup> (Haskell) "Syntax.CST.Mod"

end
