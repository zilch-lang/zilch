theory CST
  imports
    Main
    Located.At
    Syntax.ExtraList
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

(******************************************)

function (sequential)
         def_tree_height :: \<open>def' located \<Rightarrow> nat\<close>
     and parameter_tree_height :: \<open>parameter located \<Rightarrow> nat\<close>
     and expr_tree_height :: \<open>expr located \<Rightarrow> nat\<close>
where \<open>def_tree_height (Assume ps @@ _) = maximum_by parameter_tree_height 0 (concat ps) + 1\<close>
    | \<open>def_tree_height (Mutual ds @@ _) = maximum_by def_tree_height 0 ds + 1\<close>
    | \<open>def_tree_height (Val m _ ps ty @@ _) =
         max (case_option 0 expr_tree_height m)
             (max (maximum_by parameter_tree_height 0 (concat ps))
                  (expr_tree_height ty)) + 1\<close>
    | \<open>def_tree_height (Let m _ ps ty ex @@ _) =
         max (case_option 0 expr_tree_height m)
             (max (maximum_by  parameter_tree_height 0 (concat ps))
                  (max (case_option 0 expr_tree_height ty)
                       (expr_tree_height ex))) + 1\<close>
    | \<open>def_tree_height (Rec m _ ps ty ex @@ _) =
         max (case_option 0 expr_tree_height m)
             (max (maximum_by parameter_tree_height 0 (concat ps))
                  (max (case_option 0 expr_tree_height ty)
                       (expr_tree_height ex))) + 1\<close>

    | \<open>parameter_tree_height (Parameter _ m _ ty @@ _) =
         max (case_option 0 expr_tree_height m) (case_option 0 expr_tree_height ty) + 1\<close>

    | \<open>expr_tree_height (Identifier _ @@ _) = 0\<close>
    | \<open>expr_tree_height (Integer _ ty @@ _) = case_option 0 expr_tree_height ty + 1\<close>
    | \<open>expr_tree_height (ProductType ps ty @@ _) =
         max (maximum_by parameter_tree_height 0 ps) (expr_tree_height ty) + 1\<close>
    | \<open>expr_tree_height (Lambda ps ex @@ _) =
         max (maximum_by parameter_tree_height 0 (concat ps)) (expr_tree_height ex) + 1\<close>
    | \<open>expr_tree_height (MultiplicativeSigmaType ps ty @@ _) =
         max (maximum_by parameter_tree_height 0 ps) (expr_tree_height ty) + 1\<close>
    | \<open>expr_tree_height (AdditiveSigmaType ps ty @@ _) =
         max (maximum_by parameter_tree_height 0 ps) (expr_tree_height ty) + 1\<close>
    | \<open>expr_tree_height (MultiplicativeUnitType @@ _) = 0\<close>
    | \<open>expr_tree_height (MultiplicativeUnit @@ _) = 0\<close>
    | \<open>expr_tree_height (Local d ex @@ _) = max (def_tree_height d) (expr_tree_height ex) + 1\<close>
    | \<open>expr_tree_height (Application f xs @@ _) =
         max (expr_tree_height f)
             (maximum_by (maximum_by expr_tree_height 0 \<circ> snd) 0 xs) + 1\<close>
    | \<open>expr_tree_height (Parenthesized ex @@ _) = expr_tree_height ex + 1\<close>
    | \<open>expr_tree_height (Do ex @@ _) = expr_tree_height ex + 1\<close>
by pat_completeness auto

termination def_tree_height
  sorry
(* TODO: prove termination
 *
 *       this should always terminate because we are unfolding a level every time, in every definition
 *       we merely just walk the tree downwards here
 *)

fun toplevel_tree_height :: \<open>toplevel located \<Rightarrow> nat\<close>
where \<open>toplevel_tree_height (Binding _ d @@ _) = def_tree_height d + 1\<close>

fun module_tree_height :: \<open>module located \<Rightarrow> nat\<close>
where \<open>module_tree_height (Mod ts @@ _) = maximum_by toplevel_tree_height 0 ts + 1\<close>

(**************************************************)

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
