theory Constraints
  imports
    Main
begin

datatype namespace =
  Module String.literal
| Access namespace String.literal

datatype formula =
  Top
| Bottom
| Exists String.literal
| In String.literal namespace

text \<open>
  An AND-separated list of atoms.
\<close>
type_synonym constraint = \<open>formula list\<close>

text \<open>
  An OR-separated list of constraints.
\<close>
type_synonym system = \<open>constraint list\<close>

type_synonym global_system = \<open>system list\<close>

(****************************************************)

code_reserved Haskell Namespace Module Access Top Bottom Exists In

code_printing
  type_constructor namespace \<rightharpoonup> (Haskell) "ImportResolver.Namespace"
| constant Module \<rightharpoonup> (Haskell) "ImportResolver.Module"
| constant Access \<rightharpoonup> (Haskell) "ImportResolver.Access"

| type_constructor formula \<rightharpoonup> (Haskell) "ImportResolver.Formula"
| constant Top \<rightharpoonup> (Haskell) "ImportResolver.Top"
| constant Bottom \<rightharpoonup> (Haskell) "ImportResolver.Bottom"
| constant Exists \<rightharpoonup> (Haskell) "ImportResolver.Exists"
| constant In \<rightharpoonup> (Haskell) "ImportResolver.In"

end
