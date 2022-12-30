theory Constraints
  imports
    Main
begin

datatype namespace =
  Module String.literal
| Access namespace String.literal

datatype formula =
  Top formula
| Bottom formula
| Exists String.literal
| In String.literal namespace

text \<open>
  An AND-separated list of atoms.
\<close>
type_synonym constraint = \<open>formula list\<close>

text \<open>
  A XOR-separated list of constraints.
\<close>
type_synonym system = \<open>constraint list\<close>

type_synonym global_system = \<open>system list\<close>

(****************************************************)

fun is_bottom :: \<open>formula \<Rightarrow> bool\<close>
where \<open>is_bottom (Bottom _) = True\<close>
    | \<open>is_bottom _ = False\<close>

fun is_top :: \<open>formula \<Rightarrow> bool\<close>
where \<open>is_top (Top _) = True\<close>
    | \<open>is_top _ = False\<close>

definition is_false :: \<open>constraint \<Rightarrow> bool\<close>
where \<open>is_false c \<equiv> list_ex is_bottom c\<close>

definition is_true :: \<open>constraint \<Rightarrow> bool\<close>
where \<open>is_true c \<equiv> list_all is_top c\<close>

definition is_solved :: \<open>constraint \<Rightarrow> bool\<close>
where \<open>is_solved c \<equiv> (is_false c \<or> is_true c)\<close>

definition is_fully_solved :: \<open>system \<Rightarrow> bool\<close>
where \<open>is_fully_solved s \<equiv> list_all is_solved s\<close>

fun only_false_constraint :: \<open>constraint \<Rightarrow> formula option\<close>
where \<open>only_false_constraint [] = None\<close>
    | \<open>only_false_constraint (Bottom f # _) = Some f\<close>
    | \<open>only_false_constraint (_ # fs) = only_false_constraint fs\<close>

fun is_true_exists :: \<open>formula \<Rightarrow> bool\<close>
where \<open>is_true_exists (Top (Exists _)) = True\<close>
    | \<open>is_true_exists _ = False\<close>

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
