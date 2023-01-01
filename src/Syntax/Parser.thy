theory Parser
  imports
    Main

    Syntax.Tokens
    Located.At
    Diagnose.Diagnostic
    Syntax.CST
begin

axiomatization
  run_parser :: \<open>String.literal \<Rightarrow> token located list \<Rightarrow> (String.literal diagnostic + (CST.module located \<times> String.literal diagnostic))\<close>

code_reserved Haskell runParser

code_printing
  constant run_parser \<rightharpoonup> (Haskell) "Syntax.Parser.runParser"

(***********************************************************)

function extract_imports_def :: \<open>CST.def' located \<Rightarrow> String.literal list list\<close>
     and extract_imports_parameter :: \<open>CST.parameter located \<Rightarrow> String.literal list list\<close>
     and extract_imports_expr :: \<open>CST.expr located \<Rightarrow> String.literal list list\<close>
where \<open>extract_imports_def (CST.Mutual ts @@ _) = ts \<bind> extract_imports_def\<close>
    | \<open>extract_imports_def (CST.Assume ps @@ _) = concat ps \<bind> extract_imports_parameter\<close>
    | \<open>extract_imports_def (CST.Val _ _ ps ty @@ _) =
         (concat ps \<bind> extract_imports_parameter) @ extract_imports_expr ty\<close>
    | \<open>extract_imports_def (CST.Let _ _ ps ty ex @@ _) =
         (concat ps \<bind> extract_imports_parameter)
           @ case_option [] extract_imports_expr ty
           @ extract_imports_expr ex\<close>
    | \<open>extract_imports_def (CST.Rec _ _ ps ty ex @@ _) =
         (concat ps \<bind> extract_imports_parameter)
           @ case_option [] extract_imports_expr ty
           @ extract_imports_expr ex\<close>

    | \<open>extract_imports_parameter (CST.Parameter _ _ _ ty @@ _) = case_option [] extract_imports_expr ty\<close>

    | \<open>extract_imports_expr (CST.Identifier _ @@ _) = []\<close>
    | \<open>extract_imports_expr (CST.Integer _ _ @@ _) = []\<close>
    | \<open>extract_imports_expr (CST.ProductType ps ty @@ _) =
         (ps \<bind> extract_imports_parameter) @ extract_imports_expr ty\<close>
    | \<open>extract_imports_expr (CST.Lambda ps ex @@ _) =
         (concat ps \<bind> extract_imports_parameter) @ extract_imports_expr ex\<close>
    | \<open>extract_imports_expr (CST.MultiplicativeSigmaType ps ty @@ _) =
         (ps \<bind> extract_imports_parameter) @ extract_imports_expr ty\<close>
    | \<open>extract_imports_expr (CST.AdditiveSigmaType ps ty @@ _) =
         (ps \<bind> extract_imports_parameter) @ extract_imports_expr ty\<close>
    | \<open>extract_imports_expr (CST.MultiplicativeUnitType @@ _) = []\<close>
    | \<open>extract_imports_expr (CST.MultiplicativeUnit @@ _) = []\<close>
    | \<open>extract_imports_expr (CST.Local d ex @@ _) = extract_imports_def d @ extract_imports_expr ex\<close>
    | \<open>extract_imports_expr (CST.Application f xs @@ _) =
         extract_imports_expr f @ (xs \<bind> (\<lambda>(_, as). as \<bind> extract_imports_expr))\<close>
    | \<open>extract_imports_expr (CST.Parenthesized ex @@ _) = extract_imports_expr ex\<close>
    | \<open>extract_imports_expr (CST.Do ex @@ _) = extract_imports_expr ex\<close>
by pat_completeness auto

termination extract_imports_def
  apply (relation \<open>measure (case_sum def_tree_height (case_sum parameter_tree_height expr_tree_height))\<close>)
  apply (simp_all add: f_of_max_is_less f_of_max_is_less_than_max le_imp_less_Suc)
  apply (metis UN_I f_of_max_is_less le_imp_less_Suc max.coboundedI1 max.commute set_concat)
  apply (metis UN_I f_of_max_is_less le_imp_less_Suc max.coboundedI1 max.commute set_concat)
  apply (metis UN_I f_of_max_is_less le_imp_less_Suc max.coboundedI1 max.commute set_concat)
  apply (metis comp_apply dual_order.trans f_of_max_is_less le_imp_less_Suc max.coboundedI2 snd_conv)
  done

fun extract_imports_toplevel :: \<open>CST.toplevel located \<Rightarrow> String.literal list list\<close>
where \<open>extract_imports_toplevel (CST.Binding _ d @@ _) = extract_imports_def d\<close>

fun extract_imports :: \<open>CST.module located \<Rightarrow> String.literal list list\<close>
where \<open>extract_imports (CST.Mod ts @@ _) = ts \<bind> extract_imports_toplevel\<close>

end
