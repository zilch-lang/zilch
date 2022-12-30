theory Desugarer
  imports
    Main

    Located.At

    Diagnose.Diagnostic

    Syntax.CST
    Syntax.AST
begin

fun run_desugarer :: \<open>CST.module located \<Rightarrow> String.literal diagnostic + AST.module located \<times> String.literal diagnostic\<close>
where \<open>run_desugarer _ = undefined\<close>

end
