theory Driver
  imports
    Main

    Hello_World.IO

    Diagnose.Diagnostic
    Syntax.AST
begin

type_synonym registered_files = \<open>String.literal \<rightharpoonup> String.literal\<close>

fun run_driver :: \<open>String.literal list \<Rightarrow> ((String.literal diagnostic + (String.literal \<rightharpoonup> AST.module located)) \<times> registered_files) io\<close>
where \<open>run_driver mods = IO.return undefined\<close>

end
