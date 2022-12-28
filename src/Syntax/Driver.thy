theory Driver
  imports
    Main
    "HOL-Library.Monad_Syntax"

    Hello_World.IO

    Diagnose.Diagnostic
    Syntax.AST
    Syntax.Lexer
    Syntax.Parser
    Syntax.ImportResolver

    CLI.Flags
begin

fun run_driver :: \<open>input_flags \<Rightarrow> ((String.literal diagnostic + (String.literal \<rightharpoonup> AST.module located) \<times> module_order) \<times> registered_files) io\<close>
where \<open>run_driver (InputFlags idirs mods) = parse_and_resolve_modules idirs mods\<close>

end
