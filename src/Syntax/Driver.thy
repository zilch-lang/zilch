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

fun run_driver :: \<open>input_flags \<Rightarrow> ((String.literal diagnostic + (String.literal \<times> AST.module located) tree \<times> module_order) \<times> registered_files) io\<close>
where \<open>run_driver (InputFlags idirs mods) = do {
         parse_and_resolve_modules idirs mods;
         IO.return undefined
       }\<close>

(* TODO: don't forget to desugar after resolving all imports *)

end
