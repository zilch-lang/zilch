theory Driver
  imports
    Main
    "HOL-Library.Monad_Syntax"

    Hello_World.IO

    Diagnose.Diagnostic
    Syntax.AST
    Syntax.Lexer
    Syntax.Parser

    CLI.Flags
begin

type_synonym registered_files = \<open>String.literal \<rightharpoonup> String.literal\<close>

fun run_driver :: \<open>input_flags \<Rightarrow> ((String.literal diagnostic + (String.literal \<rightharpoonup> AST.module located)) \<times> registered_files) io\<close>
where \<open>run_driver (InputFlags idirs mods) = do {
         IO.return undefined
       }\<close>

end
