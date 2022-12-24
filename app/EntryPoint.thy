theory EntryPoint
  imports
    Main
    "HOL-Library.Monad_Syntax"

    Diagnose.Diagnostic
    Syntax.Driver
    Syntax.CST

    Hello_World.IO
begin

axiomatization
  exit_failure :: \<open>'a io\<close>

(*******************************************)

definition print_diagnostic_and_quit :: \<open>String.literal diagnostic \<Rightarrow> 'a io\<close>
where \<open>print_diagnostic_and_quit diag = do {
         print_diagnostic True True 4 diag;
         exit_failure
       }\<close>

fun go_parse :: \<open>String.literal list \<Rightarrow> ((String.literal diagnostic + CST.module located) \<times> (String.literal \<times> String.literal) list) io\<close>
where \<open>go_parse paths = undefined\<close>

fun go_typecheck :: \<open>'b \<Rightarrow> 'a io\<close>
where \<open>go_typecheck _ = undefined\<close>

definition entrypoint :: \<open>String.literal list \<Rightarrow> unit io\<close>
where \<open>entrypoint paths \<equiv> do {
         (result, files) \<leftarrow> go_parse paths;
         result \<leftarrow> go_typecheck result;
         IO.return ()
       }\<close>

(********************************************)

code_reserved Haskell exitFailure

code_printing
  constant exit_failure \<rightharpoonup> (Haskell) "System.IO.exitFailure"

export_code entrypoint in Haskell file_prefix "generated"

end
