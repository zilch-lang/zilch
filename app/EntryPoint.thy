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

(* export_code _ in Haskell *)

text \<open>
  Code generation in a custom directory.

  The default \<open>export_code\<close> command generates source code in a virtual file systemn
  which is inaccessible from the shell.
  This is merely a hack to generate our Haskell code so that it is available to
  our local stack project.
\<close>
ML\<open>
writeln "Generating Haskell code...";

val (files, _) =
  Code_Target.produce_code @{context} false [@{const_name entrypoint}] "Haskell" "EntryPoint" NONE [];

val project_root =
  let
    val project = getenv "PROJECT";
  in
    if project <> ""
      then Path.basic project
      else Path.parent (* That's because this file is not at the root of the project *)
  end;

val target = Path.append project_root (Path.basic "generated");

Isabelle_System.make_directory target;

List.app (fn ([file], content) => Bytes.write (Path.append target (Path.basic file)) content) files;

writeln ("Successfully exported generated Haskell code to " ^ Path.print target)
\<close>

end
