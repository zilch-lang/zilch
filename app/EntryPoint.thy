theory EntryPoint
  imports
    Main
    "HOL-Library.Monad_Syntax"
    "HOL-Library.Code_Target_Int"
    "HOL-Library.Code_Target_Nat"

    Diagnose.Diagnostic
    Syntax.Driver
    Syntax.CST
    Syntax.AST

    CLI.Flags

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

definition add_all_files :: \<open>(String.literal \<times> String.literal) list \<Rightarrow> String.literal diagnostic \<Rightarrow> String.literal diagnostic\<close>
where \<open>add_all_files \<equiv> List.fold (\<lambda>(a, b) d. add_file d a b)\<close>

(* TODO: add files to diagnostic *)

fun go_typecheck :: \<open>(String.literal \<times> AST.module located) tree \<Rightarrow> String.literal list list \<Rightarrow> unit io\<close>
where \<open>go_typecheck asts mods = IO.return ()\<close>

term run_driver

fun entrypoint :: \<open>all_flags \<Rightarrow> unit io\<close>
where \<open>entrypoint (AllFlags input output) = do {
         (result, files) \<leftarrow> run_driver input;
         let files = inorder files;
         case result of
           Inl diag \<Rightarrow> print_diagnostic_and_quit (add_all_files files diag)
         | Inr (asts, mods) \<Rightarrow> go_typecheck asts mods
       }\<close>

(********************************************)

code_reserved Haskell exitFailure

code_printing
  constant exit_failure \<rightharpoonup> (Haskell) "System.Exit.exitFailure"

  (* Just for the sake of interacting with Haskell code... *)
| type_constructor sum \<rightharpoonup> (Haskell) "Prelude.Either _ _"
| constant Inl \<rightharpoonup> (Haskell) "Prelude.Left"
| constant Inr \<rightharpoonup> (Haskell) "Prelude.Right"

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
