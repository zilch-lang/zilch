theory Diagnostic
  imports
    Main
    Diagnose.Report
    Hello_World.IO
begin

typedecl 'msg diagnostic

axiomatization
    def :: \<open>'msg diagnostic\<close>
and has_reports :: \<open>'msg diagnostic \<Rightarrow> bool\<close>
and reports_of :: \<open>'msg diagnostic \<Rightarrow> ('msg report) list\<close>
and warnings_to_errors :: \<open>'msg diagnostic \<Rightarrow> 'msg diagnostic\<close>
and errors_to_warnings :: \<open>'msg diagnostic \<Rightarrow> 'msg diagnostic\<close>
and add_report :: \<open>'msg diagnostic \<Rightarrow> 'msg report \<Rightarrow> 'msg diagnostic\<close>
and add_file :: \<open>'msg diagnostic \<Rightarrow> String.literal \<Rightarrow> String.literal \<Rightarrow> 'msg diagnostic\<close>
(* TODO: perhaps someday I'll add a \<open>'msg :: pretty\<close> constraint here *)
and print_diagnostic :: \<open>bool \<Rightarrow> bool \<Rightarrow> integer \<Rightarrow> 'msg diagnostic \<Rightarrow> unit io\<close>

(*******************************************************)

code_printing
  type_constructor diagnostic \<rightharpoonup> (Haskell) "Error.Diagnose.Diagnostic.Diagnostic _"
| constant def \<rightharpoonup> (Haskell) "Error.Diagnose.Diagnostic.def"

| constant has_reports \<rightharpoonup> (Haskell) "Error.Diagnose.Diagnostic.hasReports"
| constant reports_of \<rightharpoonup> (Haskell) "Error.Diagnose.Diagnostic.reportsOf"
| constant warnings_to_errors \<rightharpoonup> (Haskell) "Error.Diagnose.Diagnostic.warningsToErrors"
| constant errors_to_warnings \<rightharpoonup> (Haskell) "Error.Diagnose.Diagnostic.errorsToWarnings"
| constant add_report \<rightharpoonup> (Haskell) "Error.Diagnose.Diagnostic.addReport"
| constant add_file \<rightharpoonup> (Haskell) "Error.Diagnose.Diagnostic.addFile"

| constant print_diagnostic \<rightharpoonup> (Haskell) "Error.Diagnose.Diagnostic.printDiagnostic System.IO.stderr _ _ (Prelude.fromInteger _) Error.Diagnose.Style.defaultStyle _"

end
