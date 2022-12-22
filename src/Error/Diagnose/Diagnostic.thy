theory Diagnostic
  imports
    Main
    Diagnose.Report
begin

typedecl 'msg diagnostic

axiomatization
    def :: \<open>'msg diagnostic\<close>
and has_reports :: \<open>'msg diagnostic \<Rightarrow> bool\<close>
and reports_of :: \<open>'msg diagnostic \<Rightarrow> ('msg report) list\<close>
and warnings_to_errors :: \<open>'msg diagnostic \<Rightarrow> 'msg diagnostic\<close>
and errors_to_warnings :: \<open>'msg diagnostic \<Rightarrow> 'msg diagnostic›
and add_report :: \<open>'msg diagnostic \<Rightarrow> 'msg report \<Rightarrow> 'msg diagnostic\<close>
and add_file :: \<open>'msg diagnostic \<Rightarrow> string \<Rightarrow> string \<Rightarrow> 'msg diagnostic\<close>

(*******************************************************)

code_printing
  type_constructor diagnostic ⇀ (Haskell) "Error.Diagnose.Diagnostic.Diagnostic _"
| constant def ⇀ (Haskell) "Error.Diagnose.Diagnostic.def"

| constant has_reports ⇀ (Haskell) "Error.Diagnose.Diagnostic.hasReports"
| constant reports_of ⇀ (Haskell) "Error.Diagnose.Diagnostic.reportsOf"
| constant warnings_to_errors ⇀ (Haskell) "Error.Diagnose.Diagnostic.warningsToErrors"
| constant errors_to_warnings ⇀ (Haskell) "Error.Diagnose.Diagnostic.errorsToWarnings"
| constant add_report ⇀ (Haskell) "Error.Diagnose.Diagnostic.addReport"
| constant add_file ⇀ (Haskell) "Error.Diagnose.Diagnostic.addFile"

end
