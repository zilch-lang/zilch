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
and errors_to_warnings :: \<open>'msg diagnostic \<Rightarrow> 'msg diagnostic\<close>
and add_report :: \<open>'msg diagnostic \<Rightarrow> 'msg report \<Rightarrow> 'msg diagnostic\<close>
and add_file :: \<open>'msg diagnostic \<Rightarrow> string \<Rightarrow> string \<Rightarrow> 'msg diagnostic\<close>

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

end
