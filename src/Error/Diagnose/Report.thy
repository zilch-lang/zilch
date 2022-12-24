theory Report
  imports
    Main

    Diagnose.Position
begin

datatype 'msg marker =
  This 'msg
| Where 'msg
| Maybe 'msg
| Blank

datatype 'msg footnote =
  Note 'msg
| Hint 'msg

datatype 'msg report =
  Warn \<open>'msg option\<close> 'msg \<open>(position \<times> 'msg marker) list\<close> \<open>('msg footnote) list\<close>
| Err \<open>'msg option\<close> 'msg \<open>(position \<times> 'msg marker) list\<close> \<open>('msg footnote) list\<close>

axiomatization
    warning_to_error :: \<open>'msg report \<Rightarrow> 'msg report\<close>
and error_to_warning :: \<open>'msg report \<Rightarrow> 'msg report\<close>

(*****************************************************)

code_reserved Haskell Marker Note Report Warn Err This Where Blank Hint

code_printing
  type_constructor marker \<rightharpoonup> (Haskell) "Error.Diagnose.Report.Marker _"
| constant This \<rightharpoonup> (Haskell) "Error.Diagnose.Report.This"
| constant Where \<rightharpoonup> (Haskell) "Error.Diagnose.Report.Where"
| constant Maybe \<rightharpoonup> (Haskell) "Error.Diagnose.Report.Maybe"
| constant Blank \<rightharpoonup> (Haskell) "Error.Diagnose.Report.Blank"

| type_constructor footnote \<rightharpoonup> (Haskell) "Error.Diagnose.Report.Note _"
| constant Note \<rightharpoonup> (Haskell) "Error.Diagnose.Report.Note"
| constant Hint \<rightharpoonup> (Haskell) "Error.Diagnose.Report.Hint"

| type_constructor report \<rightharpoonup> (Haskell) "Error.Diagnose.Report.Report _"
| constant Warn \<rightharpoonup> (Haskell) "Error.Diagnose.Report.Warn"
| constant Err \<rightharpoonup> (Haskell) "Error.Diagnose.Report.Err"

| constant warning_to_error \<rightharpoonup> (Haskell) "Error.Diagnose.Report.warningToError"
| constant error_to_warning \<rightharpoonup> (Haskell) "Error.Diagnose.Report.errorToWarning"

end
