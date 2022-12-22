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
  Warn \<open>'msg option\<close> 'msg \<open>(position × 'msg marker) list\<close> \<open>('msg footnote) list\<close>
| Err \<open>'msg option\<close> 'msg \<open>(position × 'msg marker) list\<close> \<open>('msg footnote) list›

axiomatization
    warning_to_error :: \<open>'msg report \<Rightarrow> 'msg report›
and error_to_warning :: \<open>'msg report \<Rightarrow> 'msg report\<close>

(*****************************************************)

code_reserved Haskell Marker Note Report Warn Err This Where Blank Hint

code_printing
  type_constructor marker ⇀ (Haskell) "Error.Diagnose.Report.Marker _"
| constant This ⇀ (Haskell) "Error.Diagnose.Report.This"
| constant Where ⇀ (Haskell) "Error.Diagnose.Report.Where"
| constant Maybe ⇀ (Haskell) "Error.Diagnose.Report.Maybe"
| constant Blank ⇀ (Haskell) "Error.Diagnose.Report.Blank"

| type_constructor footnote ⇀ (Haskell) "Error.Diagnose.Report.Note _"
| constant Note ⇀ (Haskell) "Error.Diagnose.Report.Note"
| constant Hint ⇀ (Haskell) "Error.Diagnose.Report.Hint"

| type_constructor report ⇀ (Haskell) "Error.Diagnose.Report.Report _"
| constant Warn ⇀ (Haskell) "Error.Diagnose.Report.Warn"
| constant Err ⇀ (Haskell) "Error.Diagnose.Report.Err"

| constant warning_to_error ⇀ (Haskell) "Error.Diagnose.Report.warningToError"
| constant error_to_warning ⇀ (Haskell) "Error.Diagnose.Report.errorToWarning"

end
