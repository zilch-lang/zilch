theory Diagnose
  imports
    Main
    "HOL-Library.Code_Target_Nat"
begin

section \<open>Positioning markers in reports\<close>

text \<open>
  First of all, we define some type which retains all the wanted information to position e.g.
  markers in a diagnostic report.
  This type is actually implemented in Isabelle, and internally handled as a special Haskell
  type by setting up code-generation specially for this.
\<close> 

datatype position =
  Position \<open>nat \<times> nat\<close> \<open>nat \<times> nat\<close> string

fun from_point :: \<open>position \<Rightarrow> nat \<times> nat\<close>
where \<open>from_point (Position x _ _) = x\<close>

fun to_point :: \<open>position \<Rightarrow> nat \<times> nat\<close>
where \<open>to_point (Position _ x _) = x\<close>

fun in_file :: \<open>position \<Rightarrow> string\<close>
where \<open>in_file (Position _ _ x) = x\<close>

section \<open>Markers and reports\<close>

text \<open>
  Next we define the type and constructors for markers and reports.
  Same as for positions, these types are defined both in Isabelle and in Haskell, and are specially
  handled in the code generator.

  Note that in Isabelle, the requirement that \<open>'msg\<close> be pretty-printable is lifted, as we don't
  really need it, and it would take a lot of time and effort to port the library used for
  pretty-printing within \<^bold>\<open>diagnose\<close>.
\<close>

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

fun warning_to_error :: \<open>'msg report \<Rightarrow> 'msg report\<close> where
  \<open>warning_to_error (Warn code msg markers notes) = Err code msg markers notes\<close>
| \<open>warning_to_error (Err code msg markers notes) = Err code msg markers notes\<close>

fun error_to_warning :: \<open>'msg report \<Rightarrow> 'msg report\<close> where
  \<open>error_to_warning (Err code msg markers notes) = Warn code msg markers notes\<close>
| \<open>error_to_warning (Warn code msg markers notes) = Warn code msg markers notes\<close>

section \<open>Diagnostics\<close>

text \<open>
  Since diagnostic creation is restricted to specific functions on the Haskell side, we will
  basically mirror this here.
\<close> 

typedecl 'msg diagnostic

axiomatization
  empty_diagnostic :: \<open>'msg diagnostic\<close> and 
  has_reports :: \<open>'msg diagnostic \<Rightarrow> bool\<close> and 
  reports_of :: \<open>'msg diagnostic \<Rightarrow> ('msg report) list\<close> and 
  warnings_to_errors :: \<open>'msg diagnostic \<Rightarrow> 'msg diagnostic\<close> and 
  errors_to_warnings :: \<open>'msg diagnostic \<Rightarrow> 'msg diagnostic\<close> and 
  add_report :: \<open>'msg diagnostic \<Rightarrow> 'msg report \<Rightarrow> 'msg diagnostic\<close> and
  add_file :: \<open>'msg diagnostic \<Rightarrow> String.literal \<Rightarrow> String.literal \<Rightarrow> 'msg diagnostic\<close>

section \<open>Code generation setup\<close>

text \<open>
  Now we setup the code generator to take into account how all the above functions must be compiled.
  This allows us to specify where the constants we must use reside.
\<close> 

code_reserved Haskell Position Marker Note Report Warn Err This Where Blank Hint

code_printing
  code_module ExternalLibrary_Diagnose \<rightharpoonup> (Haskell) \<open>
module ExternalLibrary_Diagnose (module Exports) where

import Error.Diagnose.Position as Exports
import Error.Diagnose.Report as Exports
import Error.Diagnose.Diagnostic as Exports 
\<close>

code_printing
  type_constructor position \<rightharpoonup> (Haskell) "ExternalLibrary'_Diagnose.Position"
| constant Position \<rightharpoonup> (Haskell) "ExternalLibrary'_Diagnose.Position" 

| constant from_point \<rightharpoonup> (Haskell) "ExternalLibrary'_Diagnose.begin"
| constant to_point \<rightharpoonup> (Haskell) "ExternalLibrary'_Diagnose.end"
| constant in_file \<rightharpoonup> (Haskell) "ExternalLibrary'_Diagnose.file"

  (* Suppress unwanted class instances, because we already have them. *)
| class_instance position :: \<open>HOL.equal\<close> \<rightharpoonup> (Haskell) -

| type_constructor marker \<rightharpoonup> (Haskell) "ExternalLibrary'_Diagnose.Marker _"
| constant This \<rightharpoonup> (Haskell) "ExternalLibrary'_Diagnose.This"
| constant Where \<rightharpoonup> (Haskell) "ExternalLibrary'_Diagnose.Where"
| constant Maybe \<rightharpoonup> (Haskell) "ExternalLibrary'_Diagnose.Maybe"
| constant Blank \<rightharpoonup> (Haskell) "ExternalLibrary'_Diagnose.Blank"

| type_constructor footnote \<rightharpoonup> (Haskell) "ExternalLibrary'_Diagnose.Note _"
| constant Note \<rightharpoonup> (Haskell) "ExternalLibrary'_Diagnose.Note"
| constant Hint \<rightharpoonup> (Haskell) "ExternalLibrary'_Diagnose.Hint"

| type_constructor report \<rightharpoonup> (Haskell) "ExternalLibrary'_Diagnose.Report _"
| constant Warn \<rightharpoonup> (Haskell) "ExternalLibrary'_Diagnose.Warn"
| constant Err \<rightharpoonup> (Haskell) "ExternalLibrary'_Diagnose.Err"

| constant warning_to_error \<rightharpoonup> (Haskell) "ExternalLibrary'_Diagnose.warningToError"
| constant error_to_warning \<rightharpoonup> (Haskell) "ExternalLibrary'_Diagnose.errorToWarning"

| type_constructor diagnostic \<rightharpoonup> (Haskell) "ExternalLibrary'_Diagnose.Diagnostic _"
| constant empty_diagnostic \<rightharpoonup> (Haskell) "ExternalLibrary'_Diagnose.def"

| constant has_reports \<rightharpoonup> (Haskell) "ExternalLibrary'_Diagnose.hasReports"
| constant reports_of \<rightharpoonup> (Haskell) "ExternalLibrary'_Diagnose.reportsOf"
| constant warnings_to_errors \<rightharpoonup> (Haskell) "ExternalLibrary'_Diagnose.warningsToErrors"
| constant errors_to_warnings \<rightharpoonup> (Haskell) "ExternalLibrary'_Diagnose.errorsToWarnings"
| constant add_report \<rightharpoonup> (Haskell) "ExternalLibrary'_Diagnose.addReport"
| constant add_file \<rightharpoonup> (Haskell) "ExternalLibrary'_Diagnose.addFile"

end
