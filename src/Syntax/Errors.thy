theory Errors
  imports
    Main

    Diagnose.Diagnostic
    Diagnose.Report

    Syntax.Constraints
begin

fun join :: \<open>String.literal \<Rightarrow> String.literal list \<Rightarrow> String.literal\<close>
where \<open>join _ [] = 0\<close>
    | \<open>join _ [x] = x\<close>
    | \<open>join sep (x # y # zs) = x + sep + join sep (y # zs)\<close>

text \<open>
  Occurs when a command-line module name is deemed invalid (because it e.g. contains `=`).
\<close>
definition mk_invalid_cli_module_name_error :: \<open>String.literal \<Rightarrow> String.literal diagnostic\<close>
where \<open>mk_invalid_cli_module_name_error m =
         add_report def (Err None (STR ''Invalid module name '' + m) [] [])\<close>

text \<open>
  Occurs when a command-line module name does not correspond to any importable module in the
  include path.
  More specifically, this happens when a command-line module name has no associated constraint.
\<close>
definition mk_cannot_import_cli_module_error :: \<open>String.literal \<Rightarrow> String.literal diagnostic\<close>
where \<open>mk_cannot_import_cli_module_error m =
         add_report def (Err None (STR ''Cannot import '' + m + STR '' because it does not correspond to a valid file name in the include path'') []
           [Note (STR ''Files and directories cannot contain some reserved characters such as `/` or `:`.'')])\<close>

text \<open>
  Occurs when all constraint related to an import are false.
  In such situation, the import cannot be resolved.
\<close>
fun mk_cannot_resolve_import_error :: \<open>[position + String.literal list, formula list] \<Rightarrow> String.literal diagnostic\<close>
and mk_notes :: \<open>formula list \<Rightarrow> String.literal list\<close>
and mk_ns_str :: \<open>namespace \<Rightarrow> String.literal\<close>
where \<open>mk_cannot_resolve_import_error (Inl p) l =
         add_report def (Err None (STR ''TODO'') [] [])\<close>
    | \<open>mk_cannot_resolve_import_error (Inr m) l =
         add_report def (Err None (STR ''Cannot resolve import of '' + join (STR ''::'') m + STR '' on command-line'') []
           [Note (join (STR ''\<newline>'') (mk_notes l))])\<close>

    | \<open>mk_notes [] = []\<close>
    | \<open>mk_notes (Exists path # fs) = (STR ''- File '' + path + STR '' does not exist'') # mk_notes fs\<close>
    | \<open>mk_notes (In x n # fs) = (STR ''- '' + x + STR '' is not a public member of the namespace '' + mk_ns_str n) # mk_notes fs\<close>
    | \<open>mk_notes (Top _ # fs) = mk_notes fs\<close>
    | \<open>mk_notes (Bottom _ # fs) = mk_notes fs\<close>

    | \<open>mk_ns_str (Module path) = STR '''' + path\<close>
    | \<open>mk_ns_str (Access ns x) = mk_ns_str ns + STR ''::'' + x\<close>

hide_const mk_notes mk_ns_str

end
