theory Errors
  imports
    Main

    Diagnose.Diagnostic
    Diagnose.Report
begin

definition mk_invalid_cli_module_name_error :: \<open>String.literal \<Rightarrow> String.literal diagnostic\<close>
where \<open>mk_invalid_cli_module_name_error m =
         add_report def (Err None (STR ''Invalid module name '' + m) [] [])\<close>

definition mk_cannot_import_cli_module_error :: \<open>String.literal \<Rightarrow> String.literal diagnostic\<close>
where \<open>mk_cannot_import_cli_module_error m =
         add_report def (Err None (STR ''Cannot import '' + m + STR '' because it does not correspond to a valid file name in the include path'') []
           [Note (STR ''Files and directories cannot contain some reserved characters such as `/` or `:`.'')])\<close>

end
