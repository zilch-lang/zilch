theory Flags
  imports
    Main
begin

datatype input_flags =
  InputFlags
    \<open>String.literal list\<close>
    \<open>String.literal list\<close>

datatype output_flags =
  OutputFlags
    \<open>String.literal\<close>

datatype all_flags =
  AllFlags
    input_flags
    output_flags

(*******************************************)

code_reserved Haskell InputFlags OutputFlags AllFlags

code_printing
  type_constructor input_flags \<rightharpoonup> (Haskell) "CLI.Flags.InputFlags"
| constant InputFlags \<rightharpoonup> (Haskell) "CLI.Flags.InputFlags"

| type_constructor output_flags \<rightharpoonup> (Haskell) "CLI.Flags.OutputFlags"
| constant OutputFlags \<rightharpoonup> (Haskell) "CLI.Flags.OutputFlags"

| type_constructor all_flags \<rightharpoonup> (Haskell) "CLI.Flags.AllFlags"
| constant AllFlags \<rightharpoonup> (Haskell) "CLI.Flags.AllFlags"

end
