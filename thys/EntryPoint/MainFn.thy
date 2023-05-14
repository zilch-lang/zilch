theory MainFn
  imports
    Main
    EntryPoint
begin

text \<open>
  We only need to generate code explicitly for @{const entry_point}.
  All other functions used will be transitively generated.
\<close>

export_code entry_point in Haskell

end