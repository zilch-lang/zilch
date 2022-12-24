theory Tokens
  imports
    Main
begin

text \<open>
  An abstract token type because we don't need to be able to look at them.
\<close>
typedecl token

(********************************************)

code_reserved Haskell Token

code_printing
  type_constructor token \<rightharpoonup> (Haskell) "Syntax.Tokens.Token"

end
