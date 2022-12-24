theory Lexer
  imports
    Main
    Diagnose.Diagnostic
    Syntax.Tokens
    Located.At
begin

axiomatization
  run_lexer :: \<open>string \<Rightarrow> string \<Rightarrow> (string diagnostic + (token located list \<times> string diagnostic))\<close>

(*********************************************)

code_reserved Haskell runLexer

code_printing
  constant run_lexer \<rightharpoonup> (Haskell) "Syntax.Lexer.runLexer"

end
