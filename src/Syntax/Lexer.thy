theory Lexer
  imports
    Main
    Diagnose.Diagnostic
    Syntax.Tokens
    Located.At
begin

axiomatization
  run_lexer :: \<open>String.literal \<Rightarrow> String.literal \<Rightarrow> (String.literal diagnostic + (token located list \<times> String.literal diagnostic))\<close>

(*********************************************)

code_reserved Haskell runLexer

code_printing
  constant run_lexer \<rightharpoonup> (Haskell) "Syntax.Lexer.runLexer"

end
