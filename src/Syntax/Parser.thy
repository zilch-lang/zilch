theory Parser
  imports
    Main
    Syntax.Tokens
    Located.At
    Diagnose.Diagnostic
    Syntax.CST
begin

axiomatization
  run_parser :: \<open>string \<Rightarrow> token located list \<Rightarrow> (string diagnostic + (CST.module located \<times> string diagnostic))\<close>

(**********************************************)

code_reserved Haskell runParser

code_printing
  constant run_parser \<rightharpoonup> (Haskell) "Syntax.Parser.runParser"

end
