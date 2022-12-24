theory Parser
  imports
    Main
    Syntax.Tokens
    Located.At
    Diagnose.Diagnostic
    Syntax.CST
begin

axiomatization
  run_parser :: \<open>String.literal \<Rightarrow> token located list \<Rightarrow> (String.literal diagnostic + (CST.module located \<times> String.literal diagnostic))\<close>

(**********************************************)

code_reserved Haskell runParser

code_printing
  constant run_parser \<rightharpoonup> (Haskell) "Syntax.Parser.runParser"

end
