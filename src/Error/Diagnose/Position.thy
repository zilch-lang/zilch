theory Position
  imports
    Main
begin

datatype position =
  position \<open>nat \<times> nat\<close> \<open>nat \<times> nat\<close> string

fun from_point :: \<open>position \<Rightarrow> nat \<times> nat\<close>
where \<open>from_point (position x _ _) = x\<close>

fun to_point :: \<open>position \<Rightarrow> nat \<times> nat\<close>
where \<open>to_point (position _ x _) = x\<close>

fun in_file :: \<open>position \<Rightarrow> string\<close>
where \<open>in_file (position _ _ x) = x\<close>

(****************************************)

code_reserved Haskell Position

code_printing
  type_constructor position \<rightharpoonup> (Haskell) "Error.Diagnose.Position.Position"

| constant from_point \<rightharpoonup> (Haskell) "Error.Diagnose.Position.begin"
| constant to_point \<rightharpoonup> (Haskell) "Error.Diagnose.Position.end"
| constant in_file \<rightharpoonup> (Haskell) "Error.Diagnose.Position.file"

end
