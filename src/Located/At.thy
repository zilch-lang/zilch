theory At
  imports
    Main
    Diagnose.Position
begin

datatype 'a located =
  At 'a position (infix \<open>@@\<close> 50)

fun unloc :: \<open>'a located \<Rightarrow> 'a\<close>
where \<open>unloc (x @@ _) = x\<close>

fun get_pos :: \<open>'a located \<Rightarrow> position\<close>
where \<open>get_pos (_ @@ p) = p\<close>

text \<open>
  Use this to compare two \<open>located\<close> values without comparing their positions.

  The default \<open>equal\<close> instance compares both, hence the need for this function.
\<close>
fun loc_eq :: \<open>'a located \<Rightarrow> 'a located \<Rightarrow> bool\<close>
where \<open>loc_eq (x @@ _) (y @@ _) = (x = y)\<close>

(***************************************************)

code_reserved Haskell Located

code_printing
  type_constructor located \<rightharpoonup> (Haskell) "Located.Located _"
| constant At \<rightharpoonup> (Haskell) infix 4 "Located.:@"

| constant get_pos \<rightharpoonup> (Haskell) "Located.getPos"
| constant unloc \<rightharpoonup> (Haskell) "Located.unLoc"

| class_instance located :: \<open>HOL.equal\<close> \<rightharpoonup> (Haskell) -

end
