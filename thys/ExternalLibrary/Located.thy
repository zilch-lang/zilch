theory Located
  imports
    Main
    Diagnose
    "HOL-Library.Code_Target_Nat"
begin

section \<open>Located data\<close> 

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

lemma [measure_function]: \<open>is_measure f \<Longrightarrow> is_measure (size_located f)\<close> ..

section \<open>Code generation setup\<close>

text \<open>
  We now setup the code generator so that it uses our Haskell variants internally.
  This ensures better compatibility (for later) with the libraries for N*.
\<close> 

code_reserved Haskell Located

code_printing 
  code_module ExternalLibrary_Located \<rightharpoonup> (Haskell) \<open>
{-# LANGUAGE PackageImports #-}

module ExternalLibrary_Located (module Exports) where

import "nsc-core" Data.Located as Exports
\<close> 

code_printing
  type_constructor located \<rightharpoonup> (Haskell) "ExternalLibrary'_Located.Located _"
| constant At \<rightharpoonup> (Haskell) infix 4 "ExternalLibrary'_Located.:@"

| constant get_pos \<rightharpoonup> (Haskell) "ExternalLibrary'_Located.getPos"
| constant unloc \<rightharpoonup> (Haskell) "ExternalLibrary'_Located.unLoc"

  (* Remove this instance as it already exists in the Haskell code. *)
| class_instance located :: \<open>HOL.equal\<close> \<rightharpoonup> (Haskell) -

end 
