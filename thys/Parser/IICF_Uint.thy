theory IICF_Uint
  imports
    Main
    Refine_Imperative_HOL.IICF
    Native_Word.Native_Cast_Uint
begin

(*commit_ignore_start*)
sledgehammer_params[provers="cvc4 cvc5 verit z3 e iprover leo2 leo3 satallax spass vampire zipperposition"]
(*commit_ignore_end*)

lemma id_uint8_const[id_rules]: \<open>PR_CONST (x :: uint8) ::\<^sub>i TYPE(uint8)\<close>
  by (rule itypeI)
lemma id_uint32_const[id_rules]: \<open>PR_CONST (x :: uint32) ::\<^sub>i TYPE(uint32)\<close>
  by (rule itypeI) 

definition [to_relAPP]: \<open>uint8_rel \<equiv> Id :: uint8 rel\<close>
definition [to_relAPP]: \<open>uint32_rel \<equiv> Id :: uint32 rel\<close>
definition [to_relAPP]: \<open>uint_rel \<equiv> Id :: uint rel\<close> 

(* definition \<open>uint8_assn \<equiv> (id_assn :: uint8 \<Rightarrow> _)\<close>
declare uint8_assn_def[symmetric, fcomp_norm_unfold]
definition \<open>uint32_assn \<equiv> (id_assn :: uint32 \<Rightarrow> _)\<close>
declare uint32_assn_def[symmetric, fcomp_norm_unfold]

lemma uint8_is_pure[safe_constraint_rules]: \<open>is_pure uint8_assn\<close>
  unfolding uint8_assn_def
  by simp
lemma uint32_is_pure[safe_constraint_rules]: \<open>is_pure uint32_assn\<close>
  unfolding uint32_assn_def
  by simp *) 

sepref_decl_op take_bit_uint8: \<open>take_bit :: nat \<Rightarrow> uint8 \<Rightarrow> uint8\<close> 
  :: \<open>nat_rel \<rightarrow> uint8_rel \<rightarrow> uint8_rel\<close>
  unfolding uint8_rel_def
  by (intro frefI nres_relI) auto  
(* lemma uint8_take_bit_aref: \<open>(take_bit, op_take_bit_uint8) \<in> nat_rel \<rightarrow> uint8_rel \<rightarrow> uint8_rel\<close>
  by (simp add: uint8_rel_def) 
sepref_decl_impl take_bit_uint8: uint8_take_bit_aref[sepref_param] . *)

sepref_decl_op bit_uint8: \<open>bit :: uint8 \<Rightarrow> nat \<Rightarrow> bool\<close>
  :: \<open>uint8_rel \<rightarrow> nat_rel \<rightarrow> bool_rel\<close>
  unfolding uint8_rel_def
  by (intro frefI nres_relI) auto 
lemma [def_pat_rules]: \<open>bit$w$n \<equiv> op_bit_uint8$w$n\<close>
  by auto 
lemma uint8_bit_aref: \<open>(bit, op_bit_uint8) \<in> uint8_rel \<rightarrow> nat_rel \<rightarrow> bool_rel\<close>
  unfolding uint8_rel_def
  by auto 
sepref_decl_impl bit_uint8: uint8_bit_aref[unfolded uint8_rel_def, sepref_param] .

sepref_decl_op uint_of_uint8: \<open>uint_of_uint8\<close>
  :: \<open>uint8_rel \<rightarrow> uint_rel\<close>
  unfolding uint8_rel_def uint_rel_def
  by (intro frefI nres_relI) auto 

sepref_decl_op uint8_of_uint: \<open>uint8_of_uint\<close>
  :: \<open>uint_rel \<rightarrow> uint8_rel\<close>
  unfolding uint8_rel_def uint_rel_def
  by (intro frefI nres_relI) auto 

sepref_decl_op take_bit_uint32: \<open>take_bit :: nat \<Rightarrow> uint32 \<Rightarrow> uint32\<close>
  :: \<open>nat_rel \<rightarrow> uint32_rel \<rightarrow> uint32_rel\<close>
  unfolding uint32_rel_def
  by (intro frefI nres_relI) auto 

sepref_decl_op bit_uint32: \<open>bit :: uint32 \<Rightarrow> nat \<Rightarrow> bool\<close>
  :: \<open>uint32_rel \<rightarrow> nat_rel \<rightarrow> bool_rel\<close>
  unfolding uint32_rel_def
  by (intro frefI nres_relI) auto 
lemma [def_pat_rules]: \<open>bit$w$n \<equiv> op_bit_uint32$w$n\<close>
  by auto 

sepref_decl_op uint_of_uint32: \<open>uint_of_uint32\<close>
  :: \<open>uint32_rel \<rightarrow> uint_rel\<close>
  unfolding uint32_rel_def uint_rel_def
  by (intro frefI nres_relI) auto 

sepref_decl_op uint32_of_uint: \<open>uint32_of_uint\<close>
  :: \<open>uint_rel \<rightarrow> uint32_rel\<close>
  unfolding uint32_rel_def uint_rel_def
  by (intro frefI nres_relI) auto 



definition \<open>f (x :: uint8) \<equiv> 
  let a = bit x 1;
      b = bit x 2 in
  a \<and> b\<close>
(* definition \<open>f' x \<equiv> mop_bit_uint8 x 5\<close>

lemma \<open>f' w \<le> \<Down> Id (f w)\<close>
  unfolding f_def f'_def
  by simp *)


sepref_definition f_impl is \<open>RETURN \<circ> f\<close>
  :: \<open>id_assn\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
  unfolding f_def
  

  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
  apply sepref_dbg_opt_init
  apply sepref_dbg_monadify

  apply sepref_dbg_trans_step+

  using sepref_fr_rules(2) 
   
  
  sorry 
  (* by sepref *)

(* ML\<open>
  val x = @{code f_impl} (Word8.fromInt 6) ()
\<close> *)

end 
