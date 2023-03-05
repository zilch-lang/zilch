theory Labelled_Digraph
  imports
    Main
    Graph_Theory.Pair_Digraph
begin

record ('a, 'b) labelled_pair_pre_digraph = \<open>'a pair_pre_digraph\<close> +
  labels :: \<open>'a \<times> 'a \<rightharpoonup> 'b\<close>

definition with_proj' :: \<open>('a, 'b) labelled_pair_pre_digraph \<Rightarrow> ('a, 'a \<times> 'b \<times> 'a) pre_digraph\<close>
where \<open>with_proj' G \<equiv> \<lparr> verts = pverts G,
                        arcs = { (u, l, v) | u l v. (u, v) \<in> parcs G \<and> (labels G)((u, v)) = Some l },
                        tail = fst,
                        head = snd \<circ> snd \<rparr>\<close>

definition add_arc :: \<open>[ 'a, 'b, 'a, ('a, 'b) labelled_pair_pre_digraph ] \<Rightarrow> ('a, 'b) labelled_pair_pre_digraph\<close>
where \<open>add_arc u l v G \<equiv> \<lparr> pverts = pverts G \<union> {u, v}, parcs = insert (u, v) (parcs G), labels = (labels G)((u, v) \<mapsto> l) \<rparr>\<close>

lemma add_arc_no_new_vertex: \<open>\<lbrakk> a \<in> pverts G; b \<in> pverts G \<rbrakk> \<Longrightarrow> pverts (add_arc a l b G) = pverts G\<close>
  by (auto simp add: add_arc_def)

definition remove_arc :: \<open>[ 'a, 'a, ('a, 'b) labelled_pair_pre_digraph ] \<Rightarrow> ('a, 'b) labelled_pair_pre_digraph\<close>
where \<open>remove_arc u v G \<equiv> G \<lparr> parcs := parcs G - {(u, v)}, labels := (labels G)((u, v) := None) \<rparr>\<close>

end
