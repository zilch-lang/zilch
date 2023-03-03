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

end
