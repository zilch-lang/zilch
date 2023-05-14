theory Intf_Directed_Graph
  imports
    Main
    Collections.Collections
    Graph_Theory.Pair_Digraph
    Graph_Theory.Vertex_Walk
    Graph_Theory.Arc_Walk
    Refine_Monadic.Refine_Monadic
begin

section \<open>Abstract directed graphs\<close>

text \<open>
  First, let's define the interface of our directed graph.
  The interface is parameterized by the interface of values in the nodes.

  Here is what we need the directed graph to be able to do:
  \<^item> Insert edges (and vertices) inside the graph;
  \<^item> Check if the graph contains a cycle;
  \<^item> Perform a topological sort of the elements;
  \<^item> Do a depth-first search;
\<close> 

consts i_digraph :: \<open>interface \<Rightarrow> interface\<close> 

definition [simp]: \<open>op_digraph_empty \<equiv> \<lparr> pverts = {}, parcs = {} \<rparr> :: 'k pair_pre_digraph\<close>
definition [simp]: \<open>op_digraph_add_vert G v \<equiv> G\<lparr> pverts := pverts G \<union> {v} \<rparr>\<close>
definition [simp]: \<open>op_digraph_add_arc G u v \<equiv>
  G\<lparr> pverts := pverts G \<union> {u, v}, parcs := parcs G \<union> {(u, v)} \<rparr>\<close>
definition [simp]: \<open>op_digraph_verts_of G \<equiv> pverts G\<close> 
definition [simp]: \<open>op_digraph_ex_cycle G \<equiv> \<exists> p. pre_digraph.cycle (with_proj G) p\<close>
definition [simp]: \<open>op_digraph_depth_first_search G u v \<equiv> \<exists> p. pre_digraph.apath G u p v\<close>
definition [simp]: \<open>op_digraph_top_sort G u \<equiv> do {
  ASSERT (\<not> op_digraph_ex_cycle G);
  w \<leftarrow> SPEC (\<lambda> w. set w = op_digraph_verts_of G \<and>
    list_all (\<lambda> u. \<exists> v \<in> op_digraph_verts_of G. \<exists> p. pre_digraph.apath G u p v) w);
  RETURN w
}\<close>

end