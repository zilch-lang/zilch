theory Digraph
  imports
    Main
    "HOL-Library.Predicate_Compile_Alternative_Defs"
    HOL.Complete_Lattices
begin

record 'a digraph =
  vertices :: \<open>'a set\<close>
  edges :: \<open>'a \<rightharpoonup> 'a set\<close>

definition empty :: \<open>'a digraph\<close>
where \<open>empty = \<lparr> vertices = {}, edges = Map.empty \<rparr>\<close>

lemma finite_empty: \<open>finite (vertices empty)\<close>
  by (simp add: empty_def)

hide_const (open) empty

definition add_vert :: \<open>'a \<Rightarrow> 'a digraph \<Rightarrow> 'a digraph\<close>
where \<open>add_vert x g \<equiv> \<lparr> vertices = {x} \<union> vertices g, edges = edges g \<rparr>\<close>

lemma finite_add_vert: \<open>finite (vertices G) \<Longrightarrow> finite (vertices (add_vert x G))\<close>
  by (simp add: add_vert_def)

definition add_edge :: \<open>'a \<times> 'a \<Rightarrow> 'a digraph \<Rightarrow> 'a digraph\<close>
where \<open>add_edge x g \<equiv> (let (a, b) = x in \<lparr> vertices = {a, b} \<union> vertices g, edges = (edges g)(a \<mapsto> {b} \<union> case_option {} id (edges g a)) \<rparr>)\<close>

lemma finite_add_edge: \<open>finite (vertices G) \<Longrightarrow> finite (vertices (add_edge (x, y) G))\<close>
  by (simp add: add_edge_def)

definition has_vertex :: \<open>'a \<Rightarrow> 'a digraph \<Rightarrow> bool\<close>
where \<open>has_vertex x g \<equiv> x \<in> vertices g\<close>

lemma has_vertex_empty: \<open>has_vertex x Digraph.empty \<longleftrightarrow> False\<close>
  by (simp add: has_vertex_def empty_def)

lemma has_vertex_add_vert: \<open>has_vertex x (add_vert x G)\<close>
  by (simp add: has_vertex_def add_vert_def)

lemma has_vertex_add_vert2: \<open>x \<noteq> y \<Longrightarrow> has_vertex x (add_vert y G) \<Longrightarrow> has_vertex x G\<close>
  by (simp add: has_vertex_def add_vert_def)

lemma has_vertex_add_edge_proj1: \<open>has_vertex x (add_edge (x, y) G)\<close>
  by (simp add: has_vertex_def add_edge_def)

lemma has_vertex_add_edge_proj2: \<open>has_vertex x (add_edge (y, x) G)\<close>
  by (simp add: has_vertex_def add_edge_def)

lemma has_vertex_add_edge2: \<open>x \<noteq> y \<Longrightarrow> x \<noteq> z \<Longrightarrow> has_vertex x (add_edge (y, z) G) \<Longrightarrow> has_vertex x G\<close>
  by (simp add: has_vertex_def add_edge_def)

definition postset :: \<open>'a \<Rightarrow> 'a digraph \<Rightarrow> 'a set\<close>
where \<open>postset x g \<equiv> {y. y \<in> the (edges g x)}\<close>

lemma postset_empty: \<open>postset x Digraph.empty = {}\<close>
  sorry

lemma postset_add_vert_empty: \<open>postset x (add_vert y Digraph.empty) = {}\<close>
  sorry

lemma finite_postset: \<open>finite (vertices G) \<Longrightarrow> \<forall>x \<in> vertices G. finite (postset x G)\<close>
  sorry

definition preset :: \<open>'a \<Rightarrow> 'a digraph \<Rightarrow> 'a set\<close>
where \<open>preset x g \<equiv> {y. x \<in> the (edges g y)}\<close>

lemma finite_preset: \<open>finite (vertices G) \<Longrightarrow> \<forall>x \<in> vertices G. finite (preset x G)\<close>
  sorry

text \<open>
  Returns \<open>Inr sort\<close> when the graph could be fully walked without finding cycles (\<open>sort\<close> is the associated topsort).
  Returns \<open>Inl cycle\<close> where \<open>cycle\<close> is the first cycle found in the graph.
\<close>
function walk_aux1 :: \<open>'a \<Rightarrow> 'a digraph \<Rightarrow> 'a list \<Rightarrow> 'a list + 'a list\<close>
     and walk_aux2 :: \<open>'a digraph \<Rightarrow> 'a list + 'a list \<Rightarrow> 'a set \<Rightarrow> 'a list + 'a list\<close>
where \<open>walk_aux1 root g stack = walk_aux2 g (Inr stack) (postset root g)\<close>

    | \<open>walk_aux2 g (Inl cycle) _ = Inl cycle\<close>
    | \<open>walk_aux2 g (Inr stack) vs = (
         if Set.is_empty vs
         then Inr stack
         else
           let v = Inf vs in
           let vs = vs - {v} in
           if v \<in> set stack
           then Inl (v # stack)
           else case walk_aux1 v g (v # stack) of
             Inl cycle \<Rightarrow> Inl cycle
           | Inr stack' \<Rightarrow> walk_aux2 g (Inr (List.remdups (stack @ stack'))) vs
       )\<close>
by pat_completeness auto
(* FIXME: Somehow \<open>Inf vs\<close> requires \<open>'a :: Inf\<close> *)

termination walk_aux1
  sorry
(* TODO: this will always terminate because we exit the DFS when we find a cycle.
 *       However, we may not be able to prove it with these definitions. *)

code_pred Finite_Set.fold_graph .

(* lemma [code]:
  \<open>Finite_Set.fold f z {} \<equiv> z\<close>
  \<open>Finite_Set.fold f z (insert x A) \<equiv> f x (Finite_Set.fold f z A)\<close>
  apply simp
  sorry *)

definition walk :: \<open>'a \<Rightarrow> 'a digraph \<Rightarrow> 'a list + 'a list\<close>
where \<open>walk x g \<equiv> walk_aux1 x g [x]\<close>

lemma walk_empty_graph: \<open>walk x Digraph.empty = Inr [x]\<close>
  sorry
(*   by (simp add: postset_empty walk_def) *)

hide_const walk_aux1 walk_aux2

text \<open>
  Tries to apply a topological sort on the directed graph (any root).
  The result is a left value containing a cycle if there is one, otherwise a right value with the full sort.
\<close>
fun topsort :: \<open>'a digraph \<Rightarrow> 'a list + 'a list\<close>
where \<open>topsort g = walk (SOME x. x \<in> vertices g) g\<close>

definition has_cycle_from :: \<open>'a \<Rightarrow> 'a digraph \<Rightarrow> 'a list option\<close>
where \<open>has_cycle_from x g \<equiv> case_sum Some (\<lambda>_. None) (walk x g)\<close>

lemma no_cycle_empty_graph: \<open>has_cycle_from x Digraph.empty = None\<close>
  sorry
  (* by (simp add: has_cycle_from_def postset_empty walk_def) *)

lemma no_cycle_singleton: \<open>has_cycle_from x (add_vert x Digraph.empty) = None\<close>
  sorry
  (* by (simp add: has_cycle_from_def postset_add_vert_empty walk_def) *)

lemma has_cycle_topsort: \<open>has_cycle_from x G = Some c1 \<Longrightarrow> \<exists>c2. topsort G = Inl c2\<close>
  sorry

end
