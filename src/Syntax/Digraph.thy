theory Digraph
  imports
    Main
    "HOL-Library.Predicate_Compile_Alternative_Defs"
    HOL.Complete_Lattices
    "HOL-Data_Structures.Tree_Set"
    "HOL-Data_Structures.Tree_Map"
    (* "HOL-Data_Structures.HOL-Library.Tree" *)
begin

definition fold_set :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a tree \<Rightarrow> 'b\<close>
where \<open>fold_set f x t \<equiv> List.fold f (preorder t) x\<close>

record ('a :: linorder) digraph =
  vertices :: \<open>'a tree\<close>
  edges :: \<open>('a \<times> 'a tree) tree\<close>

definition empty :: \<open>('a :: linorder) digraph\<close>
where \<open>empty = \<lparr> vertices = \<langle>\<rangle>, edges = \<langle>\<rangle> \<rparr>\<close>

hide_const (open) empty

definition add_vert :: \<open>('a :: linorder) \<Rightarrow> 'a digraph \<Rightarrow> 'a digraph\<close>
where \<open>add_vert x g \<equiv> \<lparr> vertices = Tree_Set.insert x (vertices g), edges = edges g \<rparr>\<close>

definition add_edge :: \<open>('a :: linorder) \<times> 'a \<Rightarrow> 'a digraph \<Rightarrow> 'a digraph\<close>
where \<open>add_edge x g \<equiv> (
         let (a, b) = x in
         \<lparr> vertices = Tree_Set.insert a (Tree_Set.insert b (vertices g)),
           edges = case Tree_Map.lookup (edges g) a of
             None \<Rightarrow> Tree_Map.update a (Tree_Set.insert b \<langle>\<rangle>) (edges g)
           | Some es \<Rightarrow> Tree_Map.update a (Tree_Set.insert b es) (edges g) \<rparr>)\<close>

definition has_vertex :: \<open>('a :: linorder) \<Rightarrow> 'a digraph \<Rightarrow> bool\<close>
where \<open>has_vertex x g \<equiv> isin (vertices g) x\<close>

lemma has_vertex_empty: \<open>has_vertex x Digraph.empty \<longleftrightarrow> False\<close>
  by (simp add: has_vertex_def empty_def)

(* lemma has_vertex_add_vert: \<open>has_vertex x (add_vert x G)\<close>
  by (simp add: has_vertex_def add_vert_def)

lemma has_vertex_add_vert2: \<open>x \<noteq> y \<Longrightarrow> has_vertex x (add_vert y G) \<Longrightarrow> has_vertex x G\<close>
  by (simp add: has_vertex_def add_vert_def)

lemma has_vertex_add_edge_proj1: \<open>has_vertex x (add_edge (x, y) G)\<close>
  by (simp add: has_vertex_def add_edge_def)

lemma has_vertex_add_edge_proj2: \<open>has_vertex x (add_edge (y, x) G)\<close>
  by (simp add: has_vertex_def add_edge_def)

lemma has_vertex_add_edge2: \<open>x \<noteq> y \<Longrightarrow> x \<noteq> z \<Longrightarrow> has_vertex x (add_edge (y, z) G) \<Longrightarrow> has_vertex x G\<close>
  by (simp add: has_vertex_def add_edge_def) *)

definition postset :: \<open>('a :: linorder) \<Rightarrow> 'a digraph \<Rightarrow> 'a tree\<close>
where \<open>postset x g \<equiv> case Tree_Map.lookup (edges g) x of
         None \<Rightarrow> \<langle>\<rangle>
       | Some es \<Rightarrow> fold_set (\<lambda>y s. if isin es y then Tree_Set.insert y s else s) \<langle>\<rangle> (vertices g)\<close>

lemma postset_empty: \<open>postset x Digraph.empty = \<langle>\<rangle>\<close>
  sorry

lemma postset_add_vert_empty: \<open>postset x (add_vert y Digraph.empty) = \<langle>\<rangle>\<close>
  sorry

definition preset :: \<open>('a :: linorder) \<Rightarrow> 'a digraph \<Rightarrow> 'a tree\<close>
where \<open>preset x g \<equiv> fold_set (\<lambda>y s. case Tree_Map.lookup (edges g) y of
                                      None \<Rightarrow> s
                                    | Some es \<Rightarrow> if isin es x then Tree_Set.insert y s else s) \<langle>\<rangle> (vertices g)\<close>

text \<open>
  Returns \<open>Inr sort\<close> when the graph could be fully walked without finding cycles (\<open>sort\<close> is the associated topsort).
  Returns \<open>Inl cycle\<close> where \<open>cycle\<close> is the first cycle found in the graph.
\<close>
function walk_aux1 :: \<open>('a :: linorder) \<Rightarrow> 'a digraph \<Rightarrow> 'a list \<Rightarrow> 'a list + 'a list\<close>
     and walk_aux2 :: \<open>'a digraph \<Rightarrow> 'a \<Rightarrow> 'a list + 'a list \<Rightarrow> 'a list + 'a list\<close>
where \<open>walk_aux1 root g stack = fold_set (walk_aux2 g) (Inr stack) (postset root g)\<close>

    | \<open>walk_aux2 g _ (Inl cycle) = Inl cycle\<close>
    | \<open>walk_aux2 g v (Inr stack) = (
         if List.member stack v
         then Inl (v # stack)
         else case walk_aux1 v g (v # stack) of
           Inl cycle \<Rightarrow> Inl cycle
         | Inr stack' \<Rightarrow> Inr (List.remdups (stack @ stack'))
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

definition walk :: \<open>('a :: linorder) \<Rightarrow> 'a digraph \<Rightarrow> 'a list + 'a list\<close>
where \<open>walk x g \<equiv> walk_aux1 x g [x]\<close>

lemma walk_empty_graph: \<open>walk x Digraph.empty = Inr [x]\<close>
  sorry
(*   by (simp add: postset_empty walk_def) *)

hide_const walk_aux1 walk_aux2

text \<open>
  Tries to apply a topological sort on the directed graph (any root).
  The result is a left value containing a cycle if there is one, otherwise a right value with the full sort.
\<close>
definition topsort :: \<open>('a :: linorder) digraph \<Rightarrow> 'a list + 'a list\<close>
where \<open>topsort g \<equiv> case vertices g of
         \<langle>\<rangle> \<Rightarrow> Inr []
       | \<langle>_, x, _\<rangle> \<Rightarrow> walk x g\<close>

definition has_cycle_from :: \<open>('a :: linorder) \<Rightarrow> 'a digraph \<Rightarrow> 'a list option\<close>
where \<open>has_cycle_from x g \<equiv> case_sum Some (\<lambda>_. None) (walk x g)\<close>

lemma no_cycle_empty_graph: \<open>has_cycle_from x Digraph.empty = None\<close>
  sorry
  (* by (simp add: has_cycle_from_def postset_empty walk_def) *)

lemma no_cycle_singleton: \<open>has_cycle_from x (add_vert x Digraph.empty) = None\<close>
  sorry
  (* by (simp add: has_cycle_from_def postset_add_vert_empty walk_def) *)

lemma has_cycle_topsort: \<open>has_cycle_from x G = Some c1 \<Longrightarrow> \<exists>c2. topsort G = Inl c2\<close>
  sorry

hide_const fold_set

end
