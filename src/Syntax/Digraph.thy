theory Digraph
  imports
    Main
begin

record 'a digraph =
  vertices :: \<open>'a set\<close>
  edges :: \<open>'a \<rightharpoonup> 'a set\<close>

definition empty :: \<open>'a digraph\<close>
where \<open>empty = \<lparr> vertices = {}, edges = Map.empty \<rparr>\<close>

hide_const (open) empty

definition add_vert :: \<open>'a \<Rightarrow> 'a digraph \<Rightarrow> 'a digraph\<close>
where \<open>add_vert x g \<equiv> \<lparr> vertices = {x} \<union> vertices g, edges = edges g \<rparr>\<close>

definition add_edge :: \<open>'a \<times> 'a \<Rightarrow> 'a digraph \<Rightarrow> 'a digraph\<close>
where \<open>add_edge x g \<equiv> (let (a, b) = x in \<lparr> vertices = {a, b} \<union> vertices g, edges = (edges g)(a \<mapsto> {b} \<union> case_option {} id (edges g a)) \<rparr>)\<close>

definition has_vertex :: \<open>'a \<Rightarrow> 'a digraph \<Rightarrow> bool\<close>
where \<open>has_vertex x g \<equiv> x \<in> vertices g\<close>

text \<open>
  Tries to apply a topological sort on the directed graph (any root).
  The result is a left value containing a cycle if there is one, otherwise a right value with the full sort.
\<close>
fun topsort :: \<open>'a digraph \<Rightarrow> 'a list + 'a list\<close>
where \<open>topsort _ = undefined\<close>

end
