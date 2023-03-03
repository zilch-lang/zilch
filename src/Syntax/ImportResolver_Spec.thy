theory ImportResolver_Spec
  imports
    Main
    Refine_Monadic.Refine_Monadic
    Graph_Theory.Pair_Digraph
    Syntax.ConstraintsSolver_Spec
    Syntax.Labelled_Digraph
begin

type_synonym cst_abs = unit

type_synonym path = string
type_synonym import = \<open>string list\<close>
type_synonym import_graph = \<open>(import \<times> path, Solver_Spec.conjunctive_system) labelled_pair_pre_digraph\<close>
type_synonym import_graph' = \<open>(import \<times> path) pair_pre_digraph\<close>
type_synonym import_cache = \<open>path \<rightharpoonup> cst_abs\<close>
type_synonym all_imports = \<open>path \<rightharpoonup> import\<close>
type_synonym import_constraints = \<open>(import \<times> (import \<times> string list) set) set\<close>

type_synonym namespaces_abs = \<open>(import \<times> path) \<rightharpoonup> unit\<close>

text \<open>
  An empty import graph simply contains no vertices and no edges.
\<close>
abbreviation empty_import_graph :: \<open>import_graph\<close>
where \<open>empty_import_graph \<equiv> \<lparr> pverts = {}, parcs = {}, labels = Map.empty \<rparr>\<close>

locale Resolver_Spec =
  fixes mk_paths_from_module_name :: \<open>import \<Rightarrow> (import \<times> string list) set\<close>
    and path_from_module_name :: \<open>import \<Rightarrow> string\<close>
    and parse_file_and_extract_imports :: \<open>path \<Rightarrow> cst_abs \<times> import list\<close>
    and make_constraints_from_path_and_modules :: \<open>[ path, string list ] \<Rightarrow> Solver_Spec.conjunctive_system\<close>
    and try_solve_constraint :: \<open>[ path \<Rightarrow> bool, Solver_Spec.conjunctive_system, import_cache, namespaces_abs ] \<Rightarrow> bool option \<times> namespaces_abs\<close>
    and does_file_exist :: \<open>path \<Rightarrow> bool\<close>

  assumes import_has_paths: \<open>\<forall> i. mk_paths_from_module_name i \<noteq> {}\<close>
      and paths_finite: \<open>\<forall> i. finite (mk_paths_from_module_name i)\<close>
      and paths_contain_import: \<open>\<forall> i. (\<forall> m \<in> set i. CHR ''/'' \<notin> set m) \<Longrightarrow> \<exists> m. (i, m) \<in> mk_paths_from_module_name i\<close>
      and import_name_has_unique_paths: \<open>\<forall> x i m i' m'. (i, m) \<in> mk_paths_from_module_name x \<and> (i', m') \<in> mk_paths_from_module_name x \<and> i = i' \<longrightarrow> m = m'\<close>
      and paths_uniqueness: \<open>\<forall> i i'. i \<noteq> i' \<longleftrightarrow> mk_paths_from_module_name i \<noteq> mk_paths_from_module_name i'\<close>
      and path_uniqueness: \<open>\<forall> i i'. i \<noteq> i' \<longleftrightarrow> path_from_module_name i \<noteq> path_from_module_name i'\<close>

      and \<open>\<forall> p. make_constraints_from_path_and_modules p [] = [Solver_Spec.Exists p]\<close>
      and \<open>\<forall> p ms. Solver_Spec.Exists p \<in> set (make_constraints_from_path_and_modules p ms)\<close>
begin

definition single_module_resolver_invar1 :: \<open>[ import, import set, import list ] \<Rightarrow> bool\<close>
where \<open>single_module_resolver_invar1 p is U \<equiv> set U = \<Union> { { i'. \<exists> m'. (i', m') \<in> mk_paths_from_module_name i } | i. \<exists> cst is'. parse_file_and_extract_imports (path_from_module_name p) = (cst, is') \<and> i \<in> (set is' - is) }\<close>

definition single_module_resolver_invar2 :: \<open>[ import, import list, import, (import \<times> string list) set, import list ] \<Rightarrow> bool\<close>
where \<open>single_module_resolver_invar2 i U i' is U' \<equiv> set U' = set U \<union> ({ i. \<exists> m. (i, m) \<in> mk_paths_from_module_name i' } - { i. \<exists> m. (i, m) \<in> is })\<close>

definition single_module_resolver :: \<open>[ import, import_cache, all_imports ] \<Rightarrow> (import list \<times> import_cache \<times> import_constraints \<times> all_imports) nres\<close>
where \<open>single_module_resolver i C I \<equiv> do {
         ASSUME (\<forall> p \<in> dom C. does_file_exist p);
         ASSUME (dom C = dom I);

         let p = path_from_module_name i;
         case C p of
           None \<Rightarrow> do {
             if does_file_exist p
             then
               let
                 (cst, is) = parse_file_and_extract_imports p;
                 C = C(p \<mapsto> cst);
                 Cs = { (i, mk_paths_from_module_name i') | i'. i' \<in> set is };
                                    \<comment>\<open>Insert the file in the cache, and generate some accessibility constraints\<close>
                 I = I(p \<mapsto> i)
               in do {
                 U \<leftarrow> FOREACH\<^bsup>single_module_resolver_invar1 i\<^esup>
                             (set is) (\<lambda> i' U. do {
                   U' \<leftarrow> FOREACH\<^bsup>single_module_resolver_invar2 i U i'\<^esup>
                           (mk_paths_from_module_name i') (\<lambda> (i, _) U. do {
                     RETURN (i # U)
                   }) U;
                   ASSERT (set U' = set U \<union> { i. \<exists> m. (i, m) \<in> mk_paths_from_module_name i' });
                   RETURN U'
                 }) [];
                 ASSERT (set U = \<Union> { { i. \<exists> m. (i, m) \<in> mk_paths_from_module_name i' } | i'. i' \<in> set is });
                 RETURN (U, C, Cs, I)
               }
             else do {
               ASSERT (\<not> does_file_exist p);
               RETURN ([], C, {}, I)
             }
           }
         | Some _ \<Rightarrow> RETURN ([], C, {}, I)
       }\<close>

lemma single_module_resolver_invar1_init:
  assumes \<open>does_file_exist (path_from_module_name i)\<close>
      and \<open>parse_file_and_extract_imports (path_from_module_name i) = (cst, b)\<close>
  shows \<open>single_module_resolver_invar1 i (set b) []\<close>
  unfolding single_module_resolver_invar1_def
  by (auto simp add: assms(2))

lemma single_module_resolver_invar2_init:
  assumes \<open>does_file_exist (path_from_module_name i)\<close>
      and \<open>parse_file_and_extract_imports (path_from_module_name i) = (cst, b)\<close>
      and \<open>x \<in> it\<close>
      and \<open>it \<subseteq> set b\<close>
      and \<open>single_module_resolver_invar1 i it U\<close>
  shows \<open>single_module_resolver_invar2 i U x (mk_paths_from_module_name x) U\<close>
  by (simp add: single_module_resolver_invar2_def)

lemma single_module_resolver_invar1_step:
  assumes \<open>does_file_exist (path_from_module_name i')\<close>
      and \<open>parse_file_and_extract_imports (path_from_module_name i') = (cst, b)\<close>
      and \<open>x \<in> it\<close>
      and \<open>it \<subseteq> set b\<close>
      and \<open>single_module_resolver_invar1 i' it U\<close>
      and \<open>single_module_resolver_invar2 i' U x {} U'\<close>
      and \<open>set U' = set U \<union> {i. \<exists> m. (i, m) \<in> mk_paths_from_module_name x}\<close>
  shows \<open>single_module_resolver_invar1 i' (it - {x}) U'\<close>
  using assms
  unfolding single_module_resolver_invar2_def single_module_resolver_invar1_def
  apply auto
  apply (metis (no_types, lifting) mem_Collect_eq)
  done

lemma single_module_resolver_invar2_step:
  assumes \<open>does_file_exist (path_from_module_name i')\<close>
      and \<open>parse_file_and_extract_imports (path_from_module_name i') = (cst, b)\<close>
      and \<open>x \<in> it\<close>
      and \<open>it \<subseteq> set b\<close>
      and \<open>single_module_resolver_invar1 i' it U\<close>
      and \<open>(i, m) \<in> ita\<close>
      and \<open>ita \<subseteq> mk_paths_from_module_name x\<close>
      and \<open>single_module_resolver_invar2 i' U x ita U'\<close>
  shows \<open>single_module_resolver_invar2 i' U x (ita - {(i, m)}) (i # U')\<close>
  using assms
  unfolding single_module_resolver_invar2_def
  apply auto
  apply (meson import_name_has_unique_paths subset_eq)
  done

lemma single_module_resolver_invar1_end1:
  assumes \<open>does_file_exist (path_from_module_name i')\<close>
      and \<open>parse_file_and_extract_imports (path_from_module_name i') = (cst, b)\<close>
      and \<open>single_module_resolver_invar1 i' {} U\<close>
      and \<open>x \<in> set U\<close>
  shows \<open>\<exists> xa. (\<exists> i'. xa = {i. \<exists> m. (i, m) \<in> mk_paths_from_module_name i'} \<and> i' \<in> set b) \<and> x \<in> xa\<close>
  using assms
  unfolding single_module_resolver_invar1_def
  by auto

lemma single_module_resolver_invar1_end2:
  assumes \<open>does_file_exist (path_from_module_name i)\<close>
      and \<open>parse_file_and_extract_imports (path_from_module_name i) = (cst, b)\<close>
      and \<open>single_module_resolver_invar1 i {} U\<close>
      and \<open>i' \<in> set b\<close>
      and \<open>(x, m) \<in> mk_paths_from_module_name i'\<close>
  shows \<open>x \<in> set U\<close>
  using assms
  unfolding single_module_resolver_invar1_def
  by auto

lemma single_module_resolver_invar2_end1:
  assumes \<open>does_file_exist (path_from_module_name i)\<close>
      and \<open>parse_file_and_extract_imports (path_from_module_name i) = (cst, b)\<close>
      and \<open>x \<in> it\<close>
      and \<open>it \<subseteq> set b\<close>
      and \<open>single_module_resolver_invar1 i it U\<close>
      and \<open>single_module_resolver_invar2 i U x {} U'\<close>
      and \<open>i' \<in> set U'\<close>
      and \<open>i' \<notin> set U\<close>
  shows \<open>\<exists> m. (i', m) \<in> mk_paths_from_module_name x\<close>
  using assms(6) assms(7) assms(8) single_module_resolver_invar2_def
  by auto

lemma single_module_resolver_invar2_end2:
  assumes \<open>does_file_exist (path_from_module_name i')\<close>
      and \<open>parse_file_and_extract_imports (path_from_module_name i') = (cst, b)\<close>
      and \<open>x \<in> it\<close>
      and \<open>it \<subseteq> set b\<close>
      and \<open>single_module_resolver_invar1 i' it U\<close>
      and \<open>single_module_resolver_invar2 i' U x {} U'\<close>
      and \<open>i \<in> set U\<close>
  shows \<open>i \<in> set U'\<close>
  using assms
  unfolding single_module_resolver_invar2_def
  by auto

lemma single_module_resolver_invar2_end3:
  assumes \<open>does_file_exist (path_from_module_name i')\<close>
      and \<open>parse_file_and_extract_imports (path_from_module_name i') = (cst, b)\<close>
      and \<open>x \<in> it\<close>
      and \<open>it \<subseteq> set b\<close>
      and \<open>single_module_resolver_invar1 i' it U\<close>
      and \<open>single_module_resolver_invar2 i' U x {} U'\<close>
      and \<open>(i, m) \<in> mk_paths_from_module_name x\<close>
  shows \<open>i \<in> set U'\<close>
  using assms(6) assms(7) single_module_resolver_invar2_def
  by auto

text \<open>
  Insert labelled edges inside the import graph to account for dependencies.
\<close>

definition populate_import_graph_invar1 :: \<open>[ import_graph, import_constraints, import_graph ] \<Rightarrow> bool\<close>
where \<open>populate_import_graph_invar1 G' Cs G \<equiv> True\<close>

definition populate_import_graph_invar2 :: \<open>[ import_graph, (import \<times> string list) set, import_graph ] \<Rightarrow> bool\<close>
where \<open>populate_import_graph_invar2 G' Ps G \<equiv> True\<close>

definition populate_import_graph :: \<open>[ import_graph, import_constraints ] \<Rightarrow> import_graph nres\<close>
where \<open>populate_import_graph G Cs \<equiv> FOREACH\<^bsup>populate_import_graph_invar1 G\<^esup> Cs (\<lambda> (i, paths) G. do {
         let p = path_from_module_name i;
         FOREACH\<^bsup>populate_import_graph_invar2 G\<^esup> paths (\<lambda> (i', ms') G'. do {
           let p' = path_from_module_name i';
           let G = add_arc (i, p) (make_constraints_from_path_and_modules p' ms') (i', p') G';
                       \<comment>\<open>Set a constraint system to be solved for this edge to remain in the trimmed import graph\<close>
           RETURN G'
         }) G
       }) G\<close>

definition populate_import_graph_post :: \<open>[ import_constraints, import_graph ] \<Rightarrow> bool\<close>
where \<open>populate_import_graph_post Cs G \<equiv> True\<close>

lemma populate_import_graph_correct: \<open>populate_import_graph G Cs \<le> SPEC (populate_import_graph_post Cs)\<close>
  sorry

text \<open>
  Trim the import graph by solving all constraints on the edges.
  Eventually, all constraints will be solved and the import graph returned contains a view
  of the dependency order.

  Note: we need to be careful here, and reject negative cycles (cycles where solving a constraint \<open>C₁\<close> depends
    on solving a constraint \<open>C₂\<close> which itself depends on solving \<open>C₁\<close>).
\<close>
definition trim_import_graph :: \<open>[ import_graph, import_cache ] \<Rightarrow> (import_graph' \<times> namespaces_abs) option nres\<close>
(* TODO: in the worst case, this loops indefinitely in case of a dependency cycle, which may be as
 * this single file:
 *
 * a.zc: ```
 * public open import a
 * ```
 *
 * We need to handle this in some way. *)
(* IDEA: instead of iterating through every edge until all constraints are solved,
 * - loop through all dependency cycles, and try to solve constraints
 *   - when no constraint is solved at all in the cycle, return an error
 *   - when at least one constraint is solved, break the cycle at that point
 * - loop through all remaining edges, solving constraints on the fly
 *   - if constraint successfully solves to ⊤, add edge to final import graph
 *   - if constraint successfully solves to ⊥, do nothing
 *   - if constraints does not successfully solve, continue and try to solve it later
 * *)
where \<open>trim_import_graph G C \<equiv> do {
         let edges = { (u, l, v) | u v l. ((u, v), l) \<in> Map.graph (labels G) };
         (_, G, Ns) \<leftarrow> WHILE\<^bsup>\<lambda> (_, G', Ns). { p. \<exists> i. (i, p) \<in> dom Ns } \<subseteq> dom C \<and> pverts G' \<subseteq> pverts G \<and> parcs G' \<subseteq> parcs G\<^esup>
                            (\<lambda> (U, _, _). U \<noteq> {}) (\<lambda> (U, G, Ns). do {
           e \<leftarrow> SPEC (\<lambda> e. e \<in> U);
           let (u, l, v) = e;

           let (res, Ns) = try_solve_constraint does_file_exist l C Ns;
           case res of
             None \<Rightarrow> RETURN (U, G, Ns)
           | Some res \<Rightarrow>
               let
                 U = U - {e};
                 G = if res
                     then \<lparr> pverts = {u, v} \<union> pverts G, parcs = insert (u, v) (parcs G) \<rparr>
                     else G
               in
                 RETURN (U, G, Ns)
         }) (edges, \<lparr> pverts = {}, parcs = {} \<rparr>, Map.empty);
         RETURN (Some (G, Ns))
       }\<close>

definition trim_import_graph_post :: \<open>[ import_cache, import_graph', namespaces_abs ] \<Rightarrow> bool\<close>
where \<open>trim_import_graph_post C G Ns \<equiv> True\<close>

definition trim_import_graph_post' :: \<open>[ import_cache, (import_graph' \<times> namespaces_abs) option ] \<Rightarrow> bool\<close>
where \<open>trim_import_graph_post' C x \<equiv>
         case x of None \<Rightarrow> True | Some (G, Ns) \<Rightarrow> trim_import_graph_post C G Ns\<close>

lemma trim_import_graph_correct: \<open>trim_import_graph G C \<le> SPEC (trim_import_graph_post' C)\<close>
  sorry

text \<open>
  Try to resolve all modules (as top-level ones).
\<close>
definition full_module_resolver_invar :: \<open>import list \<Rightarrow> import set \<times> import list \<times> import_cache \<times> import_constraints \<times> all_imports \<Rightarrow> bool\<close>
where \<open>full_module_resolver_invar is x \<equiv> case x of
         (P, is', C, Cs, I) \<Rightarrow> (\<forall> p \<in> dom I. does_file_exist p)
                                    \<comment>\<open>All registered imports have an existing assoticated path.\<close>
                            \<and> dom C = dom I
                                    \<comment>\<open>There are as many parsed CSTs than registered imports.\<close>
                            \<and> (\<forall> i. path_from_module_name i \<in> dom I \<longleftrightarrow> i \<in> ran I)
                                    \<comment>\<open>If the path of an import is registered, then the import is associated to it.\<close>
                            \<and> (\<forall> i \<in> ran I. I (path_from_module_name i) = Some i)
                                    \<comment>\<open>Every import is associated to its path (if it exists).\<close>
                            \<and> { i. \<exists> is. (i, is) \<in> Cs } \<subseteq> ran I
                                    \<comment>\<open>All the source imports in the dependency set are registered.\<close>
                            \<and> ran I = { i. i \<in> P \<and> does_file_exist (path_from_module_name i) }
                                    \<comment>\<open>All imports processed (with existing files) have been registered at some point.\<close>
                            \<and> (\<forall> i \<in> set is. does_file_exist (path_from_module_name i) \<longrightarrow> i \<in> set is' \<or> i \<in> P)
                                    \<comment>\<open>All initial imports are already processed or will be in the future.\<close>
                            \<and> (\<forall> (_, is) \<in> Cs. \<forall> (i, _) \<in> is. does_file_exist (path_from_module_name i))
                                    \<comment>\<open>All imports kept in the dependency graph relate to existing files only.\<close>
                            \<and> (\<forall> (_, is) \<in> Cs. \<forall> (i, _) \<in> is. i \<in> ran I \<or> i \<in> set is')
                                    \<comment>\<open>All imports which are dependency targets are either already processed or will be later.\<close>\<close>

definition full_module_resolver :: \<open>import list \<Rightarrow> (import_graph' \<times> import_cache \<times> namespaces_abs) option nres\<close>
(* TODO: this WHILE loop *should* always terminate because:
 * - there is a finite number of canonicalized file paths on the file system;
 * - we are not re-adding files that we already processed. *)
where \<open>full_module_resolver is \<equiv> do {
         ASSUME (is \<noteq> []);
         (P, is', C, Cs, I) \<leftarrow> WHILE\<^bsup>full_module_resolver_invar is \<^esup>
                                (\<lambda> (_, is, _, _, _). is \<noteq> []) (\<lambda> (P, is, C, Cs, I). do {
           (U, C, Cs', I) \<leftarrow> single_module_resolver (hd is) C I;
           let Cs' = { (i, { (i, l). (i, l) \<in> is \<and> does_file_exist (path_from_module_name i) }) | i is. (i, is) \<in> Cs' };
                      \<comment>\<open>Filter out files whose path do not exist.\<close>
           ASSERT (\<forall> (i, _) \<in> Cs'. I (path_from_module_name i) = Some i);
           ASSERT (does_file_exist (path_from_module_name (hd is)) \<longleftrightarrow> hd is \<in> ran I);
           RETURN (insert (hd is) P, U @ tl is, C, Cs \<union> Cs', I)
         }) ({}, is, Map.empty, {}, Map.empty);
         ASSERT (is' = []);
         ASSERT ({ i \<in> set is. does_file_exist (path_from_module_name i) } \<subseteq> P);
         ASSERT (\<forall> i \<in> P. does_file_exist (path_from_module_name i) \<longrightarrow> i \<in> ran I);
         ASSERT (\<forall> (i, _) \<in> Cs. I (path_from_module_name i) = Some i);
         ASSERT (\<forall> (_, is) \<in> Cs. \<forall> (i, _) \<in> is. I (path_from_module_name i) = Some i);
         ASSERT ((\<exists> i \<in> P. does_file_exist (path_from_module_name i)) \<longrightarrow> I \<noteq> Map.empty);
         ASSERT ((\<exists> i \<in> P. does_file_exist (path_from_module_name i)) \<longrightarrow> C \<noteq> Map.empty);

         \<comment>\<open>If not all imports in \<open>is\<close> are resolved to existing files, explicitly fail.\<close>
         if (\<exists> i \<in> set is. i \<notin> ran I)
         then RETURN None
         else do {
           let G = \<lparr> pverts = insert ([], '''') { (i, p). I p = Some i },
                     parcs = {},
                     labels = Map.empty \<rparr>;
           G \<leftarrow> populate_import_graph G Cs;
           res \<leftarrow> trim_import_graph G C;
           case res of
             None \<Rightarrow> RETURN None
           | Some (G, Ns) \<Rightarrow> do {
             ASSERT (pverts G \<noteq> {});
             ASSERT (([], '''') \<in> pverts G);
                        \<comment>\<open>The main root (which serves as the "top-most" top-level module) is still in the graph.\<close>
             ASSERT (\<forall> u \<in> pverts G. card { (v, w). (u, w) \<in> parcs G \<and> (u, v) \<in> parcs G \<and> fst w = fst v } \<le> 1);
                        \<comment>\<open>There is at most one edge coming from every @{term u} to a given module
                          (meaning that imports are not ambiguous within a single module).\<close>
             ASSERT (\<forall> i \<in> set is. \<exists>! u \<in> pverts G. fst u = i);
                        \<comment>\<open>All our top-level modules do not point to code entities.\<close>

             let C = C |` { p. \<exists> i. (i, p) \<in> pverts G };
             let Ns = Ns |` pverts G;
             RETURN (Some (G, C, Ns))
           }
         }
       }\<close>

lemma full_module_resolver_invar_init:
  assumes \<open>is \<noteq> []\<close>
  shows \<open>full_module_resolver_invar is ({}, is, Map.empty, {}, Map.empty)\<close>
  unfolding full_module_resolver_invar_def
  by force

lemma full_module_resolver_invar_step2:
  assumes \<open>\<forall> x \<in> dom I. does_file_exist x\<close>
      and \<open>dom C = dom I\<close>
      and \<open>is \<noteq> []\<close>
      and \<open>is' \<noteq> []\<close>
      and \<open>C (path_from_module_name (hd is)) = None\<close>
      and \<open>does_file_exist (path_from_module_name (hd is))\<close>
      and \<open>parse_file_and_extract_imports (path_from_module_name (hd is)) = (cst, b)\<close>
      and \<open>single_module_resolver_invar1 (hd is) {} U\<close>
      and \<open>set U = \<Union> { { i. \<exists> m. (i, m) \<in> mk_paths_from_module_name i' } | i'. i' \<in> set b }\<close>
      and \<open>hd is \<in> ran (I(path_from_module_name (hd is) \<mapsto> hd is))\<close>
      and \<open>full_module_resolver_invar is' (P, is, C, Cs, I)\<close>
  shows \<open>full_module_resolver_invar
           is'
           (insert (hd is) P,
            U @ tl is,
            C(path_from_module_name (hd is) \<mapsto> cst),
            Cs \<union> { (hd is, { (i, l). (i, l) \<in> isa \<and> does_file_exist (path_from_module_name i) } ) | isa. \<exists> i'. isa = mk_paths_from_module_name i' \<and> i' \<in> set b },
            I(path_from_module_name (hd is) \<mapsto> hd is))\<close>
  using assms
  proof -
    let ?I = \<open>I(path_from_module_name (hd is) \<mapsto> hd is)\<close>
    and ?C = \<open>C(path_from_module_name (hd is) \<mapsto> cst)\<close>
    and ?Cs = \<open>Cs \<union> { (hd is, { (i, l). (i, l) \<in> isa \<and> does_file_exist (path_from_module_name i) } ) | isa. \<exists> i'. isa = mk_paths_from_module_name i' \<and> i' \<in> set b }\<close>
    and ?is = \<open>U @ tl is\<close>
    and ?P = \<open>insert (hd is) P\<close>

    have \<open>\<forall> p \<in> dom ?I. does_file_exist p\<close>
      by (simp add: assms(1) assms(6))
    moreover have \<open>dom ?C = dom ?I\<close>
      by (simp add: assms(2))
    moreover have \<open>\<forall> i. (path_from_module_name i \<in> dom I) \<longleftrightarrow> (i \<in> ran I)\<close>
      using assms(11)
      unfolding full_module_resolver_invar_def
      by blast
        then have \<open>\<forall> i. (path_from_module_name i \<in> dom ?I) \<longleftrightarrow> (i \<in> ran ?I)\<close>
          by (metis assms(2) assms(5) domIff dom_fun_upd insert_iff option.discI path_uniqueness ran_map_upd)
    moreover have \<open>{ i. \<exists> is. (i, is) \<in> Cs } \<subseteq> ran I\<close>
      using assms(11)
      unfolding full_module_resolver_invar_def
      by blast
        then have \<open>{ i. \<exists> is. (i, is) \<in> ?Cs } \<subseteq> ran ?I\<close>
          by (smt (verit, ccfv_threshold) Pair_inject Un_iff assms(2) assms(5) domIff insert_iff mem_Collect_eq ran_map_upd subset_iff)
    moreover have ***: \<open>ran I = { i \<in> P. does_file_exist (path_from_module_name i) }\<close>
      using assms(11)
      unfolding full_module_resolver_invar_def
      by blast
        then have *: \<open>ran ?I = insert (hd is) (ran I)\<close>
          by (metis assms(2) assms(5) domIff ran_map_upd)
        then have **: \<open>{ i \<in> ?P. does_file_exist (path_from_module_name i) } = insert (hd is) { i \<in> P. does_file_exist (path_from_module_name i) }\<close>
          using assms(11) assms(6)
          unfolding full_module_resolver_invar_def
          by blast
        then have \<open>ran ?I = { i \<in> ?P. does_file_exist (path_from_module_name i) }\<close>
          using * ** ***
          by auto
    moreover have \<open>\<forall> i \<in> set is'. does_file_exist (path_from_module_name i) \<longrightarrow> i \<in> P \<or> i \<in> set is\<close>
      using assms(11)
      unfolding full_module_resolver_invar_def
      by fastforce
        then have \<open>\<forall> i \<in> set is'. does_file_exist (path_from_module_name i) \<longrightarrow> i \<in> ?P \<or> i \<in> set ?is\<close>
          by (metis Un_iff insertCI not_hd_in_tl set_append)
    moreover have \<open>\<forall> i \<in> ran I. I (path_from_module_name i) = Some i\<close>
      using assms(11)
      unfolding full_module_resolver_invar_def
      by blast
        then have \<open>\<forall> i \<in> ran ?I. ?I (path_from_module_name i) = Some i\<close>
          using * path_uniqueness
          by force
    moreover have **: \<open>\<forall> (_, is'') \<in> Cs. \<forall> (i, _) \<in> is''. does_file_exist (path_from_module_name i)\<close>
      using assms(11)
      unfolding full_module_resolver_invar_def
      by fastforce
        then have \<open>\<forall> (_, is'') \<in> ?Cs. \<forall> (i, _) \<in> is''. does_file_exist (path_from_module_name i)\<close>
        by fastforce
    moreover have \<open>\<forall> (_, is'') \<in> Cs. \<forall> (i, _) \<in> is''. i \<in> ran I \<or> i \<in> set is\<close>
      using assms(11)
      unfolding full_module_resolver_invar_def
      by fastforce
        then have \<open>\<forall> (_, is'') \<in> ?Cs. \<forall> (i, _) \<in> is''. i \<in> ran ?I \<or> i \<in> set ?is\<close>
          using assms(9) assms(6)
          apply auto
          using * not_hd_in_tl
          by fastforce
      (* This is almost trivial, but somehow we need to make all steps explicit here... *)
    ultimately show ?thesis
      by (auto simp add: full_module_resolver_invar_def)
  qed

lemma full_module_resolver_invar_step3:
  assumes \<open>\<forall> p \<in> dom I. does_file_exist p\<close>
      and \<open>dom C = dom I\<close>
      and \<open>is \<noteq> []\<close>
      and \<open>is' \<noteq> []\<close>
      and \<open>C (path_from_module_name (hd is)) = None\<close>
      and \<open>\<not> does_file_exist (path_from_module_name (hd is))\<close>
      and \<open>hd is \<notin> ran I\<close>
      and \<open>full_module_resolver_invar is' (P, is, C, Cs, I)\<close>
  shows \<open>full_module_resolver_invar is' (insert (hd is) P, tl is, C, Cs, I)\<close>
  using assms
  proof -
    have \<open>\<forall> i \<in> set is'. does_file_exist (path_from_module_name i) \<longrightarrow> i \<in> P \<or> i \<in> set is\<close>
      using assms(8)
      unfolding full_module_resolver_invar_def
      by fastforce
      then have \<open>\<forall> i \<in> set is'. does_file_exist (path_from_module_name i) \<longrightarrow> i \<in> insert (hd is) P \<or> i \<in> set (tl is)\<close>
        using not_hd_in_tl
        by fastforce
    moreover have \<open>\<forall> i. (path_from_module_name i \<in> dom I) \<longleftrightarrow> (i \<in> ran I)\<close>
      using assms(8)
      unfolding full_module_resolver_invar_def
      by blast
    moreover have \<open>{ i. \<exists> is. (i, is) \<in> Cs } \<subseteq> ran I\<close>
      using assms(8)
      unfolding full_module_resolver_invar_def
      by blast
    moreover have \<open>ran I = { i \<in> insert (hd is) P. does_file_exist (path_from_module_name i) }\<close>
      using assms(8) assms(6)
      unfolding full_module_resolver_invar_def
      by blast
    moreover have \<open>\<forall> i \<in> ran I. I (path_from_module_name i) = Some i\<close>
      using assms(8)
      unfolding full_module_resolver_invar_def
      by blast
    moreover have \<open>\<forall> (_, is'') \<in> Cs. \<forall> (i, _) \<in> is''. does_file_exist (path_from_module_name i)\<close>
      using assms(8)
      unfolding full_module_resolver_invar_def
      by fastforce
    moreover have \<open>\<forall> (_, is'') \<in> Cs. \<forall> (i, _) \<in> is''. i \<in> ran I \<or> i \<in> set is\<close>
      using assms(8)
      unfolding full_module_resolver_invar_def
      by blast
        then have \<open>\<forall> (_, is'') \<in> Cs. \<forall> (i, _) \<in> is''. i \<in> ran I \<or> i \<in> set (tl is)\<close>
        by (smt (verit, ccfv_threshold) assms(6) calculation(6) case_prodD case_prodI2 not_hd_in_tl)
    ultimately show ?thesis
      unfolding full_module_resolver_invar_def
      using assms(1) assms(2)
      by fastforce
  qed

lemma full_module_resolver_invar_step4:
  assumes \<open>\<forall> x \<in> dom I. does_file_exist x\<close>
      and \<open>dom C = dom I\<close>
      and \<open>is \<noteq> []\<close>
      and \<open>is' \<noteq> []\<close>
      and \<open>C (path_from_module_name (hd is)) = Some cst\<close>
      and \<open>hd is \<in> ran I\<close>
      and \<open>full_module_resolver_invar is' (P, is, C, Cs, I)\<close>
  shows \<open>full_module_resolver_invar is' (insert (hd is) P, tl is, C, Cs, I)\<close>
  using assms
  proof -
    have \<open>\<forall> i \<in> set is'. does_file_exist (path_from_module_name i) \<longrightarrow> i \<in> P \<or> i \<in> set is\<close>
      using assms(7)
      unfolding full_module_resolver_invar_def
      by fastforce
      then have \<open>\<forall> i \<in> set is'. does_file_exist (path_from_module_name i) \<longrightarrow> i \<in> insert (hd is) P \<or> i \<in> set (tl is)\<close>
        using not_hd_in_tl
        by fastforce
    moreover have \<open>\<forall> i. (path_from_module_name i \<in> dom I) \<longleftrightarrow> (i \<in> ran I)\<close>
      using assms(7)
      unfolding full_module_resolver_invar_def
      by blast
    moreover have \<open>{ i. \<exists> is. (i, is) \<in> Cs } \<subseteq> ran I\<close>
      using assms(7)
      unfolding full_module_resolver_invar_def
      by blast
    moreover have \<open>ran I = { i \<in> insert (hd is) P. does_file_exist (path_from_module_name i) }\<close>
      using assms(7) assms(6)
      unfolding full_module_resolver_invar_def
      by blast
    moreover have \<open>\<forall> i \<in> ran I. I (path_from_module_name i) = Some i\<close>
      using assms(7)
      unfolding full_module_resolver_invar_def
      by blast
    moreover have \<open>\<forall> (_, is'') \<in> Cs. \<forall> (i, _) \<in> is''. does_file_exist (path_from_module_name i)\<close>
      using assms(7)
      unfolding full_module_resolver_invar_def
      by fastforce
    moreover have \<open>\<forall> (_, is'') \<in> Cs. \<forall> (i, _) \<in> is''. i \<in> ran I \<or> i \<in> set is\<close>
      using assms(7)
      unfolding full_module_resolver_invar_def
      by blast
        then have \<open>\<forall> (_, is'') \<in> Cs. \<forall> (i, _) \<in> is''. i \<in> ran I \<or> i \<in> set (tl is)\<close>
        by (smt (verit, ccfv_threshold) assms(6) case_prodD case_prodI2 not_hd_in_tl)
    ultimately show ?thesis
      using assms(1) assms(2)
      unfolding full_module_resolver_invar_def
      by fastforce
  qed

theorem full_module_resolver_loop_preserves_invar:
  assumes \<open>full_module_resolver_invar is' (P, is, C, Cs, I)\<close>
      and \<open>is' \<noteq> []\<close>
      and \<open>is \<noteq> []\<close>
  shows \<open>single_module_resolver (hd is) C I \<le> SPEC
           (\<lambda>(U, C, Cs', I). do {
              ASSERT (\<forall> i. (\<exists> is. (i, is) \<in> Cs') \<longrightarrow> I (path_from_module_name i) = Some i);
              ASSERT (does_file_exist (path_from_module_name (hd is)) \<longleftrightarrow> hd is \<in> ran I);
              RETURN (insert (hd is) P, U @ tl is, C,
                Cs \<union> { (i, { (i, l). (i, l) \<in> is \<and> does_file_exist (path_from_module_name i) }) | i is. (i, is) \<in> Cs' },
                I)
            } \<le> SPEC (full_module_resolver_invar is'))\<close>
  unfolding single_module_resolver_def
  apply (intro refine_vcg; simp)
  using single_module_resolver_invar1_init
    apply presburger
  using paths_finite
    apply presburger
  using single_module_resolver_invar2_init
    apply presburger
  apply auto[1]
  using single_module_resolver_invar2_step
    apply presburger
  apply auto[1]
  using single_module_resolver_invar2_end1
    apply presburger
  using single_module_resolver_invar2_end2
    apply presburger
  apply (meson single_module_resolver_invar2_end3)
  using single_module_resolver_invar1_step
    apply presburger
  apply auto[1]
  using single_module_resolver_invar1_end1
    apply presburger
  apply (meson single_module_resolver_invar1_end2)
  apply (intro refine_vcg)
  apply (meson map_upd_Some_unfold ranI)
  using assms(1) assms(2) assms(3) full_module_resolver_invar_step2
    apply presburger
  apply (intro refine_vcg)
  apply (smt (verit, best) assms(1) case_prodD full_module_resolver_invar_def)
  using assms(1) assms(2) assms(3) full_module_resolver_invar_step3
    apply presburger
  apply (intro refine_vcg)
  apply (smt (verit, ccfv_threshold) assms(1) case_prodD domI full_module_resolver_invar_def)
  apply (metis assms(1) assms(2) assms(3) domI full_module_resolver_invar_step4)
  done

lemma full_module_resolver_assert7:
  assumes \<open>\<forall> (_, is) \<in> Cs. \<forall> (i, _) \<in> is. i \<in> ran I \<or> i \<in> set is'\<close>
       and \<open>is' = []\<close>
       and \<open>\<forall> i \<in> ran I. I (path_from_module_name i) = Some i\<close>
  shows \<open>\<forall> (_, is) \<in> Cs. \<forall> (i, _) \<in> is. I (path_from_module_name i) = Some i\<close>
  using assms
  by (auto, fastforce)

(***********************************************************************)

text \<open>
  We require that we are importing at least one module, and that every import contains
  at least a single element.
\<close>
definition full_module_resolver_pre :: \<open>import list \<Rightarrow> bool\<close>
where \<open>full_module_resolver_pre is \<equiv> is \<noteq> []
                                   \<and> (\<forall>i \<in> set is. i \<noteq> [])\<close>

text \<open>
  This is our postcondition.
\<close>
definition full_module_resolver_post :: \<open>[ import list, import_graph', import_cache, namespaces_abs ] \<Rightarrow> bool\<close>
where \<open>full_module_resolver_post is G C Ns \<equiv>
         \<not> (\<exists> u \<in> pverts G. u \<leftarrow>\<^sup>*\<^bsub>with_proj G\<^esub> u)
                \<comment>\<open>• The end import graph is acyclic, meaning that no module \<open>M\<close> tries to import itself,
                    or import a module which transitively imports \<open>M\<close>.\<close>
       \<and> (\<forall> i \<in> set is. \<exists> u \<in> pverts G. fst u = i)
                \<comment>\<open>• All our top-level imports are resolved (at least once) in the graph.\<close>
       \<and> (\<forall> u \<in> pverts G. card { (v, w) | v w. (u, w) \<in> parcs G \<and> (u, v) \<in> parcs G \<and> fst v = fst w } \<le> 1)
                \<comment>\<open>• There is at most one edge coming from every node \<open>u\<close> to a given module.
                    In other words, all imports are unambiguous.\<close>
       \<and> C \<noteq> Map.empty
                \<comment>\<open>• Since we require that the list of top-level modules be non-empty, our end cache
                    must also be non-empty.\<close>
       \<and> { p. \<exists> i. (i, p) \<in> pverts G } \<subseteq> dom C
                \<comment>\<open>• Consistency is key: all modules found in the graph must belong to the cache.\<close>
       \<and> { p. \<exists> i. (i, p) \<in> dom Ns } \<subseteq> dom C
                \<comment>\<open>• We don't have more namespaces than for each file in the cache.\<close>\<close>

definition full_module_resolver_post' :: \<open>[ import list, (import_graph' \<times> import_cache \<times> namespaces_abs) option ] \<Rightarrow> bool\<close>
where \<open>full_module_resolver_post' is r \<equiv>
         case r of None \<Rightarrow> True | Some (G, C, Ns) \<Rightarrow> full_module_resolver_post is G C Ns\<close>

text \<open>
  If the precondition holds, and the module resolver terminates, then the postcondition must hold.
\<close>
theorem full_module_resolver_correct:
  fixes I :: \<open>import list\<close>
  assumes \<open>full_module_resolver_pre I\<close>
  shows \<open>full_module_resolver I \<le> SPEC (full_module_resolver_post' I)\<close>
  unfolding full_module_resolver_def full_module_resolver_post'_def
  apply (intro refine_vcg)
  using full_module_resolver_invar_init
    apply blast
  apply auto[1]
  using full_module_resolver_loop_preserves_invar
    apply blast
  (* All assertions after WHILE loop *)
  apply blast
  apply simp_all[6]
  unfolding full_module_resolver_invar_def
  apply (smt (verit) Pair_inject case_prodE empty_iff empty_set mem_Collect_eq subset_eq)
  apply blast
  apply blast
  using full_module_resolver_assert7
    apply (smt (verit, del_insts) Pair_inject case_prodE case_prodI2 empty_iff empty_set)
  apply blast
  apply fast
  (* After the loop *)
  subgoal premises
    by simp
  apply (rule SPEC_cons_rule[OF populate_import_graph_correct])
  apply (intro refine_vcg)
  apply (rule SPEC_cons_rule[OF trim_import_graph_correct])
  apply (intro refine_vcg)
  apply (metis option.simps(4))
  subgoal sorry
  subgoal sorry
  subgoal sorry
  subgoal sorry
  subgoal sorry
  done

end (* locale Resolver_Spec *)

end (* theory ImportResolver_Spec *)