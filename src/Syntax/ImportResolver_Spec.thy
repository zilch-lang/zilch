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
  (* NOTE: We may need to revisit this? *)
type_synonym import_constraints = \<open>(import \<times> path \<times> (import \<times> path \<times> string list) set) set\<close>
type_synonym include_path = \<open>path set\<close>

type_synonym namespaces_abs = \<open>(import \<times> path) \<rightharpoonup> unit\<close>

text \<open>
  An empty import graph simply contains no vertices and no edges.
\<close>
abbreviation empty_import_graph :: \<open>import_graph\<close>
where \<open>empty_import_graph \<equiv> \<lparr> pverts = {}, parcs = {}, labels = Map.empty \<rparr>\<close>

definition set_to_list :: \<open>'a set \<Rightarrow> 'a list\<close>
where \<open>set_to_list s \<equiv> SOME l. set l = s\<close>

lemma set_set_to_list: \<open>finite s \<Longrightarrow> set (set_to_list s) = s\<close>
  unfolding set_to_list_def
  by (meson finite_list someI)

lemma restrict_map_empty_iff[iff]: \<open>m |` A = Map.empty \<longleftrightarrow> m = Map.empty \<or> A \<inter> dom m = {}\<close>
  by (metis dom_eq_empty_conv dom_restrict inf_bot_right inf_commute)

locale Resolver_Spec =
  fixes mk_paths_from_module_name :: \<open>[ import, include_path ] \<Rightarrow> (import \<times> path \<times> string list) set\<close>
    and parse_file_and_extract_imports :: \<open>path \<Rightarrow> cst_abs \<times> import list\<close>
    and make_constraints_from_path_and_modules :: \<open>[ path, string list ] \<Rightarrow> Solver_Spec.conjunctive_system\<close>
    and try_solve_constraint :: \<open>[ Solver_Spec.conjunctive_system, import_cache, namespaces_abs ] \<Rightarrow> bool option \<times> namespaces_abs\<close>
    and does_file_exist :: \<open>path \<Rightarrow> bool\<close>

  assumes import_has_paths: \<open>\<forall> i INC. INC \<noteq> {} \<longrightarrow> mk_paths_from_module_name i INC \<noteq> {}\<close>
      and paths_finite: \<open>\<forall> i INC. finite (mk_paths_from_module_name i INC)\<close>
      and paths_contain_import: \<open>\<forall> i. (\<forall> m \<in> set i. CHR ''/'' \<notin> set m) \<Longrightarrow> \<exists> p m. (i, p, m) \<in> mk_paths_from_module_name i INC\<close>
      and import_name_has_unique_paths: \<open>\<forall> x i p m i' p' m' INC. (i, p, m) \<in> mk_paths_from_module_name x INC \<and> (i', p', m') \<in> mk_paths_from_module_name x INC \<and> i = i' \<longrightarrow> p = p' \<and> m = m'\<close>
      and paths_uniqueness: \<open>\<forall> i i' INC. i \<noteq> i' \<longleftrightarrow> mk_paths_from_module_name i INC \<noteq> mk_paths_from_module_name i' INC\<close>
      and module_path_unique: \<open>\<forall> i p i' p' I m m' INC. (i, p, m) \<in> mk_paths_from_module_name I INC \<and> (i', p', m') \<in> mk_paths_from_module_name I INC \<and> i \<noteq> i' \<longrightarrow> p \<noteq> p'\<close>
      and import_non_empty: \<open>\<forall> i i' p m INC. (i, p, m) \<in> mk_paths_from_module_name i' INC \<longrightarrow> i \<noteq> []\<close>
begin

definition single_module_resolver_invar1 :: \<open>[ include_path, import, path, import set, (import \<times> path) list ] \<Rightarrow> bool\<close>
where \<open>single_module_resolver_invar1 INC i p is U \<equiv>
         set U = \<Union> { { (i', p'). \<exists> m'. (i', p', m') \<in> mk_paths_from_module_name i INC } | i. \<exists> cst is'. parse_file_and_extract_imports p = (cst, is') \<and> i \<in> (set is' - is) }\<close>

definition single_module_resolver_invar2 :: \<open>[ include_path, import, (import \<times> path) list, import, (import \<times> path \<times> string list) set, (import \<times> path) list ] \<Rightarrow> bool\<close>
where \<open>single_module_resolver_invar2 INC i U i' is U' \<equiv>
         set U' = set U \<union> ({ (i, p). \<exists> m. (i, p, m) \<in> mk_paths_from_module_name i' INC } - { (i, p). \<exists> m. (i, p, m) \<in> is })\<close>

definition single_module_resolver :: \<open>[ include_path, import, path, import_cache, all_imports ] \<Rightarrow> ((import \<times> path) list \<times> import_cache \<times> import_constraints \<times> all_imports) nres\<close>
where \<open>single_module_resolver INC i p C I \<equiv> do {
         ASSUME (\<forall> p \<in> dom C. does_file_exist p);
         ASSUME (dom C = dom I);
         ASSUME (p \<in> dom I \<longrightarrow> (p, i) \<in> Map.graph I);

         case I p of
           None \<Rightarrow> do {
             if does_file_exist p
             then
               let
                 (cst, is) = parse_file_and_extract_imports p;
                 C = C(p \<mapsto> cst);
                 Cs = { (i, p, mk_paths_from_module_name i' INC) | i'. i' \<in> set is };
                                    \<comment>\<open>Insert the file in the cache, and generate some accessibility constraints\<close>
                 I = I(p \<mapsto> i)
               in do {
                 U \<leftarrow> FOREACH\<^bsup>single_module_resolver_invar1 INC i p\<^esup>
                              (set is) (\<lambda> i' U. do {
                   U' \<leftarrow> FOREACH\<^bsup>single_module_resolver_invar2 INC i U i'\<^esup>
                                (mk_paths_from_module_name i' INC) (\<lambda> (i, p, _) U. do {
                     RETURN ((i, p) # U)
                   }) U;
                   ASSERT (set U' = set U \<union> { (i, p). \<exists> m. (i, p, m) \<in> mk_paths_from_module_name i' INC });
                   RETURN U'
                 }) [];
                 ASSERT (set U = \<Union> { { (i, p). \<exists> m. (i, p, m) \<in> mk_paths_from_module_name i' INC } | i'. i' \<in> set is });
                 RETURN (U, C, Cs, I)
               }
             else do {
               ASSERT (\<not> does_file_exist p);
               RETURN ([], C, {}, I)
             }
           }
         | Some i' \<Rightarrow> do {
           ASSERT (i = i');
           RETURN ([], C, {}, I)
         }
       }\<close>

lemma single_module_resolver_invar1_init:
  assumes \<open>does_file_exist p\<close>
      and \<open>parse_file_and_extract_imports p = (cst, b)\<close>
  shows \<open>single_module_resolver_invar1 INC i p (set b) []\<close>
  unfolding single_module_resolver_invar1_def
  by (auto simp add: assms(2))

lemma single_module_resolver_invar2_init:
  assumes \<open>does_file_exist p\<close>
      and \<open>parse_file_and_extract_imports p = (cst, b)\<close>
      and \<open>x \<in> it\<close>
      and \<open>it \<subseteq> set b\<close>
      and \<open>single_module_resolver_invar1 INC i p it U\<close>
  shows \<open>single_module_resolver_invar2 INC i U x (mk_paths_from_module_name x INC) U\<close>
  by (simp add: single_module_resolver_invar2_def)

lemma single_module_resolver_invar1_step:
  assumes \<open>does_file_exist p\<close>
      and \<open>parse_file_and_extract_imports p = (cst, b)\<close>
      and \<open>x \<in> it\<close>
      and \<open>it \<subseteq> set b\<close>
      and \<open>single_module_resolver_invar1 INC i' p it U\<close>
      and \<open>single_module_resolver_invar2 INC i' U x {} U'\<close>
      and \<open>set U' = set U \<union> {(i, p). \<exists> m. (i, p, m) \<in> mk_paths_from_module_name x INC}\<close>
  shows \<open>single_module_resolver_invar1 INC i' p (it - {x}) U'\<close>
  using assms
  unfolding single_module_resolver_invar2_def single_module_resolver_invar1_def
  by (auto, blast)

lemma single_module_resolver_invar2_step:
  assumes \<open>does_file_exist p'\<close>
      and \<open>parse_file_and_extract_imports p' = (cst, b)\<close>
      and \<open>x \<in> it\<close>
      and \<open>it \<subseteq> set b\<close>
      and \<open>single_module_resolver_invar1 INC i' p' it U\<close>
      and \<open>(i, p, m) \<in> ita\<close>
      and \<open>ita \<subseteq> mk_paths_from_module_name x INC\<close>
      and \<open>single_module_resolver_invar2 INC i' U x ita U'\<close>
  shows \<open>single_module_resolver_invar2 INC i' U x (ita - {(i, p, m)}) ((i, p) # U')\<close>
  using assms
  unfolding single_module_resolver_invar2_def
  by (auto, meson import_name_has_unique_paths subset_eq)

lemma single_module_resolver_invar1_end1:
  assumes \<open>does_file_exist p\<close>
      and \<open>parse_file_and_extract_imports p = (cst, b)\<close>
      and \<open>single_module_resolver_invar1 INC i' p {} U\<close>
      and \<open>x \<in> set U\<close>
  shows \<open>\<exists> xa. (\<exists> i'. xa = {(i, p). \<exists> m. (i, p, m) \<in> mk_paths_from_module_name i' INC} \<and> i' \<in> set b) \<and> x \<in> xa\<close>
  using assms
  unfolding single_module_resolver_invar1_def
  by auto

lemma single_module_resolver_invar1_end2:
  assumes \<open>does_file_exist p\<close>
      and \<open>parse_file_and_extract_imports p = (cst, b)\<close>
      and \<open>single_module_resolver_invar1 INC i p {} U\<close>
      and \<open>i' \<in> set b\<close>
      and \<open>(x, y, m) \<in> mk_paths_from_module_name i' INC\<close>
  shows \<open>(x, y) \<in> set U\<close>
  using assms
  unfolding single_module_resolver_invar1_def
  by auto

lemma single_module_resolver_invar2_end1:
  assumes \<open>does_file_exist p\<close>
      and \<open>parse_file_and_extract_imports p = (cst, b)\<close>
      and \<open>x \<in> it\<close>
      and \<open>it \<subseteq> set b\<close>
      and \<open>single_module_resolver_invar1 INC i p it U\<close>
      and \<open>single_module_resolver_invar2 INC i U x {} U'\<close>
      and \<open>(i', p') \<in> set U'\<close>
      and \<open>(i', p') \<notin> set U\<close>
  shows \<open>\<exists> m. (i', p', m) \<in> mk_paths_from_module_name x INC\<close>
  using assms(6) assms(7) assms(8) single_module_resolver_invar2_def
  by auto

lemma single_module_resolver_invar2_end2:
  assumes \<open>does_file_exist p\<close>
      and \<open>parse_file_and_extract_imports p = (cst, b)\<close>
      and \<open>x \<in> it\<close>
      and \<open>it \<subseteq> set b\<close>
      and \<open>single_module_resolver_invar1 INC i' p it U\<close>
      and \<open>single_module_resolver_invar2 INC i' U x {} U'\<close>
      and \<open>i \<in> set U\<close>
  shows \<open>i \<in> set U'\<close>
  using assms
  unfolding single_module_resolver_invar2_def
  by auto

lemma single_module_resolver_invar2_end3:
  assumes \<open>does_file_exist p\<close>
      and \<open>parse_file_and_extract_imports p = (cst, b)\<close>
      and \<open>x \<in> it\<close>
      and \<open>it \<subseteq> set b\<close>
      and \<open>single_module_resolver_invar1 INC i' p it U\<close>
      and \<open>single_module_resolver_invar2 INC i' U x {} U'\<close>
      and \<open>(i, p', m) \<in> mk_paths_from_module_name x INC\<close>
  shows \<open>(i, p') \<in> set U'\<close>
  using assms(6) assms(7) single_module_resolver_invar2_def
  by auto

text \<open>
  Insert labelled edges inside the import graph to account for dependencies.
\<close>

definition populate_import_graph_invar1 :: \<open>[ import_graph, import_constraints, import_constraints, import_graph ] \<Rightarrow> bool\<close>
where \<open>populate_import_graph_invar1 G' Cs' Cs G \<equiv> pverts G' = pverts G
                                                  \<comment>\<open>No vertex is added to the graph.\<close>
                                                \<and> parcs G = parcs G' \<union> { ((i, p), (i', p')). \<exists> is m. (i, p, is) \<in> (Cs' - Cs) \<and> (i', p', m) \<in> is }
                                                  \<comment>\<open>All arcs inserted come from our generated constraints.\<close>\<close>

definition populate_import_graph_invar2 :: \<open>[ import_graph, (import \<times> path \<times> string list) set, import, path, (import \<times> path \<times> string list) set, import_graph ] \<Rightarrow> bool\<close>
where \<open>populate_import_graph_invar2 G' Ps' i p Ps G \<equiv> pverts G = pverts G'
                                                         \<comment>\<open>No vertex is added to the graph.\<close>
                                                    \<and> parcs G = parcs G' \<union> { ((i, p), (v, p')) | v p'. \<exists> m. (v, p', m) \<in> Ps' - Ps }
                                                         \<comment>\<open>All arcs inserted come from our generated constraints.\<close>\<close>

lemma populate_import_graph_invar1_init:
  assumes \<open>finite Cs\<close>
      and \<open>\<forall> (_, _, is) \<in> Cs. finite is\<close>
      and \<open>\<forall> (i, p, _) \<in> Cs. (i, p) \<in> pverts G\<close>
      and \<open>\<forall> (_, _, is) \<in> Cs. \<forall> (i, p, _) \<in> is. (i, p) \<in> pverts G\<close>
  shows \<open>populate_import_graph_invar1 G Cs Cs G\<close>
  using assms
  unfolding populate_import_graph_invar1_def
  by auto

lemma populate_import_graph_invar1_step:
  assumes \<open>finite Cs\<close>
      and \<open>\<forall> (_, _, is) \<in> Cs. finite is\<close>
      and \<open>\<forall> (i, p, _) \<in> Cs. (i, p) \<in> pverts G\<close>
      and \<open>\<forall> (_, _, is) \<in> Cs. \<forall> (i, p, _) \<in> is. (i, p) \<in> pverts G\<close>
      and \<open>(a, b, c) \<in> it\<close>
      and \<open>it \<subseteq> Cs\<close>
      and \<open>populate_import_graph_invar1 G Cs it G'\<close>
      and \<open>populate_import_graph_invar2 G' c a b {} G''\<close>
  shows \<open>populate_import_graph_invar1 G Cs (it - {(a, b, c)}) G''\<close>
  using assms
  unfolding populate_import_graph_invar1_def populate_import_graph_invar2_def
  by auto

lemma populate_import_graph_invar2_init:
  assumes \<open>finite Cs\<close>
      and \<open>\<forall> (_, _, is) \<in> Cs. finite is\<close>
      and \<open>\<forall> (i, p, _) \<in> Cs. (i, p) \<in> pverts G\<close>
      and \<open>\<forall> (_, _, is) \<in> Cs. \<forall> (i, p, _) \<in> is. (i, p) \<in> pverts G\<close>
      and \<open>(a, b, c) \<in> it\<close>
      and \<open>it \<subseteq> Cs\<close>
      and \<open>populate_import_graph_invar1 G Cs it G'\<close>
  shows \<open>populate_import_graph_invar2 G' c a b c G'\<close>
  unfolding populate_import_graph_invar2_def
  by auto

lemma populate_import_graph_invar2_step:
  assumes \<open>finite Cs\<close>
      and \<open>\<forall> (_, _, is) \<in> Cs. finite is\<close>
      and \<open>\<forall> (i, p, _) \<in> Cs. (i, p) \<in> pverts G\<close>
      and \<open>\<forall> (_, _, is) \<in> Cs. \<forall> (i, p, _) \<in> is. (i, p) \<in> pverts G\<close>
      and \<open>(a, b, c) \<in> it\<close>
      and \<open>it \<subseteq> Cs\<close>
      and \<open>populate_import_graph_invar1 G Cs it G'\<close>
      and \<open>(aa, ba, ca) \<in> ita\<close>
      and \<open>ita \<subseteq> c\<close>
      and \<open>populate_import_graph_invar2 G' c a b ita G''\<close>
  shows \<open>populate_import_graph_invar2 G' c a b (ita - {(aa, ba, ca)})
           (add_arc (a, b) (make_constraints_from_path_and_modules ba ca) (aa, ba) G'')\<close>
proof -
  have assm: \<open>pverts G'' = pverts G' \<and> parcs G'' = parcs G' \<union> { ((a, b), v, p') | v p'. \<exists>m. (v, p', m) \<in> c - ita }\<close>
    using assms(10) populate_import_graph_invar2_def
    by force
  have 1: \<open>pverts G'' = pverts G'\<close>
    by (simp add: assm)
  have 2: \<open>parcs G'' = parcs G' \<union> { ((a, b), v, p') | v p'. \<exists>m. (v, p', m) \<in> c - ita }\<close>
    by (simp add: assm)
  have *: \<open>(a, b) \<in> pverts G''\<close>
    using assms(4) assms(5) assms(6)
    using Resolver_Spec.populate_import_graph_invar1_def Resolver_Spec_axioms \<open>pverts G'' = pverts G'\<close> assms(3) assms(7)
    by auto
  have **: \<open>(aa, ba) \<in> pverts G''\<close>
    by (metis (mono_tags, lifting) \<open>pverts G'' = pverts G'\<close> assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) case_prodD populate_import_graph_invar1_def subsetD)
  show ?thesis
    unfolding populate_import_graph_invar2_def
  proof (intro conjI)
    show \<open>pverts (add_arc (a, b) (make_constraints_from_path_and_modules ba ca) (aa, ba) G'') = pverts G'\<close>
      by (metis "*" "**" \<open>pverts G'' = pverts G'\<close> add_arc_no_new_vertex)
  next
    let ?G'' = \<open>add_arc (a, b) (make_constraints_from_path_and_modules ba ca) (aa, ba) G''\<close>
    let ?new_arcs = \<open>{ ((a, b), v, p') | v p'. \<exists> m. (v, p', m) \<in> c - (ita - {(aa, ba, ca)}) }\<close>

    have \<open>parcs ?G'' = insert ((a, b), (aa, ba)) (parcs G'')\<close>
      unfolding add_arc_def
      by simp
    moreover have \<open>(aa, ba, ca) \<in> c - (ita - {(aa, ba, ca)})\<close>
      using assms(8) assms(9)
      by fastforce
    then have \<open>((a, b), (aa, ba)) \<in> ?new_arcs\<close>
      by fastforce
    ultimately show \<open>parcs ?G'' = parcs G' \<union> ?new_arcs\<close>
      using "2" assms(8) assms(9)
      by auto
  qed
qed

definition populate_import_graph :: \<open>[ (import \<times> path) list, all_imports, import_graph, import_constraints ] \<Rightarrow> import_graph nres\<close>
where \<open>populate_import_graph is I G Cs \<equiv> do {
         ASSUME (finite Cs);
         ASSUME (\<forall> (_, _, is) \<in> Cs. finite is);
         ASSUME (\<forall> (i, p, _) \<in> Cs. (i, p) \<in> pverts G);
         ASSUME (\<forall> (_, _, is) \<in> Cs. \<forall> (i, p, _) \<in> is. (i, p) \<in> pverts G);
         ASSUME (\<forall> u \<in> set is. (('''', ''''), u) \<in> parcs G);
         ASSUME (set is \<subseteq> pverts G);
         ASSUME (\<forall> (i, p, _) \<in> Cs. (p, i) \<in> Map.graph I);
         ASSUME (\<forall> (_, _, is) \<in> Cs. \<forall> (i, p, _) \<in> is. (p, i) \<in> Map.graph I);
         ASSUME (pverts G = insert ('''', '''') { (i, p). (p, i) \<in> Map.graph I });
         ASSUME (parcs G = { (('''', ''''), u) | u. u \<in> set is });
         FOREACH\<^bsup>populate_import_graph_invar1 G Cs\<^esup> Cs (\<lambda> (i, p, paths) G. do {
           FOREACH\<^bsup>populate_import_graph_invar2 G paths i p\<^esup> paths (\<lambda> (i', p', ms') G'. do {
             let G' = add_arc (i, p) (make_constraints_from_path_and_modules p' ms') (i', p') G';
                         \<comment>\<open>Set a constraint system to be solved for this edge to remain in the trimmed import graph\<close>
             RETURN G'
           }) G
         }) G
       }\<close>

definition populate_import_graph_post :: \<open>[ import_graph, import_constraints, import_graph ] \<Rightarrow> bool\<close>
where \<open>populate_import_graph_post G' Cs G \<equiv> pverts G' = pverts G
                                                 \<comment>\<open>We do not add vertices to the graph.\<close>\<close>

lemma populate_import_graph_invar1_imp_post:
  assumes \<open>populate_import_graph_invar1 G Cs {} G'\<close>
  shows \<open>populate_import_graph_post G Cs G'\<close>
  unfolding populate_import_graph_post_def
  using assms(1) populate_import_graph_invar1_def
  by blast

lemma populate_import_graph_correct: \<open>populate_import_graph is I G Cs \<le> SPEC (populate_import_graph_post G Cs)\<close>
  unfolding populate_import_graph_def
proof (intro refine_vcg)
  assume \<open>finite Cs\<close>
  then show \<open>finite Cs\<close> .
next
  assume \<open>finite Cs\<close>
     and \<open>\<forall> (_, _, is) \<in> Cs. finite is\<close>
     and \<open>\<forall> (i, p, _) \<in> Cs. (i, p) \<in> pverts G\<close>
     and \<open>\<forall> (_, _, is) \<in> Cs. \<forall> (i, p, _) \<in> is. (i, p) \<in> pverts G\<close>
  then show \<open>populate_import_graph_invar1 G Cs Cs G\<close>
    using populate_import_graph_invar1_init
    by fastforce
next
  fix x it G'
  assume 1: \<open>\<forall> (_, _, is) \<in> Cs. finite is\<close>
     and 2: \<open>populate_import_graph_invar1 G Cs it G'\<close>
     and 3: \<open>x \<in> it\<close>
     and 4: \<open>it \<subseteq> Cs\<close>
     and 5: \<open>finite Cs\<close>
     and 6: \<open>\<forall> (_, _, is) \<in> Cs. finite is\<close>
     and 7: \<open>\<forall> (i, p, _) \<in> Cs. (i, p) \<in> pverts G\<close>
     and 8: \<open>\<forall> (_, _, is) \<in> Cs. \<forall> (i, p, _) \<in> is. (i, p) \<in> pverts G\<close>

  obtain i p paths where 9: \<open>x = (i, p, paths)\<close>
    using prod_cases3
    by blast
  then have 10: \<open>(i, p, paths) \<in> it\<close>
    using "3"
    by simp

  show \<open>(case x of (i, p, paths) \<Rightarrow> \<lambda> G'.
               FOREACH\<^bsup>populate_import_graph_invar2 G' paths i p\<^esup> paths
                 (\<lambda> (i', p', ms') G'. Let (add_arc (i, p) (make_constraints_from_path_and_modules p' ms') (i', p') G') RETURN)
               G') G'
             \<le> SPEC (populate_import_graph_invar1 G Cs (it - {x}))\<close>
    using "9"
    proof (simp, intro refine_vcg)
      assume \<open>x = (i, p, paths)\<close>
      then show \<open>finite paths\<close>
         using "1" "3" "4"
         by fastforce
    next
      show \<open>populate_import_graph_invar2 G' paths i p paths G'\<close>
        using populate_import_graph_invar2_init[OF "5" "6" "7" "8" "10" "4" "2"]
        by simp
    next
      fix x' it' G''
      assume 11: \<open>x' \<in> it'\<close>
         and 12: \<open>it' \<subseteq> paths\<close>
         and 13: \<open>populate_import_graph_invar2 G' paths i p it' G''\<close>

      obtain i' p' m' where 14: \<open>x' = (i', p', m')\<close>
        using prod_cases3
        by blast
      then have 15: \<open>(i', p', m') \<in> it'\<close>
        using "11"
        by simp

      show \<open>(case x' of (i', p', m') \<Rightarrow>
              \<lambda>G'. RETURN (add_arc (i, p) (make_constraints_from_path_and_modules p' m') (i', p') G'))
             G''
            \<le> SPEC (populate_import_graph_invar2 G' paths i p (it' - {x'}))\<close>
        using "14" populate_import_graph_invar2_step[OF "5" "6" "7" "8" "10" "4" "2" "15" "12" "13"]
        by fastforce
    next
      fix G''
      assume \<open>populate_import_graph_invar2 G' paths i p {} G''\<close>
      then show \<open>populate_import_graph_invar1 G Cs (it - {(i, p, paths)}) G''\<close>
        using populate_import_graph_invar1_step[OF "5" "6" "7" "8" "10" "4" "2"]
        by simp
    qed
next
  fix G'
  assume \<open>populate_import_graph_invar1 G Cs {} G'\<close>
  then show \<open>populate_import_graph_post G Cs G'\<close>
    using populate_import_graph_invar1_imp_post
    by fastforce
qed

text \<open>
  Trim the import graph by solving all constraints on the edges.
  Eventually, all constraints will be solved and the import graph returned contains a view
  of the dependency order.

  Note: we need to be careful here, and reject negative cycles (cycles where solving a constraint \<open>C₁\<close> depends
    on solving a constraint \<open>C₂\<close> which itself depends on solving \<open>C₁\<close>).
\<close>

definition trim_import_graph_invar1 :: \<open>import_graph \<times> import_graph' \<times> bool \<times> namespaces_abs \<Rightarrow> bool\<close>
where \<open>trim_import_graph_invar1 x \<equiv> case x of
         (G, G', _, Ns) \<Rightarrow> pverts G = pverts G'
                               \<comment>\<open>We do not add or remove vertices.\<close>
                        \<and> wf_digraph (with_proj G')
                               \<comment>\<open>Our dependency graph is well formed.\<close>\<close>

definition trim_import_graph_invar2 :: \<open>[ ((import \<times> path) \<times> Solver_Spec.conjunctive_system \<times> (import \<times> path)) set, import_graph \<times> import_graph' \<times> bool \<times> namespaces_abs ] \<Rightarrow> bool\<close>
where \<open>trim_import_graph_invar2 ps x \<equiv> case x of
         (G, G', _, Ns) \<Rightarrow> True\<close>

definition trim_import_graph_invar3 :: \<open>import_graph \<times> import_graph' \<times> namespaces_abs \<Rightarrow> bool\<close>
where \<open>trim_import_graph_invar3 x \<equiv> case x of
         (G, G', Ns) \<Rightarrow> pverts G = pverts G'\<close>

lemma trim_import_graph_invar1_init:
  assumes \<open>pverts G \<noteq> {}\<close>
  shows \<open>trim_import_graph_invar1 (G, \<lparr> pverts = pverts G, parcs = {} \<rparr>, False, Map.empty)\<close>
  unfolding trim_import_graph_invar1_def
  by (simp add: with_proj_def wf_digraph_def)

lemma trim_import_graph_invar1_step1:
  assumes \<open>trim_import_graph_invar1 (G, G', False, Ns)\<close>
      and \<open>\<not> b \<and> Ex (pre_digraph.cycle (with_proj' a))\<close>
      and \<open>pre_digraph.cycle (with_proj' G) p\<close>
      and \<open>trim_import_graph_invar2 {} S\<close>
      and \<open>case S of (_, _, b, _) \<Rightarrow> b\<close>
  shows \<open>trim_import_graph_invar1 S\<close>
  sorry

lemma trim_import_graph_invar1_step2:
  assumes \<open>trim_import_graph_invar1 (G, G', False, Ns)\<close>
      and \<open>\<not> b \<and> Ex (pre_digraph.cycle (with_proj' G))\<close>
      and \<open>pre_digraph.cycle (with_proj' G) p\<close>
      and \<open>it \<subseteq> set p\<close>
      and \<open>trim_import_graph_invar2 it S\<close>
      and \<open>\<not> (case S of (uu_, uua_, b, uub_) \<Rightarrow> b)\<close>
  shows \<open>trim_import_graph_invar1 S\<close>
  sorry

lemma trim_import_graph_invar1_end:
  assumes \<open>trim_import_graph_invar1 (G, G', True, Ns)\<close>
      and \<open>b\<close>
  shows \<open>\<exists> p. (pre_digraph.cycle (with_proj' G)) p\<close>
  sorry

lemma trim_import_graph_invar2_init:
  assumes \<open>trim_import_graph_invar1 (G, G', False, Ns)\<close>
      and \<open>\<not> b \<and> (\<exists> p. pre_digraph.cycle (with_proj' G) p)\<close>
      and \<open>pre_digraph.cycle (with_proj' G) p\<close>
  shows \<open>trim_import_graph_invar2 (set p) (G, G', True, Ns)\<close>
  sorry

lemma trim_import_graph_loop_preserves_invar2:
  assumes \<open>trim_import_graph_invar1 (G, G', False, Ns)\<close>
      and \<open>\<not> b \<and> Ex (pre_digraph.cycle (with_proj' G))\<close>
      and \<open>pre_digraph.cycle (with_proj' G) p\<close>
      and \<open>(u, l, v) \<in> it\<close>
      and \<open>it \<subseteq> set p\<close>
      and \<open>trim_import_graph_invar2 it S\<close>
      and \<open>case S of (_, _, b, _) \<Rightarrow> b\<close>
  shows \<open>(case S of
           (G, G', _, Ns) \<Rightarrow>
             (case try_solve_constraint l C Ns of
               (None, Ns) \<Rightarrow> RETURN (G, G', True, Ns)
             | (Some resa, Ns) \<Rightarrow>
               let G = remove_arc u v G;
                   G' = if resa
                        then \<lparr> pverts = {u, v} \<union> pverts G', parcs = insert (u, v) (parcs G') \<rparr>
                        else G'
               in RETURN (G, G', False, Ns)))
         \<le> SPEC (trim_import_graph_invar2 (it - { (u, l, v) }))\<close>
  sorry

lemma trim_import_graph_invar3_init:
  assumes \<open>trim_import_graph_invar1 (G, G', False, Ns)\<close>
      and \<open>wf_digraph (with_proj G')\<close>
      and \<open>\<forall> p. \<not> pre_digraph.cycle (with_proj' G) p\<close>
  shows \<open>trim_import_graph_invar3 (G, G', Ns)\<close>
  sorry

lemma trim_import_graph_invar3_step1:
  assumes \<open>trim_import_graph_invar1 (G, G', False, Ns')\<close>
      and \<open>\<not> b\<close>
      and \<open>wf_digraph (with_proj G')\<close>
      and \<open>\<forall> p. \<not> pre_digraph.cycle (with_proj' G) p\<close>
      and \<open>trim_import_graph_invar3 (G1, G1', Ns)\<close>
      and \<open>parcs G1 \<noteq> {}\<close>
      and \<open>(u, v) \<in> parcs G1\<close>
      and \<open>try_solve_constraint (the (labels G1 (u, v))) C Ns = (None, Ns'')\<close>
  shows \<open>trim_import_graph_invar3 (G1, G1', Ns'')\<close>
  sorry

lemma trim_import_graph_invar3_step2:
  assumes \<open>trim_import_graph_invar1 (G, G', False, Ns)\<close>
      and \<open>\<not> b\<close>
      and \<open>wf_digraph (with_proj G')\<close>
      and \<open>\<forall> p. \<not> pre_digraph.cycle (with_proj' G) p\<close>
      and \<open>trim_import_graph_invar3 (G1, G1', Ns')\<close>
      and \<open>parcs G1 \<noteq> {}\<close>
      and \<open>(u, v) \<in> parcs G1\<close>
      and \<open>try_solve_constraint (the (labels G1 (u, v))) C Ns' = (Some True, Ns'')\<close>
  shows \<open>trim_import_graph_invar3
           (remove_arc u v G1,
            \<lparr> pverts = insert u (insert v (pverts G1')), parcs = insert (u, v) (parcs G1') \<rparr>,
            Ns'')\<close>
  sorry

lemma trim_import_graph_invar3_step3:
  assumes \<open>trim_import_graph_invar1 (G, G', False, Ns)\<close>
      and \<open>\<not> b\<close>
      and \<open>wf_digraph (with_proj G')\<close>
      and \<open>\<forall> p. \<not> pre_digraph.cycle (with_proj' G) p\<close>
      and \<open>trim_import_graph_invar3 (G1, G1', Ns')\<close>
      and \<open>parcs G1 \<noteq> {}\<close>
      and \<open>(u, v) \<in> parcs G1\<close>
      and \<open>try_solve_constraint (the (labels G1 (u, v))) C Ns' = (Some False, Ns'')\<close>
  shows \<open>trim_import_graph_invar3
           (remove_arc u v G1,
            G1',
            Ns'')\<close>
  sorry

lemma trim_import_graph_invar3_end:
  assumes \<open>pverts G \<noteq> {}\<close>
      and \<open>trim_import_graph_invar1 (G0, G0', False, Ns')\<close>
      and \<open>\<not> b\<close>
      and \<open>wf_digraph (with_proj G0')\<close>
      and \<open>\<forall> p. \<not> pre_digraph.cycle (with_proj' G0) p\<close>
      and \<open>trim_import_graph_invar3 (G1, G1', Ns)\<close>
      and \<open>parcs G1 = {}\<close>
      and \<open>\<forall> p. \<not> pre_digraph.cycle (with_proj G1') p\<close>
      and \<open>\<forall> u \<in> pverts G0. \<exists>a b. (a, b) \<in> pverts G1' \<and> (u, a, b) \<notin> parcs G1' \<and> ((a, b), u) \<notin> parcs G1'\<close>
      and \<open>\<forall> u \<in> pverts G1'. \<forall> v \<in> pverts G1'. \<not> Suc 0 < card {w \<in> pverts G1'. (u, w) \<in> parcs G1' \<and> fst w = fst v}\<close>
  shows \<open>trim_import_graph_post' G C (Some (G1', Ns))\<close>
  sorry

definition trim_import_graph :: \<open>[ import_graph, import_cache ] \<Rightarrow> (import_graph' \<times> namespaces_abs) option nres\<close>
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
         ASSUME (pverts G \<noteq> {});

         (G, G', b, Ns) \<leftarrow> WHILE\<^bsup>trim_import_graph_invar1\<^esup>
                            \<comment>\<open>While we are able to break a cycle, and there still exists a cycle…\<close>
                            (\<lambda> (G, _, b, _). \<not> b \<and> (\<exists> p. pre_digraph.cycle (with_proj' G) p)) (\<lambda> (G, G', _, Ns). do {
           p \<leftarrow> SPEC (\<lambda> p. pre_digraph.cycle (with_proj' G) p);
           FOREACH\<^sub>C\<^bsup>trim_import_graph_invar2\<^esup>
                    (set p) (\<lambda> (_, _, b, _). b) (\<lambda> (u, l, v) (G, G', _, Ns). do {
                      \<comment>\<open>Loop through each edge of the cycle, try solving any constraint.
                        If any constraint is solved, break the cycle at this point.
                        If no constraint is solved at all, return an error.\<close>
             let (res, Ns) = try_solve_constraint l C Ns;
             case res of
               None \<Rightarrow> RETURN (G, G', True, Ns)
             | Some res \<Rightarrow>
                      \<comment>\<open>We were able to solve the constraint, so remove the edge and stop processing the cycle.\<close>
                 let G = remove_arc u v G;
                     G' = if res
                          then \<lparr> pverts = {u, v} \<union> pverts G', parcs = insert (u, v) (parcs G') \<rparr>
                          else G' in
                 RETURN (G, G', False, Ns)
           }) (G, G', True, Ns)
                      \<comment>\<open>Returns @{term True} if no constraint is solved, @{term False} otherwise.\<close>
         }) (G, \<lparr> pverts = pverts G, parcs = {} \<rparr>, False, Map.empty);

         if b
               \<comment>\<open>If no constraint has been solved in the last cycle found…\<close>
         then do {
           ASSERT (\<exists> p. pre_digraph.cycle (with_proj' G) p);
           RETURN None
         }
         else do {
           ASSERT (wf_digraph (with_proj G'));
           ASSERT (∄ p. pre_digraph.cycle (with_proj' G) p);

               \<comment>\<open>Loop through each edge, solve constraints and add edges in the final graph when needed.\<close>
           (_, G', Ns) \<leftarrow> WHILE\<^bsup>trim_import_graph_invar3\<^esup>
                           (\<lambda> (G, _, _). parcs G \<noteq> {}) (\<lambda> (G, G', Ns). do {
             (u, v) \<leftarrow> SPEC (\<lambda> e. e \<in> parcs G);
             let l = the ((labels G) (u, v));
             let (res, Ns) = try_solve_constraint l C Ns;
             case res of
                      \<comment>\<open>Constraint has not been solved, try again later.\<close>
               None \<Rightarrow> RETURN (G, G', Ns)
             | Some res \<Rightarrow>
                 let G = remove_arc u v G;
                     G' = if res
                          then \<lparr> pverts = {u, v} \<union> pverts G', parcs = insert (u, v) (parcs G') \<rparr>
                          else G' in
                 RETURN (G, G', Ns)
           }) (G, G', Ns);

           if \<exists> p. pre_digraph.cycle (with_proj G') p
           then RETURN None
           else if \<exists> u \<in> pverts G. ∄ v. v \<in> pverts G' \<and> (u, v) \<notin> parcs G' \<and> (v, u) \<notin> parcs G'
                         \<comment>\<open>If there exists an isolated vertex, error out:
                           - Either all its dependencies are not resolved (constraints unsatisfied)
                           - Or it is an unresolved dependency\<close>
           then RETURN None
           else if \<exists> u \<in> pverts G'. \<exists> v \<in> pverts G'. card { w \<in> pverts G'. (u, w) \<in> parcs G' \<and> fst w = fst v } > 1
                         \<comment>\<open>If there exists a vertex having more than one edge to another vertex, error out:
                           An import is ambiguous as it could not be resolved to a single file.\<close>
           then RETURN None
           else RETURN (Some (G', Ns))
         }
       }\<close>

definition trim_import_graph_post :: \<open>[ import_graph, import_cache, import_graph', namespaces_abs ] \<Rightarrow> bool\<close>
where \<open>trim_import_graph_post G' C G Ns \<equiv> (∄ p. pre_digraph.cycle G p)
                                                 \<comment>\<open>The final import graph does not contain a dependency cycle.\<close>
                                        \<and> (\<forall> u \<in> pverts G. \<forall> v \<in> pverts G. card { w \<in> pverts G. (u, w) \<in> parcs G \<and> fst w = fst v } \<le> 1)
                                                 \<comment>\<open>For all pairs of imports, there is at most one edge between them.\<close>
                                        \<and> (\<forall> u \<in> pverts G. \<exists> v \<in> pverts G. (u, v) \<in> parcs G \<or> (v, u) \<in> parcs G)
                                                 \<comment>\<open>No vertex is isolated, meaning that there is at least one incoming/outcoming edge for every vertex.\<close>
                                        \<and> ('''', '''') \<in> pverts G
                                                 \<comment>\<open>Our top-level node still is in the import graph.\<close>
                                        \<and> pverts G = pverts G'
                                                 \<comment>\<open>No vertex was added in the import graph.\<close>\<close>

definition trim_import_graph_post' :: \<open>[ import_graph, import_cache, (import_graph' \<times> namespaces_abs) option ] \<Rightarrow> bool\<close>
where \<open>trim_import_graph_post' G C x \<equiv>
         case x of None \<Rightarrow> True | Some (G', Ns) \<Rightarrow> trim_import_graph_post G C G' Ns\<close>

lemma trim_import_graph_correct: \<open>trim_import_graph G C \<le> SPEC (trim_import_graph_post' G C)\<close>
  (* TODO: remove that ugly apply style *)
  unfolding trim_import_graph_def
  apply (intro refine_vcg)
  apply simp_all[16]
  using trim_import_graph_invar1_init
    apply presburger
  apply (meson trim_import_graph_invar2_init)
  using trim_import_graph_loop_preserves_invar2
    apply auto[1]
    apply meson
  using trim_import_graph_invar1_step1
    apply metis
  using trim_import_graph_invar1_step2
    apply metis
  using trim_import_graph_invar1_end
    apply blast
  apply (simp add: trim_import_graph_post'_def)
  using trim_import_graph_invar1_def
    apply fastforce
  using trim_import_graph_invar3_init
    apply presburger
  apply (meson trim_import_graph_invar3_step1)
  using trim_import_graph_invar3_step2 trim_import_graph_invar3_step3 Resolver_Spec_axioms
    apply (smt (verit, ccfv_threshold))
  using trim_import_graph_post'_def Resolver_Spec_axioms
    apply auto[3]
  apply (auto simp add: trim_import_graph_invar3_end)[1]
  done

text \<open>
  Try to resolve all modules (as top-level ones).
\<close>
definition full_module_resolver_invar :: \<open>[ include_path, (import \<times> path) list, (import \<times> path) set \<times> (import \<times> path) list \<times> import_cache \<times> import_constraints \<times> all_imports ] \<Rightarrow> bool\<close>
where \<open>full_module_resolver_invar INC is x \<equiv> case x of
         (P, is', C, Cs, I) \<Rightarrow> (\<forall> p \<in> dom I. does_file_exist p)
                                    \<comment>\<open>All registered imports have an existing assoticated path.\<close>
                            \<and> dom C = dom I
                                    \<comment>\<open>There are as many parsed CSTs than registered imports.\<close>
                            \<and> { (p, i). \<exists> is. (i, p, is) \<in> Cs } \<subseteq> Map.graph I
                                    \<comment>\<open>All the source imports in the dependency set are registered.\<close>
                            \<and> Map.graph I = { (p, i). (i, p) \<in> P \<and> does_file_exist p }
                                    \<comment>\<open>All imports processed (with existing files) have been registered at some point.\<close>
                            \<and> (\<forall> (i, p) \<in> set is. does_file_exist p \<longrightarrow> (i, p) \<in> set is' \<or> (i, p) \<in> P)
                                    \<comment>\<open>All initial imports are already processed or will be in the future.\<close>
                            \<and> (\<forall> (_, _, is) \<in> Cs. \<forall> (i, p, _) \<in> is. does_file_exist p)
                                    \<comment>\<open>All imports kept in the dependency graph relate to existing files only.\<close>
                            \<and> (\<forall> (_, _, is) \<in> Cs. \<forall> (i, p, _) \<in> is. (p, i) \<in> Map.graph I \<or> (i, p) \<in> set is')
                                    \<comment>\<open>All  imports which are dependency targets are either already processed or will be later.\<close>
                            \<and> finite Cs
                                    \<comment>\<open>We only generate a finite number of dependencies.\<close>
                            \<and> (\<forall> (_, _, is) \<in> Cs. finite is)
                                    \<comment>\<open>Every file can depend on a finite number of imports.\<close>
                            \<and> (\<forall> i \<in> ran I. i \<noteq> [])
                            \<and> (\<forall> (i, _, _) \<in> Cs. i \<noteq> [])
                            \<and> (\<forall> (_, _, is) \<in> Cs. \<forall> (i, _, _) \<in> is. i \<noteq> [])
                            \<and> (\<forall> (i, _) \<in> set is'. i \<noteq> [])
                                    \<comment>\<open>Safety constraints: imports are never empty.\<close>
                            \<and> (\<forall> (p, i) \<in> Map.graph I. \<exists> i' m. (i, p, m) \<in> mk_paths_from_module_name i' INC)
                            \<and> (\<forall> (i, p) \<in> set is'. \<exists> i' m. (i, p, m) \<in> mk_paths_from_module_name i' INC)
                                    \<comment>\<open>All our file/import combination are generated from an external function.\<close>
                            \<and> { (p, i). (i, p) \<in> P \<and> does_file_exist p } \<subseteq> Map.graph I\<close>

definition full_module_resolver :: \<open>[ include_path, (import \<times> path) list ] \<Rightarrow> (import_graph' \<times> import_cache \<times> namespaces_abs) option nres\<close>
(* TODO: this WHILE loop *should* always terminate because:
 * - there is a finite number of canonicalized file paths on the file system;
 * - we are not re-adding imports of files that we already processed. *)
where \<open>full_module_resolver INC is \<equiv> do {
         ASSUME (is \<noteq> []);
         ASSUME (\<forall> (i, _) \<in> set is. i \<noteq> []);
         ASSUME (\<forall> (i, p) \<in> set is. (i, p, []) \<in> mk_paths_from_module_name i INC);
         (P, is', C, Cs, I) \<leftarrow> WHILE\<^bsup>full_module_resolver_invar INC is \<^esup>
                                (\<lambda> (_, is, _, _, _). is \<noteq> []) (\<lambda> (P, is, C, Cs, I). do {
           let (i, p) = hd is;
           (U, C, Cs', I) \<leftarrow> single_module_resolver INC i p C I;
           let Cs' = { (i, p, { (i, p, l). (i, p, l) \<in> is \<and> does_file_exist p }) | i p is. (i, p, is) \<in> Cs' };
                      \<comment>\<open>Filter out files whose path do not exist.\<close>
           ASSERT (\<forall> (i, p, _) \<in> Cs'. I p = Some i);
           ASSERT (does_file_exist p \<longleftrightarrow> (p, i) \<in> Map.graph I);
           RETURN (insert (i, p) P, U @ tl is, C, Cs \<union> Cs', I)
         }) ({}, is, Map.empty, {}, Map.empty);
         ASSERT (is' = []);
         ASSERT ({ (i, p) \<in> set is. does_file_exist p } \<subseteq> P);
         ASSERT (\<forall> (i, p) \<in> P. does_file_exist p \<longrightarrow> (p, i) \<in> Map.graph I);
         ASSERT ({ (p, i). (i, p) \<in> P \<and> does_file_exist p } \<subseteq> Map.graph I);
         ASSERT ({ (p, i). (i, p) \<in> set is \<and> does_file_exist p } \<subseteq> { (p, i). (i, p) \<in> P \<and> does_file_exist p });
         ASSERT ({ (p, i). (i, p) \<in> set is \<and> does_file_exist p } \<subseteq> Map.graph I);
         ASSERT (\<forall> (i, p, _) \<in> Cs. I p = Some i);
         ASSERT (\<forall> (_, _, is) \<in> Cs. \<forall> (i, p, _) \<in> is. I p = Some i);
         ASSERT ((\<exists> (_, p) \<in> P. does_file_exist p) \<longrightarrow> I \<noteq> Map.empty);
         ASSERT ((\<exists> (_, p) \<in> P. does_file_exist p) \<longrightarrow> C \<noteq> Map.empty);
         ASSERT (finite Cs);
         ASSERT (\<forall> (_, _, is) \<in> Cs. finite is);
         ASSERT (\<forall> i \<in> ran I. i \<noteq> []);
         ASSERT (\<forall> (i, _, _) \<in> Cs. i \<noteq> []);
         ASSERT (\<forall> (_, _, is) \<in> Cs. \<forall> (i, _, _) \<in> is. i \<noteq> []);

         \<comment>\<open>If not all imports in \<open>is\<close> are resolved to existing files, explicitly fail.\<close>
         if (\<exists> (i, p) \<in> set is. (p, i) \<notin> Map.graph I)
         then RETURN None
         else do {
           ASSERT (\<forall> (_, p) \<in> set is. does_file_exist p);
           ASSERT (I \<noteq> Map.empty);
           ASSERT (C \<noteq> Map.empty);
           ASSERT (\<forall> (_, p) \<in> set is. does_file_exist p);
           let G = \<lparr> pverts = insert ('''', '''') { (i, p). (p, i) \<in> Map.graph I },
                     parcs = { (('''', ''''), v) | v. v \<in> set is },
                     labels = (\<lambda> (x, _). if x = ('''', '''') then Some [] else None) \<rparr>;
           ASSERT (\<forall> (i, p, _) \<in> Cs. (i, p) \<in> pverts G);
           ASSERT (\<forall> (_, _, is) \<in> Cs. \<forall> (i, p, _) \<in> is. (i, p) \<in> pverts G);
           ASSERT (\<forall> u \<in> set is. (('''', ''''), u) \<in> parcs G);
           ASSERT (set is \<subseteq> pverts G);
           ASSERT ({ (i, p). (p, i) \<in> Map.graph I } \<subseteq> pverts G);
           G \<leftarrow> populate_import_graph is I G Cs;
           ASSERT (pverts G \<noteq> {});
           res \<leftarrow> trim_import_graph G C;
           case res of
             None \<Rightarrow> RETURN None
           | Some (G, Ns) \<Rightarrow> do {
             ASSERT (pverts G \<noteq> {});
             ASSERT (('''', '''') \<in> pverts G);
                        \<comment>\<open>The main root (which serves as the "top-most" top-level module) is still in the graph.\<close>
             ASSERT (\<forall> u \<in> pverts G. \<forall> v \<in> pverts G. card { w \<in> pverts G. (u, w) \<in> parcs G \<and> fst w = fst v } \<le> 1);
                        \<comment>\<open>There is at most one edge coming from every @{term u} to a given module
                          (meaning that imports are not ambiguous within a single module).\<close>
             ASSERT (\<forall> i \<in> set is. \<exists>! u \<in> pverts G. u = i);
                        \<comment>\<open>All our top-level modules do not point to code entities.\<close>

             let C = C |` { p | i p. (i, p) \<in> pverts G };
             let Ns = Ns |` pverts G;
             RETURN (Some (G, C, Ns))
           }
         }
       }\<close>

lemma full_module_resolver_invar_init:
  assumes \<open>is \<noteq> []\<close>
      and \<open>\<forall> (i, _) \<in> set is. i \<noteq> []\<close>
      and \<open>\<forall> (i, p) \<in> set is. (i, p, []) \<in> mk_paths_from_module_name i INC\<close>
  shows \<open>full_module_resolver_invar INC is ({}, is, Map.empty, {}, Map.empty)\<close>
  using assms
  unfolding full_module_resolver_invar_def
  by fastforce

lemma full_module_resolver_invar_step2:
  assumes \<open>\<forall> x \<in> dom I. does_file_exist x\<close>
      and \<open>dom C = dom I\<close>
      and \<open>is \<noteq> []\<close>
      and \<open>\<forall> (i, _) \<in> set is'. i \<noteq> []\<close>
      and \<open>\<forall> (i, p) \<in> set is'. (i, p, []) \<in> mk_paths_from_module_name i INC\<close>
      and \<open>is' \<noteq> []\<close>
      and \<open>hd is = (x, y)\<close>
      and \<open>I y = None\<close>
      and \<open>does_file_exist y\<close>
      and \<open>parse_file_and_extract_imports y = (cst, b)\<close>
      and \<open>single_module_resolver_invar1 INC x y {} U\<close>
      and \<open>set U = \<Union> { { (i, p). \<exists> m. (i, p, m) \<in> mk_paths_from_module_name i' INC } | i'. i' \<in> set b }\<close>
      and \<open>full_module_resolver_invar INC is' (P, is, C, Cs, I)\<close>
  shows \<open>full_module_resolver_invar
           INC
           is'
           (insert (x, y) P,
            U @ tl is,
            C(y \<mapsto> cst),
            Cs \<union> { (x, y, { (i, p, l). (i, p, l) \<in> isa \<and> does_file_exist p } ) | isa. \<exists> i'. isa = mk_paths_from_module_name i' INC \<and> i' \<in> set b },
            I(y \<mapsto> x))\<close> (is \<open>full_module_resolver_invar INC is' (?P, ?is, ?C, ?Cs, ?I)\<close>)
  using assms
  proof -
    have \<open>\<forall> p \<in> dom ?I. does_file_exist p\<close>
      by (simp add: assms(1) assms(9))
    moreover have \<open>dom ?C = dom ?I\<close>
      by (simp add: assms(2))
    moreover have **: \<open>{ (p, i). \<exists> is. (i, p, is) \<in> Cs } \<subseteq> Map.graph I\<close>
      using assms(13)
      unfolding full_module_resolver_invar_def
      by blast
        then have \<open>(y, x) \<in> Map.graph ?I\<close>
          by fastforce
        then have \<open>{ (p, i). \<exists> is. (i, p, is) \<in> { (x, y, { (i, p, l). (i, p, l) \<in> isa \<and> does_file_exist p } ) | isa. \<exists> i'. isa = mk_paths_from_module_name i' INC \<and> i' \<in> set b } } \<subseteq> { (y, x) }\<close>
          by fastforce
        then have \<open>{ (p, i). \<exists> is. (i, p, is) \<in> ?Cs } \<subseteq> Map.graph ?I\<close>
          using **
          apply (simp only: subset_iff graph_map_upd, simp)
          by (metis (mono_tags, lifting) assms(8) fun_upd_triv)
    moreover have ***: \<open>Map.graph I = { (p, i). (i, p) \<in> P \<and> does_file_exist p }\<close>
      using assms(13)
      unfolding full_module_resolver_invar_def
      by fastforce
        then have *: \<open>Map.graph ?I = insert (y, x) (Map.graph I)\<close>
          by (metis (no_types, opaque_lifting) assms(8) fun_upd_triv graph_map_upd)
        then have **: \<open>{ (p, i). (i, p) \<in> ?P \<and> does_file_exist p } = insert (y, x) { (p, i). (i, p) \<in> P \<and> does_file_exist p }\<close>
          using assms(13) assms(9)
          unfolding full_module_resolver_invar_def
          by blast
        then have \<open>Map.graph ?I = { (p, i). (i, p) \<in> ?P \<and> does_file_exist p }\<close>
          using * ** ***
          by auto
    moreover have \<open>\<forall> (i, p) \<in> set is'. does_file_exist p \<longrightarrow> (i, p) \<in> P \<or> (i, p) \<in> set is\<close>
      using assms(13)
      unfolding full_module_resolver_invar_def
      by fastforce
        then have \<open>\<forall> (i, p) \<in> set is'. does_file_exist p \<longrightarrow> (i, p) \<in> ?P \<or> (i, p) \<in> set ?is\<close>
          apply auto
          apply (metis (no_types, lifting) assms(7) case_prodD not_hd_in_tl prod.inject)
          apply (metis (no_types, lifting) assms(7) case_prodD not_hd_in_tl prod.inject)
          done
    moreover have **: \<open>\<forall> (_, _, is'') \<in> Cs. \<forall> (i, p, _) \<in> is''. does_file_exist p\<close>
      using assms(13)
      unfolding full_module_resolver_invar_def
      by fastforce
        then have \<open>\<forall> (_, _, is'') \<in> ?Cs. \<forall> (i, p, _) \<in> is''. does_file_exist p\<close>
          by fastforce
    moreover have \<open>\<forall> (_, _, is'') \<in> Cs. \<forall> (i, p, _) \<in> is''. (p, i) \<in> Map.graph I \<or> (i, p) \<in> set is\<close>
      using assms(13)
      unfolding full_module_resolver_invar_def
      by fastforce
        then have \<open>\<forall> (_, _, is'') \<in> ?Cs. \<forall> (i, p, _) \<in> is''. (p, i) \<in> Map.graph ?I \<or> (i, p) \<in> set ?is\<close>
          using assms(11) assms(8)
          apply auto
          using * not_hd_in_tl
          apply (smt (verit) Pair_inject assms(2) assms(6) assms(7) case_prodE domIff fun_upd_None_if_notin_dom)
          apply (smt (verit) Pair_inject assms(2) assms(6) assms(7) case_prodE domIff fun_upd_None_if_notin_dom not_hd_in_tl)
          apply (meson assms(10) assms(9) single_module_resolver_invar1_end2)
          apply (meson assms(10) assms(9) single_module_resolver_invar1_end2)
          done
    moreover have \<open>finite Cs\<close>
      using assms(13)
      unfolding full_module_resolver_invar_def
      by fastforce
        then have \<open>finite (set b)\<close>
          by blast
        then have \<open>finite ?Cs\<close>
          using \<open>finite Cs\<close>
          by fastforce
    moreover have \<open>\<forall> (_, _, is) \<in> Cs. finite is\<close>
      using assms(13)
      unfolding full_module_resolver_invar_def
      by fastforce
        then have \<open>\<forall> isa. (\<exists> i'. isa = mk_paths_from_module_name i' INC \<and> i' \<in> set b) \<longrightarrow> finite { (i, p, l) | i p l. (i, p, l) \<in> isa \<and> does_file_exist p }\<close>
          using paths_finite
          by (smt (verit, ccfv_threshold) mem_Collect_eq rev_finite_subset subset_iff)
        then have \<open>\<forall> (_, _, is) \<in> { (x, y, { (i, p, l). (i, p, l) \<in> isa \<and> does_file_exist p } ) | isa. \<exists> i'. isa = mk_paths_from_module_name i' INC \<and> i' \<in> set b }. finite is\<close>
          using paths_finite \<open>finite (set b)\<close>
          apply auto
          by (smt (verit, ccfv_threshold) Collect_cong Pair_inject case_prodE case_prodI2)
        then have \<open>\<forall> (_, _, is) \<in> ?Cs. finite is\<close>
          by (smt (verit) UnE \<open>\<forall> (_, _, is) \<in> Cs. finite is\<close>)
    moreover have *: \<open>\<forall> (i, _) \<in> set is. i \<noteq> []\<close>
      using assms(13)
      unfolding full_module_resolver_invar_def
      by fastforce
        then have \<open>\<forall> (i, _) \<in> set (tl is). i \<noteq> []\<close>
          by (meson assms(3) list.set_sel(2))
        then have \<open>\<forall> (i, _) \<in> set U. i \<noteq> []\<close>
          using assms(12) import_non_empty
          by fastforce
        then have \<open>\<forall> (i, _) \<in> set ?is. i \<noteq> []\<close>
          using \<open>\<forall> (i, _) \<in> set (tl is). i \<noteq> []\<close>
          by fastforce
    moreover have \<open>\<forall> i \<in> ran I. i \<noteq> []\<close>
      using assms(13)
      unfolding full_module_resolver_invar_def
      by fastforce
        then have \<open>\<forall> i \<in> ran ?I. i \<noteq> []\<close>
          using \<open>\<forall> i \<in> ran I. i \<noteq> []\<close> ran_map_upd
          by (metis (mono_tags, lifting) * assms(3) assms(7) assms(8) case_prodD insertE list.set_sel(1))
    moreover have \<open>\<forall> (i, _, _) \<in> Cs. i \<noteq> []\<close>
      using assms(13)
      unfolding full_module_resolver_invar_def
      by fastforce
        then have \<open>\<forall> (i, _, _) \<in> ?Cs. i \<noteq> []\<close>
        using \<open>\<forall> (i, _) \<in> set is. i \<noteq> []\<close> assms(3) list.set_sel(1) assms(7)
        by fastforce
    moreover have \<open>\<forall> (_, _, is) \<in> Cs. \<forall> (i, _, _) \<in> is. i \<noteq> []\<close>
      using assms(13)
      unfolding full_module_resolver_invar_def
      by fastforce
        then have \<open>\<forall> (_, _, is) \<in> ?Cs. \<forall> (i, _, _) \<in> is. i \<noteq> []\<close>
          by (smt (verit, ccfv_threshold) Pair_inject UnE case_prodD case_prodI2 import_non_empty mem_Collect_eq)
    moreover have ****: \<open>\<forall> (i, p) \<in> set is. \<exists> i' m. (i, p, m) \<in> mk_paths_from_module_name i' INC\<close>
      using assms(13)
      unfolding full_module_resolver_invar_def
      by fastforce
        then have ***: \<open>\<forall> (i, p) \<in> set (tl is). \<exists> i' m. (i, p, m) \<in> mk_paths_from_module_name i' INC\<close>
          by (meson assms(3) list.set_sel(2))
        then have \<open>\<forall> (i, p) \<in> set U. \<exists> i' m. (i, p, m) \<in> mk_paths_from_module_name i' INC\<close>
          by (smt (verit, ccfv_SIG) assms(10) assms(11) assms(9) case_prodD case_prodI2 mem_Collect_eq single_module_resolver_invar1_end1)
        then have \<open>\<forall> (i, p) \<in> set ?is. \<exists> i' m. (i, p, m) \<in> mk_paths_from_module_name i' INC\<close>
          using ***
          by fastforce
    moreover have **: \<open>\<forall> (p, i) \<in> Map.graph I. \<exists> i' m. (i, p, m) \<in> mk_paths_from_module_name i' INC\<close>
      using assms(13)
      unfolding full_module_resolver_invar_def
      by fastforce
        then have \<open>\<exists> i' m. (x, y, m) \<in> mk_paths_from_module_name i' INC\<close>
          using **** assms(3) assms(7) list.set_sel(1)
          by fastforce
        then have \<open>\<forall> (p, i) \<in> Map.graph ?I. \<exists> i' m. (i, p, m) \<in> mk_paths_from_module_name i' INC\<close>
          using **
          by (metis (mono_tags, lifting) assms(8) case_prodI fun_upd_triv graph_map_upd insert_iff)
    moreover have \<open>{ (p, i). (i, p) \<in> P \<and> does_file_exist p } \<subseteq> Map.graph I\<close>
      using assms(13)
      unfolding full_module_resolver_invar_def
      by fastforce
        then have \<open>{ (p, i). (i, p) \<in> ?P \<and> does_file_exist p } \<subseteq> Map.graph ?I\<close>
          using calculation(4)
          by auto
      (* This is almost trivial, but somehow we need to make all steps explicit here... *)
    ultimately show ?thesis
      unfolding full_module_resolver_invar_def
      by fastforce
  qed

lemma full_module_resolver_invar_step3:
  assumes \<open>\<forall> p \<in> dom I. does_file_exist p\<close>
      and \<open>dom C = dom I\<close>
      and \<open>is \<noteq> []\<close>
      and \<open>\<forall> (i, _) \<in> set is'. i \<noteq> []\<close>
      and \<open>\<forall> (i, p) \<in> set is'. (i, p, []) \<in> mk_paths_from_module_name i INC\<close>
      and \<open>is' \<noteq> []\<close>
      and \<open>hd is = (x, y)\<close>
      and \<open>I y = None\<close>
      and \<open>\<not> does_file_exist y\<close>
      and \<open>(y, x) \<notin> Map.graph I\<close>
      and \<open>full_module_resolver_invar INC is' (P, is, C, Cs, I)\<close>
  shows \<open>full_module_resolver_invar INC is' (insert (x, y) P, tl is, C, Cs, I)\<close>
  using assms
  proof -
    have \<open>\<forall> (i, p) \<in> set is'. does_file_exist p \<longrightarrow> (i, p) \<in> P \<or> (i, p) \<in> set is\<close>
      using assms(11)
      unfolding full_module_resolver_invar_def
      by fastforce
      then have \<open>\<forall> (i, p) \<in> set is'. does_file_exist p \<longrightarrow> (i, p) \<in> insert (x, y) P \<or> (i, p) \<in> set (tl is)\<close>
        by (smt (verit, best) assms(7) case_prodD case_prodI2 insert_iff not_hd_in_tl)
    moreover have \<open>{ (p, i). \<exists> is. (i, p, is) \<in> Cs } \<subseteq> Map.graph I\<close>
      using assms(11)
      unfolding full_module_resolver_invar_def
      by blast
    moreover have \<open>Map.graph I = { (p, i). (i, p) \<in> insert (x, y) P \<and> does_file_exist p }\<close>
      using assms(11) assms(9)
      unfolding full_module_resolver_invar_def
      by fastforce
    moreover have \<open>\<forall> (_, _, is'') \<in> Cs. \<forall> (i, p, _) \<in> is''. does_file_exist p\<close>
      using assms(11)
      unfolding full_module_resolver_invar_def
      by fastforce
    moreover have \<open>\<forall> (_, _, is'') \<in> Cs. \<forall> (i, p, _) \<in> is''. (p, i) \<in> Map.graph I \<or> (i, p) \<in> set is\<close>
      using assms(11)
      unfolding full_module_resolver_invar_def
      by fastforce
        then have \<open>\<forall> (_, _, is'') \<in> Cs. \<forall> (i, p, _) \<in> is''. (p, i) \<in> Map.graph I \<or> (i, p) \<in> set (tl is)\<close>
          using assms(6) assms(9) assms(7)
          by (smt (verit) Pair_inject calculation(4) case_prodE case_prodI2 not_hd_in_tl)
    moreover have \<open>finite Cs\<close>
      using assms(11)
      unfolding full_module_resolver_invar_def
      by fastforce
    moreover have \<open>\<forall> (_, _, is) \<in> Cs. finite is\<close>
      using assms(11)
      unfolding full_module_resolver_invar_def
      by fastforce
    moreover have \<open>\<forall> i \<in> ran I. i \<noteq> []\<close>
      using assms(11)
      unfolding full_module_resolver_invar_def
      by fastforce
    moreover have \<open>\<forall> (i, _) \<in> set is. i \<noteq> []\<close>
      using assms(11)
      unfolding full_module_resolver_invar_def
      by fastforce
        then have \<open>\<forall> (i, _) \<in> set (tl is). i \<noteq> []\<close>
        using assms(3)
        by (meson list.set_sel(2))
    moreover have \<open>\<forall> (i, _) \<in> Cs. i \<noteq> []\<close>
      using assms(11)
      unfolding full_module_resolver_invar_def
      by fastforce
    moreover have \<open>\<forall> (_, _, is) \<in> Cs. \<forall> (i, _, _) \<in> is. i \<noteq> []\<close>
      using assms(11)
      unfolding full_module_resolver_invar_def
      by fastforce
    moreover have \<open>\<forall> (i, p) \<in> set is. \<exists> i' m. (i, p, m) \<in> mk_paths_from_module_name i' INC\<close>
      using assms(11)
      unfolding full_module_resolver_invar_def
      by fastforce
        then have \<open>\<forall> (i, p) \<in> set (tl is). \<exists> i' m. (i, p, m) \<in> mk_paths_from_module_name i' INC\<close>
          by (meson assms(3) list.set_sel(2))
    moreover have \<open>\<forall> (p, i) \<in> Map.graph I. \<exists> i' m. (i, p, m) \<in> mk_paths_from_module_name i' INC\<close>
      using assms(11)
      unfolding full_module_resolver_invar_def
      by fastforce
    moreover have \<open>{ (p, i). (i, p) \<in> P \<and> does_file_exist p } \<subseteq> Map.graph I\<close>
      using assms(11)
      unfolding full_module_resolver_invar_def
      by fastforce
    ultimately show ?thesis
      unfolding full_module_resolver_invar_def
      using assms(1) assms(2)
      by fastforce
  qed

lemma full_module_resolver_invar_step4:
  assumes \<open>\<forall> x \<in> dom I. does_file_exist x\<close>
      and \<open>dom C = dom I\<close>
      and \<open>is \<noteq> []\<close>
      and \<open>\<forall> (i, _) \<in> set is'. i \<noteq> []\<close>
      and \<open>\<forall> (i, p) \<in> set is'. (i, p, []) \<in> mk_paths_from_module_name i INC\<close>
      and \<open>is' \<noteq> []\<close>
      and \<open>hd is = (x, y)\<close>
      and \<open>I y = Some x\<close>
      and \<open>(y, x) \<in> Map.graph I\<close>
      and \<open>full_module_resolver_invar INC is' (P, is, C, Cs, I)\<close>
  shows \<open>full_module_resolver_invar INC is' (insert (x, y) P, tl is, C, Cs, I)\<close>
  using assms
  proof -
    have \<open>\<forall> (i, p) \<in> set is'. does_file_exist p \<longrightarrow> (i, p) \<in> P \<or> (i, p) \<in> set is\<close>
      using assms(10)
      unfolding full_module_resolver_invar_def
      by fastforce
      then have \<open>\<forall> (i, p) \<in> set is'. does_file_exist p \<longrightarrow> (i, p) \<in> insert (x, y) P \<or> (i, p) \<in> set (tl is)\<close>
        using not_hd_in_tl
        by (smt (verit, del_insts) assms(7) case_prodD case_prodI2 insertCI)
    moreover have \<open>{ (p, i). \<exists> is. (i, p, is) \<in> Cs } \<subseteq> Map.graph I\<close>
      using assms(10)
      unfolding full_module_resolver_invar_def
      by blast
    moreover have \<open>Map.graph I = { (p, i). (i, p) \<in> P \<and> does_file_exist p }\<close>
      using assms(10)
      unfolding full_module_resolver_invar_def
      by fastforce
        then have \<open>Map.graph I = { (p, i). (i, p) \<in> insert (x, y) P \<and> does_file_exist p }\<close>
          using assms(9)
          by fastforce
    moreover have \<open>\<forall> (_, _, is'') \<in> Cs. \<forall> (i, p, _) \<in> is''. does_file_exist p\<close>
      using assms(10)
      unfolding full_module_resolver_invar_def
      by fastforce
    moreover have *: \<open>\<forall> (_, _, is'') \<in> Cs. \<forall> (i, p, _) \<in> is''. (p, i) \<in> Map.graph I \<or> (i, p) \<in> set is\<close>
      using assms(10)
      unfolding full_module_resolver_invar_def
      by fastforce
        then have \<open>\<forall> (_, _, is'') \<in> Cs. \<forall> (i, p, _) \<in> is''. (p, i) \<in> Map.graph I \<or> (i, p) \<in> set (tl is)\<close>
          using assms(9) assms(7)
          by (smt (verit, ccfv_threshold) Pair_inject case_prodD case_prodI2 not_hd_in_tl)
    moreover have \<open>finite Cs\<close>
      using assms(10)
      unfolding full_module_resolver_invar_def
      by fastforce
    moreover have \<open>\<forall> (_, _, is) \<in> Cs. finite is\<close>
      using assms(10)
      unfolding full_module_resolver_invar_def
      by fastforce
    moreover have \<open>\<forall> i \<in> ran I. i \<noteq> []\<close>
      using assms(10)
      unfolding full_module_resolver_invar_def
      by fastforce
    moreover have \<open>\<forall> (i, _) \<in> set is. i \<noteq> []\<close>
      using assms(10)
      unfolding full_module_resolver_invar_def
      by fastforce
        then have \<open>\<forall> (i, _) \<in> set (tl is). i \<noteq> []\<close>
        using assms(3)
        by (meson list.set_sel(2))
    moreover have \<open>\<forall> (i, _) \<in> Cs. i \<noteq> []\<close>
      using assms(10)
      unfolding full_module_resolver_invar_def
      by fastforce
    moreover have \<open>\<forall> (_, _, is) \<in> Cs. \<forall> (i, _, _) \<in> is. i \<noteq> []\<close>
      using assms(10)
      unfolding full_module_resolver_invar_def
      by fastforce
    moreover have \<open>\<forall> (i, p) \<in> set is. \<exists> i' m. (i, p, m) \<in> mk_paths_from_module_name i' INC\<close>
      using assms(10)
      unfolding full_module_resolver_invar_def
      by fastforce
        then have \<open>\<forall> (i, p) \<in> set (tl is). \<exists> i' m. (i, p, m) \<in> mk_paths_from_module_name i' INC\<close>
          by (meson assms(3) list.set_sel(2))
    moreover have \<open>\<forall> (p, i) \<in> Map.graph I. \<exists> i' m. (i, p, m) \<in> mk_paths_from_module_name i' INC\<close>
      using assms(10)
      unfolding full_module_resolver_invar_def
      by fastforce
    moreover have \<open>{ (p, i). (i, p) \<in> P \<and> does_file_exist p } \<subseteq> Map.graph I\<close>
      using assms(10)
      unfolding full_module_resolver_invar_def
      by fastforce
    ultimately show ?thesis
      unfolding full_module_resolver_invar_def
      using assms(1) assms(2)
      by fastforce
qed

theorem full_module_resolver_loop_preserves_invar:
  assumes \<open>full_module_resolver_invar INC is' (P, is, C, Cs, I)\<close>
      and \<open>is' \<noteq> []\<close>
      and \<open>is \<noteq> []\<close>
      and \<open>\<forall> (i, _) \<in> set is'. i \<noteq> []\<close>
      and \<open>\<forall> (i, p) \<in> set is'. (i, p, []) \<in> mk_paths_from_module_name i INC\<close>
      and \<open>hd is = (x, y)\<close>
  shows \<open>single_module_resolver INC x y C I \<le> SPEC
           (\<lambda>(U, C, Cs', I). do {
              ASSERT (\<forall> i p. (\<exists> is. (i, p, is) \<in> Cs') \<longrightarrow> I p = Some i);
              ASSERT (does_file_exist y \<longleftrightarrow> (y, x) \<in> Map.graph I);
              RETURN (insert (x, y) P, U @ tl is, C,
                Cs \<union> { (i, p, { (i, p, l). (i, p, l) \<in> is \<and> does_file_exist p }) | i p is. (i, p, is) \<in> Cs' },
                I)
            } \<le> SPEC (full_module_resolver_invar INC is'))\<close>
  (* TODO: remove that ugly apply style *)
  unfolding single_module_resolver_def
  apply (intro refine_vcg; simp)
  using single_module_resolver_invar1_init
    apply presburger
  using paths_finite
    apply presburger
  using single_module_resolver_invar2_init
    apply presburger
  apply auto[1]
  apply (meson single_module_resolver_invar2_step)
  using single_module_resolver_invar2_step
    apply presburger
  apply auto[1]
  apply (meson single_module_resolver_invar2_end1)
  using single_module_resolver_invar2_end1
    apply presburger
  apply (meson single_module_resolver_invar2_end2)
  using single_module_resolver_invar2_end2
    apply presburger
  apply (meson single_module_resolver_invar2_end3)
  apply (meson single_module_resolver_invar2_end3)
  using single_module_resolver_invar1_step
    apply presburger
  apply auto[1]
  apply (smt (verit, best) case_prod_conv mem_Collect_eq single_module_resolver_invar1_end1)
  using single_module_resolver_invar1_end1
    apply presburger
  apply (meson single_module_resolver_invar1_end2)
  apply (meson single_module_resolver_invar1_end2)
  using assms full_module_resolver_invar_step2
    apply presburger
  apply (intro refine_vcg)
  apply (meson domI in_graphD)
  apply (simp add: assms full_module_resolver_invar_step3)
  using in_graphD
    apply fastforce
  apply (intro refine_vcg)
  using in_graphI
    apply fast
  apply (smt (verit, ccfv_threshold) assms case_prodD case_prodI2 domI full_module_resolver_invar_step4 in_graphD)
  done

(***********************************************************************)

text \<open>
  We require that we are importing at least one module, and that every import contains
  at least a single element.
\<close>
definition full_module_resolver_pre :: \<open>[ include_path, (import \<times> path) list ] \<Rightarrow> bool\<close>
where \<open>full_module_resolver_pre INC is \<equiv> is \<noteq> []
                                       \<and> (\<forall> (i, _) \<in> set is. i \<noteq> [])
                                       \<and> (\<forall> (i, p) \<in> set is. (i, p, []) \<in> mk_paths_from_module_name i INC)\<close>

text \<open>
  This is our postcondition.
\<close>
definition full_module_resolver_post :: \<open>[ (import \<times> path) list, import_graph', import_cache, namespaces_abs ] \<Rightarrow> bool\<close>
where \<open>full_module_resolver_post is G C Ns \<equiv>
         (∄ p. pre_digraph.cycle (with_proj G) p)
                \<comment>\<open>• The end import graph is acyclic, meaning that no module \<open>M\<close> tries to import itself,
                    or import a module which transitively imports \<open>M\<close>.\<close>
       \<and> (\<forall> i \<in> set is. \<exists>! u \<in> pverts G. u = i)
                \<comment>\<open>• All our top-level imports are resolved (at least once) in the graph.\<close>
       \<and> (\<forall> u \<in> pverts G. \<forall> v \<in> pverts G. card { w \<in> pverts G. (u, w) \<in> parcs G \<and> fst w = fst v } \<le> 1)
                \<comment>\<open>• There is at most one edge coming from every node \<open>u\<close> to a given module.
                    In other words, all imports are unambiguous.\<close>
       \<and> C \<noteq> Map.empty
                \<comment>\<open>• Since we require that the list of top-level modules be non-empty, our end cache
                    must also be non-empty.\<close>
       \<and> { p. \<exists> i. (i, p) \<in> pverts G } \<subseteq> insert '''' (dom C)
                \<comment>\<open>• Consistency is key: all modules found in the graph must belong to the cache.\<close>
       \<and> { p. \<exists> i. (i, p) \<in> dom Ns } \<subseteq> dom C
                \<comment>\<open>• We don't have more namespaces than for each file in the cache.\<close>\<close>

definition full_module_resolver_post' :: \<open>[ (import \<times> path) list, (import_graph' \<times> import_cache \<times> namespaces_abs) option ] \<Rightarrow> bool\<close>
where \<open>full_module_resolver_post' is r \<equiv>
         case r of None \<Rightarrow> True | Some (G, C, Ns) \<Rightarrow> full_module_resolver_post is G C Ns\<close>

text \<open>
  If the precondition holds, and the module resolver terminates, then the postcondition must hold.
\<close>
theorem full_module_resolver_correct:
  fixes I :: \<open>(import \<times> path) list\<close>
  assumes \<open>full_module_resolver_pre INC I\<close>
  shows \<open>full_module_resolver INC I \<le> SPEC (full_module_resolver_post' I)\<close>
  unfolding full_module_resolver_def full_module_resolver_post'_def
  (* TODO: remove that ugly apply style *)
  apply (intro refine_vcg)
  using full_module_resolver_invar_init
    apply blast
  subgoal premises assms
    apply auto
    using assms full_module_resolver_loop_preserves_invar
    apply fast
    done
  (* All assertions after WHILE loop *)
  apply fastforce
  apply simp_all[19]
  unfolding full_module_resolver_invar_def
  apply simp_all[17]
  apply fastforce
  apply fastforce
  apply fastforce
  subgoal premises prems
    using prems(4) in_graphD
    by fast
  apply (smt (verit, ccfv_threshold) case_prodD case_prodI2 in_graphD)
  apply fastforce
  apply fastforce
  (* After checking that all top-level imports are resolved *)
  apply fastforce
  subgoal premises prems
    using prems(1) prems(23) prems(15) prems(10)
    by (metis (no_types, lifting) case_prodI2 in_hd_or_tl_conv prems(22))
  apply fast
  subgoal premises prems
    using prems(4)
    by fast
  subgoal premises prems
    using prems(4) prems(6) prems(7) prems(8) prems(9) prems(10)
    by fastforce
  apply auto[3] (* WARNING: a bit slow (> 5s) *)
  apply (rule SPEC_cons_rule[OF populate_import_graph_correct])
  apply (intro refine_vcg)
  subgoal
    apply simp
    using Resolver_Spec.populate_import_graph_post_def Resolver_Spec_axioms
    by force
  apply (rule SPEC_cons_rule[OF trim_import_graph_correct])
  apply (intro refine_vcg)
  apply (metis option.simps(4))
  (* Assertions at the end of the function *)
  unfolding trim_import_graph_post_def trim_import_graph_post'_def
  apply simp_all[4]
  apply argo
  subgoal premises prems
    using prems(31)
    by force
  subgoal
    unfolding populate_import_graph_post_def
    by (simp, meson subset_eq)
  (* Post condition *)
  unfolding populate_import_graph_post_def
  unfolding full_module_resolver_post'_def full_module_resolver_post_def
  apply (simp only: option.cases(2) case_prod_conv)
  apply (intro conjI)
  apply metis
  apply meson
  apply blast
  subgoal
    apply simp
    sorry
  subgoal
    apply simp
    sorry
  subgoal
    apply simp
    sorry
  done

(*
definition resolve_module :: \<open>[ include_path, import list ] \<Rightarrow> (import_graph' \<times> import_cache \<times> namespaces_abs) option\<close>
where \<open>resolve_module INC is \<equiv>
         let is = [ (i, p). i \<leftarrow> is, (i', p, m) \<leftarrow> set_to_list (mk_paths_from_module_name i INC), i = i' \<and> m = [] ] in
         full_module_resolver INC is\<close>
*)

end (* locale Resolver_Spec *)

end (* theory ImportResolver_Spec *)
