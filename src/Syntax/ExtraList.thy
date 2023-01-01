theory ExtraList
  imports
    Main
begin

definition maximum_by :: \<open>('a \<Rightarrow> ('b::ord)) \<Rightarrow> ('b::ord) \<Rightarrow> 'a list \<Rightarrow> ('b::ord)\<close>
where \<open>maximum_by f e l \<equiv> List.fold (max \<circ> f) l e\<close>

definition maximum :: \<open>('a::ord) \<Rightarrow> ('a::ord) list \<Rightarrow> ('a::ord)\<close>
where \<open>maximum \<equiv> maximum_by id\<close>

(******************************************)

lemma maximum_by_simps [code]:
  \<open>maximum_by f e [] = e\<close>
  \<open>maximum_by f e (x # xs) = maximum_by f (max (f x) e) xs\<close>
  by (simp_all add: maximum_by_def)

lemma maximum_nil [simp]: \<open>maximum n [] = n\<close>
  by (simp add: maximum_by_simps(1) maximum_def)

lemma maximum_cons [simp]: \<open>maximum n (x # xs) = maximum (max x n) xs\<close>
  by (simp add: maximum_by_simps(2) maximum_def)

(* NOTE: why does it not work for an arbitrary \<open>x\<close>? *)
lemma max_is_less: \<open>\<forall>x \<in> set xs. (x :: nat) \<le> maximum n xs\<close>
  unfolding maximum_def maximum_by_def
  apply simp
  by (metis List.finite_set Max.set_eq_fold Max_ge set_subset_Cons subsetD)

lemma max_is_less_than_max: \<open>x \<in> set xs \<Longrightarrow> (x :: nat) \<le> max (maximum n xs) m\<close>
  by (simp add: max.coboundedI1 max_is_less)

lemma f_of_max_is_less:
  fixes f :: \<open>'a \<Rightarrow> nat\<close>
  shows \<open>x \<in> set xs \<Longrightarrow> f x \<le> maximum_by f n xs\<close>
  unfolding maximum_def maximum_by_def
  by (metis List.finite_set Max.set_eq_fold Max_ge fold_map image_eqI insertCI list.set(2) list.set_map)

lemma f_of_max_is_less_than_max:
  fixes f :: \<open>'a \<Rightarrow> nat\<close>
    and g :: \<open>'b \<Rightarrow> nat\<close>
  shows \<open>x \<in> set xs \<Longrightarrow> f x \<le> max (maximum_by f 0 xs) (g y)\<close>
  by (simp add: f_of_max_is_less max.coboundedI1)

end
