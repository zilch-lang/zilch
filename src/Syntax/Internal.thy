theory Internal
  imports Main
begin

instantiation list :: (linorder) linorder
begin
  fun less_eq_list :: \<open>'a list \<Rightarrow> 'a list \<Rightarrow> bool\<close>
  where \<open>[] \<le> _ = True\<close>
      | \<open>(_ # _) \<le> [] = False\<close>
      | \<open>(x # xs) \<le> (y # ys) = (x \<le> y \<and> xs \<le> ys)\<close>

  fun less_list :: \<open>'a list \<Rightarrow> 'a list \<Rightarrow> bool\<close>
  where \<open>[] < _ = True\<close>
      | \<open>(_ # _) < [] = False\<close>
      | \<open>(x # xs) < (y # ys) = (x < y \<and> xs < ys)\<close>

  instance
    sorry
end

end
