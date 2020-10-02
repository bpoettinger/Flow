\<^marker>\<open>creator Bernhard Pöttinger\<close>

chapter \<open>Endomorphism\<close>
theory Endomorphism
imports Flow_Base "HOL-Library.Multiset" "HOL-Library.Function_Algebras" Alternating
begin

text \<open>@{cite \<open>p. 327\<close> krishna20}\<close>

class pos_monoid_add = canonically_ordered_monoid_add
class pos_cancel_comm_monoid_add = pos_monoid_add + cancel_comm_monoid_add

text \<open>@{cite \<open>def. 8\<close> krishna20}\<close>

definition endo :: "('m \<Rightarrow> 'm :: cancel_comm_monoid_add) \<Rightarrow> bool" where
  "endo f \<equiv> \<forall>x1 x2. f (x1 + x2) = f x1 + f x2"

abbreviation "End \<equiv> { f . endo f }"
                        
definition End_closed where
  "End_closed E \<equiv> E \<subseteq> End \<and>
    (\<forall>f1 f2. f1 \<in> E \<longrightarrow> f2 \<in> E \<longrightarrow> f1 + f2 \<in> E \<and> f2 o f1 \<in> E)"

lemma endo_id[simp]: "endo id" "endo (\<lambda>x. x)"
  unfolding endo_def by simp_all

lemma endo_zero[simp]: "endo (\<lambda>_. 0)" "endo 0"
  unfolding endo_def by simp_all

lemma endo_f_0_0_closed[simp]:
  assumes "f \<in> E" "End_closed E"
  shows "f 0 = 0"
proof -
  have "f 0 = f (0 + 0)" by simp
  also have "... = f 0 + f 0" using assms unfolding endo_def End_closed_def by blast
  finally show "f 0 = 0" by simp
qed

lemma endo_f_0_0_closed_comp[simp]:
  assumes "f \<in> E" "End_closed E"
  shows "f o 0 = 0"
  using assms endo_f_0_0_closed[where E=E]
  unfolding End_closed_def endo_def comp_def zero_fun_def
  by auto

lemma endo_f_n0_n0_closed:
  assumes "f \<in> E" "End_closed E" "f x \<noteq> 0"
  shows "x \<noteq> 0"
  using assms
  by auto

lemma
  assumes "End_closed E" "f1 \<in> E" "f2 \<in> E"
  shows End_sum_closed: "f1 + f2 \<in> E"
    and End_comp_closed: "f2 o f1 \<in> E"
  using assms
  unfolding endo_def plus_fun_def End_closed_def
  by (auto simp: algebra_simps)

lemma End_closed_End: "End_closed End"
  unfolding End_closed_def endo_def
  by (auto simp add: algebra_simps)

lemma endo_iterated_sum_closed:
  "finite xs \<Longrightarrow> f \<in> E \<Longrightarrow> End_closed E \<Longrightarrow> f (\<Sum>x \<in> xs. g x) = (\<Sum>x \<in> xs. f (g x))"
proof (induction xs rule: finite_induct)
  case empty
  have "f (\<Sum> {}) = f 0" by simp
  also have "... = 0" using empty End_closed_def by auto
  also have "... = sum f {}" by simp
  ultimately show ?case by simp
next
  case (insert x xs)
  then have "f (\<Sum>x \<in> insert x xs. g x) = f (g x + (\<Sum>x \<in> xs. g x))" using sum.insert by auto
  also have "... = f (g x) + f (\<Sum>x \<in> xs. g x)" using insert unfolding endo_def End_closed_def by auto
  also have "... = f (g x) + (\<Sum>x \<in> xs. f (g x))" using insert by auto
  also have "... = (\<Sum>x \<in> insert x xs. f (g x))" using insert by auto
  finally show ?case by simp
qed

lemma endo_sum_closed:
  "f \<in> E \<Longrightarrow> End_closed E \<Longrightarrow> f (x + y) = f x + f y"
  unfolding End_closed_def endo_def by auto

lemma End_closedE:
  assumes "End_closed E" "f \<in> E" "g \<in> E"
  shows "f + g \<in> E" "f o g \<in> E"
  using assms unfolding End_closed_def
  by auto

lemma End_closed_sumE:
  assumes "finite X" "End_closed E" "(\<lambda>_. 0) \<in> E" "\<forall>x. f x \<in> E"
  shows "(\<Sum>x \<in> X. f x) \<in> E"
  using assms
proof (induct X)
case empty
  then show ?case by simp
next
case (insert x F)
  then show ?case
    unfolding End_closed_def plus_fun_def endo_def
    by auto
qed

lemma pos_endo_mono_closed:
  fixes f1 f2 g1 g2 :: "'m \<Rightarrow> 'm :: pos_cancel_comm_monoid_add"
  assumes "f1 \<le> g1" "f2 \<le> g2" "f1 \<in> E" "g1 \<in> E" "End_closed E"
  shows "f1 o f2 \<le> g1 o g2"
  unfolding comp_def le_fun_def
proof
  fix x
  obtain m1 m2 m3 where *: "g1 x = f1 x + m1" "g2 x = f2 x + m2" "g1 (f2 x) = f1 (f2 x) + m3"
    using assms le_iff_add[of "f1 x" "g1 x"] le_iff_add[of "f2 x" "g2 x"] le_iff_add[of "f1 (f2 x)" "g1 (f2 x)"]
    unfolding le_fun_def by auto

  have "f1 (f2 x) \<le> f1 (f2 x) + m3" by (simp add: le_iff_add)
  also have "... \<le> g1 (f2 x) + g1 m2" using * by (simp add: le_iff_add)
  also have "... = g1 (g2 x)" using * assms unfolding endo_def End_closed_def by auto
  finally show "f1 (f2 x) \<le> g1 (g2 x)" .
qed

lemma pos_endo_mono'_closed:
  fixes f :: "'m \<Rightarrow> 'm :: pos_cancel_comm_monoid_add"
  assumes "x \<le> y" "f \<in> E" "End_closed E"
  shows "f x \<le> f y"
  using assms pos_endo_mono_closed[of f f "\<lambda>_. x" "\<lambda>_. y" E]
  by (auto simp: endo_def comp_def le_funD le_funI, metis le_funD)

lemma pos_endo_mono''_closed:
  fixes f :: "'m \<Rightarrow> 'm :: pos_cancel_comm_monoid_add"
  assumes "x \<le> y" "f \<le> g" "f \<in> E" "g \<in> E" "End_closed E"
  shows "f x \<le> g y"
  using assms pos_endo_mono_closed[of f g "\<lambda>_. x" "\<lambda>_. y" E]
  apply auto
  by (simp add: le_fun_def)

lemma pos_endo_mono_sandwich':
  fixes f :: "'m \<Rightarrow> 'm :: pos_cancel_comm_monoid_add"
  assumes "f \<le> g" "x \<le> y" "f \<in> E" "g \<in> E" "h \<in> E" "End_closed E"
  shows "h (f x) \<le> h (g y)"
proof -
  have "f x \<le> g y"
    using assms pos_endo_mono_closed[of f g "\<lambda>_. x" "\<lambda>_. y"]
    apply auto
    by (metis le_fun_def order_trans pos_endo_mono'_closed)
  then show ?thesis
    using pos_endo_mono'_closed assms by blast
qed

definition nilpotent :: "('a \<Rightarrow> 'a :: zero) set \<Rightarrow> bool" where
  "nilpotent E \<equiv> \<exists>p > 1. \<forall>f \<in> E. f^^p = (\<lambda>_. 0)"

lemma fun_dist_left[simp]: "(f1 + f2) o g = (f1 o g) + (f2 o g)"
  unfolding plus_fun_def
  by auto

lemma fun_dist_left'[simp]: "finite X \<Longrightarrow> (\<Sum>x\<in>X. f x) o g = (\<Sum>x\<in>X. (f x) o g)"
  by (induct X rule: finite_induct, auto simp: zero_fun_def plus_fun_def, metis)

lemma fun_dist_list_left'[simp]: "(\<Sum>x \<leftarrow> xs. f x) o g = (\<Sum>x \<leftarrow> xs. (f x) o g)"
  by (induction xs, auto simp: zero_fun_def plus_fun_def, metis)

lemma fun_dist_right[simp]: "endo g \<Longrightarrow> g o (f1 + f2) = (g o f1) + (g o f2)"
  unfolding plus_fun_def endo_def
  by auto

lemma fun_dist_right_closed[simp]:
  assumes "g \<in> E" "End_closed E"
  shows "g o (f1 + f2) = (g o f1) + (g o f2)"
  using assms
  unfolding plus_fun_def endo_def End_closed_def comp_def
  by auto

lemma fun_dist_right2[simp]:
  assumes "endo g"
  shows "g (f1 x + f2 x) = (g (f1 x)) + (g (f2 x))"
  using assms
  unfolding plus_fun_def endo_def
  by auto

lemma fun_dist_right2_closed[simp]:
  assumes "g \<in> E" "End_closed E"
  shows "g (f1 x + f2 x) = (g (f1 x)) + (g (f2 x))"
  using assms
  unfolding plus_fun_def endo_def End_closed_def
  by auto

lemma fun_dist_right''[simp]:
 "finite xs \<Longrightarrow> g \<in> E \<Longrightarrow> End_closed E \<Longrightarrow> g (\<Sum>x \<in> xs. f x) = (\<Sum>x \<in> xs. g (f x))"
  using endo_iterated_sum_closed by auto

lemma fun_dist_right'_closed[simp]:
 "finite X \<Longrightarrow> g \<in> E \<Longrightarrow> End_closed E \<Longrightarrow> g o (\<Sum>x \<in> X. f x) = (\<Sum>x \<in> X. g o (f x))"
  unfolding plus_fun_def
  by (induction X rule: finite_induct, auto)

lemma fun_dist_list_right'[simp]:
 "g \<in> E \<Longrightarrow> End_closed E \<Longrightarrow> g o (\<Sum>x \<leftarrow> xs. f x) = (\<Sum>x \<leftarrow> xs. g o (f x))"
  unfolding plus_fun_def
  by (induct xs, auto simp: zero_fun_def)

text \<open>Definition 12 from @{cite krishna20}\<close>

definition reduced where
  "reduced E \<equiv> \<forall>e \<in> E. e o e = 0 \<longrightarrow> e = 0"

definition pointwise_reduced where
  "pointwise_reduced E \<equiv> \<forall>e \<in> E. \<forall>x. e x \<noteq> 0 \<longrightarrow> e (e x) \<noteq> 0"

lemma pointwise_reduced_reduced:
  "pointwise_reduced E \<Longrightarrow> reduced E"
  unfolding pointwise_reduced_def reduced_def
proof
  fix e
  assume A1: "\<forall>e\<in>E. \<forall>x. e x \<noteq> 0 \<longrightarrow> e (e x) \<noteq> 0"
   and A2: "e \<in> E"

  have "e \<noteq> 0 \<Longrightarrow> e o e \<noteq> 0"
  proof -
    assume "e \<noteq> 0"
    then obtain x where "e x \<noteq> 0" by fastforce
    then have "e (e x) \<noteq> 0" using A1 A2 by blast
    then show "e o e \<noteq> 0" unfolding comp_def zero_fun_def by metis
  qed

  then show "e \<circ> e = 0 \<longrightarrow> e = 0"
    unfolding zero_fun_def comp_def
    by auto
qed

lemma reduced_not_equal:
  "reduced E \<Longrightarrow> e \<in> E \<Longrightarrow> e \<noteq> 0 \<Longrightarrow> e o e \<noteq> 0"
  unfolding reduced_def
  by auto

lemma sum_insert_pos_monoid:
  fixes f :: "'a \<Rightarrow> ('b :: pos_cancel_comm_monoid_add)"
  assumes "finite X" "a \<in> X"
  shows "f a \<le> sum f X"
proof -
  have "sum f (insert a (X - {a})) = f a + sum f (X - {a})"
    by (rule sum.insert, simp_all add: assms)
  then show ?thesis
    using le_iff_add insert_absorb[of a X] assms
    by auto
qed

lemma sum_cong2:
  assumes "\<forall>x \<in> X. \<forall>y \<in> Y. f x y = g x y"
  shows "(\<Sum>x \<in> X. \<Sum>y \<in> Y. f x y) = (\<Sum>x \<in> X. \<Sum>y \<in> Y. g x y)"
  using assms
  by auto

lemma plus_fun_apply_iterated:
  assumes "finite X"
  shows "(\<Sum>x \<in> X. f x) a = (\<Sum>x \<in> X. f x a)"
  using assms by (induction X rule: finite_induct, auto)

lemma endo_edge_fg_plus_fg:
  assumes "End_closed E" "h1 + h2 \<noteq> bot" "\<forall>x y. edge_fg h1 x y \<in> E"
    "\<forall>x y. edge_fg h2 x y \<in> E" "(\<lambda>_. 0) \<in> E"
  shows "\<forall>x y. edge_fg (h1 + h2) x y \<in> E"
proof -
  have "edge_fg (h1 + h2) = edge_fg h1 on dom_fg h1"
    using edge_fg_plus_fg_on1[of h1 h2] assms by blast

  show ?thesis
  proof
    fix x
    consider (a) "x \<in> dom_fg h1" | (b) "x \<in> dom_fg h2" | (c) "x \<in> - (dom_fg h1 \<union> dom_fg h2)"
      by blast
    then show "\<forall>y. edge_fg (h1 + h2) x y \<in> E"
    proof cases
      case a
      then show ?thesis
        using assms edge_fg_plus_fg_on1[of h1 h2] by simp
    next
      case b
      then show ?thesis
        using assms edge_fg_plus_fg_on2[of h1 h2] by simp
    next
      case c
      then show ?thesis
        using assms edge_fg_0_outside_dom[of x "h1 + h2"]
        by simp
    qed
  qed
qed

text \<open>@{cite \<open>lem. 3\<close> krishna20}\<close>
text \<open>Our formalization of flow domains deviating from the definition of flow domain in
@{cite krishna20} (which includes the set of allowed edge functions)
reduces to this instantiation of prod for cancellative commutative monoids.
As the original definition does not impose any constraints on the set of allowed edge functions
except for the domain and codomain of the function this limitation has no consequences.\<close>

instantiation prod :: (cancel_comm_monoid_add, cancel_comm_monoid_add) cancel_comm_monoid_add
begin
definition "zero_prod \<equiv> (0,0)"
definition "plus_prod \<equiv> \<lambda>(x1,y1) (x2,y2). (x1+x2, y1+y2)"
definition "minus_prod \<equiv> \<lambda>(x1,y1) (x2,y2). (x1-x2, y1-y2)"

instance
  apply standard
  unfolding zero_prod_def plus_prod_def minus_prod_def
  by (auto split: prod.splits simp: algebra_simps)
end

definition End_prod  where
"End_prod E1 E2 \<equiv> {\<lambda>(x,y). (e1 x,e2 y) | e1 e2. e1 \<in> E1 \<and> e2 \<in> E2}"

lemma endo_prod:
  assumes "End_closed E1" "End_closed E2"
  shows "End_closed (End_prod E1 E2)"
  using assms
  unfolding End_closed_def End_prod_def endo_def
  apply (auto split: prod.splits simp: zero_prod_def plus_prod_def plus_fun_def)
  apply (rule_tac x="\<lambda>x. e1 x + e1a x" in exI)
   apply (rule_tac x="\<lambda>x. e2 x + e2a x" in exI)
  apply (auto split: prod.splits simp: zero_prod_def plus_prod_def plus_fun_def comp_def)
  apply (rule_tac x="\<lambda>x. e1a (e1 x)" in exI)
  apply (rule_tac x="\<lambda>x. e2a (e2 x)" in exI)
  by (auto split: prod.splits simp: zero_prod_def plus_prod_def plus_fun_def comp_def)

end
