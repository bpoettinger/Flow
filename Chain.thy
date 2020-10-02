\<^marker>\<open>creator Bernhard Pöttinger\<close>

chapter \<open>Function Chains\<close>
theory Chain
imports Endomorphism Auxiliary
begin

paragraph \<open>Summary\<close>
text \<open>This theory introduces function chains and corresponding
 lemmas about appending/monotonicity/endomorphisms.\<close>

paragraph \<open>Major definitions\<close>
text \<open>
\<^item> chains
\<^item> chains'
\<^item> cap
\<^item> cap
\<^item> @{term cap_fg}
\<^item> @{term \<delta>}
\<close>

paragraph \<open>Major Lemmas\<close>
text \<open>@{text cap'_unrolled_closed}\<close>

section \<open>chain\<close>

fun chain :: "('a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> ('b \<Rightarrow> 'b)" where
  "chain f [] _ = id" |
  "chain f (x#[]) y = f x y" |
  "chain f (x1#x2#xs) y = (chain f (x2#xs) y) o (f x1 x2)"

lemma chain_cong:
  assumes "f1 = f2 on set ns"
  shows "chain f1 ns n = chain f2 ns n"
  using assms
  apply (induction ns, simp)
  subgoal for a ns
    apply (cases ns)
    by auto
  done

lemma chain_cong':
  assumes "f = g on N" "set ns \<subseteq> N"
  shows "chain f ns n = chain g ns n"
  using assms
  by (simp add: chain_cong subset_eq)

lemma chain_append:
  assumes "ys \<noteq> []"
  shows "chain f (xs @ ys) z = (chain f ys z) o (chain f xs (hd ys))"
  using assms
  apply (induction xs rule: induct_list012)
    apply auto
  apply (case_tac ys)
  by auto

lemma chain_append_nonempty:
  "chain f (xs @ ys) z a = chain f ys z (chain f xs (hd (ys @ [z])) a)"
  apply (induction xs arbitrary: a z rule: induct_list012)
    apply auto
  apply (case_tac ys)
  by auto

lemma chain_append1:
  shows "xs \<noteq> [] \<Longrightarrow> chain f xs y z = f (last xs) y (chain f (butlast xs) (last xs) z)"
  by (induction xs arbitrary: z rule: induct_list012, auto)

lemma chain_extend_right:
  "((f y y') o (chain f zs y)) x = chain f (zs@[y]) y' x"
 by (induction zs arbitrary: x rule: induct_list012, auto)

lemma endo_chain_closed:
  assumes "\<forall>x y. f x y \<in> E" "End_closed E" "id \<in> E"
  shows "chain f xs y \<in> E"
  using assms
proof (induction xs rule: induct_list012)
case 1
  then show ?case unfolding endo_def End_closed_def by simp 
next
  case (2 x)
  then show ?case unfolding endo_def by simp
next
  case (3 x1 x2 xs)
  then show ?case
    unfolding endo_def End_closed_def comp_def
    by auto
qed

lemma endo_chain_closed_nonempty:
  assumes "xs \<noteq> []" "\<forall>x y. f x y \<in> E" "End_closed E"
  shows "chain f xs y \<in> E"
  using assms
proof (induction xs rule: induct_list012)
case 1
  then show ?case unfolding endo_def End_closed_def by simp 
next
  case (2 x)
  then show ?case unfolding endo_def by simp
next
  case (3 x1 x2 xs)
  then show ?case
    unfolding endo_def End_closed_def comp_def
    by auto
qed

lemma chain_append_not_zero:
  assumes "xs = xs1 @ xs2" "chain f xs y z \<noteq> 0" "xs2 \<noteq> []" "\<forall>x y. f x y \<in> E" "End_closed E"
  shows "chain f xs1 (hd xs2) z \<noteq> 0" "chain f xs2 y (chain f xs1 (hd xs2) z) \<noteq> 0"
proof -    
  have "chain f xs y z = (chain f xs2 y o chain f xs1 (hd xs2)) z"
    using chain_append[of xs2 f xs1 y] assms by simp
  then show "chain f xs2 y (chain f xs1 (hd xs2) z) \<noteq> 0"
    using assms by simp
  then show "chain f xs1 (hd xs2) z \<noteq> 0"
    using endo_f_n0_n0_closed[of "chain f xs2 y" E "chain f xs1 (hd xs2) z"]
      endo_chain_closed[of f E xs2 y] assms
    by (simp add: endo_chain_closed_nonempty)
qed

lemma chain_append_not_zero3:
  fixes z :: "'a :: pos_cancel_comm_monoid_add"
  assumes "xs = xs1 @ xs2 @ xs3" "chain f xs y z \<noteq> 0" "xs2 \<noteq> []" "xs3 \<noteq> []" "\<forall>x y. f x y \<in> E"
    "End_closed E"
  shows "chain f xs1 (hd xs2) z \<noteq> 0" "chain f xs2 (hd xs3) (chain f xs1 (hd xs2) z) \<noteq> 0"
    "chain f xs3 y (chain f (xs1 @ xs2) (hd xs3) z) \<noteq> 0"
proof -
  have "chain f xs y z = (chain f xs3 y o chain f (xs1 @ xs2) (hd xs3)) z"
    using chain_append[of xs3 f "xs1 @ xs2" y] assms by simp
  then have *:
    "chain f (xs1 @ xs2) (hd xs3) z \<noteq> 0" "chain f xs3 y (chain f (xs1 @ xs2) (hd xs3) z) \<noteq> 0"
    using chain_append_not_zero[of xs "xs1 @ xs2" xs3 f y z E] assms by force+
  then show "chain f xs1 (hd xs2) z \<noteq> 0" "chain f xs2 (hd xs3) (chain f xs1 (hd xs2) z) \<noteq> 0"
    using chain_append_not_zero[of "xs1 @ xs2" xs1 xs2 f "hd xs3" z E] assms by force+
  then show "chain f xs3 y (chain f (xs1 @ xs2) (hd xs3) z) \<noteq> 0"
    using * by simp
qed

lemma chain_mono:
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm :: pos_cancel_comm_monoid_add"
  assumes "x \<le> x'" "End_closed E" "\<forall>x y. f x y \<in> E"
  shows "chain f xs y x \<le> chain f xs y x'"
  using assms
proof (induction xs arbitrary: x x' rule: induct_list012)
  case 1
  then show ?case by simp
next
  case (2 xs)
  then show ?case
    using pos_endo_mono'_closed[of x x' "f xs y" E] by simp
next
  case (3 a b zs)
  then show ?case
    using pos_endo_mono'_closed[of x x' "f a b" E] by simp
qed

section \<open>chains\<close>

fun chains :: "('a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list list \<Rightarrow> 'a \<Rightarrow> ('b \<Rightarrow> 'b)" where
  "chains f [] _ = id" |
  "chains f (xs#[]) y = chain f xs y" |
  "chains f (xs1#xs2#xss) y = (chains f (xs2#xss) y) o (chain f xs1 (hd xs2))"

lemma chain_chains:
  assumes "xs = concat xss" "\<forall>xs \<in> set (tl xss). xs \<noteq> []"
  shows "chain f xs y = chains f xss y"
  using assms
  by (induction xss arbitrary: xs rule: induct_list012, auto simp: chain_append)

lemma chains_prepend_append:
  assumes "xss = xs # yss @ [zs]" "yss \<noteq> []"
  shows "chains f xss y = (chain f zs y) o (chains f yss (hd zs)) o (chain f xs (hd (hd yss)))"
  using assms
  by (induction yss arbitrary: xss xs rule: induct_list012, auto)

lemma endo_chains_closed:
  assumes "\<forall>x y. f x y \<in> E" "End_closed E" "id \<in> E"
  shows "chains f xss y \<in> E"
  using assms
proof (induction xss rule: induct_list012)
  case 1
  then show ?case by simp
next
  case (2 xs)
  then show ?case
    using endo_chain_closed[of f E xs y] assms by fastforce
next
  case (3 x y' zs)
  have "chain f x (hd y') \<in> E"
    using endo_chain_closed[of f E x "hd y'"] assms by simp
  then show ?case
    using endo_chain_closed[of f E x "hd y'"] 3
    unfolding endo_def End_closed_def comp_def
    by auto
qed

lemma endo_chains_closed_nonempty:
  assumes "\<forall>x y. f x y \<in> E" "End_closed E" "xss \<noteq> []" "\<forall>xs \<in> set xss. xs \<noteq> []"
  shows "chains f xss y \<in> E"
  using assms
proof (induction xss rule: induct_list012)
  case 1
  then show ?case by simp
next
  case (2 xs)
  then show ?case
    using endo_chain_closed_nonempty[of xs] 2 by auto
next
  case (3 x y' zs)
  have "chain f x (hd y') \<in> E"
    using endo_chain_closed_nonempty[of x f E "hd y'"] 3 by simp
  then show ?case
    using endo_chain_closed[of f E x "hd y'"] 3
    unfolding endo_def End_closed_def comp_def
    by auto
qed

lemma chain_cong'':
  assumes "f = g on N" "set ns \<subseteq> N"
  shows "chain f ns n a = chain g ns n a"
  using assms chain_cong subset_eq
  by metis

lemma chain_append':
  assumes "ys \<noteq> []"
  shows "chain f (xs @ ys) z a = (chain f ys z (chain f xs (hd ys) a))"
  using assms
  apply (induction xs arbitrary: a z rule: induct_list012)
  by (auto, case_tac "ys", auto)

lemma chain_concat_chains:
  assumes "\<forall>xs \<in> set xss. xs \<noteq> []"
  shows "chain f (concat xss) y z = chains f xss y z"
  using assms
  apply (induction xss arbitrary: z rule: induct_list012, simp, simp)
  by (simp, subst chain_append_nonempty, simp)

lemma chains_cong:
  assumes "f = f' on N" "\<And>xs. xs \<in> set xss \<Longrightarrow> set xs \<subseteq> N"
  shows "chains f xss y z = chains f' xss y z"
  using assms
  by (induction xss arbitrary: z rule: induct_list012, simp_all add: chain_cong')

section \<open>Capacity\<close>

definition \<delta> :: "'n \<Rightarrow> 'n \<Rightarrow> 'm \<Rightarrow> 'm::cancel_comm_monoid_add" where
"\<delta> \<equiv> \<lambda>n n'. \<lambda>x. if n = n' then x else 0"

lemma \<delta>_id[simp]: "\<delta> n n = id" "n \<noteq> n' \<Longrightarrow> \<delta> n n' = (\<lambda>_. 0)"
  unfolding \<delta>_def by auto

text \<open>@{cite \<open>def. 10\<close> krishna20}\<close>

fun cap'
  :: "nat \<Rightarrow> 'n set \<Rightarrow> ('n \<Rightarrow> 'n \<Rightarrow> 'm \<Rightarrow> 'm) \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow>
      ('m \<Rightarrow> 'm::cancel_comm_monoid_add)"
where
  "cap'      0  N e n n' = \<delta> n n'" |
  "cap' (Suc i) N e n n' = \<delta> n n' + (\<Sum>n'' \<in> N. (e n'' n') o (cap' i N e n n''))"

abbreviation "cap N \<equiv> cap' (card N) N"

abbreviation "cap_fg \<equiv> \<lambda>h. cap (dom_fg h) (edge_fg h)"

lemma cap'_cong_e:
  assumes "e = e' on N"
  shows "cap' k N e x y = cap' k N e' x y"
proof (induction k arbitrary: y)
  case 0
  then show ?case
    by simp
next
  case (Suc k)
  then show ?case
    using assms by auto
qed

section \<open>chain2\<close>

text \<open>chain2 x xs y should be avoided and replaced by chain (x\#xs) y\<close>

fun chain2 where
"chain2 f x [] y = f x y" |
"chain2 f x (z#zs) y = (chain2 f z zs y) o (f x z)"

lemma chain2_extend_right:
  "(f y y') o (chain2 f x zs y) = chain2 f x (zs@[y]) y'"
  by (induction zs arbitrary: x, auto, metis comp_assoc)

lemma chain2_endo:
  assumes "\<forall>x y. f x y \<in> E" "End_closed E"
  shows "chain2 f x ys z \<in> E"
  using assms
  by (induction ys arbitrary: x, auto intro: End_closedE)

lemma chain2_cong_e:
  assumes "e = e' on ({x} \<union> set ys)"
  shows "chain2 e x ys z u = chain2 e' x ys z u"
  using assms
  by (induction ys arbitrary: x u, auto)

lemma chain2_cong_e':
  assumes "e = e' on ({x} \<union> set ys)"
  shows "chain2 e x ys z = chain2 e' x ys z"
  using assms
  by (induction ys arbitrary: x, auto)

lemma chain_chain2:
  "ns \<noteq> [] \<Longrightarrow> chain f ns y = chain2 f (hd ns) (tl ns) y"
  by (induction ns rule: induct_list012, auto)

lemma chain2_chain:
  "chain2 f x ys z a = chain f (x # ys) z a"
  by (induction ys arbitrary: a x rule: induct_list012, auto)

section \<open>Unrolling Capacities\<close>

text \<open>@{cite \<open>lem. 9\<close> krishna19b}\<close>
text \<open>should be restated in terms of chains instead of chains2\<close>

lemma cap'_unrolled_closed:
  assumes "\<forall>x y. e x y \<in> E" "finite N" "n \<in> N" "End_closed E"
  shows "cap' i N e n n' = \<delta> n n' + (\<Sum>ns \<in> l_lists' N i. chain2 e n ns n')"
  using assms(3)
proof (induction i arbitrary: n n')
  case 0
  then show ?case
    unfolding l_lists'_def
    by simp
next
  case (Suc i)

  have **: "n \<in> N \<Longrightarrow> (\<Sum>n'' \<in> N. e n'' n' o \<delta> n n'') = (\<Sum>n'' \<in> {n}. e n n')"
  proof -
    assume A: "n \<in> N"
    have *: "\<And>n''. n'' \<noteq> n \<Longrightarrow> e n'' n' o \<delta> n n'' = 0"
      unfolding \<delta>_def using assms endo_f_0_0_closed[of "e _ _" E] by auto
    have "(\<Sum>n'' \<in> {n} \<union> (N - {n}). e n'' n' o \<delta> n n'') =
      (\<Sum>n'' \<in> {n}. e n'' n' o \<delta> n n'') + (\<Sum>n'' \<in> N - {n}. e n'' n' o \<delta> n n'')"
      by (rule sum.union_disjoint, simp_all add:assms)
    also have "... = (\<Sum>n'' \<in> {n}. e n'' n' o \<delta> n n'') + 0"
      by (subst sum.neutral[of "N - {n}"], auto simp: *)
    finally show ?thesis
      unfolding \<delta>_def
      by (auto simp: insert_absorb A)
  qed

  have "inj_on (\<lambda>(n, ns). ns @ [n])  (N \<times> l_lists' N i)"
    by (auto intro: inj_onI)
  moreover have "(\<Sum>x\<in>N \<times> l_lists' N i. chain2 e n (case x of (n, ns) \<Rightarrow> ns @ [n]) n') =
        (\<Sum>x\<in>N \<times> l_lists' N i. case x of (n'', ns) \<Rightarrow> chain2 e n (ns @ [n'']) n')"
    by (auto intro: sum.cong)
  ultimately  have ****: "(\<Sum>(n'', ns)\<in>N \<times> l_lists' N i. chain2 e n (ns @ [n'']) n')
    = (\<Sum>ns\<in>(\<lambda>(n, ns). ns @ [n]) ` (N \<times> l_lists' N i). chain2 e n ns n')"
    using sum.reindex[symmetric,of "\<lambda>(n,ns). ns @ [n]" "N \<times> l_lists' N i" "\<lambda>ns. chain2 e n ns n'"]
    by (auto)

  have "cap' (Suc i) N e n n' = \<delta> n n' + (\<Sum>n'' \<in> N. (e n'' n') o (cap' i N e n n''))"
    by simp
  also have "... = \<delta> n n' + (\<Sum>n'' \<in> N. (e n'' n') o (\<delta> n n'' + (\<Sum>ns\<in>l_lists' N i. chain2 e n ns n'')))"
    by (simp, rule sum.cong, auto simp: Suc)
  also have "... = \<delta> n n' + (\<Sum>n'' \<in> N. (e n'' n' o \<delta> n n'') + ((e n'' n') o (\<Sum>ns\<in>l_lists' N i. chain2 e n ns n'')))"
    apply (subst fun_dist_right_closed) using assms by auto
  also have "... = \<delta> n n' + (\<Sum>n'' \<in> N. (e n'' n' o \<delta> n n'') + (\<Sum>ns\<in>l_lists' N i. e n'' n' o chain2 e n ns n''))"
    apply (subst fun_dist_right'_closed[where g="e _ _"]) using assms by auto
  also have "... = \<delta> n n' + (\<Sum>n'' \<in> N. (e n'' n' o \<delta> n n'') + (\<Sum>ns\<in>l_lists' N i. chain2 e n (ns@[n'']) n'))"
    by (simp add: chain2_extend_right)
  also have "... = \<delta> n n' + (\<Sum>n'' \<in> N. e n'' n' o \<delta> n n'') + (\<Sum>n'' \<in> N. \<Sum>ns\<in>l_lists' N i. chain2 e n (ns@[n'']) n')"
    by (simp add: algebra_simps sum.distrib)
  also have "... = \<delta> n n' + (\<Sum>n'' \<in> N. e n'' n' o \<delta> n n'') + (\<Sum>(n'',ns) \<in> N \<times> l_lists' N i. chain2 e n (ns@[n'']) n')"
    by (auto simp: sum.cartesian_product)
  also have "... = \<delta> n n' + (\<Sum>ns \<in> {[]}. chain2 e n ns n') + (\<Sum>(n'',ns) \<in> N \<times> l_lists' N i. chain2 e n (ns@[n'']) n')"
    by (simp add: ** Suc)
  also have "... = \<delta> n n' + chain2 e n [] n' + (\<Sum>ns \<in> (\<lambda>(n,ns). ns @ [n]) ` (N \<times> l_lists' N i). chain2 e n ns n')"
    using **** by simp
  also have "... = \<delta> n n' + (\<Sum>ns \<in> {[]} \<union> ((\<lambda>(n,ns). ns@[n]) ` ((N \<times> l_lists' N i))). chain2 e n ns n')"
    by (simp add: algebra_simps del: chain2.simps, rule sum.insert[symmetric], auto simp: assms)
  also have "... = \<delta> n n' + (\<Sum>ns \<in> l_lists' N (Suc i). chain2 e n ns n')"
    using l_lists'_img_Suc_l[of N i] by (simp add: Un_commute)
  finally show ?case by simp
qed

lemma cap_unrolled_closed:
  assumes "\<forall>x y. e x y \<in> E" "End_closed E" "finite N" "n \<in> N"
  shows "cap N e n n' = \<delta> n n' + (\<Sum>ns \<in> l_lists' N (card N). chain2 e n ns n')"
  by (rule cap'_unrolled_closed[where E=E], auto simp: assms)

lemma cap_unrolled_closed':
  assumes "\<forall>x y. e x y \<in> E" "End_closed E" "finite N" "n \<in> N"
  shows "cap N e n n' m = \<delta> n n' m + (\<Sum>ns \<in> l_lists' N (card N). chain2 e n ns n' m)"
proof -
  have "cap N e n n' m = (\<delta> n n' + (\<Sum>ns \<in> l_lists' N (card N). chain2 e n ns n')) m"
    by (subst cap_unrolled_closed[where E=E], simp_all add: assms)
  also have "... = \<delta> n n' m + (\<Sum>ns \<in> l_lists' N (card N). chain2 e n ns n') m"
    by simp
  also have "... = \<delta> n n' m + (\<Sum>ns \<in> l_lists' N (card N). chain2 e n ns n' m)"
    apply simp by (rule plus_fun_apply_iterated[OF l_lists'_finite[OF \<open>finite N\<close>]])
  finally show ?thesis .
qed

lemma endo_cap':
  assumes "End_closed E" "\<forall>x y. e x y \<in> E" "(\<lambda>_. 0) \<in> E" "id \<in> E" "finite N"
  shows "cap' i N e n n' \<in> E"
  using assms
proof (induction i arbitrary: n n')
  case 0
  then show ?case 
    using assms
    by (cases "n = n'", auto)
next
  case (Suc i)
  have *: "\<delta> n n' \<in> E"
    using assms
    by (cases "n = n'", auto)
  have "\<forall>n''. e n'' n' \<circ> cap' i N e n n'' \<in> E"
    apply safe
    subgoal for n''
      using Suc End_closedE(2)[of E "e n'' n'" "cap' i N e n n''"] by simp
    done
  then have "(\<Sum>n''\<in>N. e n'' n' \<circ> cap' i N e n n'') \<in> E"
    using Suc End_closed_sumE[of N E "\<lambda>n''. e n'' n' \<circ> cap' i N e n n''"]
    by auto
  then show ?case
    using * Suc End_closedE
    by (simp only: cap'.simps)
qed

lemma chain2_chain':
  "chain2 f x ys z = chain f (x # ys) z"
  using chain2_chain by fast

section \<open>chains'\<close>

text \<open>Generalization of chains, should replace chains\<close>

fun chains' :: "('a list \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list list \<Rightarrow> 'a \<Rightarrow> ('b \<Rightarrow> 'b)" where
  "chains' f [] _ = id" |
  "chains' f (xs#[]) y = f xs y" |
  "chains' f (xs1#xs2#xss) y = (chains' f (xs2#xss) y) o (f xs1 (hd xs2))"

lemma endo_chains':
  assumes "End_closed E" "\<forall>x y. f x y \<in> E" "id \<in> E"
  shows "chains' f xs y \<in> E"
  using assms
proof (induction xs rule: induct_list012)
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 x y' zs)
  then have *: "chains' f (y' # zs) y \<in> E"
    by simp
  have "(chains' f (y' # zs) y) o (f x (hd y')) \<in> E"
    apply (rule End_comp_closed[OF assms(1)])
    using assms * by simp_all
  then show ?case
    by (metis chains'.simps(3))
qed

lemma chains'_mono':
  fixes f :: "'a list \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b :: pos_cancel_comm_monoid_add"
  assumes "End_closed E" "\<And>xs y. f xs y \<le> g xs y" "\<And>xs y. f xs y \<in> E" "\<And>xs y. g xs y \<in> E" "z \<le> z'"
  shows "chains' f xss y z \<le> chains' g xss y z'"
  using assms
proof (induction xss arbitrary: y z z' rule: induct_list012)
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case
    apply simp
    apply (rule pos_endo_mono''_closed[where f="\<lambda>z. f x y z" and g="\<lambda>z. g x y z" and E=E])
    by simp_all
next
  case (3 xs ys zss)
  have *: "f xs (hd ys) z \<le> g xs (hd ys) z'"
    apply (rule pos_endo_mono''_closed[where f="\<lambda>z. f xs (hd ys) z" and g="\<lambda>z. g _ _ z" and E=E])
    by (auto simp: 3)
  from 3 show ?case
    using * by simp
qed

lemma chains'_mono:
  fixes f :: "'a list \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b :: pos_cancel_comm_monoid_add"
  assumes "End_closed E" "\<And>xs y. f xs y \<le> g xs y" "\<And>xs y. f xs y \<in> E" "\<And>xs y. g xs y \<in> E"
  shows "chains' f xss y \<le> chains' g xss y"
  using assms
  by (simp add: chains'_mono' le_funI)

lemma chains'_append1:
  assumes "xss \<noteq> []"
  shows "chains' f xss y a = f (last xss) y (chains' f (butlast xss) (hd (last xss)) a)"
  using assms
  by (induction xss arbitrary: a rule: induct_list012, auto)

lemma chains'_append:
  assumes "xss = xss1 @ xss2" "\<forall>xs \<in> set xss. xs \<noteq> []"
  shows "chains' f xss y a = chains' f xss2 y (chains' f xss1 (hd (concat xss2 @ [y])) a)"
  using assms
proof (induction xss1 arbitrary: a xss rule: induct_list012)
  case 1
  then show ?case by simp
next
  case (2 xs)
  then show ?case by (cases xss2, simp, simp)
next
  case (3 xs ys zss)
  then show ?case by simp
qed

lemma "chains' (chain f) xss y z = chains f xss y z"
  by (induction xss arbitrary: z rule: induct_list012, auto)

lemma chains'_cong:
  assumes "\<And>xs y. xs \<in> set xss \<Longrightarrow> f xs y = g xs y"
  shows "chains' f xss y z = chains' g xss y z"
  using assms
  by (induction xss arbitrary: z rule: induct_list012, auto)

lemma chains'_chains:  "chains' (chain e) xss y z = chains e xss y z"
  by (induction xss arbitrary: z rule: induct_list012, auto)

lemma chains'_chain:
  assumes "concat xss = xs" "\<forall>xs \<in> set xss. xs \<noteq> []"
  shows "chains' (chain f) xss y z = chain f xs y z"
  using assms
proof (induction xss arbitrary: xs z rule: induct_list012)
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 xs' ys' zss')
  have "chain f (ys' @ concat zss') y (chain f xs' (hd ys') z) =
        chain f (ys' @ concat zss') y (chain f xs' (hd ((ys' @ concat zss') @ [y])) z)"
    using 3 by simp
  also have "... =  chain f (xs' @ ys' @ concat zss') y z"
    by (rule chain_append_nonempty[symmetric])
  finally show ?case
    using 3 by simp
qed

end
