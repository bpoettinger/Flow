\<^marker>\<open>creator Bernhard Pöttinger\<close>

chapter \<open>Auxiliary\<close>
theory Auxiliary \<comment> \<open>name Misc already taken\<close>
imports Main Pigeonhole
begin

paragraph \<open>Summary\<close>
text \<open>Some important definitions/abbreviations,
and many random auxiliary results on lists/sets/functions.\<close>

paragraph \<open>Major Definitions\<close>
text \<open>\<^item> restrict N x0 f: restrict function f to domain N, provide default value x0 outside N
\<^item> combine N1 N2 x0 f1 f2: combine f1 and f2 into a new function, provide default value outside
  their domains. If N1 and N2 overlap then f1 takes precedence.
\<^item> @{term eq_on} f1 f2 X: do f1 and f2 agree on X?

We have to introduce vacuously named definitions for sets of lists to safe space
(the set comprehensions already represent basically the minimal description of these sets,
we can only use arbitrary names to obtain shorter names):
\<^item> @{term "l_lists N k"}: originally inspired by length less than constructed from elements in N
\<^item> @{term "l_lists' N k"}: @{term l_lists} including empty list
\<^item> @{term "k_lists N k"}: lists of exactly length k from elements in N
\<^item> @{term "ck_lists N K"}: circular @{term k_lists} (@{term "head xs = last xs"})
\<^item> @{term "cl_lists N k"}: circular @{term l_lists} (@{term "head xs = last xs"})\<close>

section \<open>Important Definitions and related lemmas\<close>

abbreviation restrict where
  "restrict N x0 f \<equiv> \<lambda>n. if n \<in> N then f n else x0"

abbreviation combine where
  "combine N1 N2 x0 f1 f2 \<equiv> \<lambda>n. if n \<in> N1 then f1 n else if n \<in> N2 then f2 n else x0"

(* same as combine except that sometimes its advantageous to use definitions *)
definition combined where
  "combined N1 N2 x0 f1 f2 \<equiv> \<lambda>n. if n \<in> N1 then f1 n else if n \<in> N2 then f2 n else x0"

lemma combine_commute[simp]:
  assumes "N1 \<inter> N2 = {}"
  shows "combine N1 N2 x0 f1 f2 = combine N2 N1 x0 f2 f1"
proof
  fix n
  show "combine N1 N2 x0 f1 f2 n = combine N2 N1 x0 f2 f1 n"
    using assms by auto
qed

abbreviation eq_on ("(_ =/ _/ on _)" [50,0,50] 50) where
  "eq_on f1 f2 X \<equiv> \<forall>x \<in> X. f1 x = f2 x"

lemma on_eq_superset:
  "X \<subseteq> Y \<Longrightarrow> f1 = f2 on Y \<Longrightarrow> f1 = f2 on X"
  by auto

lemma eq_on_unionI:
  assumes "f1 = f2 on X" "f1 = f2 on Y"
  shows "f1 = f2 on (X \<union> Y)"
  using assms
  by auto

lemma eq_on_refl: "f = f on X"
  by simp

definition "l_lists  X k \<equiv> { xs. set xs \<subseteq> X \<and> length xs < k \<and> length xs \<ge> 1 }"
definition "l_lists' X k \<equiv> { xs. set xs \<subseteq> X \<and> length xs < k }"
definition "k_lists  X k \<equiv> { xs. set xs \<subseteq> X \<and> length xs = k }"
definition "ck_lists  N k \<equiv> { xs. length xs = k \<and> set xs \<subseteq> N \<and> hd xs = last xs }"
definition "cl_lists  N k \<equiv> { xs. k \<ge> 1 \<and> length xs < k \<and> set xs \<subseteq> N \<and> hd xs = last xs }"

section \<open>Auxiliary stuff\<close>

lemma ck_lists_props[simp]:
  "xs \<in> ck_lists X k \<Longrightarrow> length xs = k"
  "xs \<in> ck_lists X k \<Longrightarrow> set xs \<subseteq> X"
  "xs \<in> ck_lists X k \<Longrightarrow> k \<ge> 1 \<Longrightarrow> xs \<noteq> []"
  "xs \<in> ck_lists X k \<Longrightarrow> k \<ge> 1 \<Longrightarrow> hd xs = last xs"
  unfolding ck_lists_def by auto

lemma l_lists_dom: "xs \<in> l_lists X k \<Longrightarrow> set xs \<subseteq> X" unfolding l_lists_def by auto
lemma k_lists_dom: "xs \<in> k_lists X k \<Longrightarrow> set xs \<subseteq> X" unfolding k_lists_def by auto

lemma l_lists_k_lists_union: "k \<ge> 1 \<Longrightarrow> l_lists X k \<union> k_lists X k = l_lists X (Suc k)"
  unfolding l_lists_def k_lists_def
  by auto

lemma l_lists_k_lists_disjoint: "k \<ge> 1 \<Longrightarrow> l_lists X k \<inter> k_lists X k = {}"
  unfolding l_lists_def k_lists_def
  by auto

lemma l_lists_finite:
  assumes "finite X"
  shows "finite (l_lists X l)"
  using assms
  apply (rule rev_finite_subset[OF finite_lists_length_le[of X l]])
  unfolding l_lists_def by auto

lemma l_lists'_finite[simp]:
  assumes "finite X"
  shows "finite (l_lists' X l)"
  using assms
  apply (rule rev_finite_subset[OF finite_lists_length_le[of X l]])
  unfolding l_lists'_def by auto

lemma l_lists'_mono:
  assumes "N \<subseteq> N'" "k \<le> k'"
  shows "l_lists' N k \<subseteq> l_lists' N' k'"
  using assms
  unfolding l_lists'_def
  by auto

lemma "k \<ge> 1 \<Longrightarrow> l_lists X k \<union> {[]} = l_lists' X k"
  unfolding l_lists_def l_lists'_def
  by (auto simp: Suc_leI)

lemma k_lists_nonempty:
  assumes "k \<ge> 1" "xs \<in> k_lists X k"
  shows "length xs = k" "xs \<noteq> []"
  using assms
  unfolding k_lists_def
  by auto

lemma k_lists_nonempty':
  assumes "X \<noteq> {}"
  shows "k_lists X k \<noteq> {}"
proof -
  obtain x where "x \<in> X" using assms by blast
  then have "replicate k x \<in> k_lists X k"
    unfolding k_lists_def
    by auto
  then show "k_lists X k \<noteq> {}"
    by blast
qed

lemma l_lists_eq_l_lists':
  assumes "k \<ge> 1"
  shows "insert [] (l_lists N k) = l_lists' N k"
proof
  show "insert [] (l_lists N k) \<subseteq> l_lists' N k"
    using assms unfolding l_lists_def l_lists'_def by auto
  show "l_lists' N k \<subseteq> insert [] (l_lists N k)"
    using assms unfolding l_lists_def l_lists'_def by (auto simp: Suc_leI)
qed

lemma k_lists_finite:
  assumes "finite X"
  shows "finite (k_lists X l)"
  using assms
  unfolding k_lists_def
  by (simp add: finite_lists_length_eq)

lemma set_hd_in: "length xs \<ge> 1 \<Longrightarrow> set xs \<subseteq> X \<Longrightarrow> hd xs \<in> X"
  by (cases xs) auto

lemma l_lists'_x_Suc:
  "{ n#ns | ns n. (ns,n) \<in> l_lists' X l \<times> X } \<union> {[]} = l_lists' X (Suc l)"
  unfolding l_lists'_def
  apply auto
  subgoal for x
  apply (rule exI[where x="tl x"])
    apply (rule exI[where x="hd x"])
    apply auto
     apply (simp add: list.set_sel(2) subsetD)
    by (metis Nitpick.size_list_simp(2) One_nat_def Suc_less_SucD length_tl)
  done

lemma l_lists'_img_Suc_l:
  "{[]} \<union> (\<lambda>(x,xs). xs@[x]) ` (X \<times> l_lists' X l) = l_lists' X (Suc l)"
  unfolding l_lists_def l_lists'_def
  apply (auto simp: image_def)
  subgoal for x
  apply (rule bexI[where x="last x"])
     apply (rule exI[where x="butlast x"])
     apply auto
     apply (simp add: in_set_butlastD subsetD)
    by (metis Nitpick.size_list_simp(2) One_nat_def Suc_less_SucD length_tl)
  done

lemma l_lists_x_Suc:
  "l \<ge> 1 \<Longrightarrow> { n#ns | ns n. (ns,n) \<in> l_lists X l \<times> X } \<union> { [n'] | n'. n' \<in> X } = l_lists X (Suc l)"
  unfolding l_lists_def
  apply auto
  subgoal for xs
    apply (rule exI[where x="tl xs"])
    apply (rule exI[where x="hd xs"])
    apply auto
       apply (metis One_nat_def hd_Cons_tl list.size(3) not_one_le_zero)
      apply (metis Suc_le_lessD length_greater_0_conv list.set_sel(2) subsetD)
     apply (metis One_nat_def Suc_leI Suc_length_conv le_less length_0_conv list.sel(1) set_hd_in zero_less_diff)
    by (simp add: set_hd_in)
  done

lemma k_lists_x_Suc:
  "l \<ge> 1 \<Longrightarrow> { n#ns | ns n. (ns,n) \<in> k_lists X l \<times> X } = k_lists X (Suc l)"
  unfolding k_lists_def
  apply auto
  subgoal for xs
    apply (rule exI[where x="tl xs"])
    apply (rule exI[where x="hd xs"])
    apply (auto)
      apply (metis hd_Cons_tl list.size(3) nat.simps(3))
     apply (metis Nitpick.size_list_simp(2) list.set_sel(2) nat.simps(3) subsetD)
    by (metis Nitpick.size_list_simp(2) list.set_sel(1) nat.simps(3) subsetD)
  done

lemma notin_count: "count_list xs a = 0 \<Longrightarrow> a \<notin> set xs"
  by (induction xs, auto split: if_splits)

lemma in_count: "count_list xs a \<ge> 1 \<Longrightarrow> a \<in> set xs"
  apply (induction xs, simp)
  subgoal for aa xs
    apply (cases "aa = a")
     apply (simp add: list.set_intros)
    by fastforce
  done

lemma decompose_list_count_list:
  "count_list xs a \<ge> 1 \<Longrightarrow> \<exists>ys zs. xs = ys @ [a] @ zs \<and> a \<notin> set ys"
proof (induction xs rule: induct_list012)
  case 1
  have "count_list [] a = 0"
    by simp
  then have False
    using 1 by simp
  then show ?case
    by simp
next
  case (2 x)
  then have "a = x"
    using in_count[of "[x]" a]
    by simp
  then have "[x] = [] @ [a] @ [] \<and> a \<notin> set []"
    using 2 by simp
  then show ?case
    by blast
next
  case (3 x y zs)
  then show ?case
  proof (cases "x = a")
    case True
    show ?thesis
      apply (rule exI[where x="[]"], rule exI[where x="y # zs"])
      using \<open>x = a\<close> by simp
  next
    case False
    then have "1 \<le> count_list (y # zs) a"
      using 3 by simp
    then obtain ys zss where "y # zs = ys @ [a] @ zss \<and> a \<notin> set ys"
      using 3 by blast
    then have *: "x # y # zs = x # ys @ [a] @ zss \<and> a \<notin> set ys"
      using False by simp
    show ?thesis
      apply (rule exI[where x="x#ys"], rule exI[where x="zss"])
      using * False by simp
  qed
qed

lemma count_list_append_notin:
  "x \<notin> set xs \<Longrightarrow> count_list (xs @ ys) x = count_list ys x"
  by (induction xs, auto)

lemma decompose_list_count_list_multi:
  assumes "count_list xs a \<ge> k"
  shows "\<exists>ys yss. xs = ys @ concat yss \<and> (\<forall>ys \<in> set yss. ys \<noteq> []) \<and> (\<forall>ys \<in> set yss. hd ys = a) \<and> (\<forall> ys \<in> set yss. set ys \<subseteq> set xs) \<and> length yss = k"
  using assms
proof (induct k arbitrary: xs)
  case 0
  then have "xs = xs @ concat [] \<and> (\<forall>ys \<in> set []. ys \<noteq> []) \<and> (\<forall> ys \<in> set []. set [] \<subseteq> set xs) \<and> (hd = \<lambda>ys. a on set [])"
    using notin_count[of xs a] by simp
  then show ?case
    by auto
next
  case (Suc k)
  then obtain ys zs where *: "xs = ys @ [a] @ zs" "a \<notin> set ys"
    using decompose_list_count_list[of xs a] by auto
  then have "count_list zs a \<ge> k"
    using count_list_append_notin[of a ys "[a] @ zs"] Suc by simp
  then obtain us uss where **: "zs = us @ concat uss" "\<forall>us \<in> set uss. hd us = a" "length uss = k" "\<forall>ys \<in> set uss. ys \<noteq> []"
    using Suc by blast
  then have X: "xs = ys @ concat ((a # us) # uss)"
    using * by auto
  show ?case
    apply (rule exI[where x="ys"])
    apply (rule exI[where x="(a # us) # uss"])
    using X ** by auto
qed

lemma merge_k_list_1:
  assumes "k \<ge> 1"
  shows "k_lists N 1 \<union> (\<lambda>(n,ns). ns@[n]) ` (N \<times> l_lists N k) = l_lists N (Suc k)"
proof
  show "k_lists N 1 \<union> (\<lambda>(n, ns). ns @ [n]) ` (N \<times> l_lists N k) \<subseteq> l_lists N (Suc k)"
    unfolding k_lists_def l_lists_def
    using assms by auto
  show "l_lists N (Suc k) \<subseteq> k_lists N 1 \<union> (\<lambda>(n, ns). ns @ [n]) ` (N \<times> l_lists N k)"
  proof
    fix x
    assume A: "x \<in> l_lists N (Suc k)"
    then show "x \<in> k_lists N 1 \<union> (\<lambda>(n, ns). ns @ [n]) ` (N \<times> l_lists N k)"
      using assms
      unfolding k_lists_def l_lists_def
      apply (cases "length x = 1")
       apply (auto)
      apply (rule image_eqI[where x="(last x, butlast x)"])
       apply auto
      using append_butlast_last_id[symmetric, of x] apply fastforce
      using last_in_set[of x] A unfolding l_lists_def  apply (metis One_nat_def list.size(3) not_one_le_zero subsetD)
      using in_set_butlastD[of _ x] A unfolding l_lists_def by (auto simp: subsetD)
  qed
qed

lemma list_decompose_last: "xs \<noteq> [] \<Longrightarrow> \<exists>y ys. xs = ys @ [y]"
proof (induction xs rule: list_nonempty_induct)
  case (single x)
  then show ?case by simp
next
  case (cons x xs)
  then show ?case by auto
qed

lemma set_to_list:
  assumes "finite X"
  shows "\<exists>xs. length xs = card X \<and> set xs = X"
  using assms
proof (induction X rule: finite_induct)
  case empty
  then have "length [] = card {} \<and> set [] = {}"
    by simp
  then show ?case 
    by simp
next
  case (insert x F)
  then obtain xs' where "length xs' = card F \<and> set xs' = F"
    by blast
  then have "length (x#xs') = card (insert x F) \<and> set (x#xs') = insert x F"
    using insert by auto
  then show ?case
    by blast
qed

lemma tl_l_lists':
  assumes "ms \<in> l_lists' N l"
  shows "tl ms \<in> l_lists' N l"
  using assms
  unfolding l_lists'_def
  apply auto
  by (metis list.sel(2) list.set_sel(2) subsetD)

lemma sum_reindex_cong_mono:
  fixes f :: "'a \<Rightarrow> 'b :: ordered_comm_monoid_add"
    and g :: "'c \<Rightarrow> 'b"
    and l :: "'c \<Rightarrow> 'a"
  assumes "A \<subseteq> l ` B" "inj l" "\<forall>x \<in> B. f (l x) \<le> g x" "finite B" "\<forall>x \<in> B. g x \<ge> 0"
  shows "(\<Sum>x \<in> A. f x) \<le> (\<Sum>x \<in> B. g x)"
proof -
  have "finite A" using assms finite_surj by blast

  have "(\<Sum>x \<in> A. f x) \<le> (\<Sum>x \<in> l -` A. g x)"
    using \<open>finite A\<close> \<open>A \<subseteq> l ` B\<close> proof (induction A rule: finite_induct)
    case empty
    then show ?case by simp
  next
    case (insert x F)

    have F2: "finite (l -` {x})" using assms by (intro finite_vimageI, simp_all)
    have F3: "finite (l -` F)" using insert assms by (intro finite_vimageI, simp_all)
    have F4: "\<And>x. l -` {l x} = {x}"
      by (smt assms inj_vimage_singleton insert_absorb singletonI singleton_insert_inj_eq' subset_singleton_iff vimageI)

    have G: "\<And>x. x \<in> B \<Longrightarrow> f (l x) \<le> g x"
      using assms by simp

    from insert have "(l -` {x}) \<inter> (l -` F) = {}" by auto
    moreover have "(l -` insert x F) = (l -` {x}) \<union> (l -` F)" using insert by auto
    ultimately show ?case 
      using insert
      apply simp
      apply (subst sum.union_disjoint)
      using insert assms F2 F3 F4 apply auto
      apply (rule order_trans[OF add_left_mono[OF insert.IH]])
      using insert apply simp
      apply (rule order_trans[OF add_right_mono[OF G]], simp)
      by simp
  qed

  also have "... \<le> (\<Sum>x \<in> l -` A. g x) + (\<Sum>x \<in> B - (l -` A). g x)"
    using assms sum_nonneg[of "B - (l -` A)" g] add_increasing2 by blast

  also have "... = (\<Sum>x \<in> B. g x)"
    using sum.union_disjoint[of "l -` A" "B - (l -` A)", symmetric] insert assms
    by (metis add.commute sum.subset_diff vimage_subsetI) 

  finally show ?thesis .
qed

lemma split_list_concat:
  assumes "xs \<in> set xss"
  shows "\<exists>xss1 xss2. concat xss = concat xss1 @ xs @ concat xss2"
proof -
  obtain xss1 xss2 where *: "xss = xss1 @ xs # xss2"
    using split_list[of xs xss] assms by blast
  show ?thesis
    apply (rule exI[where x=xss1])
    apply (rule exI[where x="xss2"])
    using * by simp
qed

lemma split_list_list:
  assumes "\<exists>xs \<in> set xss. x \<in> set xs"
  shows "\<exists>xss1 xs1 xs2 xss2. concat xss = concat xss1 @ xs1 @ x # xs2 @ concat xss2 \<and> xss = xss1 @ (xs1 @ x # xs2) # xss2"
proof -
  obtain xs where A: "x \<in> set xs" "xs \<in> set xss"
    using assms by blast
  obtain xss1 xss2 where B: "xss = xss1 @ xs # xss2"
    using split_list A by metis
  obtain xs1 xs2 where C: "xs = xs1 @ x # xs2"
    using split_list A by metis

  show ?thesis
    using A B C by auto
qed

lemma butlast_subset[simp]:
  "set (butlast xs) \<subseteq> set xs"
  by (induction xs, auto)

lemma distinct_length_le:
  assumes "set xs \<subseteq> X" "distinct xs" "finite X"
  shows "length xs \<le> card X"
proof (rule ccontr)
  assume "\<not> length xs \<le> card X"
  then have "length xs > card X" by simp
  then obtain xs1 xs2 xs3 x where "xs = xs1 @ x # xs2 @ x # xs3"
    using pigeonhole_split_list[of X xs] assms by auto
  then show False using assms by simp
qed

lemma distinct_from_concat:
  "distinct (concat xss) \<Longrightarrow> \<forall>xs \<in> set xss. xs \<noteq> [] \<Longrightarrow> \<forall>xs \<in> set xss. distinct xs"
  by (induction xss, simp_all)

lemma length_length_concat:
  assumes "\<forall>xs\<in>set xss. xs \<noteq> []"
  shows "length xss \<le> length (concat xss)"
  using assms
  apply (induction xss, simp)
  by (simp, metis Suc_leI le_neq_implies_less length_greater_0_conv less_add_same_cancel2 less_imp_le_nat less_trans_Suc)

lemma length_length_concat_in:
  assumes "xss \<noteq> []" "xs \<in> set xss"
  shows "length xs \<le> length (concat xss)"
  using assms
proof (induction xss rule: list_nonempty_induct)
  case (single x)
  then show ?case by auto
next
  case (cons xs' xss')
  then show ?case
    by (cases "xs' = xs", auto)
qed

lemma length_concat_le_length: "length (concat xss) < l \<Longrightarrow> \<forall>xs \<in> set xss. xs \<noteq> [] \<Longrightarrow> length xss < l"
  apply (induction xss arbitrary: l, simp, simp)
  by (meson length_greater_0_conv less_add_same_cancel2 less_trans_Suc)

lemma length_concat_le: "length (concat xss) < n \<Longrightarrow> \<forall>xs \<in> set xss. length xs < n"
  by (induction xss, auto)

lemma distinct_map_hd:
  "distinct (concat xss) \<Longrightarrow> \<forall>xs \<in> set xss. xs \<noteq> [] \<Longrightarrow> distinct (map hd xss)"
  apply (induction xss, simp_all) by (smt UN_I disjoint_iff_not_equal hd_in_set imageE)


lemma concat_cons_length_hd_hd: "xss \<noteq> [] \<Longrightarrow> \<forall>xs \<in> set xss. xs \<noteq> [] \<Longrightarrow> (concat (xs # xss)) ! (length xs) = hd (hd xss)"
  apply (induction xs, simp)
   apply (metis append_is_Nil_conv concat.simps(2) hd_Cons_tl hd_append2 hd_conv_nth hd_in_set)
  by simp

lemma hd_append_Cons_hd[simp]: "hd (xs @ [hd ys]) = hd (xs @ ys)"
  apply (induction xs)
  by auto

lemma length_ge_2:
  assumes "N1 \<inter> N2 = {}" "n1 \<in> N1" "n2 \<in> N2" "n1 \<in> set ns" "n2 \<in> set ns"
  shows "length ns \<ge> 2"
proof (rule ccontr)
  assume "\<not> 2 \<le> length ns"
  then have "length ns = 0 \<or> length ns = 1" by linarith
  then consider (a) "length ns = 0" | (b) "length ns = 1" by blast
  then show False
  proof cases
    case a
    then show ?thesis using assms by simp
  next
    case b
    then obtain n where "ns = [n]" by (metis One_nat_def Suc_length_conv length_0_conv)
    then show False using assms by auto
  qed
qed

lemma hd_hd_concat_hd:
  assumes "ns = concat nss" "\<forall>ns \<in> set nss. ns \<noteq> []" "nss \<noteq> []"
  shows "hd (hd nss) = hd ns"
  using assms
  by (metis concat.simps(2) hd_Cons_tl hd_append2 list.set_sel(1))

lemma set_concat_subset:
  assumes "set ns \<subseteq> N" "set ns' \<subseteq> set ns"
  shows "set (ns @ ns') \<subseteq> N"
  using assms by simp

lemma finiteUn: "finite Z \<Longrightarrow> Z = X \<union> Y \<Longrightarrow> finite X \<and> finite Y"
  by simp
fun indexed_list where
"indexed_list xs i = (if i < length xs then Some (xs!i) else None)"

lemma count_list_sum:
  "count_list xs m = (\<Sum>x \<leftarrow> xs. if x = m then 1 else 0)"
  by (induction xs, auto)

lemma "(\<Sum>x \<leftarrow> xs. if x = m then 1 else 0) = (\<Sum>x \<in> set xs. count_list xs x * (if x = m then 1 else 0))"
  using sum_list_map_eq_sum_count by auto

lemma sum_list_map: "(\<Sum>x \<leftarrow> xs. f (g x)) = (\<Sum>x \<leftarrow> map g xs. f x)"
  by (induction xs, auto)

lemma card_count_list:
  fixes X :: "nat set"
  assumes "\<forall>x \<in> X. xs!x = m" "card X \<le> length xs" "finite X" "\<forall>x \<in> X. x < length xs"
  shows "card X \<le> count_list xs m"
proof -
  let ?X = "{x . x \<in> {0..<length xs} \<and> xs!x = m}"
  let ?X' = "{0..<length xs}"

  have S: "X \<subseteq> ?X" using assms by auto
  have SS: "?X \<subseteq> ?X'" by auto

  have "card X = (\<Sum>x \<in> X. 1)" by simp
  also have "... \<le> (\<Sum>x \<in> ?X. 1)" using sum_mono2[OF _ S] by fastforce
  also have "... = (\<Sum>x \<in> ?X. if xs!x = m then 1 else 0)" using assms by simp
  also have "... \<le> (\<Sum>x \<in> ?X'. if xs!x = m then 1 else 0)" using sum_mono2[OF _ SS] by fastforce
  also have "... = (\<Sum>x \<in> set [0..<length xs]. if xs!x = m then 1 else 0)" by simp
  also have "... = (\<Sum>x \<leftarrow> map id [0..<length xs]. if xs!x = m then 1 else 0)"
    using sum_list_distinct_conv_sum_set[of "[0..<length xs]", symmetric] by auto
  also have "... = (\<Sum>x \<leftarrow> map ((!) xs) [0..<length xs]. if x = m then 1 else 0)"
    using sum_list_map by auto
  also have "... = (\<Sum>x \<leftarrow> xs. if x = m then 1 else 0)"
    by (simp add: map_nth)
  also have "... = count_list xs m"
    by (induction xs, auto)
  finally show ?thesis .
qed

lemma finite_index_fun_vimage: 
  "finite ((\<lambda>n. if n < length ns then Some (ns ! n) else None) -` {Some m})"
proof -
  let ?f = "\<lambda>n. if n < length ns then Some (ns ! n) else None"

  have "?f -` {Some m} \<subseteq> {0..<length ns}"
    unfolding vimage_def by auto
  moreover have "finite ({0..<length ns})" by simp
  ultimately show ?thesis
    using finite_subset by blast
qed

lemma fold_cons:
  "fold (o) (fs :: ('a \<Rightarrow> 'a) list) (g :: 'a \<Rightarrow> 'a) o h = fold (o) fs (g o h)"
proof (induction fs arbitrary: g)
  case Nil
  then show ?case by simp
next
  case (Cons a fs)
  then show ?case by simp
qed


end
