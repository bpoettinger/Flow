\<^marker>\<open>creator Bernhard Pöttinger\<close>

chapter \<open>Transfer Capacity\<close>
theory Effectively_Acyclic_Equal_Capacity
imports Effectively_Acyclic_Switch_Worlds
begin

paragraph \<open>Summary\<close>
text \<open>A quite technical theory that relates capacities with sums over alternating chains.
This result then is used in thm @{term cap_fg_eq_cap_fg} to transfer chains from @{term "h = h1 + h2"} to
@{term "h' = h1' + h2'"} using subflow-preserving extensions @{term "h1 \<lesssim>\<^sub>S h1'"} and
@{term "h2 \<lesssim>\<^sub>S h2'"}.\<close>

text \<open>
  Main lemma: @{term cap_fg_eq_cap_fg}
    equate capacities in two flow graphs related by subflow-preserving extensions.
  Everything else in this theory is required to prove this lemma.
\<close>

section \<open>Auxiliary Development\<close>

text \<open>This section shows many results that are required in the next section.
These results primarily show the equalities between and decompositions of sets
which are used in sum transformations.\<close>

definition "dl_lists' N l \<equiv> {xs | xs. set xs \<subseteq> N \<and> length xs < l \<and> distinct xs }"
definition "ddl_lists' x0 N l \<equiv>
  {xs | xs. hd xs = x0 \<and> xs \<noteq> [] \<and> set xs \<subseteq> N \<and> length xs < l \<and> distinct xs }"

lemma cap'_eq_dl_lists_chain:
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "End_closed E" "\<forall>x y. edge_fg h x y \<in> E" "x \<in> dom_fg h" "x' \<notin> dom_fg h"
   "eff_acyclic' h" "h \<noteq> bot" "id \<in> E" "(\<lambda>_. 0) \<in> E" "z \<le> inf_fg h x" 
  shows "cap' k (dom_fg h) (edge_fg h) x x' z =
    (\<Sum>ns \<in> dl_lists' (dom_fg h - {x}) k. chain (edge_fg h) (x # ns) x' z)"
proof -
  let ?e = "edge_fg h" let ?N = "dom_fg h"

  have *:
    "(\<Sum>ns\<in>{xs. xs \<in> l_lists' ?N k \<and> \<not>(x \<notin> set xs \<and> distinct xs)}. chain ?e (x # ns) x' z) = 0"
    apply (rule sum.neutral, safe)
    subgoal premises prems for xs
    proof -
      have D: "\<not> distinct (x # xs)" using prems by simp
      have "chain (edge_fg h) (x # xs) x' z = 0"
        apply (rule chain_eff_acylic_zero_not_distinct [of h "x # xs" E z])
        using prems D assms unfolding l_lists'_def by simp_all
      then show False using prems by simp
    qed
    subgoal premises prems for xs
    proof (rule ccontr)
      assume D: "\<not> distinct xs"
      have "chain (edge_fg h) (x # xs) x' z = 0"
        apply (rule chain_eff_acylic_zero_not_distinct [of h "x # xs" E z])
        using prems D assms unfolding l_lists'_def by simp_all
      then show False using prems by simp
    qed
    done

  have **: "{xs. xs \<in> l_lists' ?N k \<and> distinct xs} = dl_lists' ?N k"
    unfolding l_lists'_def dl_lists'_def by auto

  let ?X1 = "{xs. xs \<in> l_lists' ?N k \<and> x \<notin> set xs \<and> distinct xs}"
  let ?X2 = "{xs. xs \<in> l_lists' ?N k \<and> \<not>(x \<notin> set xs \<and> distinct xs)}"

  have "cap' k ?N ?e x x' z = (\<Sum>ns\<in>l_lists' ?N k. chain2 ?e x ns x') z"
    using cap'_unrolled_closed[of ?e E] assms unfolding \<delta>_def by auto
  also have "... = (\<Sum>ns\<in>l_lists' ?N k. chain2 ?e x ns x' z)"
    by (subst plus_fun_apply_iterated[OF l_lists'_finite[OF dom_fg_finite]], simp)
  also have "... = (\<Sum>ns\<in>l_lists' ?N k. chain ?e (x # ns) x' z)"
    by (subst chain2_chain, simp)
  also have "... = (\<Sum>ns\<in>?X1 \<union> ?X2. chain ?e (x # ns) x' z)"
    by (rule sum.cong, auto)
  also have "... = (\<Sum>ns\<in>?X1. chain ?e (x # ns) x' z) + (\<Sum>ns\<in>?X2. chain ?e (x # ns) x' z)"
    apply (rule sum.union_disjoint) using l_lists'_finite[of ?N k] assms by auto
  also have "... = (\<Sum>ns\<in>?X1. chain ?e (x # ns) x' z)"
    using * ** by simp
  also have "... = (\<Sum>ns\<in> dl_lists' (?N - {x}) k. chain ?e (x # ns) x' z)"
    unfolding dl_lists'_def l_lists'_def
    apply (rule sum.cong) apply blast using * ** by simp
  finally show ?thesis .
qed

text \<open>an essential property for disjoint decompositions is the alternating ownership of disjoint sets\<close>


(* TODO: can distinct be removed again? *)
definition "ll_lists' x0 N1 N2 k \<equiv>
  {xss | xss. hd (hd xss) = x0 \<and> xss \<noteq> [] \<and> distinct (concat xss) \<and> set (concat xss) \<subseteq> N1 \<union> N2 \<and>
              length (concat xss) < k \<and> alternating (segment N1) (segment N2) xss}"
definition "kl_lists' x0 N1 N2 k l \<equiv>
  {xss | xss. hd (hd xss) = x0 \<and> xss \<noteq> [] \<and> distinct (concat xss) \<and> set (concat xss) \<subseteq> N1 \<union> N2 \<and>
              length (concat xss) < k  \<and> alternating (segment N1) (segment N2) xss \<and>
              length xss = l \<and> (\<forall>xs \<in> set xss. xs \<noteq> [])}"
definition "xx_lists' N1 N2 k xs \<equiv>
  {xss | xss. distinct (concat xss) \<and> set (concat xss) \<subseteq> N1 \<union> N2 \<and> length (concat xss) < k  \<and>
              alternating (segment N1) (segment N2) xss \<and> map hd xss = xs \<and>
              (\<forall>xs \<in> set xss. xs \<noteq> [])}"
definition "yy_lists' N1 N2 k1 k2 xs \<equiv>
  {xss | xss. distinct (concat xss) \<and> set (concat xss) \<subseteq> N1 \<union> N2 \<and>
              alternating (\<lambda>xs. segment N1 xs \<and> length xs < k1) (\<lambda>xs. segment N2 xs \<and> length xs < k2) xss \<and>
              map hd xss = xs}"
definition "a_lists x0 N1 N2 k \<equiv>
  {xs | xs. hd xs = x0 \<and> xs \<noteq> [] \<and> alternating (\<lambda>x. x \<in> N1) (\<lambda>x. x \<in> N2) xs \<and>
            length xs = k \<and> distinct xs}"

definition "PL \<equiv> \<lambda>x ns zss. distinct (concat ((x # ns) # zss))"

lemma yy_lists'_cons:
  "ys \<in> yy_lists' N1 N2 k1 k2 (x # xs) \<Longrightarrow> hd (hd ys) = x"
  unfolding yy_lists'_def by auto

lemma yy_lists'_finite:
  assumes "finite N1" "finite N2"
  shows "finite (yy_lists' N1 N2 k1 k2 xs)"
proof -
  let ?L = "{xs . xs \<noteq> [] \<and> set xs \<subseteq> N1 \<union> N2 \<and> distinct xs}"
  let ?LL = "{xs . set xs \<subseteq> N1 \<union> N2 \<and> length xs \<le> card (N1 \<union> N2)}"
  let ?X = "{xss . set (concat xss) \<subseteq> N1 \<union> N2 \<and> (\<forall>xs \<in> set xss. xs \<noteq> []) \<and> distinct (concat xss)}"
  let ?Y = "{xss . set xss \<subseteq> ?L \<and> length xss \<le> card (N1 \<union> N2)}"

  have L_LL: "?L \<subseteq> ?LL"
    using distinct_length_le assms by auto
  have F: "finite ?LL"
    using finite_lists_length_le[OF finite_UnI[OF assms(1) assms(2)]]
    by simp
  have F: "finite ?L"
    by (fact rev_finite_subset[OF F L_LL])

  have S: "yy_lists' N1 N2 k1 k2 xs \<subseteq> ?X"
    unfolding yy_lists'_def using alternating_props by auto

  have T: "?X \<subseteq> ?Y"
    apply safe
       apply auto[1]
      apply auto[1]
    using distinct_from_concat apply blast
    subgoal for xss
      using distinct_length_le[of "concat xss" "N1 \<union> N2"] assms length_length_concat[of xss] by simp
    done

  have F: "finite ?Y"
    using finite_lists_length_le[OF F] by blast

  show ?thesis
    by (fact rev_finite_subset[OF rev_finite_subset[OF F T] S])
qed

lemma chain_cap_yy_lists'_sum:
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "alternating (\<lambda>x. x \<in> dom_fg h1) (\<lambda>x. x \<in> dom_fg h2) xs" "eff_acyclic' h"
    "xs \<noteq> []" "distinct xs" "set xs \<subseteq> dom_fg h" "y \<notin> dom_fg h" "h = h1 + h2" "h \<noteq> bot"
    "End_closed E" "\<forall>x y. edge_fg h x y \<in> E" "id \<in> E" "(\<lambda>_. 0) \<in> E"
    "\<forall>x y. edge_fg h1 x y \<in> E" "\<forall>x y. edge_fg h2 x y \<in> E" "eff_acyclic' h1" "eff_acyclic' h2"
    "z \<le> inf_fg h1 (hd xs)"
  shows "(\<Sum>zss \<in> yy_lists' (dom_fg h1) (dom_fg h2) (card (dom_fg h1) + 1) (card (dom_fg h2) + 1) xs.
            chains (edge_fg h) zss y z) =
         chain (alt_cap_hd_fg h1 h2) xs y z"
  using assms
proof (induction xs arbitrary: z rule: alternating_induct'_symmetric[where a=h1 and b=h2])
  case (empty h1 h2)
  then show ?case by simp
next
  case (base h1 h2 x)
  then have *: "x \<in> dom_fg h1" "x \<notin> dom_fg h2" "dom_fg h = dom_fg h1 \<union> dom_fg h2"
    using plus_fg_dom_un plus_fg_dom_disj by blast+
  let ?e1 = "edge_fg h1" let ?N1 = "dom_fg h1" let ?k1 = "card ?N1" let ?N2 = "dom_fg h2"
  let ?k2 = "card ?N2" let ?N2 = "dom_fg h2"

  have EQ: "Cons x ` dl_lists' (?N1 - {x}) ?k1 = concat ` yy_lists' ?N1 ?N2 (?k1 + 1) (?k2 + 1) [x]"
  proof 
    show "(#) x ` dl_lists' (?N1 - {x}) (card ?N1) \<subseteq> concat ` yy_lists' ?N1 ?N2 (?k1 + 1) (?k2 + 1) [x]"
      unfolding dl_lists'_def yy_lists'_def
    proof (safe, goal_cases)
      case (1 x' xa xs)
      let ?xss = "[x # xs]"
      show ?case 
        unfolding yy_lists'_def image_def
        apply (simp, rule exI[where x="?xss"]) using * 1 by auto
    qed
    show "concat ` yy_lists' ?N1 ?N2 (?k1 + 1) (?k2 + 1) [x] \<subseteq> (#) x ` dl_lists' (?N1 - {x}) (card ?N1)"
      unfolding yy_lists'_def dl_lists'_def image_def
      apply safe
      subgoal for xa xaa xss z zs
        apply (rule bexI[where x="tl z"], simp, simp, intro conjI)
          apply (metis Diff_empty Diff_eq_empty_iff base.hyps(2) distinct.simps(2) hd_Cons_tl
                 insert_Diff1 list.simps(15) subset_Diff_insert)
         apply (metis diff_Suc_less length_greater_0_conv less_SucE less_imp_diff_less)
        using distinct_tl by blast
      done
  qed

  have inf: "z \<le> inf_fg h1 x" using inf_fg_le_inf_fg[of h1 h2 x E] base by simp

  have "cap' ?k1 ?N1 ?e1 x y z = (\<Sum>ns \<in> dl_lists' (?N1 - {x}) ?k1. chain ?e1 (x # ns) y z)"
    using cap'_eq_dl_lists_chain[of E h1 x y z "card ?N1"] plus_fg_ops_exist(1)[of h1 h2] base inf
    unfolding eff_acyclic'_def by simp
  also have "... = (\<Sum>ns \<in> Cons x ` dl_lists' (?N1 - {x}) ?k1. chain ?e1 ns y z)"
    apply (rule sum.reindex_cong[symmetric, where l="Cons x"])
    by (intro inj_onI, simp_all add: dl_lists'_def)
  also have "... = (\<Sum>ns \<in> concat ` yy_lists' ?N1 ?N2 (?k1 + 1) (?k2 + 1) [x]. chain ?e1 ns y z)"
    using EQ by simp
  also have "... = (\<Sum>nss \<in> yy_lists' ?N1 ?N2 (?k1 + 1) (?k2 + 1) [x]. chain ?e1 (concat nss) y z)"
    apply (rule sum.reindex_cong[where l=concat])
    by (intro inj_onI, auto simp: yy_lists'_def)
  also have "... = (\<Sum>nss \<in> yy_lists' ?N1 ?N2 (?k1 + 1) (?k2 + 1) [x]. chains ?e1 nss y z)"
    apply (rule sum.cong, simp) using chain_concat_chains unfolding yy_lists'_def by auto
  also have "... = (\<Sum>nss \<in> yy_lists' ?N1 ?N2 (?k1 + 1) (?k2 + 1) [x]. chains (edge_fg h) nss y z)"
    apply (rule sum.cong, simp)
    subgoal for xss
      using chains_cong[OF edge_fg_plus_fg_on1[of h1 h2], of xss y z] base
      unfolding yy_lists'_def by auto
    done
  finally show ?case
    using * by simp
next
  case (step h1 h2 x y' zs)
  then have *: "x \<in> dom_fg h1" "x \<notin> dom_fg h2" "dom_fg h = dom_fg h1 \<union> dom_fg h2"
    "dom_fg h1 \<inter> dom_fg h2 = {}"
    using plus_fg_dom_un plus_fg_dom_disj by blast+
  let ?e1 = "edge_fg h1" let ?N1 = "dom_fg h1" let ?k1 = "card ?N1"
  let ?N2 = "dom_fg h2" let ?k2 = "card ?N2" let ?N2 = "dom_fg h2"

  let ?L = "\<lambda>zss. l_lists' (dom_fg h1) (card (dom_fg h1))"
  let ?L1 = "\<lambda>zss. {ns . ns \<in> l_lists' (dom_fg h1) (card (dom_fg h1)) \<and> PL x ns zss}"
  let ?L2 = "\<lambda>zss. {ns . ns \<in> l_lists' (dom_fg h1) (card (dom_fg h1)) \<and> \<not> PL x ns zss}"

  have S: "\<And>zss. ?L zss = ?L1 zss \<union> ?L2 zss"
    by auto

  have inf: "z \<le> flow_fg (h1 + h2) x"
    using inf_fg_le_flow_fg[of h1 x] flow_fg_plus_fg_on1[of h1 h2]
      plus_fg_ops_exist(1)[of h1 h2] step
    by simp

  have ZERO: "(\<Sum>zss\<in>yy_lists' ?N2 ?N1 (card ?N2 + 1) (card ?N1 + 1) (y' # zs).
      chains (edge_fg h) zss y (\<Sum>ns\<in>?L2 zss. chain (edge_fg h1) (x # ns) y' z)) = 0"
    apply (rule sum.neutral, safe)
    apply (subst fun_dist_right''[where g="chains _ _ _" and E=E])
    using step apply simp_all
     apply (rule endo_chains_closed)
    using step apply blast+
    apply clarsimp
    apply (subst chain_cong'[OF edge_fg_plus_fg_on1[of h1 h2], symmetric])
      apply blast
    unfolding l_lists'_def apply simp
    subgoal premises prems for xss xs
    proof -
      have "chains (edge_fg (h1 + h2)) xss y (chain (edge_fg (h1 + h2)) (x # xs) y' z) =
            chains (edge_fg (h1 + h2)) ((x # xs) # xss) y z"
        using prems(1) unfolding yy_lists'_def
        by (cases xss, auto)
      moreover have "chains (edge_fg (h1 + h2)) ((x # xs) # xss) y z = 0"
        apply (rule chains_eff_acylic_zero_not_distinct)
        using prems inf unfolding PL_def apply blast
        using prems apply blast
        using inf unfolding PL_def apply simp
        subgoal
          using prems apply simp
        using alternating_props prems(1) inf unfolding PL_def yy_lists'_def by blast
        using prems subgoal
          apply simp
        using alternating_props prems(1) inf unfolding PL_def yy_lists'_def by blast
        using prems inf unfolding PL_def id_def by blast+
      ultimately show ?thesis
        by simp
    qed
    done

  let ?X = "yy_lists' ?N2 ?N1 (card ?N2 + 1) (card ?N1 + 1) (y' # zs)"
  let ?X' = "yy_lists' ?N1 ?N2 (card ?N1 + 1) (card ?N2 + 1) (x # y' # zs)"

  have XL1: "?X' = (\<lambda>(zss,ns). (x # ns) # zss) ` Sigma ?X ?L1"
  proof (safe, goal_cases)
    case (1 xs)
    then show ?case
      unfolding yy_lists'_def image_def PL_def
      apply auto
      subgoal for z zs zss
        apply (rule exI[where x="zs # zss"])
        apply auto
        apply (rule exI[where x="tl z"])
        apply auto
        unfolding l_lists'_def 
        subgoal premises prems 
        proof -
          have "set z \<subseteq> ?N1" using prems by blast
          then have "set (tl z) \<subseteq> ?N1" by (simp add: list.set_sel(2) prems subset_code(1))
          moreover have "length (tl z) < card ?N1"
            using distinct_length_le[OF \<open>set z \<subseteq> ?N1\<close> \<open>distinct z\<close> dom_fg_finite] \<open>z \<noteq> []\<close>
            by (simp add: Suc_le_lessD)
          ultimately show ?thesis by simp
        qed
             apply (metis distinct.simps(2) hd_Cons_tl)
        using "*"(2) apply auto[1]
        apply (meson UN_I UnCI disjoint_iff_not_equal list.set_sel(1))
          apply (simp add: distinct_tl)
         apply (meson "*"(4) disjoint_iff_not_equal in_mono list.set_sel(2))
        by (meson UN_I UnCI disjoint_iff_not_equal list.set_sel(2))
      done
  next
    case (2 z a b)
    then show ?case
      unfolding yy_lists'_def l_lists'_def PL_def
      apply safe
      apply (rule_tac x="(x # b) # z # zsa" in exI)
      using * by auto
  qed

  have "cap_fg h1 (hd [x]) y' z \<le> cap_fg h1 (hd [x]) y' (inf_fg h1 (hd [x]))"
    apply (rule pos_endo_mono'_closed[where f="cap_fg h1 (hd [x]) y'" and E=E])
    using inf_fg_le_inf_fg[of h1 h2 x E] step apply simp
    by (rule endo_cap', auto simp: step)
  also have "... \<le> inf_fg h2 y'"
    using cap'_fg_inf_fg_fg_le_inf_fg[of h h1 h2 "[x]" E y'] step by simp
  finally have inf: "cap_fg h1 (hd [x]) y' z \<le> inf_fg h2 y'" .

  have "chain (alt_cap_hd_fg h1 h2) (x # y' # zs) y z =
        chain (alt_cap_hd_fg h1 h2) (y' # zs) y (cap_fg h1 x y' z)"
    using step by simp
  also have "... = (\<Sum>zss\<in>yy_lists' ?N2 ?N1 (card ?N2 + 1) (card ?N1 + 1) (y' # zs).
          chains (edge_fg h) zss y (cap_fg h1 x y' z))"
    apply (subst alt_cap_hd_fg_sym', simp add: *)
    apply (subst step.IH[symmetric])
    using step inf unfolding id_def
                    apply blast+
    using step inf apply simp
    using step inf apply simp
    using step inf ac_simps unfolding id_def apply blast+
    using step inf by (simp_all add: algebra_simps)
  also have "... = (\<Sum>zss\<in>yy_lists' ?N2 ?N1 (card ?N2 + 1) (card ?N1 + 1) (y' # zs).
          chains (edge_fg h) zss y (\<Sum>ns\<in>?L zss. chain (edge_fg h1) (x # ns) y' z))"
    apply (subst cap'_unrolled_closed'[OF dom_fg_finite _ \<open>End_closed E\<close>])
    using step apply simp
    using step apply simp
    using step unfolding id_def apply simp
    using step apply simp
    using step unfolding \<delta>_def apply simp
    by (subst plus_fun_apply_iterated[OF l_lists'_finite[OF dom_fg_finite]], simp)
  also have "... = (\<Sum>zss\<in>yy_lists' ?N2 ?N1 (card ?N2 + 1) (card ?N1 + 1) (y' # zs).
          chains (edge_fg h) zss y (\<Sum>ns\<in>?L1 zss \<union> ?L2 zss. chain (edge_fg h1) (x # ns) y' z))"
    apply (rule sum.cong, simp)
    subgoal for zss by (subst S[of zss], simp)
    done
  also have "... = (\<Sum>zss\<in>?X. chains (edge_fg h) zss y ((\<Sum>ns\<in>?L1 zss. chain (edge_fg h1) (x # ns) y' z) +
                                                        (\<Sum>ns\<in>?L2 zss. chain (edge_fg h1) (x # ns) y' z)))"
    by (subst sum.union_disjoint, auto)
  also have "... = (\<Sum>zss\<in>?X. chains (edge_fg h) zss y (\<Sum>ns\<in>?L1 zss. chain (edge_fg h1) (x # ns) y' z)) +
                   (\<Sum>zss\<in>?X. chains (edge_fg h) zss y (\<Sum>ns\<in>?L2 zss. chain (edge_fg h1) (x # ns) y' z)) "
    apply (subst endo_sum_closed[where f="chains _ _ _"])
      apply (rule endo_chains_closed)
    using step apply blast+
    by (rule sum.distrib)
  also have "... = (\<Sum>zss\<in>?X. chains (edge_fg h) zss y (\<Sum>ns\<in>?L1 zss. chain (edge_fg h1) (x # ns) y' z))"
    using ZERO by simp
  also have "... = (\<Sum>zss\<in>?X. \<Sum>ns\<in>?L1 zss. chains (edge_fg h) zss y (chain (edge_fg h1) (x # ns) y' z))"
    apply (rule sum.cong[OF _ fun_dist_right''[where E=E]], simp_all add: step)
    apply (rule endo_chains_closed)
    using step unfolding id_def by blast+
  also have "... = (\<Sum>zss\<in>?X. \<Sum>ns\<in>?L1 zss. chains (edge_fg h) ((x # ns) # zss) y z)"
    apply (rule sum.cong[OF _ sum.cong], simp, simp)
    apply (case_tac zss, simp)
    unfolding yy_lists'_def apply simp
    using step apply simp
    by (subst chain_cong'[OF edge_fg_plus_fg_on1[of h1 h2], symmetric], simp_all add: l_lists'_def)
  also have "... = (\<Sum>(zss,ns)\<in>Sigma ?X ?L1. chains (edge_fg h) ((x # ns) # zss) y z)"
    apply (rule sum.Sigma)
    apply (rule yy_lists'_finite[OF dom_fg_finite dom_fg_finite])
    by simp
  also have "... = (\<Sum>zss\<in>(\<lambda>(zss,ns). (x # ns) # zss) ` Sigma ?X ?L1. chains (edge_fg h) zss y z)"
    by (rule sum.reindex_cong[where l="\<lambda>(zss,ns). (x # ns) # zss", symmetric], auto intro: inj_onI)
  also have "... = (\<Sum>zss\<in>?X'. chains (edge_fg h) zss y z)"
    by (subst XL1, simp)
  finally show ?case by simp
qed

lemma dl_lists'_eq_concat_ll_lists':
  assumes "x0 \<in> N1"
  shows "ddl_lists' x0 (N1 \<union> N2) k = concat ` ll_lists' x0 N1 N2 k"
proof (standard, goal_cases)
  case 1 show ?case
  proof (standard, goal_cases)
    case (1 xs)
    then have *: "set xs \<subseteq> N1 \<union> N2" "length xs < k" "distinct xs" "hd xs = x0" "xs \<noteq> []"
      unfolding ddl_lists'_def by auto
    moreover have
      "\<exists>xss. concat xss = xs \<and> xss \<noteq> [] \<and> (\<forall>xs\<in>set xss. xs \<noteq> []) \<and>
             alternating (segment N1) (segment N2) xss"
      apply (rule split_segments[of xs N1 N2])
      using assms * by simp_all
    ultimately obtain xss where **:
      "concat xss = xs \<and> xss \<noteq> [] \<and> (\<forall>xs\<in>set xss. xs \<noteq> []) \<and>
       alternating (segment N1) (segment N2) xss"
      using split_segments[of xs N1 N2] by auto 
    then have "xss \<in> ll_lists' x0 N1 N2 k"
      using * ** unfolding ll_lists'_def
      apply clarsimp
      using hd_hd_concat_hd by blast
    then show ?case
      using ** unfolding ll_lists'_def by auto
  qed
next
  case 2 show ?case
    unfolding ll_lists'_def ddl_lists'_def
    apply auto
         apply (metis (mono_tags, lifting) alternating.simps(2) concat.simps(2) hd_Cons_tl hd_append2)
        apply (metis (mono_tags, lifting) alternating.simps(2) hd_Cons_tl hd_in_set)
    by auto[1]
qed

lemma ll_lists'_UN_kl_lists':
  "ll_lists' x0 N1 N2 l = (\<Union>k \<in> {0..<l}. kl_lists' x0 N1 N2 l k)"
proof
  show "ll_lists' x0 N1 N2 l \<subseteq> \<Union> (kl_lists' x0 N1 N2 l ` {0..<l})"
    unfolding ll_lists'_def kl_lists'_def
    using length_concat_le_length alternating_props by fastforce+

  show "\<Union> (kl_lists' x0 N1 N2 l ` {0..<l}) \<subseteq> ll_lists' x0 N1 N2 l"
    unfolding kl_lists'_def ll_lists'_def by auto
qed

lemma alternating_hd:
  assumes "alternating P Q xs" "alternating P Q xs \<Longrightarrow> alternating P' Q' (map hd xs)"
    "alternating Q P xs \<Longrightarrow> alternating Q' P' (map hd xs)"
  shows "alternating P' Q' (map hd xs)"
  using assms disj_forward by blast

lemma UN_kl_lists'_UN_UN_a_lists:
  "(\<Union>k \<in> {0..<l}. kl_lists' x0 N1 N2 l k) =
   (\<Union>k \<in> {0..<l}. \<Union>xs \<in> a_lists x0 N1 N2 k. xx_lists' N1 N2 l xs)"
proof
  have blub1: "\<And>xss. alternating (segment N1) (segment N2) xss
    \<Longrightarrow> alternating (\<lambda>x. x \<in> N1) (\<lambda>x. x \<in> N2) (map hd xss)"
    subgoal for xss
      by (induction xss arbitrary: N1 N2, simp, auto)
    done
  have blub2:"\<And>xss. alternating (segment N2) (segment N1) xss
    \<Longrightarrow> alternating (\<lambda>x. x \<in> N2) (\<lambda>x. x \<in> N1) (map hd xss)"
    subgoal for xss
      by (induction xss arbitrary: N2 N1, simp, auto)
    done

  show "\<Union> (kl_lists' x0 N1 N2 l ` {0..<l})
    \<subseteq> (\<Union>k\<in>{0..<l}. \<Union>xs\<in>a_lists x0 N1 N2 k. xx_lists' N1 N2 l xs)"
  proof (safe, goal_cases)
    case (1 xss k)
    then show ?case
      apply auto
      apply (rule bexI[where x=k])
       apply (rule bexI[where x="map hd xss"])
      unfolding xx_lists'_def kl_lists'_def a_lists_def apply simp_all
      apply (intro conjI)
        apply (simp add: hd_map)
       apply (rule alternating_hd[where P="segment N1" and Q="segment N2"], blast)
      using blub1 blub2 distinct_map_hd by auto
  qed

  show "(\<Union>k\<in>{0..<l}. \<Union>xs\<in>a_lists x0 N1 N2 k. xx_lists' N1 N2 l xs) \<subseteq> \<Union> (kl_lists' x0 N1 N2 l ` {0..<l})"
    unfolding a_lists_def kl_lists'_def xx_lists'_def
    by (clarsimp, metis hd_map)
qed

lemma xx_lists'_eq_yy_lists':
  assumes "l > card (N1 \<union> N2)" "finite N1" "finite N2" "k > card N1" "kk > card N2" "N1 \<inter> N2 = {}"
  shows "xx_lists' N1 N2 l xs = yy_lists' N1 N2 k kk xs"
proof
  have A1: "alternating (segment N1) (segment N2) xss \<Longrightarrow> distinct (concat xss) \<Longrightarrow>
    alternating (\<lambda>xs. segment N1 xs \<and> length xs < k) (\<lambda>xs. segment N2 xs \<and> length xs < kk) xss"
    for xss
  proof (induction xss rule: alternating_induct'[where a=N1 and aa=k and b=N2 and bb=kk])
    case emptyP
    then show ?case by simp
  next
    case emptyQ
    then show ?case by simp
  next
    case (baseP xs)
    then show ?case using distinct_length_le[of xs N1] assms by simp
  next
    case (baseQ xs)
    then show ?case using distinct_length_le[of xs N2] assms by simp
  next
    case (stepP xs ys zss)
    then show ?case using distinct_length_le[of xs N1] assms by simp
  next
    case (stepQ xs ys zss)
    then show ?case using distinct_length_le[of xs N2] assms by simp
  qed

  have A3: "alternating (\<lambda>xs. set xs \<subseteq> N1 \<and> xs \<noteq> [] \<and> length xs < k) (\<lambda>xs. set xs \<subseteq> N2 \<and> xs \<noteq> [] \<and> length xs < kk) xss \<Longrightarrow>
        alternating (segment N1) (segment N2) xss \<and> (\<forall>xs\<in>set xss. xs \<noteq> [])" for xss
    apply (induction xss rule: alternating_induct'[where a=N1 and aa=k and b=N2 and bb=kk])
    using assms by simp_all

  show "xx_lists' N1 N2 l xs \<subseteq> yy_lists' N1 N2 k kk xs"
    unfolding yy_lists'_def xx_lists'_def
    apply safe
     apply (rule_tac x=xss in exI, simp)
    using A1 by simp

  show "yy_lists' N1 N2 k kk xs \<subseteq> xx_lists' N1 N2 l xs"
    unfolding yy_lists'_def xx_lists'_def
    apply safe
     apply (rule_tac x=xss in exI)
    subgoal for x xss
      using distinct_length_le[of "concat xss" "N1 \<union> N2"] assms apply simp
      apply (intro conjI)
      using A3 by blast+
    done
qed

lemma Cons_dl_lists'_ddl_lists':
  assumes "x \<in> N"
  shows "Cons x ` dl_lists' (N - {x}) k = ddl_lists' x N (k + 1)"
  using assms
  unfolding dl_lists'_def ddl_lists'_def image_def
  apply auto
  apply (rule_tac x="tl xa" in exI, auto)
     apply (simp add: list.set_sel(2) subsetD)
    apply (metis distinct.simps(2) hd_Cons_tl)
   apply (metis diff_Suc_less length_greater_0_conv less_antisym less_imp_diff_less)
  using distinct_tl by metis

lemma a_lists_finite:
  assumes "finite N1" "finite N2"
  shows "finite (a_lists x0 N1 N2 k)"
proof -
  have "a_lists x0 N1 N2 k \<subseteq> k_lists (N1 \<union> N2) k"
    unfolding a_lists_def k_lists_def apply auto
    using alternating_props by blast+
  then show ?thesis
    using k_lists_finite[OF finite_UnI[OF \<open>finite N1\<close> \<open>finite N2\<close>]] finite_subset by blast
qed

lemma alternating_concat_inj_False:
  assumes "alternating (\<lambda>xs. segment N1 xs \<and> length xs < k1) (\<lambda>xs. segment N2 xs \<and> length xs < k2) xss"
    "alternating (\<lambda>xs. segment N2 xs \<and> length xs < k1) (\<lambda>xs. segment N1 xs \<and> length xs < k2) yss"
    "concat xss = concat yss"  "N1 \<inter> N2 = {}" "xss \<noteq> []" "yss \<noteq> []"
  shows False
proof -
  from assms have A: "hd (hd xss) \<in> N1" apply (cases xss) using alternating_props by auto
  from assms have B: "hd (hd yss) \<in> N2" apply (cases yss) using alternating_props by auto

  from assms have "hd (hd xss) = hd (hd yss)"
    using alternating_props[where xs=xss] alternating_props[where xs=yss]
    by (smt alternating.elims(2) concat.simps(2) hd_append2 list.sel(1))
  then show False using assms A B by auto
qed

lemma alternating_concat_inj:
  assumes "alternating (\<lambda>xs. segment N1 xs \<and> length xs < k1) (\<lambda>xs. segment N2 xs \<and> length xs < k2) xss"
    "alternating (\<lambda>xs. segment N1 xs \<and> length xs < k1) (\<lambda>xs. segment N2 xs \<and> length xs < k2) yss"
    "concat xss = concat yss"  "N1 \<inter> N2 = {}"
  shows "xss = yss"
  using assms
proof (induction xss yss arbitrary: N1 N2 k1 k2 rule: list_induct2')
  case 1
  then show ?case by simp
next
  case (2 x xs)
  then show ?case by simp
next
  case (3 y ys)
  then show ?case by simp
next
  case (4 xs xss ys yss)
  have **: "xs = ys"
  proof (rule ccontr, goal_cases)
    case 1
    then show ?case
    proof (cases "length xs = length ys")
      case True
      then obtain n where "xs!n \<noteq> ys!n" using "1" nth_equalityI by blast
      then show ?thesis using 4 True by auto
    next
      case False
      then show ?thesis
      proof (cases "length xs < length ys")
        case True
        with 1 4 have *: "ys!(length xs) \<in> N1" "xss \<noteq> []" by auto
        have **: "alternating (segment N2) (segment N1) xss" using 1 4 True
          apply (cases "xs # xss", simp, simp) by (rule alternating_map_fwd, blast+)
        then have ***: "hd (hd (xss)) \<in> N2" using 1 4 True * by (cases xss, auto)
        have "\<forall>xs \<in> set xss. xs \<noteq> []" using ** alternating_props[where xs=xss] by auto
        then  have A: "hd (hd xss) = concat (xs # xss) ! (length xs) "
          using 1 4 True * concat_cons_length_hd_hd[of xss xs] by simp
        then have AA: "concat (ys # yss) ! (length xs) = hd (hd xss)" using 4 by simp
        have "concat (ys # yss) ! (length xs) = ys ! (length xs)"
          using True by (simp add: nth_append)
        then show False using *** ** * A AA 4 by auto
      next
        case False
        then have False: "length ys < length xs" using False \<open>length xs \<noteq> length ys\<close> by simp
        with 1 4 have *: "xs!(length ys) \<in> N1" "yss \<noteq> []" by auto
        have **: "alternating (segment N2) (segment N1) yss" using 1 4 False
          apply (cases "ys # yss", simp, simp) by (rule alternating_map_fwd, blast+)
        then have ***: "hd (hd (yss)) \<in> N2" using 1 4 False * by (cases yss, auto)
        have "\<forall>xs \<in> set yss. xs \<noteq> []" using ** alternating_props[where xs=yss] by auto
        then  have A: "hd (hd yss) = concat (ys # yss) ! (length ys) "
          using 1 4 False * concat_cons_length_hd_hd[of yss ys] by simp
        then have AA: "concat (xs # xss) ! (length ys) = hd (hd yss)" using 4 by simp
        have "concat (xs # xss) ! (length ys) = xs ! (length ys)"
          using False by (simp add: nth_append)
        then show False using *** ** * A AA 4 by auto
      qed
    qed
  qed
  with 4 have *: "concat xss = concat yss" by simp
  have "xss = yss"
    apply (rule "4.IH"[of N2 k2 N1 k1])
    using 4 * by auto
  then show ?case
    using ** by simp
qed

text \<open>Main auxiliary result: decompose capacity into sum of alternating chains\<close>

lemma cap_fg_to_sums:
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "m \<le> inf_fg h x" "x \<in> dom_fg h1" "x' \<notin> dom_fg h" "h = h1 + h2""h \<noteq> bot"
    "eff_acyclic' h" "eff_acyclic' h1" "eff_acyclic' h2"
    "End_closed E" "\<forall>x y. edge_fg h x y \<in> E" "\<forall>x y. edge_fg h1 x y \<in> E"
    "\<forall>x y. edge_fg h2 x y \<in> E" "id \<in> E" "(\<lambda>_. 0) \<in> E"
  shows "cap_fg h x x' m =
    (\<Sum>k\<in>{0..<card (dom_fg h) + 1}.
      \<Sum>xs \<in> a_lists x (dom_fg h1) (dom_fg h2) k. chain (alt_cap_hd_fg h1 h2) xs x' m)"
proof -
  let ?N = "dom_fg h" let ?e = "edge_fg h" let ?f = "flow_fg h"
  let ?N1 = "dom_fg h1" let ?N2 = "dom_fg h2"

  have D: "dom_fg h = dom_fg h1 \<union> dom_fg h2" "dom_fg h1 \<inter> dom_fg h2 = {}" using assms by auto
  then have "x \<notin> ?N2" using assms by blast
  then have DD: "dom_fg h1 - {x} \<union> dom_fg h2 = dom_fg h1 \<union> dom_fg h2 - {x}" by auto
  have DDD: "x \<in> dom_fg (h1 + h2)" using assms by simp

  have "cap_fg h x x' m = (\<Sum>ns\<in>dl_lists' (?N - {x}) (card ?N). chain ?e (x # ns) x' m)"
    using cap'_eq_dl_lists_chain[of E h x x' m] assms unfolding eff_acyclic'_def by simp
  also have "... = (\<Sum>ns\<in>Cons x ` dl_lists' (?N - {x}) (card ?N). chain ?e ns x' m)"
    by (rule sum.reindex_cong[symmetric, where l="Cons x"], simp_all)
  also have "... = (\<Sum>ns\<in>ddl_lists' x ?N (card ?N + 1). chain ?e ns x' m)"
    by (rule sum.cong, rule Cons_dl_lists'_ddl_lists', simp_all add: assms DDD)
  also have "... = (\<Sum>ns\<in>concat ` ll_lists' x ?N1 ?N2 (card ?N + 1). chain ?e ns x' m)"
    apply (rule sum.cong) using assms D DD dl_lists'_eq_concat_ll_lists'[of x ?N1 ?N2 "card ?N + 1"]
    by simp_all
  also have "... =
    (\<Sum>ns\<in>concat ` (\<Union>k \<in> {0..<card ?N + 1}. kl_lists' x ?N1 ?N2 (card ?N + 1) k). chain ?e ns x' m)"
    apply (rule sum.cong) using ll_lists'_UN_kl_lists' by metis+
  also have "... = (\<Sum>ns\<in>concat ` (\<Union>k \<in> {0..<card ?N + 1}.
    \<Union>xs \<in> a_lists x ?N1 ?N2 k. xx_lists' ?N1 ?N2 (card ?N + 1) xs). chain ?e ns x' m)"
    apply (rule sum.cong) using arg_cong[OF UN_kl_lists'_UN_UN_a_lists[of x ?N1 ?N2 "card ?N + 1"]]
    by metis+
  also have "... = (\<Sum>nss\<in>(\<Union>k \<in> {0..<card ?N + 1}.
    \<Union>xs \<in> a_lists x ?N1 ?N2 k. yy_lists' ?N1 ?N2 (card ?N1 + 1) (card ?N2 + 1) xs).
      chain ?e (concat nss) x' m)"
    apply (subst xx_lists'_eq_yy_lists'[where k="card ?N1 + 1" and kk="card ?N2 + 1"])
    using assms apply simp
    using dom_fg_finite[of h1] dom_fg_finite[of h2] plus_fg_dom_disj[of h1 h2]
    using \<open>h = h1 + h2\<close> \<open>h \<noteq> bot\<close> apply simp_all
    apply (rule sum.reindex_cong[where l=concat])
      apply (intro inj_onI)
    subgoal unfolding yy_lists'_def
      apply safe
      using alternating_concat_inj[of ?N1 "Suc (card ?N1)" ?N2 "Suc (card ?N2)"] by simp
    by auto
  also have "... = (\<Sum>nss\<in>(\<Union>k \<in> {0..<card ?N + 1}.
    \<Union>xs \<in> a_lists x ?N1 ?N2 k. yy_lists' ?N1 ?N2 (card ?N1 + 1) (card ?N2 + 1) xs).
      chains ?e nss x' m)"
    apply (rule sum.cong, simp) apply (subst chain_concat_chains)
    unfolding yy_lists'_def
    using alternating_props apply blast
    by simp
  also have "... = (\<Sum>k\<in>{0..<card ?N + 1}.
    \<Sum>nss \<in> (\<Union>xs \<in> a_lists x ?N1 ?N2 k. yy_lists' ?N1 ?N2 (card ?N1 + 1) (card ?N2 + 1) xs).
      chains ?e nss x' m)"
    apply (rule sum.UNION_disjoint, simp, safe)
     apply (intro finite_UN_I[OF a_lists_finite[OF dom_fg_finite dom_fg_finite]])
    apply (rule yy_lists'_finite)
    unfolding a_lists_def yy_lists'_def by auto
  also have "... = (\<Sum>k\<in>{0..<card ?N + 1}. \<Sum>xs \<in> a_lists x ?N1 ?N2 k.
                    \<Sum>nss \<in> yy_lists' ?N1 ?N2 (card ?N1 + 1) (card ?N2 + 1) xs. chains ?e nss x' m)"
    apply (rule sum.cong[OF _ sum.UNION_disjoint, simp], simp)
      apply (rule a_lists_finite[OF dom_fg_finite dom_fg_finite])
    apply safe
    apply (rule yy_lists'_finite)
    unfolding a_lists_def yy_lists'_def by auto
  also have "... = (\<Sum>k\<in>{0..<card ?N + 1}. \<Sum>xs \<in> a_lists x ?N1 ?N2 k. chain (alt_cap_hd_fg h1 h2) xs x' m)"
    apply (rule sum.cong[OF _ sum.cong[OF _ chain_cap_yy_lists'_sum]])
    using assms alternating_props D unfolding a_lists_def
    apply blast
    apply blast
    apply blast
    using assms apply blast
    apply blast
                 apply blast
    using D(1) alternating_props apply fastforce
    using assms apply blast+
    subgoal for xs xa
      apply (rule order_trans[OF _ inf_fg_le_inf_fg[of h1 h2 "hd xa"]])
      using assms by simp_all
    done
  finally show ?thesis .
qed

section \<open>Equality of capacities\<close>

text \<open>Use previous result to prove equality of capacities in flow graph sums related by
subflow-preserving extensions.

The difference to @{term Effectively_Acyclic_Switch_World} is that we have to transfer a capacity
in h=h1+h2 to a capacity h'=h1'+h2' instead of a convoluted alternating path (where we already
know the path segments within h1 and h2, respectively). Therefore, we first have to decompose
the capacity in h1+h2 into a convoluted alternating path with segments in h1 and h2, resp.,
then apply the already existing result, and convert back to a capacity.\<close>

lemma cap_fg_eq_cap_fg_case:
  fixes h h1 h2 h' h1' h2' :: "('a,'b :: pos_cancel_comm_monoid_add) fg"
  assumes "m \<le> inf_fg h x" "x \<in> dom_fg h1" "x' \<notin> dom_fg h" "h = h1 + h2" "h' = h1' + h2'" "h \<noteq> bot"
    "h' \<noteq> bot" "id \<in> E" "eff_acyclic' h" "End_closed E" "\<forall>x y. edge_fg h x y \<in> E"
    "\<forall>x y. edge_fg h1 x y \<in> E" "\<forall>x y. edge_fg h2 x y \<in> E" "m \<le> inf_fg h x" "m \<le> inf_fg h' x"
    "\<forall>x y. edge_fg h' x y \<in> E" "\<forall>x y. edge_fg h1' x y \<in> E" "\<forall>x y. edge_fg h2' x y \<in> E"
    "dom_fg h = dom_fg h'" "dom_fg h1 = dom_fg h1'" "dom_fg h2 = dom_fg h2'" "eff_acyclic' h'"
    "eff_acyclic' h1" "eff_acyclic' h2" "(\<lambda>_. 0) \<in> E" "eff_acyclic' h1'" "eff_acyclic' h2'"
    "\<forall>n \<in> dom_fg h1. \<forall>n' \<in> -dom_fg h1. \<forall>m \<le> inf_fg h1 n. cap_fg h1 n n' m = cap_fg h1' n n' m"
    "\<forall>n \<in> dom_fg h2. \<forall>n' \<in> -dom_fg h2. \<forall>m \<le> inf_fg h2 n. cap_fg h2 n n' m = cap_fg h2' n n' m"
  shows "cap_fg h x x' m = cap_fg h' x x' m"
proof -
  let ?N = "dom_fg h" let ?e = "edge_fg h" let ?f = "flow_fg h"
  let ?N1 = "dom_fg h1" let ?N2 = "dom_fg h2"
  let ?N1' = "dom_fg h1'" let ?N2' = "dom_fg h2'" let ?N' = "dom_fg h'"

  have S1: "card ?N = card ?N'"
    using assms by simp

  have "cap_fg h x x' m =
    (\<Sum>k\<in>{0..<card ?N + 1}. \<Sum>xs \<in> a_lists x ?N1 ?N2 k. chain (alt_cap_hd_fg h1 h2) xs x' m)"
    apply (cases "x \<in> dom_fg h1")
    apply (rule cap_fg_to_sums)
    using assms by blast+
  also have "... =
    (\<Sum>k\<in>{0..<card ?N + 1}. \<Sum>xs \<in> a_lists x ?N1' ?N2' k. chain (alt_cap_hd_fg h1' h2') xs x' m)"
    apply (rule sum.cong[OF _ sum.cong], simp, simp, simp add: assms)
    unfolding a_lists_def apply simp
    subgoal for k xs
      apply (rule chains'_switch_world_chain[of h1 h2 xs h1' h2' E m, symmetric])
      using assms apply simp_all
      apply (cases xs, simp)
      using inf_fg_le_inf_fg[of h1 h2 x E] S1 by simp
    done
  also have "... = cap_fg h' x x' m"
    apply (cases "x \<in> dom_fg h1'")
    apply (subst S1, rule cap_fg_to_sums[symmetric])
    using assms by blast+
  finally show ?thesis .
qed

lemma cap_fg_eq_cap_fg:
  fixes h h1 h2 h' h1' h2' :: "('a,'b :: pos_cancel_comm_monoid_add) fg"
  assumes "m \<le> inf_fg h x" "x \<in> dom_fg h" "x' \<notin> dom_fg h" "h = h1 + h2" "h' = h1' + h2'" "h \<noteq> bot"
    "h' \<noteq> bot" "id \<in> E" "eff_acyclic' h" "End_closed E" "\<forall>x y. edge_fg h x y \<in> E"
    "\<forall>x y. edge_fg h1 x y \<in> E" "\<forall>x y. edge_fg h2 x y \<in> E" "m \<le> inf_fg h x" "m \<le> inf_fg h' x"
    "\<forall>x y. edge_fg h' x y \<in> E" "\<forall>x y. edge_fg h1' x y \<in> E" "\<forall>x y. edge_fg h2' x y \<in> E"
    "dom_fg h = dom_fg h'" "dom_fg h1 = dom_fg h1'" "dom_fg h2 = dom_fg h2'" "eff_acyclic' h'"
    "eff_acyclic' h1" "eff_acyclic' h2" "(\<lambda>_. 0) \<in> E" "eff_acyclic' h1'" "eff_acyclic' h2'"
    "\<forall>n \<in> dom_fg h1. \<forall>n' \<in> -dom_fg h1. \<forall>m \<le> inf_fg h1 n. cap_fg h1 n n' m = cap_fg h1' n n' m"
    "\<forall>n \<in> dom_fg h2. \<forall>n' \<in> -dom_fg h2. \<forall>m \<le> inf_fg h2 n. cap_fg h2 n n' m = cap_fg h2' n n' m"
  shows "cap_fg h x x' m = cap_fg h' x x' m"
proof (cases "x \<in> dom_fg h1")
  case True
  then show ?thesis using cap_fg_eq_cap_fg_case[of m h x h1 x' h2 h' h1' h2' E] assms by blast
next
  case False
  then show ?thesis using cap_fg_eq_cap_fg_case[of m h x h2 x' h1 h' h2' h1' E] assms
    by (simp add: algebra_simps)
qed



end
