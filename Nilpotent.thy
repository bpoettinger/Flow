\<^marker>\<open>creator Bernhard Pöttinger\<close>

chapter \<open>Nilpotent Flows\<close>
theory Nilpotent
  imports Flow_Base Chain Pigeonhole Auxiliary Approximations
begin

paragraph \<open>Summary\<close>
text \<open>This theory proves the existence of unique flows for flow graphs restricted to nilpotent
edge functions (see @{cite \<open>lem. 4\<close> krishna20}).\<close>

lemma fold_funpow:
  fixes f :: "'a \<Rightarrow> 'a"
  shows "fold (o) (map (\<lambda>_. f) xs) g = (f ^^ (length xs)) o g"
  apply (induction xs arbitrary: g)
  by (auto, metis comp_funpow funpow_swap1 o_assoc)

lemma nilpotent_flow_exists':
  fixes E :: "('m \<Rightarrow> 'm :: pos_cancel_comm_monoid_add) set"
  assumes "\<forall>x y. e x y \<in> E" "End_closed E" "nilpotent E" "finite N" "N \<noteq> {}" "(\<lambda>_. 0) \<in> E"
    "finite N"
  shows "\<exists>f. flow_eq (fg N e f) i \<and> (\<forall>f'. flow_eq (fg N e f') i \<longrightarrow> f = f' on N)"
proof -
  obtain p where nilp: "p > 1" "\<forall>e \<in> E. e^^p = (\<lambda>_. 0)"
    using assms unfolding nilpotent_def by blast

  let ?l = "p * card N + 1"
  let ?f = "\<lambda>n. i n + (\<Sum>ns \<in> l_lists N ?l. chain e ns n (i (hd ns)))"

  have endo_e: "\<forall>x y. endo (e x y)"
    using assms unfolding End_closed_def End_closed_def by blast

  let ?g = "\<lambda>xs n. if n < length xs then Some (xs!n) else None"

  have reoccur:
    "\<forall>xs \<in> k_lists N ?l. \<exists>y \<in> ran (?g xs). card ((?g xs) -` {Some y}) \<ge> p + 1"
  proof 
    fix xs
    assume *: "xs \<in> k_lists N ?l"
    then obtain x where "x \<in> set xs" using k_lists_nonempty(1)[of ?l xs N] by fastforce
    then obtain i where EX: "?g xs i = Some x" "i < length xs" by (metis in_set_conv_nth)
    have RANDOM: "ran (?g xs) \<subseteq> N" "dom (?g xs) = {0..<?l}"
      unfolding ran_def using * unfolding k_lists_def by (auto split: if_splits)
    show "\<exists>y \<in> ran (?g xs). card ((?g xs) -` {Some y}) \<ge> p + 1"
      apply (rule generalized_pigeonhole[of "?g xs" p])
      subgoal unfolding dom_def using EX by blast
      subgoal unfolding dom_def by auto
      subgoal using * assms RANDOM card_mono[of N] unfolding k_lists_def by auto
      done
  qed

  have "\<And>n i ns. ns \<in> k_lists N ?l \<Longrightarrow> chain e ns n = 0"
  proof -
    fix n ns
    assume A: "ns \<in> k_lists N ?l"
    then obtain m where card:
      "m \<in> ran (?g ns)" "card ((?g ns) -` {Some m}) \<ge> p + 1"
      using reoccur by blast
    moreover have fin: "finite ((?g ns) -` {Some m})"
      by (fact finite_index_fun_vimage)
    ultimately obtain xs where xs:
      "length xs = card ((?g ns) -` {Some m}) \<and> set xs = ((?g ns) -` {Some m})"
      using set_to_list[of "(?g ns) -` {Some m}"] by auto

    have L: "\<forall>x \<in> (?g ns) -` {Some m}. x < length ns"
      by (auto split: if_splits)

    have "\<And>n. n \<in> (?g ns) -` {Some m} \<Longrightarrow> ?g ns n = Some m"
      by auto
    then have "\<forall>n \<in> (?g ns) -` {Some m}. ns!n = m"
      by (metis (no_types, lifting) option.inject option.simps(3))
    moreover have "card ((?g ns) -` {Some m}) \<le> length ns"
    proof -
      have "?g ns -` {Some m} \<subseteq> {0..<length ns}" unfolding vimage_def by auto
      then have "card (?g ns -` {Some m} ) \<le> card {0..<length ns}"
        using card_mono by blast
      also have "... = length ns" by simp
      finally show ?thesis .
    qed
    ultimately have "count_list ns m \<ge> p + 1"
      using card card_count_list[of "(?g ns) -` {Some m}" ns m] fin L by linarith
    then obtain ms mss where decomp: "ns = ms @ concat mss" "\<forall>ms \<in> set mss. hd ms = m"
        "\<forall>ms \<in> set mss. set ms \<subseteq> set ns" "length mss = p + 1" "\<forall>ms \<in> set mss. ms \<noteq> []"
      using decompose_list_count_list_multi[of "p + 1" ns m] by auto
    then have b_bb: "chain e ns n = chains e (ms#mss) n"
      by (subst chain_chains[of ns "ms#mss" e n], simp_all)
    have len_ns: "length ns = sum_list (map length (ms#mss))"
      using length_concat decomp by auto
    then have len: "\<And>ms'. ms' \<in> set (ms#mss) \<Longrightarrow> length ms' \<le> length ns"
      subgoal for ms'
        using length_length_concat_in[of "ms#mss" ms'] decomp by auto
      done
    let ?bound = "\<Sum>ns \<in> l_lists' N (length ns). chain2 e m ns m"
    have bound_in_E: "?bound \<in> E"
      using chain2_endo[of e E m _ m] l_lists'_finite[of N "length ns"]
        End_closed_sumE[of "l_lists' N (length ns)" E "\<lambda>ns. chain2 e m ns m"] assms
        by blast
    then have "?bound ^^ p = 0"
      using nilp by auto

    have bound_in_End: "?bound \<in> End"
      using bound_in_E assms unfolding End_closed_def by auto

    have "mss \<noteq> []"
      using decomp by auto
    then obtain mss' ms' where decomp_mss: "mss = mss' @ [ms']"
      using list_decompose_last[of mss] by auto
    then have mss'_ne: "mss' \<noteq> []"
      using nilp decomp by auto

    have ms_ne: "\<And>ms. ms \<in> set mss' \<Longrightarrow> ms \<noteq> []"
      using decomp decomp_mss by simp
    then have ms_ne': "\<And>ms. ms \<in> set (tl mss') \<Longrightarrow> ms \<noteq> []"
      by (simp add: list.set_sel(2) mss'_ne)

    have ineq: "\<And>ms. ms \<in> set mss' \<Longrightarrow> chain e ms m \<le> ?bound"
      subgoal premises prems for ms'
      proof -
        have XXX: "set (tl ms') \<subseteq> N"
        proof -
          have "ms' \<in> set mss'" using prems by simp
          with decomp_mss have "ms' \<in> set mss" by simp
          with decomp have "set ms' \<subseteq> set ns" by auto
          with A have "set ms' \<subseteq> N" unfolding k_lists_def by auto
          then show ?thesis by (simp add: list.set_sel(2) ms_ne prems subset_iff)
        qed

        have hdm: "hd ms' = m"
          using decomp decomp_mss prems by simp
        have tlm: "tl ms' \<in> l_lists' N (length ns)"
          using prems assms decomp decomp_mss length_length_concat_in[of "ms#mss" ms'] mss'_ne
          unfolding l_lists'_def apply clarsimp
          apply (intro conjI)
          using XXX apply simp
          by (metis diff_Suc_less le_neq_implies_less length_greater_0_conv less_imp_diff_less)
        have "(\<Sum>ns \<in> l_lists' N (length ns) - {tl ms'}. chain2 e m ns m) \<ge> 0"
          using sum_nonneg
          by (subst sum_nonneg, simp_all add: le_fun_def)
        then have"chain e ms' m \<le>
          chain e ms' m + (\<Sum>ns \<in> l_lists' N (length ns) - {tl ms'}. chain2 e m ns m)"
          by (metis add.commute add_increasing order_refl)
        also have "... = (\<Sum>ns \<in> l_lists' N (length ns). chain2 e m ns m)"
          apply (subst chain_chain2[of ms' e m])
          using decomp decomp_mss len[of ms'] sum.insert prems apply simp
          apply (subst hdm)
          apply (subst sum.insert[symmetric])
          using l_lists'_finite[of N "length ns"] assms tlm
            insert_absorb[of "tl ms'" "l_lists' N (length ns)"]
          by simp_all
        finally show ?thesis .
      qed
      done
    have **: "chain e ns n = chain e ms' n o chains e mss' (hd ms') o chain e ms (hd (hd mss))"
      by (subst b_bb, subst chains_prepend_append, simp_all add: decomp_mss mss'_ne)
    then have *: "chains e mss' (hd ms') \<le> fold (o) (map (\<lambda>_. ?bound) mss') id"
      apply (subst chains_le_fold[where E=E])
      using ineq decomp decomp_mss bound_in_End assms ms_ne apply (simp_all)
      apply (rule End_closed_sumE[OF l_lists'_finite[OF \<open>finite N\<close>]])
      using assms apply simp_all
      by (intro allI, rule chain2_endo, simp_all add: assms)
    have chain_ge0: "chains e mss' (hd ms') \<ge> 0"
      by (simp add: le_fun_def)
    have "fold (o) (map (\<lambda>_. ?bound) mss') id = ?bound ^^ (length mss')"
      by (simp add: fold_funpow)
    then have "chains e mss' (hd ms') \<le> (?bound ^^ (length mss'))"
      using * by auto
    also have "... = (\<lambda>_. 0)"
      using nilp bound_in_E decomp decomp_mss by auto
    finally have "chains e mss' (hd ms') = 0"
      using chain_ge0 unfolding zero_fun_def by simp
    then show "chain e ns n = 0"
      using ** chain_chains[of "concat mss'" "mss'" e n] ms_ne' A
       endo_f_0_0_closed_comp[of "chain e ms' n" E] endo_chain_closed_nonempty[of ns e E n] assms
      unfolding k_lists_def
      apply simp
      apply (subst endo_f_0_0_closed_comp[of "chain e ms' n" E])
      by (auto simp: decomp decomp_mss endo_chain_closed_nonempty)
  qed
  then have **: "\<And>n i. (\<Sum>ns \<in> k_lists N ?l. chain e ns n (i (hd ns))) = 0"
    by (subst sum.neutral, simp_all)

  have F: "flow_eq (fg N e ?f) i"
  proof (rule flow_eqI, safe, goal_cases)
    case (1 n)

    let ?ll = "l_lists N ?l"

    have xs_props: "\<forall>xs \<in> k_lists N ?l. set xs \<subseteq> N \<and> length xs = ?l"
      unfolding k_lists_def by auto

    have "i n + (\<Sum>n'\<in>N. e n' n (?f n')) =
      i n + (\<Sum>n'\<in>N. e n' n (i n') + e n' n (\<Sum>ns \<in> ?ll. chain e ns n' (i (hd ns))))"
      using assms
      apply (simp, intro sum.cong, simp)
      using endo_e unfolding endo_def by auto
    also have "... = i n + (\<Sum>n'\<in>N. e n' n (i n')
                         + (\<Sum>ns \<in> ?ll. e n' n (chain e ns n' (i (hd ns)))))"
      apply (simp, intro sum.cong, simp, simp)
      apply (rule endo_iterated_sum_closed[OF l_lists_finite[OF \<open>finite N\<close>], where E=E])
      using assms by auto
    also have "... = i n + (\<Sum>n'\<in>N. e n' n (i n')
                         + (\<Sum>ns \<in> ?ll. chain e (ns@[n']) n (i (hd ns))))"
      apply (simp, intro sum.cong, simp, simp, intro sum.cong, simp)
      using chain_extend_right by auto
    also have "... = i n + (\<Sum>n'\<in>N. chain e [n'] n (i n')
                         + (\<Sum>ns \<in> ?ll. chain e (ns@[n']) n (i (hd ns))))"
      by simp
    also have "... = i n + (\<Sum>n'\<in>N. chain e [n'] n (i n'))
                         + (\<Sum>n' \<in> N. (\<Sum>ns \<in>?ll. chain e (ns@[n']) n (i (hd ns))))"
      by (simp add: algebra_simps sum.distrib)
    also have "... = i n + (\<Sum>n'\<in>N. chain e [n'] n (i n'))
                         + (\<Sum>(n',ns) \<in> N \<times> ?ll. chain e (ns@[n']) n (i (hd ns)))"
      by (simp add: sum.cartesian_product)
    also have "... = i n + (\<Sum>n'\<in>N. chain e [n'] n (i n'))
                         + (\<Sum>ns \<in> (\<lambda>(n,ns). ns@[n]) ` (N \<times> ?ll). chain e ns n (i (hd ns)))"
      apply (subst sum.reindex, auto intro: inj_onI, subst sum.cong, auto)
      unfolding l_lists_def
      by (auto simp: hd_def split: list.splits)
    also have "... = i n + (\<Sum>ns\<in>k_lists N 1. chain e ns n (i (hd ns)))
                         + (\<Sum>ns \<in> (\<lambda>(n,ns). ns@[n]) ` (N \<times> ?ll). chain e ns n (i (hd ns)))"
      apply (simp del: chain.simps) unfolding k_lists_def
      apply (subst sum.reindex_cong[symmetric, where l="\<lambda>x. [x]"], auto intro: inj_onI)
      by (metis (no_types, lifting) One_nat_def Suc_length_conv image_iff
          length_0_conv list.sel(1) order_refl set_hd_in)
    also have
      "... = i n + (\<Sum>ns \<in> k_lists N 1 \<union> (\<lambda>(n,ns). ns@[n]) ` (N \<times> ?ll). chain e ns n (i (hd ns)))"
      apply (simp add: algebra_simps del: chain.simps, rule sum.union_disjoint[symmetric])
        apply (auto simp: assms k_lists_finite l_lists_finite)
      unfolding l_lists_def k_lists_def by auto
    also have "... = i n + (\<Sum>ns \<in> l_lists N (Suc ?l). chain e ns n (i (hd ns)))"
      by (subst merge_k_list_1, simp_all)
    also have "... = i n + (\<Sum>ns \<in> l_lists N ?l. chain e ns n (i (hd ns)))
                         + (\<Sum>ns \<in> k_lists N ?l. chain e ns n (i (hd ns)))"
      apply (subst l_lists_k_lists_union[symmetric,of ?l N], simp)
      by (subst sum.union_disjoint,
          simp_all add: l_lists_k_lists_disjoint l_lists_finite k_lists_finite algebra_simps assms)
    finally show "?f n = i n + (\<Sum>n'\<in>N. e n' n (?f n'))"
      using ** by simp
  next
    case 2
    show ?case using assms by simp
  qed

  have FF: "\<forall>f'. flow_eq (fg N e f') i \<longrightarrow> ?f = f' on N"
  proof safe
    fix f' x
    assume "flow_eq (fg N e f') i" "x \<in> N"

    then have "f' x = i x + (\<Sum>ns\<in>l_lists N (p * card N + 1). chain e ns x (i (hd ns)))
                          + (\<Sum>ns\<in>k_lists N (p * card N + 1). chain e ns x (f' (hd ns)))"
      by (subst unroll_flow_eq'[of ?l N e f' i E x], simp_all add: assms)
    also have "... = i x + (\<Sum>ns\<in>l_lists N (p * card N + 1). chain e ns x (i (hd ns)))"
      using **[of x] by simp
    finally show "?f x = f' x"
      by simp
  qed

  from F FF show ?thesis by auto
qed

text \<open>@{cite \<open>lem. 4\<close> krishna20}\<close>

lemma nilpotent_flow_exists:
  fixes E :: "('m \<Rightarrow> 'm :: pos_cancel_comm_monoid_add) set"
  assumes "\<forall>x y. e x y \<in> E" "End_closed E" "nilpotent E" "finite N"
    "(\<lambda>_. 0) \<in> E" "finite N"
  shows "\<exists>f. flow_eq (fg N e f) i \<and> (\<forall>f'. flow_eq (fg N e f') i \<longrightarrow> f = f' on N)"
  proof (cases "N \<noteq> {}")
case True
  then show ?thesis using nilpotent_flow_exists' assms by blast
next
  case False
  show ?thesis
    apply (rule exI[where x="\<lambda>_. 0"])
    using False by (auto intro!: flow_eqI)
qed

end
