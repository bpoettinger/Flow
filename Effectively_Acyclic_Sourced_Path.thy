\<^marker>\<open>creator Bernhard Pöttinger\<close>

theory Effectively_Acyclic_Sourced_Path
imports Effectively_Acyclic Effectively_Acyclic_Approximations
begin

paragraph \<open>Summary\<close>
text \<open>This theory culminates in a lemma that constructs a path within a flow graph h' = h1' + h2'
by using an effectively acyclic flow graph h = h1 + h2 and subflow-preserving extensions
h1 <=S h1' and h2 <= h2'. This path is guaranteed to have flow starting with some inflow from the
outside of h'. h' is explicitly not effectively acyclic.

This result is purely technical in order to conduct a proof by contradiction in
@{term maintain_eff_acyclic_dom_eq}\<close>

paragraph \<open>Major Lemmas\<close>

text \<open>
@{term eff_acyclic_flow_is_sourced}: find some path xs to a given node y such that
  there is inflow to hd xs and flow along xs to y.
@{term eff_acyclic_sourced_path_in_bigraph}: lemma described in summary.
\<close>

section \<open>Sourced Paths in Simple Flow Graphs\<close>

text \<open>Given a node with flow, there must be a path to this node such that the starting node of
that path has inflow.\<close>

lemma eff_acyclic_flow_is_sourced:
  fixes E :: "('b \<Rightarrow> 'b :: pos_cancel_comm_monoid_add) set"
  assumes "eff_acyclic' h" "f (flow_fg h x) \<noteq> 0" "End_closed E" "\<forall>x y. edge_fg h x y \<in> E"
    "f \<in> E" "id \<in> E" "(\<lambda>_. 0) \<in> E"
  shows "\<exists>xs. f (chain (edge_fg h) xs x (inf_fg h (if xs \<noteq> [] then hd xs else x))) \<noteq> 0 \<and>
              set xs \<subseteq> dom_fg h"
proof (rule ccontr)
  assume "\<nexists>xs. f (chain (edge_fg h) xs x (inf_fg h (if xs \<noteq> [] then hd xs else x))) \<noteq> 0 \<and>
               set xs \<subseteq> dom_fg h"
  then have **: "\<forall>xs. set xs \<subseteq> dom_fg h \<longrightarrow>
    f (chain (edge_fg h) xs x (inf_fg h (if xs \<noteq> [] then hd xs else x))) = 0"
    by blast
  then have ***: "f (inf_fg h x) = 0"
    by (smt bot.extremum chain.simps(1) empty_set id_apply)

  have "flow_fg h x \<noteq> 0"
    using endo_f_n0_n0_closed assms by auto
  then have X: "x \<in> dom_fg h" "h \<noteq> bot"
    using pos_flow_nbot pos_flow_dom[of h x] by auto

  have "flow_eq2' (dom_fg h) (edge_fg h) (flow_fg h) (inf_fg h)"
    using X nbot_fg_to_flow_eq2' by blast
  then have "\<forall>x \<in> dom_fg h. flow_fg h x = inf_fg h x +
    (\<Sum>xs\<in>l_lists (dom_fg h) (card (dom_fg h) + 1). chain (edge_fg h) xs x (inf_fg h (hd xs)))"
    using assms unroll_flow_eq_eff_acyclic[of "dom_fg h" "edge_fg h" "flow_fg h"] dom_fg_finite[of h]
    unfolding eff_acyclic'_def
    by auto
  then have "f (flow_fg h x) = f (inf_fg h x) +
    f (\<Sum>xs\<in>l_lists (dom_fg h) (card (dom_fg h) + 1). chain (edge_fg h) xs x (inf_fg h (hd xs)))"
    using X assms unfolding endo_def End_closed_def by auto
  also have "... = f (inf_fg h x) +
    (\<Sum>xs\<in>l_lists (dom_fg h) (card (dom_fg h) + 1). f (chain (edge_fg h) xs x (inf_fg h (hd xs))))"
    apply (subst fun_dist_right''[where g="f"])
    using l_lists_finite[OF dom_fg_finite] assms by simp_all
  also have "... = f (inf_fg h x)"
    apply (subst sum.neutral)
    unfolding l_lists_def
     apply (auto simp: ** assms split: if_splits)
    subgoal for xs
      apply (cases xs, simp)
      using **
      by (smt Suc_le_lessD length_greater_0_conv)
    done
  also have "... = 0"
    using *** by simp
  finally show False
    using assms by simp
qed

section \<open>Sourced Paths in Flow Graph Sums\<close>

text \<open> Proof structure of @{term eff_acyclic_sourced_path_in_bigraph}:
- two cases, both solved with @{term eff_acyclic_sourced_path_in_bigraph_case}
- @{term eff_acyclic_sourced_path_in_bigraph_case} prepares all assumptions required by
  @{term eff_acyclic_sourced_path_in_bigraph'}
- then @{term eff_acyclic_sourced_path_in_bigraph'} finds the path
\<close>

lemma eff_acyclic_sourced_path_in_bigraph':
  fixes E :: "('b \<Rightarrow> 'b :: pos_cancel_comm_monoid_add) set"
  assumes "chain (edge_fg h') as b (chain (edge_fg h) xs (hd (as @ [b])) (outf_fg h2 (hd (xs @ as @ [b])))) \<noteq> 0"
      "set xs \<subseteq> dom_fg h" "b \<in> dom_fg h"
      "eff_acyclic' h" "eff_acyclic' h1" "eff_acyclic' h1'" "eff_acyclic' h2" "eff_acyclic' h2'"
      "\<forall>n \<in> dom_fg h1. \<forall>n' \<in> -dom_fg h1'. \<forall>m \<le> inf_fg h1 n. cap_fg h1 n n' m = cap_fg h1' n n' m"
      "\<forall>n \<in> dom_fg h2. \<forall>n' \<in> -dom_fg h2'. \<forall>m \<le> inf_fg h2 n. cap_fg h2 n n' m = cap_fg h2' n n' m"
      "h = h1 + h2" "h' = h1' + h2'" "hd (xs @ as @ [b]) \<in> dom_fg h1" "h \<noteq> bot" "h' \<noteq> bot"
      "\<forall>x y. edge_fg h x y \<in> E" "\<forall>x y. edge_fg h1' x y \<in> E" "\<forall>x y. edge_fg h1 x y \<in> E"
      "\<forall>x y. edge_fg h2 x y \<in> E" "End_closed E" "id \<in> E" "int_fg h1 = int_fg h1'"
      "int_fg h2 = int_fg h2'" "dom_fg h1 = dom_fg h1'" "dom_fg h2 = dom_fg h2'"
      "inf_fg h' = inf_fg h" "card (dom_fg h) \<le> k" "card (dom_fg h') \<le> k"
      "\<forall>x y. edge_fg h2' x y \<in> E" "set as \<subseteq> dom_fg h" "\<forall>x y. edge_fg h' x y \<in> E"
      "\<forall>x y. edge_fg h x y \<in> E" "(\<lambda>_. 0) \<in> E" "id \<in> E"
    shows "\<exists>ys. chain (edge_fg h') as b (chain (edge_fg h) xs (hd (as @ [b])) (chain (edge_fg h') ys (hd (xs @ as @ [b])) (inf_fg h' (hd (ys @ xs @ as @ [b]))))) \<noteq> 0 \<and>
            chain (edge_fg h') ys (hd (xs @ as @ [b])) (inf_fg h' (hd (ys @ xs @ as @ [b]))) \<le> inf_fg h1 (hd (xs @ as @ [b])) \<and>
            set ys \<subseteq> dom_fg h'"
  using assms
proof (induction "length xs" arbitrary: xs h h' h1 h1' h2 h2' rule: nat_descend_induct[where n="k"])
  case base

  let ?N = "dom_fg h" let ?e = "edge_fg h" let ?f = "flow_fg h" let ?i = "inf_fg h"
  let ?N1 = "dom_fg h1" let ?f1 = "flow_fg h1" let ?i1 = "inf_fg h1"
  let ?o2 = "outf_fg h2" let ?e2 = "edge_fg h2" let ?f2 = "flow_fg h2" let ?N2 = "dom_fg h2"
  let ?N' = "dom_fg h'" let ?e' = "edge_fg h'" let ?f' = "flow_fg h'" let ?i' = "inf_fg h'"
  let ?y = "hd (xs @ as @ [b])"

  have L: "length xs \<ge> card ?N + 1" using \<open>k < length xs\<close> \<open>card ?N \<le> k\<close>
    by simp
  then obtain x xs1 xs2 xs3 where *: "xs = xs1 @ x # xs2 @ x # xs3"
    using pigeonhole_split_list[of ?N xs] base by auto
  moreover have "chain ?e xs (hd (as @ [b])) (?o2 ?y) \<noteq> 0"
    apply (rule endo_f_n0_n0_closed[of "chain (edge_fg h') as b" E "chain ?e xs (hd (as @ [b])) (?o2 ?y)"])
    using base(2) apply simp_all
    using endo_chain_closed[of ?e' E as b] \<open>id \<in> E\<close> \<open>End_closed E\<close> \<open>\<forall>x y. edge_fg h' x y \<in> E\<close> by auto
  ultimately have A1: "chain ?e (x # xs2) x (chain ?e xs1 x (?o2 ?y)) \<noteq> 0"
    using chain_append_not_zero3(2)[of xs xs1 "x # xs2" "x # xs3" ?e "hd (as @ [b])" "?o2 ?y" E] base *
    by (metis append_Cons list.sel(1) list.simps(3))

  have "chain ?e xs1 x (?o2 ?y) \<le> chain ?e xs1 x (?i1 ?y)"
    apply (rule pos_endo_mono'_closed[OF outf_fg_le_inf_fg[of h]])
    using \<open>End_closed E\<close> \<open>h = h1 + h2\<close> \<open>h \<noteq> bot\<close> \<open>hd (xs @ as @ [b]) \<in> ?N1\<close> \<open>\<forall>x y. edge_fg h x y \<in> E\<close> \<open>id \<in> E\<close>
    by (auto simp: algebra_simps elim!: endo_chain_closed)
  also have "... \<le> chain ?e xs1 x (?f1 ?y)"
    apply (rule pos_endo_mono'_closed[OF inf_fg_le_flow_fg])
    using \<open>End_closed E\<close> \<open>h = h1 + h2\<close> \<open>h \<noteq> bot\<close> \<open>hd (xs @ as @ [b]) \<in> ?N1\<close> \<open>\<forall>x y. edge_fg h x y \<in> E\<close> \<open>id \<in> E\<close>
    by (auto simp: algebra_simps elim!: endo_chain_closed)
  also have "... = chain ?e xs1 x (?f ?y)"
    using flow_fg_plus_fg_on1'[of h1 h2 ?y] base by metis
  also have "... \<le> ?f x"
    using chain_flow_fg_le_flow_fg[of h E x xs1] base * apply simp
    by (metis append_self_conv2 hd_append2 list.sel(1))
  finally have B: "chain ?e xs1 x (?o2 ?y) \<le> ?f x" .

  have C: "chain ?e (x # xs2) x \<in> E"
    using endo_chain_closed[of ?e E "x # xs2" x] base by metis

  have "x # xs2 \<in> k_lists ?N (length xs2 + 1)"
    using base * unfolding k_lists_def
    by (smt One_nat_def insert_subset le_sup_iff list.set(2) list.size(4) mem_Collect_eq set_append)
  then have "chain ?e (x # xs2) x (?f (hd (x # xs2))) = 0"
    using base
    by (metis eff_acyclic'_def eff_acyclic_def le_add2 list.sel(1))
  then have A2: "chain ?e (x # xs2) x (chain ?e xs1 x (?o2 ?y)) = 0"
    using pos_endo_mono'_closed[OF B C] base
    by (metis add_eq_0_iff_both_eq_0 le_iff_add list.sel(1))

  show ?case
    using A1 A2
    by simp
next 
  case descend

  let ?N1 = "dom_fg h1" let ?e1 = "edge_fg h1" let ?f1 = "flow_fg h1" let ?i1 = "inf_fg h1"
  let ?N1' = "dom_fg h1'" let ?e1' = "edge_fg h1'" let ?f1' = "flow_fg h1'" let ?i1' = "inf_fg h1'"
  let ?o2 = "outf_fg h2" let ?o2' = "outf_fg h2'" let ?o1 = "outf_fg h1"
  let ?e2' = "edge_fg h2'" let ?f2' = "flow_fg h2'"
  let ?N = "dom_fg h" let ?e = "edge_fg h" let ?f = "flow_fg h" let ?i = "inf_fg h"
  let ?N2 = "dom_fg h2" let ?e2 = "edge_fg h2" let ?f2 = "flow_fg h2" let ?i2 = "inf_fg h2"
  let ?N2' = "dom_fg h2'" let ?e2' = "edge_fg h2'" let ?f2' = "flow_fg h2'" let ?i2' = "inf_fg h2'"
  let ?N' = "dom_fg h'" let ?e' = "edge_fg h'" let ?f' = "flow_fg h'" let ?i' = "inf_fg h'"
  let ?o' = "outf_fg h'"
  let ?y = "hd (as @ [b])" let ?y' = "hd (xs @ as @ [b])"
  let ?b = "chain ?e' as b"

  have "?i1 ?y' = (\<lambda>x. ?i x + ?o2 x) ?y'"
    using flow_eq_to_sum[of h1 h2] \<open>h = h1 + h2\<close> \<open>h \<noteq> bot\<close> \<open>?y' \<in> ?N1\<close> by blast
  then have "chain ?e xs ?y (?i1 ?y') = ((chain ?e xs ?y) o (\<lambda>x. ?i x + ?o2 x)) ?y'"
    by simp
  then have **: "chain ?e xs ?y (?i ?y') + chain ?e xs ?y (?o2 ?y') \<noteq> 0"
    using descend(3) fun_dist_right[of "chain ?e xs ?y"]
    by (metis (no_types, lifting) add_eq_0_iff_both_eq_0 append_Nil chain.simps(1)
        chain_append_not_zero(1) descend.prems(20) descend.prems(21) descend.prems(31)
        endo_f_n0_n0_closed)

  have nez: "?b (chain ?e xs ?y (?o2 ?y')) \<noteq> 0"
    using descend by blast

  have "?b (chain ?e xs ?y (?o2 ?y')) = ?b (chain ?e xs ?y (\<Sum>z \<in> ?N2. ?e2 z ?y' (?f2 z)))"
    apply (subst outf_fg_unfold[of h2 ?y'])
    using \<open>h = h1 + h2\<close> \<open>h \<noteq> bot\<close> plus_fg_ops_exist[of h1 h2] \<open>?y' \<in> ?N1\<close> plus_fg_dom_disj[of h1 h2] by blast+
  also have "... = ?b (\<Sum>z \<in> ?N2. chain ?e xs ?y (?e2 z ?y' (?f2 z)))"
    apply (subst fun_dist_right''[where g="chain ?e xs ?y" and E="E"])
    using dom_fg_finite endo_chain_closed[of ?e E xs ?y] descend by blast+
  also have "... = ?b (\<Sum>z \<in> ?N2. chain ?e xs ?y (?e2 z ?y' (\<Sum>xs'\<in>l_lists' ?N2 (card ?N2). chain ?e2 xs' z (?i2 (hd (xs' @ [z]))))))"
    apply (subst sum.cong, simp)
    apply (subst unroll_flow_eq_eff_acyclic'[of ?N2 ?e2 ?f2 ?i2 E "card ?N2"], simp_all add: descend)
    using \<open>?N2 = ?N2'\<close> \<open>eff_acyclic' h2\<close> unfolding eff_acyclic'_def apply simp
     apply (metis descend.prems(23) disjoint_iff_not_equal dom_fg_bot dom_fi_int_fg inf_bot_right nbot_fg_to_flow_eq2')
    by (metis Suc_leI card_gt_0_iff dom_fg_finite equals0D)
  also have "... = ?b (\<Sum>z \<in> ?N2. \<Sum>xs'\<in>l_lists' ?N2 (card ?N2). chain ?e xs ?y (?e2 z ?y' (chain ?e2 xs' z (?i2 (hd (xs' @ [z]))))))"
    apply (subst (2) sum.cong, simp)
    apply (subst fun_dist_right''[where xs="l_lists' ?N2 (card ?N2)" and E="E" and g="?e2 _ ?y'"], simp, simp add: descend, simp add: descend)
     apply (subst fun_dist_right''[where xs="l_lists' ?N2 (card ?N2)" and E="E" and g="chain ?e xs ?y"], simp_all add: descend)
    apply (rule endo_chain_closed, simp_all add: descend)
    using descend by blast
  also have "... = ?b (\<Sum>z \<in> ?N2. \<Sum>xs'\<in>l_lists' ?N2 (card ?N2). chain ?e xs ?y (?e z ?y' (chain ?e2 xs' z (?i2 (hd (xs' @ [z]))))))"
    using edge_fg_plus_fg_on2'[of h1 h2, symmetric] \<open>h = h1 + h2\<close> \<open>h \<noteq> bot\<close>  by simp
  also have "... = ?b (\<Sum>z \<in> ?N2. \<Sum>xs'\<in>l_lists' ?N2 (card ?N2). chain ?e xs ?y (?e z ?y' (chain ?e xs' z (?i2 (hd (xs' @ [z]))))))"
    apply (subst sum.cong, simp, subst sum.cong, simp)
    apply (subst chain_cong'[where f="?e2" and g="?e" and N="?N2"])
    using edge_fg_plus_fg_on2[of h1 h2] \<open>h = h1 + h2\<close> \<open>h \<noteq> bot\<close>
    unfolding l_lists'_def by simp_all
  also have "... = ?b (\<Sum>z \<in> ?N2. \<Sum>xs'\<in>l_lists' ?N2 (card ?N2). chain ?e xs ?y (chain ?e (xs' @ [z]) ?y' (?i2 (hd (xs' @ [z])))))"
    by (subst sum_cong2, auto, subst chain_extend_right[symmetric], auto)
  also have "... = ?b (\<Sum>z \<in> ?N2. \<Sum>xs'\<in>l_lists' ?N2 (card ?N2). chain ?e (xs' @ [z] @ xs) ?y (?i2 (hd (xs' @ [z]))))"
    apply (subst sum_cong2, auto)
    subgoal for z xs'
    using chain_append_nonempty[where f="?e" and xs="xs' @ [z]" and ys="xs"] by simp
    done
  also have "... = ?b (\<Sum>xs'\<in>l_lists ?N2 (card ?N2 + 1). chain ?e (xs' @ xs) ?y (?i2 (hd xs')))"
    apply (subst sum.cartesian_product)
    apply (subst sum.reindex_cong[where l="\<lambda>xs. (last xs, butlast xs)" and A="?N2 \<times> l_lists' ?N2 (card ?N2)" and B="l_lists ?N2 (card ?N2 + 1)"], intro inj_onI)
    unfolding l_lists_def apply auto[1]  apply (metis Suc_le_lessD append_butlast_last_id length_greater_0_conv)
    unfolding l_lists'_def l_lists_def image_def
      apply auto
    subgoal for a b by (rule exI[where x="b @ [a]"], simp)
    using Suc_le_lessD last_in_set apply blast
     apply (simp add: in_set_butlastD subsetD)
    by (smt One_nat_def append_Cons append_butlast_last_id append_eq_append_conv2 append_self_conv list.size(3) not_one_le_zero)
  finally have "?b (\<Sum>xs'\<in>l_lists ?N2 (card ?N2 + 1). chain ?e (xs' @ xs) ?y (?i2 (hd xs'))) \<noteq> 0"
    using nez by simp
  then have "(\<Sum>xs'\<in>l_lists ?N2 (card ?N2 + 1). ?b (chain ?e (xs' @ xs) ?y (?i2 (hd xs')))) \<noteq> 0"
    apply (subst (asm) fun_dist_right''[where xs="l_lists ?N2 (card ?N2 + 1)" and E=E])
    using l_lists_finite[of ?N2] dom_fg_finite[of h2] apply auto[1]
    using endo_chain_closed[of ?e' E] \<open>End_closed E\<close> \<open>id \<in> E\<close> \<open>\<forall>x y. edge_fg h' x y \<in> E\<close> by blast+
  then obtain xs' where xs'props:
    "xs' \<in> l_lists ?N2 (card ?N2 + 1)" "?b (chain ?e (xs' @ xs) ?y (?i2 (hd xs'))) \<noteq> 0"
    using sum.not_neutral_contains_not_neutral by blast
  then have "length xs' \<ge> 1" "length xs' \<le> card ?N2" "xs' \<noteq> []" "set xs' \<subseteq> ?N2"
    unfolding l_lists_def by auto

  have xsin: "hd xs' \<in> ?N2"
    using xs'props set_hd_in unfolding l_lists_def by blast

  have "\<exists>ys. ?b (chain ?e (xs' @ xs) ?y (chain ?e' ys (hd ((xs' @ xs) @ as @ [b])) (?i' (hd (ys @ (xs' @ xs) @ as @ [b]))))) \<noteq> 0
              \<and> chain ?e' ys (hd ((xs' @ xs) @ as @ [b])) (?i' (hd (ys @ (xs' @ xs) @ as @ [b]))) \<le> ?i2' (hd ((xs' @ xs) @ as @ [b])) \<and>
             set ys \<subseteq> dom_fg h'"
  proof (cases "?b (chain ?e (xs' @ xs) ?y (?i' (hd (xs' @ xs @ as @ [b])))) \<noteq> 0")
    case True
    show ?thesis
      apply (rule exI[where x="[]"])
      using True \<open>h' = h1' + h2'\<close>  apply simp
      apply (rule inf_fg_le_inf_fg2[of h1' h2'])
      using descend.prems(15) apply blast
      using \<open>xs' \<noteq> []\<close> descend.prems(25) xsin(1) apply auto[1]
      by auto
  next
    case False
    then have Y': "?b (chain (edge_fg h) (xs' @ xs) ?y (?i' (hd xs'))) = 0"
      using \<open>xs' \<noteq> []\<close> by simp
    have Y: "?i2 (hd xs') = ?i (hd xs') + ?o1 (hd xs')"
      using flow_eq_to_sum[of h2 h1] \<open>h = h1 + h2\<close> \<open>h \<noteq> bot\<close> \<open>hd xs' \<in> ?N2\<close> \<open>xs' \<noteq> []\<close>
      by (simp add: algebra_simps)
    have X: "?b (chain ?e (xs' @ xs) ?y (?o1 (hd xs'))) \<noteq> 0"
      using xs'props(2)
      apply (subst (asm) Y)
      apply (subst (asm) endo_sum_closed[where E=E])
        apply (fold comp_def, rule End_closedE(2), simp_all add: descend)
        apply (rule endo_chain_closed, auto simp: descend)
      using descend apply blast
        apply (rule endo_chain_closed, auto simp: descend)
      using descend apply blast
      using Y' descend by auto
    have inf2: "?i2 = ?i2'"
      by (metis descend.prems(23) int_fg_to_inf_fg)
    show ?thesis
      apply (subst inf2[symmetric])
      apply (rule descend(2)[of "xs' @ xs" h' h h1 h2 h2' h1'])
      using \<open>xs' \<noteq> []\<close> X apply auto[2]
      using plus_fg_dom_un[of h1 h2] \<open>h = h1 + h2\<close> \<open>h \<noteq> bot\<close> \<open>set xs' \<subseteq> ?N2\<close> \<open>set xs \<subseteq> ?N\<close> apply auto[1]
      using descend apply blast+
      using \<open>h = h1 + h2\<close> apply (simp add: algebra_simps)
      using \<open>h' = h1' + h2'\<close> apply (simp add: algebra_simps)
      using \<open>xs' \<noteq> []\<close> \<open>set xs' \<subseteq> ?N2\<close> apply auto[1]
      using descend apply blast+
      done
  qed
  then obtain ys' where ys'def: "?b (chain ?e (xs' @ xs) ?y (chain ?e' ys' (hd (xs' @ xs @ as @ [b])) (?i' (hd (ys' @ xs' @ xs @ as @ [b]))))) \<noteq> 0"
      "chain ?e' ys' (hd (xs' @ xs @ as @ [b])) (?i' (hd (ys' @ xs' @ xs @ as @ [b]))) \<le> ?i2' (hd (xs' @ xs @ as @ [b]))" "set ys' \<subseteq> dom_fg h'"
    using append_assoc by auto

  have xsin: "hd (xs @ [?y]) \<in> -?N2" "hd xs' \<in> ?N2"
    using xsin \<open>hd (xs @ as @ [b]) \<in> ?N1\<close>
     apply simp_all
    by (metis descend.prems(11) descend.prems(14) dom_fg_plus_fg_iff dom_fg_plus_fg_subs1 subsetD)

  have S1: "hd xs' \<noteq> hd (xs @ [?y])"
    using xsin by auto

  have "?e' = ?e2' on ?N2'"
    using edge_fg_plus_fg_on2[of h1' h2']
    using descend by blast

  let ?m = "chain ?e' ys' (hd (xs' @ xs @ as @ [b])) (?i' (hd (ys' @ xs' @ xs @ as @ [b])))"
  have "\<forall>m\<le>inf_fg h2 (hd xs'). cap_fg h2 (hd xs') (hd (xs @ [?y])) m = cap_fg h2' (hd xs') (hd (xs @ [?y])) m"
    using xsin \<open>\<forall>n\<in>dom_fg h2. \<forall>n' \<in> -dom_fg h2'. \<forall>m \<le> inf_fg h2 n. cap_fg h2 n n' m = cap_fg h2' n n' m\<close>
      \<open>dom_fg h2 = dom_fg h2'\<close> by blast
  moreover have inf2eq: "inf_fg h2' = inf_fg h2" "inf_fg h1' = inf_fg h1"
    using \<open>int_fg h1 = int_fg h1'\<close> \<open>int_fg h2 = int_fg h2'\<close> by (metis int_fg_to_inf_fg)+
  ultimately have cap_eq: "cap_fg h2 (hd xs') (hd (xs @ [?y])) ?m = cap_fg h2' (hd xs') (hd (xs @ [?y])) ?m"
    using  ys'def(2) \<open>xs' \<noteq> []\<close> by auto

  from ys'def have "0 < ?b (chain ?e xs ?y (chain ?e xs' (hd (xs @ [?y])) (chain ?e' ys' (hd (xs' @ xs @ as @ [b])) (?i' (hd (ys' @ xs' @ xs @ as @ [b]))))))"
    apply (subst (asm) chain_append_nonempty)
    unfolding comp_def
    using gr_zeroI by blast
  also have "... \<le> ?b (chain ?e xs ?y (cap_fg h2 (hd (xs' @ [(hd (xs @ [?y]))])) (hd (xs @ [?y])) (chain ?e' ys' (hd (xs' @ xs @ as @ [b])) (?i' (hd (ys' @ xs' @ xs @ as @ [b]))))))"
    apply (rule pos_endo_mono'_closed[where f="?b" and E=E])
      apply (rule pos_endo_mono'_closed[where f="chain ?e xs ?y" and E=E])
        apply (subst \<open>h = h1 + h2\<close>, subst chain_cong''[OF edge_fg_plus_fg_on2])
    using descend apply blast
    using xs'props unfolding l_lists_def apply blast
       apply (rule chain_le_cap'[where E=E])
    using xs'props unfolding l_lists_def apply blast
    using xs'props unfolding l_lists_def apply auto[1]
    using xs'props unfolding l_lists_def apply auto[1]
            apply (fact dom_fg_finite)
    using descend apply blast
          apply simp
    using descend apply blast+
    apply (rule endo_chain_closed)
    using descend apply blast+
    apply (rule endo_chain_closed)
    using descend by blast+
  also have "... = ?b (chain ?e xs ?y (cap_fg h2' (hd xs') (hd (xs @ [?y])) (chain ?e' ys' (hd (xs' @ xs @ as @ [b])) (?i' (hd (ys' @ xs' @ xs @ as @ [b]))))))"
    using cap_eq \<open>xs' \<noteq> []\<close> by simp
  also have "... = ?b (chain ?e xs ?y ((\<delta> (hd xs') (hd (xs @ [?y])) + (\<Sum>ns\<in>l_lists' ?N2' (card ?N2'). chain2 ?e2' (hd xs') ns (hd (xs @ [?y])))) (chain ?e' ys' (hd (xs' @ xs @ as @ [b]))(?i' (hd (ys' @ xs' @ xs @ as @ [b]))))))"
    apply (subst cap_unrolled_closed[where E=E], simp_all)
    using descend apply blast+
    using descend.prems(25) xsin(2) by blast
  also have "... = ?b (chain ?e xs ?y (((\<Sum>ns\<in>l_lists' ?N2' (card ?N2'). chain2 ?e2' (hd xs') ns (hd (xs @ [?y])))) (chain ?e' ys' (hd (xs' @ xs @ as @ [b]))(?i' (hd (ys' @ xs' @ xs @ as @ [b]))))))"
    using \<open>hd xs' \<noteq> hd (xs @ [?y])\<close> \<open>xs' \<noteq> []\<close> unfolding \<delta>_def by simp
  also have "... = ?b (\<Sum>ns\<in>l_lists' ?N2' (card ?N2'). chain ?e xs ?y (chain2 ?e2' (hd xs') ns (hd (xs @ [?y])) (chain ?e' ys' (hd (xs' @ xs @ as @ [b])) (?i' (hd (ys' @ xs' @ xs @ as @ [b]))))))"
    apply (subst fun_dist_right''[symmetric, where E=E and xs="l_lists' ?N2' (card ?N2')" and g="chain ?e xs ?y"], simp_all)
      apply (rule endo_chain_closed)
    using descend apply blast+
    by (subst plus_fun_apply_iterated[OF l_lists'_finite[OF dom_fg_finite]], simp)
  also have "... = (\<Sum>ns\<in>l_lists' ?N2' (card ?N2'). ?b (chain ?e xs ?y (chain2 ?e2' (hd xs') ns (hd (xs @ [?y])) (chain ?e' ys' (hd (xs' @ xs @ as @ [b])) (?i' (hd (ys' @ xs' @ xs @ as @ [b])))))))"
    apply (subst fun_dist_right''[where E=E and xs="l_lists' ?N2' (card ?N2')"], simp_all)
    using endo_chain_closed[of "edge_fg h'" E as b] descend by blast+
  finally have "(\<Sum>ns\<in>l_lists' ?N2' (card ?N2').  ?b (chain ?e xs ?y (chain2 ?e2' (hd xs') ns (hd (xs @ [?y])) (chain ?e' ys' (hd (xs' @ xs @ as @ [b])) (?i' (hd (ys' @ xs' @ xs @ as @ [b]))))))) \<noteq> 0"
    using zero_less_iff_neq_zero by blast
  then obtain ys where ys: "ys \<in> l_lists' ?N2' (card ?N2')" "?b (chain ?e xs ?y (chain2 ?e2' (hd xs') ys (hd (xs @ [?y])) (chain ?e' ys' (hd (xs' @ xs @ as @ [b])) (?i' (hd (ys' @ xs' @ xs @ as @ [b])))))) \<noteq> 0"
    by auto
  then have "?b (chain ?e xs ?y (chain2 ?e2' (hd xs') ys (hd (xs @ [?y])) (chain ?e' ys' (hd (xs' @ xs @ as @ [b])) (?i' (hd (ys' @ xs' @ xs @ as @ [b])))))) \<noteq> 0"
    by simp
  then have "?b (chain ?e xs ?y (chain ?e2' (hd xs' # ys) (hd (xs @ [?y])) (chain ?e' ys' (hd (xs' @ xs @ as @ [b])) (?i' (hd (ys' @ xs' @ xs @ as @ [b])))))) \<noteq> 0"
    by (simp add: chain_chain2)
  then have "?b (chain ?e xs ?y (chain ?e' (hd xs' # ys) (hd (xs @ [?y])) (chain ?e' ys' (hd (xs' @ xs @ as @ [b])) (?i' (hd (ys' @ xs' @ xs @ as @ [b])))))) \<noteq> 0"
    apply (subst (asm) chain_cong[symmetric, OF on_eq_superset[of "set (hd xs' # ys)", OF _ edge_fg_plus_fg_on2[of h1' h2']]])
    using \<open>h' = h1' + h2'\<close> \<open>h' \<noteq> bot\<close> \<open>set xs' \<subseteq> dom_fg h2\<close> \<open>?N2 = ?N2'\<close> ys xsin unfolding l_lists'_def by auto
  then have T: "?b (chain ?e xs ?y (chain ?e' (ys' @ hd xs' # ys) (hd (xs @ [?y])) (?i' (hd (ys' @ xs' @ xs @ as @ [b]))))) \<noteq> 0"
    by (subst chain_append, simp_all add: \<open>xs' \<noteq> []\<close>)

  have "chain ?e' (hd xs' # ys) (hd (xs @ as @ [b])) (chain ?e' ys' (hd (xs' @ xs @ as @ [b])) (?i' (hd (ys' @ xs' @ xs @ as @ [b])))) =
            chain ?e2' (hd xs' # ys) (hd (xs @ as @ [b])) (chain ?e' ys' (hd (xs' @ xs @ as @ [b])) (?i' (hd (ys' @ xs' @ xs @ as @ [b]))))"
    apply (subst \<open>h' = h1' + h2'\<close>)
    apply (subst chain_cong[OF on_eq_superset[of "set (hd xs' # ys)", OF _ edge_fg_plus_fg_on2]])
    using \<open>h' = h1' + h2'\<close> \<open>h' \<noteq> bot\<close> apply simp_all
    using \<open>set xs' \<subseteq> dom_fg h2\<close> \<open>?N2 = ?N2'\<close> ys xsin unfolding l_lists'_def by auto
  also have "... \<le> chain ?e2' (hd xs' # ys) (hd (xs @ as @ [b])) (inf_fg h2' (hd (xs' @ xs @ as @ [b])))"
    apply (rule pos_endo_mono'_closed[OF ys'def(2), where f="chain ?e2' (hd xs' # ys) (hd (xs @ as @ [b]))" and E=E])
    using endo_chain_closed[of ?e2' E] descend by blast+
  also have "... \<le> inf_fg h1' (hd (xs @ as @ [b]))"
    using \<open>xs' \<noteq> []\<close> apply simp
    apply (subst chain_inf_fg_le_inf_fg[of h' E h2' "hd xs' # ys" "hd (xs @ as @ [b])" h1', simplified])
    using \<open>h' = h1' + h2'\<close> \<open>h' \<noteq> bot\<close> apply (simp add: algebra_simps)
    using descend apply blast+
    using \<open>set xs' \<subseteq> dom_fg h2\<close> \<open>?N2 = ?N2'\<close> ys unfolding l_lists'_def apply auto[1]
    using descend.prems(13,24) \<open>h' = h1' + h2'\<close> \<open>h' \<noteq> bot\<close> plus_fg_comm descend by blast+
  finally have T': "chain (edge_fg h') (ys' @ hd xs' # ys) (hd (xs @ as @ [b])) (inf_fg h' (hd ((ys' @ xs') @ xs @ as @ [b]))) \<le> inf_fg h1' (hd (xs @ as @ [b]))"
    by (simp add: \<open>xs' \<noteq> []\<close> chain_append_nonempty)

  have S2: "hd ((ys' @ xs') @ xs @ as @ [b]) = hd ((ys' @ hd xs' # ys) @ xs @ as @ [b])"
    using \<open>xs' \<noteq> []\<close> by (simp add: hd_append)

  show ?case
    apply (rule exI[where x="ys' @ hd xs' # ys"], intro conjI)
    using T \<open>xs' \<noteq> []\<close> ys'def 
      apply (smt Nil_is_append_conv append_self_conv2 hd_append2 list.discI list.sel(1))
    using T' inf2eq S2 apply auto
    using \<open>set xs' \<subseteq> ?N2\<close> \<open>h' = h1' + h2'\<close> \<open>h' \<noteq> bot\<close> \<open>xs' \<noteq> []\<close> ys'def ys descend.prems(25) xsin(2)
    unfolding l_lists'_def by auto
qed

lemma eff_acyclic_sourced_path_in_bigraph_case:
  fixes E :: "('m \<Rightarrow> 'm :: pos_cancel_comm_monoid_add) set"
  assumes ea: "\<not> eff_acyclic' (h1' + h2')" "eff_acyclic' (h1 + h2)" "eff_acyclic' h1"
    "eff_acyclic' h2" "eff_acyclic' h1'" "eff_acyclic' h2'"
    and def: "h1 + h2 \<noteq> bot" "h1' + h2' \<noteq> bot"
    and dom: "End_closed E" "\<forall>x y. edge_fg (h1' + h2') x y \<in> E" "\<forall>x y. edge_fg h1' x y \<in> E" "id \<in> E"
      "\<forall>x y. edge_fg h1 x y \<in> E" "\<forall>x y. edge_fg h2 x y \<in> E" "\<forall>x y. edge_fg h1' x y \<in> E"
      "\<forall>x y. edge_fg h2' x y \<in> E" "\<forall>x y. edge_fg (h1 + h2) x y \<in> E" "(\<lambda>_. 0) \<in> E"
    and inf: "inf_fg (h1 + h2) = inf_fg (h1' + h2')" "int_fg h1 = int_fg h1'" "int_fg h2 = int_fg h2'"
    and ext:
      "\<forall>n \<in> dom_fg h1. \<forall>n' \<in> -dom_fg h1'. \<forall>m \<le> inf_fg h1 n. cap_fg h1 n n' m = cap_fg h1' n n' m"
      "\<forall>n \<in> dom_fg h2. \<forall>n' \<in> -dom_fg h2'. \<forall>m \<le> inf_fg h2 n. cap_fg h2 n n' m = cap_fg h2' n n' m"
    and cycle_ne0: "k \<ge> 1" "xs \<in> k_lists (dom_fg (h1' + h2')) k"
      "chain (edge_fg (h1' + h2')) xs (hd xs) (flow_fg (h1' + h2') (hd xs)) \<noteq> 0"
    and True: "hd xs \<in> dom_fg h1'"
  shows "\<exists>xs y. chain (edge_fg (h1' + h2')) xs y (inf_fg (h1 + h2) (hd xs)) \<noteq> 0 \<and>
                y \<in> set  xs \<and> set xs \<subseteq> dom_fg (h1' + h2')"
proof -
  let ?h' = "h1' + h2'" let ?h = "h1 + h2"
  let ?N' = "dom_fg ?h'"
  let ?e' = "edge_fg ?h'" let ?e = "edge_fg ?h"
  let ?f' = "flow_fg ?h'"
  let ?N1' = "dom_fg h1'" let ?N2' = "dom_fg h2'"
  let ?e1' = "edge_fg h1'" let ?f1' = "flow_fg h1'"
  let ?i' = "inf_fg ?h'" let ?o' = "outf_fg ?h'" let ?i = "inf_fg ?h" let ?o2' = "outf_fg h2'"
  let ?i1' = "inf_fg h1'" let ?i2 = "inf_fg h2"
  let ?e1' = "edge_fg h1'" let ?e2 = "edge_fg h2"
  let ?o2 = "outf_fg h2" let ?N2' = "dom_fg h2'" let ?N2 = "dom_fg h2" let ?N1 = "dom_fg h1"
  let ?N1' = "dom_fg h1'"

  have xs_ne: "xs \<noteq> []" "length xs \<ge> 1"
    using cycle_ne0 unfolding k_lists_def by auto

  have domeq: "?N2 = ?N2'" "?N1 = ?N1'"
    by (metis dom_fi_int_fg inf)+

  have "?N1' \<inter> ?N2' = {}" "set xs \<subseteq> ?N1' \<union> ?N2'"
    using def cycle_ne0 unfolding k_lists_def by auto
  moreover have "?f' (hd xs) = ?f1' (hd xs)"
    using flow_fg_plus_fg_on1[of h1' h2'] True assms by simp
  moreover have "chain (edge_fg (h1' + h2')) xs (hd xs) \<in> E"
    using endo_chain_closed assms by simp
  ultimately obtain xs' where xs':
    "chain ?e' xs (hd xs) (chain ?e1' xs' (hd xs) (?i1' (if xs' \<noteq> [] then hd xs' else hd xs))) \<noteq> 0"
    "set xs' \<subseteq> ?N1'"
    using cycle_ne0 eff_acyclic_flow_is_sourced[of h1' "chain ?e' xs (hd xs)" "hd xs" E] ea dom
    by auto
  moreover have "?i1' = (\<lambda>x. ?i' x + ?o2' x) on ?N1'"
    using flow_eq_to_sum[of h1' h2'] assms by simp
  ultimately have
    "chain ?e' xs (hd xs) (chain ?e' xs' (hd xs) (?i' (hd (xs' @ xs)) + ?o2' (hd (xs' @ xs)))) \<noteq> 0"
    apply (subst chain_cong[of xs' ?e' ?e1'])
     apply (simp add: True def(2) edge_fg_plus_fg_on1 subsetD)
    by (smt True hd_append2 hd_in_set self_append_conv2 subsetD)
  then have "chain ?e' xs (hd xs) (chain ?e' xs' (hd xs) (?i' (hd (xs' @ xs)))) + 
                 chain ?e' xs (hd xs) (chain ?e' xs' (hd xs) (?o2' (hd (xs' @ xs)))) \<noteq> 0"
    apply (subst (asm) endo_sum_closed[where f="chain ?e' xs' (hd xs)" and E=E])
      apply (simp add: dom endo_chain_closed)
    using assms apply simp
    using \<open>chain (edge_fg (h1' + h2')) xs (hd xs) \<in> E\<close> dom(1) endo_sum_closed by fastforce
  then consider (a) "chain ?e' xs (hd xs) (chain ?e' xs' (hd xs) (?i' (hd (xs' @ xs)))) \<noteq> 0" |
    (b) "chain ?e' xs (hd xs) (chain ?e' xs' (hd xs) (?o2' (hd (xs' @ xs)))) \<noteq> 0" by auto
  then show ?thesis
  proof cases
    case a
    then have *: "chain ?e' (xs' @  xs) (hd xs) (?i' (hd (xs' @ xs))) \<noteq> 0"
      using chain_append[of  xs ?e' xs' "last xs"]
      unfolding comp_def
      by (simp add: chain_append_nonempty xs_ne)
    show ?thesis
      apply (rule exI[where x="xs' @ xs"])
      apply (rule exI[where x="hd xs"])
      apply (intro conjI)
      using * xs_ne inf \<open>xs \<noteq> []\<close> apply simp
      using \<open>xs \<noteq> []\<close> apply simp
      using \<open>set xs \<subseteq> ?N1' \<union> ?N2'\<close> \<open>h1' + h2' \<noteq> bot\<close> xs' by auto
  next
    case b
    then have X: "chain ?e' (xs' @ xs) (hd xs) (?o2 (hd (xs' @ xs))) \<noteq> 0"
      apply (subst chain_append_nonempty) using \<open>xs \<noteq> []\<close>
      by (metis def hd_append2 inf(3) outf_fg_eqI plus_fg_ops_exist)
    have "\<exists>ys. chain ?e' (xs' @ xs) (hd xs) (chain ?e' ys (hd (xs' @ xs @ [hd xs])) (?i (hd (ys @ xs' @ xs @ [hd xs])))) \<noteq> 0 \<and>
     chain (edge_fg (h1' + h2')) ys (hd (xs' @ xs @ [hd xs])) (inf_fg (h1 + h2) (hd (ys @ xs' @ xs @ [hd xs]))) \<le> inf_fg h1 (hd (xs' @ xs @ [hd xs])) \<and>
     set ys \<subseteq> dom_fg h1' \<union> dom_fg h2'"
      apply (rule eff_acyclic_sourced_path_in_bigraph'[of ?h' "xs' @ xs" "hd xs" ?h "[]" h2 h1 h1' h2' E "card (dom_fg (h1 + h2))", simplified])
      using X \<open>xs \<noteq> []\<close> apply (metis hd_append2 self_append_conv2)
      using True apply blast
      using ea dom apply blast+
      using \<open>?N1 = ?N1'\<close> ext apply simp
      using \<open>?N2 = ?N2'\<close>[symmetric] ext apply simp
                      apply (metis True \<open>set xs' \<subseteq> dom_fg h1'\<close> hd_append2 hd_in_set self_append_conv2 subsetD xs_ne(1))
      using ea dom def inf apply blast+
           apply (metis dom_fi_int_fg inf(2))
          apply (metis dom_fi_int_fg inf(3))
      using inf dom apply simp_all
      by (metis \<open>set xs \<subseteq> dom_fg h1' \<union> dom_fg h2'\<close> \<open>set xs' \<subseteq> dom_fg h1'\<close> sup.coboundedI1)
    then obtain ys where ys: "chain ?e' (xs' @ xs) (hd xs) (chain ?e' ys (hd (xs' @ xs @ [hd xs])) (?i (hd (ys @ xs' @ xs @ [hd xs])))) \<noteq> 0"
      "set ys \<subseteq> dom_fg h1' \<union> dom_fg h2'"
      by blast
    then have T: "chain ?e' (ys @ xs' @ xs) (hd xs) (?i (hd (ys @ xs' @ xs @ [hd xs]))) \<noteq> 0"
      using chain_append_nonempty[symmetric, of ?e' "xs' @ xs" "hd xs" ys "?i (hd (ys @ xs' @ xs @ [hd xs]))"]
      by simp
    show ?thesis
      apply (rule exI[where x="ys @ xs' @ xs"])
      apply (rule exI[where x="hd xs"])
      apply (intro conjI)
      using T \<open>xs \<noteq> []\<close> apply (metis append_self_conv2 hd_append2)
      using \<open>xs \<noteq> []\<close> \<open>set xs \<subseteq> dom_fg h1' \<union> dom_fg h2'\<close> \<open>set xs' \<subseteq> dom_fg h1'\<close> \<open>h1' + h2' \<noteq> bot\<close> ys by auto
  qed
qed

lemma eff_acyclic_sourced_path_in_bigraph:
  fixes E :: "('m \<Rightarrow> 'm :: pos_cancel_comm_monoid_add) set"
  assumes ea: "\<not> eff_acyclic' (h1' + h2')" "eff_acyclic' (h1 + h2)" "eff_acyclic' h1"
    "eff_acyclic' h2" "eff_acyclic' h1'" "eff_acyclic' h2'"
    and def: "h1 + h2 \<noteq> bot" "h1' + h2' \<noteq> bot"
    and dom: "End_closed E" "\<forall>x y. edge_fg (h1' + h2') x y \<in> E"
      "\<forall>x y. edge_fg h1' x y \<in> E" "id \<in> E"
      "\<forall>x y. edge_fg h1 x y \<in> E" "\<forall>x y. edge_fg h2 x y \<in> E"
      "\<forall>x y. edge_fg h1' x y \<in> E" "\<forall>x y. edge_fg h2' x y \<in> E"
      "\<forall>x y. edge_fg (h1 + h2) x y \<in> E" "(\<lambda>_. 0) \<in> E"
    and inf: "inf_fg (h1 + h2) = inf_fg (h1' + h2')"
      "int_fg h1 = int_fg h1'" "int_fg h2 = int_fg h2'"
    and ext: "\<forall>n \<in> dom_fg h1. \<forall>n' \<in> -dom_fg h1'. \<forall>m \<le> inf_fg h1 n.
              cap_fg h1 n n' m = cap_fg h1' n n' m"
      "\<forall>n \<in> dom_fg h2. \<forall>n' \<in> -dom_fg h2'. \<forall>m \<le> inf_fg h2 n.
       cap_fg h2 n n' m = cap_fg h2' n n' m"
  shows "\<exists>xs y. chain (edge_fg (h1' + h2')) xs y (inf_fg (h1 + h2) (hd xs)) \<noteq> 0 \<and>
    y \<in> set  xs \<and> set xs \<subseteq> dom_fg (h1' + h2')"
proof -
  let ?h' = "h1' + h2'"
  let ?N' = "dom_fg ?h'" let ?e' = "edge_fg ?h'" let ?f' = "flow_fg ?h'"

  obtain k xs where cycle_ne0: "k \<ge> 1" "xs \<in> k_lists ?N' k" "chain ?e' xs (hd xs) (?f' (hd xs)) \<noteq> 0"
    using ea unfolding eff_acyclic'_def eff_acyclic_def by blast

  show ?thesis
  proof (cases "hd xs \<in> dom_fg h1'")
    case True
    show ?thesis
      using eff_acyclic_sourced_path_in_bigraph_case[of h1' h2' h1 h2] assms True cycle_ne0
      by blast
  next
    case False
    then have "hd xs \<in> dom_fg h2'"
      by (metis (mono_tags, lifting) UnE cycle_ne0 def k_lists_def mem_Collect_eq plus_fg_dom_un
          set_hd_in)
    then show ?thesis
      using eff_acyclic_sourced_path_in_bigraph_case[of h2' h1' h2 h1] assms cycle_ne0
      by (smt add.commute)
  qed
qed

end
