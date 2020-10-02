\<^marker>\<open>creator Bernhard Pöttinger\<close>

theory Effectively_Acyclic_Maintain
  imports Effectively_Acyclic Effectively_Acyclic_Sourced_Path Effectively_Acyclic_Approximations
    Effectively_Acyclic_Equal_Capacity
begin

paragraph \<open>Summary\<close>
text \<open>This theory proves @{cite \<open>th. 3\<close> krishna20} / @{cite \<open>th. 3.38\<close> krishna19a}.

The proof structure of theorem 3 is:
theorem 3 (@{term maintain_eff_acyclic_dom})
- case @{term "dom_fg h1 = dom_fg h1'"} (@{term maintain_eff_acyclic_dom_eq})
  - Effective Acyclicity (@{term maintain_eff_acyclic_dom_eq'})
  - Subflowpreserving Extension (part of @{term maintain_eff_acyclic_dom})
- case @{term "dom_fg h1 \<subset> dom_fg h1'"} (@{term maintain_eff_acyclic_dom_ne})
\<close>
section \<open>Proof of Theorem 3.38\<close>

text \<open>Auxiliary lemma\<close>

lemma alt_edge:
  fixes h h1 h2 :: "('n,'m :: cancel_comm_monoid_add) fg"
  assumes "\<forall>x y. edge_fg h2 x y \<in> E" "\<forall>x y. edge_fg h1 x y \<in> E" "End_closed E" "xs \<noteq> []"
  shows "\<And>x y. edge_fg (alt h1 h2 xs) x y \<in> E"
proof (goal_cases)
  case (1 x y)
  have "alt h1 h2 xs \<in> {h1,h2}" using alt_in[of xs h1 h2] assms by simp
  then consider (a) "alt h1 h2 xs = h1" | (b) "alt h1 h2 xs = h2" by blast
  then show ?case
  proof cases
    case a
    with assms show ?thesis by simp
  next
    case b
    with assms show ?thesis by simp
  qed
qed

text \<open>Part on effective acyclicity of Case 1 (@{term "h1 = dom_fg h1'"}) of Theorem 3 in
@{cite krishna20}, factored out to address symmetric cases\<close>

lemma maintain_eff_acyclic_dom_eq':
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "pointwise_reduced E" "h = h1 + h2" "h \<noteq> bot" "h' = h1' + h2'" "h' \<noteq> bot" "h1' \<noteq> bot"
    "h1 \<lesssim>\<^sub>S h1'" "dom_fg h1' \<inter> dom_fg h2' = {}"
    "\<forall>n \<in> dom_fg h1' - dom_fg h1. outf_fg h2 n = 0"
    "\<forall>x y. edge_fg h x y \<in> E"
    "eff_acyclic' h" "eff_acyclic' h1" "eff_acyclic' h1'" "eff_acyclic' h2" "eff_acyclic' h2'"
    "dom_fg h1 = dom_fg h1'" "dom_fg h2 = dom_fg h2'" "End_closed E" "id \<in> E"
    "\<forall>x y. edge_fg h2 x y \<in> E" "\<forall>x y. edge_fg h1 x y \<in> E" "\<forall>x y. edge_fg h1' x y \<in> E"
    "\<forall>x y. edge_fg h2' x y \<in> E" "\<forall>x y. edge_fg (h1' + h2') x y \<in> E"
    "(\<lambda>_. 0) \<in> E" "id \<in> E"
    "\<forall>n\<in>dom_fg h1. \<forall>n'\<in>- dom_fg h1'. \<forall>m\<le>inf_fg h1 n. cap_fg h1 n n' m = cap_fg h1' n n' m"
    "\<forall>n\<in>dom_fg h2. \<forall>n'\<in>- dom_fg h2'. \<forall>m\<le>inf_fg h2 n. cap_fg h2 n n' m = cap_fg h2' n n' m"
    "\<forall>x y. edge_fg (h1 + h2) x y \<in> E"
    and nbot: "h1' + h2' \<noteq> bot" "int_fg (h1' + h2') = int_fg (h1 + h2)"
    and infeq: "inf_fg (h1' + h2') = inf_fg (h1 + h2)" "int_fg h1' = int_fg h1"
    and False: "\<not> (set ns \<subseteq> dom_fg h1' \<or> set ns \<subseteq> dom_fg h2')"
    and True: "hd ns \<in> dom_fg h1'"
    and nsdef:
    "chain (edge_fg (h1' + h2')) ns n (inf_fg (h1 + h2) (hd ns)) \<noteq> 0"
    "n \<in> set ns" "set ns \<subseteq> dom_fg (h1' + h2')"
  shows False
proof -
  have *: "h1 \<noteq> bot" "h2 \<noteq> bot" using assms plus_fg_ops_exist by metis+

  let ?h' = "h1' + h2'"
  let ?h = "h1 + h2"
  let ?e' = "edge_fg ?h'"
  let ?e1' = "edge_fg h1'"
  let ?e2' = "edge_fg h2'"
  let ?e = "edge_fg h" let ?e1 = "edge_fg h1" let ?e2 = "edge_fg h2"
  let ?f' = "flow_fg ?h'"
  let ?N' = "dom_fg ?h'"
  let ?N1 = "dom_fg h1"
  let ?N2 = "dom_fg h2"
  let ?N1' = "dom_fg h1'"
  let ?N = "dom_fg h" let ?Na = "dom_fg h1" let ?Nb = "dom_fg h2"
  let ?i = "inf_fg ?h"
  let ?i' = "inf_fg ?h'"
  let ?i1 = "inf_fg h1"
  let ?f = "flow_fg (h1 + h2)"
  let ?f1 = "flow_fg h1"
  let ?f1' = "flow_fg h1'"
  let ?i1' = "inf_fg h1'"
  let ?i2' = "inf_fg h2'"

  let ?g1 = "\<lambda>xs y. if set xs \<subseteq> ?Na then cap' (card ?Na) ?Na ?e' (hd (xs @ [y])) y else if set xs \<subseteq> ?Nb then cap' (card ?Nb) ?Nb ?e' (hd (xs @ [y])) y else 0"
  let ?g2 = "\<lambda>xs y. if set xs \<subseteq> ?Na then cap' (card ?Na) ?Na ?e1' (hd (xs @ [y])) y else if set xs \<subseteq> ?Nb then cap' (card ?Nb) ?Nb ?e2' (hd (xs @ [y])) y else 0"
  let ?g3 = "\<lambda>xs y. if set xs \<subseteq> ?Na then cap' (card ?Na) ?Na ?e1 (hd (xs @ [y])) y else if set xs \<subseteq> ?Nb then cap' (card ?Nb) ?Nb ?e2 (hd (xs @ [y])) y else 0"
  let ?altg2 = "\<lambda>h1 h2 xs y. if set xs \<subseteq> dom_fg h1 then cap' (card (dom_fg h1)) (dom_fg h1) (edge_fg h1) (hd (xs @ [y])) y else if set xs \<subseteq> dom_fg h2 then cap' (card (dom_fg h2)) (dom_fg h2) (edge_fg h2) (hd (xs @ [y])) y else 0"
  let ?altg3 = "\<lambda>h1 h2 xs y. if set xs \<subseteq> dom_fg h1 then cap' (card (dom_fg h1)) (dom_fg h1) (edge_fg h1) (hd (xs @ [y])) y else if set xs \<subseteq> dom_fg h2 then cap' (card (dom_fg h2)) (dom_fg h2) (edge_fg h2) (hd (xs @ [y])) y else 0"
  let ?g4 = "\<lambda>xs y. cap' (card ?N) ?N ?e (hd (xs @ [y])) y"
  let ?P = "\<lambda>ys. set ys \<subseteq> ?Na \<and> ys \<noteq> [] \<and> length ys \<le> card ?Na"
  let ?Q = "\<lambda>ys. set ys \<subseteq> ?Nb \<and> ys \<noteq> [] \<and> length ys \<le> card ?Nb"
  let ?altP = "\<lambda>h ys. set ys \<subseteq> dom_fg h \<and> ys \<noteq> [] \<and> length ys \<le> card (dom_fg h)"
  let ?altQ = "\<lambda>h ys. set ys \<subseteq> dom_fg h \<and> ys \<noteq> [] \<and> length ys \<le> card (dom_fg h)"
  let ?alte = "\<lambda>xs. if set xs \<subseteq> ?Na then ?e1 else ?e2"

  let ?k = "length ns"

  have dom: "dom_fg h1' \<inter> dom_fg h2' = {}" "ns \<noteq> []" "set ns \<subseteq> dom_fg h1' \<union> dom_fg h2'"
    "dom_fg h1' \<inter> dom_fg h2' = {}" "?N1 \<inter> ?N2 = {}" "?N1 \<union> ?N2 = ?N"
    using False nsdef ck_lists_props[of ns "dom_fg (h1' + h2')" ?k] nbot
    using assms apply blast
    using nsdef nbot \<open>h = h1 + h2\<close> \<open>h \<noteq> bot\<close> by auto

  with False obtain n1 n2 where ***: "n1 \<in> set ns" "n2 \<in> set ns" "n1 \<notin> dom_fg h1'"
    "n2 \<notin> dom_fg h2'" "n1 \<noteq> n2" "n1 \<in> dom_fg h2'" "n2 \<in> dom_fg h1'"
    by blast
  then have "length ns \<ge> 2"
    using assms dom by (meson length_ge_2)
  then have "butlast ns \<noteq> []"
    by (cases ns, simp_all, case_tac list, simp_all)

  have "\<exists>xss. concat xss = ns \<and> xss \<noteq> [] \<and> (\<forall>xs\<in>set xss. xs \<noteq> []) \<and>
    alternating (segment_fg h1') (segment_fg h2') xss"
    apply (rule split_segments[of ns "dom_fg h1'" "dom_fg h2'"])
    using True dom by simp_all
  then obtain xss where xssdef: "concat xss = ns" "xss \<noteq> []" "\<forall>xs \<in> set xss. xs \<noteq> []"
    "alternating (segment_fg h1') (segment_fg h2') xss"
    by blast

  have "chain ?e' ns n = chains ?e' xss n"
    apply (subst chain_chains[of ns xss ?e' n], simp_all add: list.set_sel)
    using xssdef by (simp_all add: list.set_sel(2))
  also have "... = chains' (chain ?e') xss n"
    by (induction xss, simp, case_tac xss, auto)
  finally have XXX: "chain ?e' ns n = chains' (chain ?e') xss n" .

  have "hd ns = hd (hd xss)"
    using hd_hd_concat_hd[of ns xss] xssdef nsdef by simp
  then have "0 < chains' (chain ?e') xss n (?i (hd (hd xss)))"
    using nsdef XXX xssdef apply simp
    using gr_zeroI by blast
  also have "... \<le> chains' (chain ?e') xss n (?i1' (hd (hd xss)))"
    apply (subst infeq[symmetric])
    apply (rule pos_endo_mono'_closed[OF inf_fg_le_inf_fg, where E=E])
    using assms nbot xssdef nsdef apply blast
    using xssdef nsdef apply (metis True concat.simps(2) hd_Cons_tl hd_append2 hd_in_set)
    using assms apply blast+
    apply (rule endo_chains'[OF \<open>End_closed E\<close>], clarsimp)
    apply (rule endo_chain_closed)
    using assms by (simp_all (no_asm))
  finally have GGG: "chains' (chain ?e') xss n (?i1' (hd (hd xss))) \<noteq> 0"
    by simp
  have altpq: "alternating ?P ?Q xss"
    apply (subst \<open>?N1 = ?N1'\<close>)+
    apply (subst \<open>?N2 = dom_fg h2'\<close>)+
    apply (rule eff_acyclic_chain_length_le_card')
    using xssdef nsdef \<open>?N1 = ?N1'\<close> apply simp
    using assms nbot apply blast+
    using GGG by simp

  have ne: "length xss \<ge> 2"
    using length_ge_2_alternating[of ?N1 ?N2 n2 n1 xss] xssdef assms *** by metis
  then have bl_xss_ne: "butlast xss \<noteq> []"
    by (cases xss, simp_all, case_tac list, simp_all)

  have hdns: "hd ns = hd (hd (butlast xss))"
  proof -
    have B: "hd (butlast xss) \<noteq> []"
      using xssdef by (simp add: bl_xss_ne in_set_butlastD)
    have C: "hd (concat (butlast xss @ [last xss])) = hd ns"
      using xssdef by simp
    then have D: "hd (concat (butlast xss)) = hd ns"
      by (metis bl_xss_ne B concat_append concat_eq_Nil_conv hd_append2 hd_in_set)
    then show ?thesis
      apply (cases "butlast xss")
      using bl_xss_ne apply blast
      using B by auto
  qed

  have sum: "h = h2 + h1"
    using \<open>h = h1 + h2\<close> by (simp add: algebra_simps)

  show False
  proof (cases "n \<in> set (last xss)")
    case True
    show ?thesis
    proof (cases "hd (last xss) \<in> ?Na")
      case True
      then have "\<not> ?Q (last xss)"
        using dom \<open>?N1 = ?N1'\<close>
        by (metis disjoint_iff_not_equal hd_in_set subsetD)
      then have altv: "alt h1' h2' xss = h1'" "alt h1 h2 xss = h1"
        using alt_odd[OF altpq xssdef(2), of h1' h2'] alt_odd[OF altpq xssdef(2), of h1 h2]
        by simp_all
      then have altv': "alt h2 h1 (butlast xss) = h1" "alt h2' h1' (butlast xss) = h1'"
        using alt_butlast[OF \<open>xss \<noteq> []\<close>, of h1 h2] alt_butlast[OF \<open>xss \<noteq> []\<close>, of h1' h2']
        by auto

      have "set (last xss) \<subseteq> ?N1'"
        using alternating_props[OF altpq] True dom \<open>?N1 = ?N1'\<close> \<open>xss \<noteq> []\<close>
        by (metis \<open>\<not> ?Q (last xss)\<close> last_in_set)

      have AUX: "xs \<in> set xss \<Longrightarrow> chain (edge_fg (h1' + h2')) xs y = alt_chain h1' h2' xs y" for xs y
      proof (goal_cases)
        case 1
        have "\<not> set xs \<subseteq> dom_fg h1' \<Longrightarrow> set xs \<subseteq> dom_fg h2'"
          using dom alternating_props[OF xssdef(4)] 1 by blast
        with 1 show ?case
          apply (clarsimp, intro conjI impI)
          apply (rule chain_cong'[OF edge_fg_plus_fg_on1[OF nbot(1)]], simp)
          by (rule chain_cong'[OF edge_fg_plus_fg_on2[OF nbot(1)]], simp)
      qed

      have "chains' (chain ?e') (butlast xss) (hd (last xss)) (?i (hd ns)) =
          chains' (alt_chain h1' h2') (butlast xss) (hd (last xss)) (?i (hd ns))"
        apply (rule chains'_cong[OF AUX])
        by (simp add: in_set_butlastD)
      also have "... \<le> chains' (alt_chain h1' h2') (butlast xss) (hd (last xss)) (?i1' (hd ns))"
        apply (subst infeq(1)[symmetric])
        apply (rule pos_endo_mono'_closed[where f="chains' _ _ _" and E=E, OF inf_fg_le_inf_fg])
        using \<open>hd ns \<in> dom_fg h1'\<close> \<open>?N1 = ?N1'\<close> nbot
        by (auto intro!: endo_chains' endo_chain_closed simp: assms)
      also have "... \<le> inf_fg (alt h2' h1' (butlast xss)) (hd (last xss))"
        using chains'_chain_inf_fg_le_inf_fg[of h1' h2' "butlast xss" "last xss"] hdns assms
          bl_xss_ne nbot alternating_to_alternating'[where xs=xss] xssdef
        by (metis (no_types, lifting))
      finally have DDD: "chains' (chain ?e') (butlast xss) (hd (last xss)) (?i (hd ns)) \<le>
        inf_fg (alt h2' h1' (butlast xss)) (hd (last xss))" .

      have "0 < chain ?e' ns n (?i (hd ns))"
        using nsdef gr_zeroI by blast
      also have "... = chains' (chain ?e') xss n (?i (hd ns))"
        using XXX by simp
      also have "... =
        chain ?e' (last xss) n (chains' (chain ?e') (butlast xss) (hd (last xss)) (?i (hd ns)))"
        by (rule chains'_append1, simp add: \<open>xss \<noteq> []\<close>)
      also have "... \<le> chain ?e' (last xss) n (inf_fg (alt h2' h1' (butlast xss)) (hd (last xss)))"
        apply (rule pos_endo_mono'_closed[where f="chain _ _ _", where E=E])
        by (auto intro!: endo_chain_closed simp: assms DDD)
      finally have "0 \<noteq> chain ?e' (last xss) n (inf_fg (alt h2' h1' (butlast xss)) (hd (last xss)))"
        by simp
      then have Y: "0 \<noteq> chain ?e1' (last xss) n (inf_fg (alt h2' h1' (butlast xss)) (hd (last xss)))"
        apply (subst (asm) chain_cong')
        apply (rule edge_fg_plus_fg_on1)
        using nbot apply blast
        using \<open>set (last xss) \<subseteq> dom_fg h1'\<close> apply blast
        by simp

      show ?thesis
        using contradict_eff_acyclic[of h1' "last xss" n E] altv' altv infeq Y nbot assms
          \<open>set (last xss) \<subseteq> ?N1'\<close> \<open>n \<in> set (last xss)\<close> by metis
    next
      case False (* symmetric case *)
      then have "\<not> ?P (last xss)"
        using dom \<open>?N1 = ?N1'\<close>
        by (metis hd_in_set subsetD)
      then have altv: "alt h1' h2' xss = h2'" "alt h1 h2 xss = h2"
        using alt_even[OF altpq xssdef(2), of h1' h2'] alt_even[OF altpq xssdef(2), of h1 h2]
        by simp_all
      then have altv': "alt h2' h1' (butlast xss) = h2'"
        using alt_butlast[OF \<open>xss \<noteq> []\<close>, of h1' h2'] by simp

      have "set (last xss) \<subseteq> ?N2"
        using alternating_props[OF altpq] True dom \<open>?N1 = ?N1'\<close> \<open>xss \<noteq> []\<close>
        by (metis \<open>\<not> ?P (last xss)\<close> last_in_set)

      have AUX: "xs \<in> set (butlast xss)
        \<Longrightarrow> chain (edge_fg (h1' + h2')) xs y = alt_chain h2' h1' xs y" for xs y
      proof (goal_cases)
        case 1
        have "\<not> set xs \<subseteq> dom_fg h2' \<Longrightarrow> set xs \<subseteq> dom_fg h1'"
          using dom alternating_props[OF xssdef(4)] 1 by (meson in_set_butlastD)
        with 1 show ?case
          apply (clarsimp, intro conjI impI)
          apply (rule chain_cong'[OF edge_fg_plus_fg_on2[OF nbot(1)]], simp)
          by (rule chain_cong'[OF edge_fg_plus_fg_on1[OF nbot(1)]], simp)
      qed

      have AUX2: "xs \<in> set xss \<Longrightarrow> alt_chain h1' h2' xs y = alt_chain h2' h1' xs y" for xs y
        using dom by (smt alternating_props disjoint_iff_not_equal list.set_sel(1) subsetD xssdef(4))

      have "chains' (chain ?e') (butlast xss) (hd (last xss)) (?i (hd ns)) =
          chains' (alt_chain h2' h1') (butlast xss) (hd (last xss)) (?i (hd ns))"
        apply (rule chains'_cong[OF AUX])
        by (simp add: in_set_butlastD)
      also have "... \<le> chains' (alt_chain h2' h1') (butlast xss) (hd (last xss)) (?i1' (hd ns))"
        apply (subst infeq(1)[symmetric])
        apply (rule pos_endo_mono'_closed[where f="chains' _ _ _" and E=E, OF inf_fg_le_inf_fg])
        using \<open>hd ns \<in> dom_fg h1'\<close> \<open>?N1 = ?N1'\<close> nbot
        by (auto intro!: endo_chains' endo_chain_closed simp: assms)
      also have "... \<le> inf_fg (alt h2' h1' (butlast xss)) (hd (last xss))"
        apply (subst chains'_cong[OF AUX2[symmetric]], simp add: in_set_butlastD)
        using chains'_chain_inf_fg_le_inf_fg[of h1' h2' "butlast xss" "last xss"] hdns assms
          bl_xss_ne nbot alternating_to_alternating'[where xs=xss] xssdef
        by (metis (no_types, lifting))
      finally have DDD: "chains' (chain ?e') (butlast xss) (hd (last xss)) (?i (hd ns)) \<le>
        inf_fg (alt h2' h1' (butlast xss)) (hd (last xss))" .

      have "0 < chain ?e' ns n (?i (hd ns))"
        using nsdef gr_zeroI by blast
      also have "... = chains' (chain ?e') xss n (?i (hd ns))"
        using XXX by simp
      also have "... =
        chain ?e' (last xss) n (chains' (chain ?e') (butlast xss) (hd (last xss)) (?i (hd ns)))"
        by (rule chains'_append1, simp add: \<open>xss \<noteq> []\<close>)
      also have "... \<le> chain ?e' (last xss) n (inf_fg (alt h2' h1' (butlast xss)) (hd (last xss)))"
        apply (rule pos_endo_mono'_closed[where f="chain _ _ _", where E=E])
        by (auto intro!: endo_chain_closed simp: assms DDD)
      finally have "0 \<noteq> chain ?e' (last xss) n (inf_fg (alt h2' h1' (butlast xss)) (hd (last xss)))"
        by simp
      then have Y: "0 \<noteq> chain ?e2' (last xss) n (inf_fg (alt h2' h1' (butlast xss)) (hd (last xss)))"
        apply (subst (asm) chain_cong')
        apply (rule edge_fg_plus_fg_on2[of h1' h2'])
        using nbot apply blast
        using \<open>set (last xss) \<subseteq> dom_fg h2\<close> assms apply blast
        by simp

      have "h2' \<noteq> bot" using assms
        by (meson plus_fg_bot_bot(2))

      then show ?thesis
        using contradict_eff_acyclic[of h2' "last xss" n E] altv' altv infeq Y nbot assms
          \<open>set (last xss) \<subseteq> dom_fg h2\<close> \<open>n \<in> set (last xss)\<close> * by metis
    qed
  next
    case False

    have X1: "\<And>xs y x x'. ?P xs \<Longrightarrow> x \<le> x' \<Longrightarrow> chain ?e' xs y x \<le> ?g1 xs y x'"
      apply (split if_split, intro conjI impI, rule chain_le_cap'[where E=E])
      using assms dom_fg_finite[of h1] unfolding zero_fun_def by blast+

    have X2: "\<And>xs y x x'. ?Q xs \<Longrightarrow> x \<le> x' \<Longrightarrow> chain ?e' xs y x \<le> ?g1 xs y x'"
      apply (split if_split, intro conjI impI)
      subgoal using dom(1) \<open>?N1 = ?N1'\<close>
        by (metis assms(17) disjoint_iff_not_equal list.set_sel(1) subset_iff)
      apply (split if_splits, intro conjI impI)
      apply (rule chain_le_cap'[where E=E])
      using assms dom_fg_finite[of h2] unfolding zero_fun_def by blast+

    have X3: "alternating ?P ?Q (butlast xss)"
      using alternating_append1[of ?P ?Q "butlast xss" "[last xss]"] altpq xssdef
      by simp

    have X4: "\<And>xs y x x'. ?P xs \<Longrightarrow> x \<le> x' \<Longrightarrow> ?g1 xs y x \<le> ?g2 xs y x'"
      apply simp
      apply (subst \<open>dom_fg h1 = dom_fg h1'\<close>)+
      apply (subst cap'_cong_e[OF edge_fg_plus_fg_on1], simp_all add: nbot)
      apply (rule pos_endo_mono'_closed[OF _ endo_cap', where E=E])
      using assms dom_fg_finite[of h1'] unfolding zero_fun_def by blast+

    have X5: "\<And>xs y x x'. ?Q xs \<Longrightarrow> x \<le> x' \<Longrightarrow> ?g1 xs y x \<le> ?g2 xs y x'"
      apply clarsimp
      apply (intro conjI impI)
      apply (subst \<open>dom_fg h1 = dom_fg h1'\<close>)+
      using \<open>?N1' \<inter> dom_fg h2' = {}\<close> \<open>?N1 = ?N1'\<close>
      apply (metis Int_subset_iff assms(17) set_empty subset_empty)
      apply (subst \<open>dom_fg h2 = dom_fg h2'\<close>)+
      apply (subst cap'_cong_e[OF edge_fg_plus_fg_on2], simp_all add: nbot)+
      apply (rule pos_endo_mono'_closed[OF _ endo_cap', where E=E])
      using assms dom_fg_finite[of h2'] unfolding zero_fun_def by blast+

    have "\<exists>xs \<in> set xss. n \<in> set xs"
      using xssdef nsdef by auto
    then obtain nss1 ns1 ns2 nss2 where nss: "concat xss = concat nss1 @ ns1 @ n # ns2 @ concat nss2"
      "xss = nss1 @ (ns1 @ n # ns2) # nss2"
      using split_list_list[of xss n] by auto

    have nss2_ne: "nss2 \<noteq> []" "hd nss2 \<noteq> []"
      using False nss apply auto[1]
      using xssdef nss 
      by (metis (no_types, lifting) False Un_iff insert_iff last.simps last_appendR list.distinct(1)
          list.set(2) list.set_sel(1) set_append)
    then have blub: "hd (concat nss2) = hd (hd nss2)"
      by (metis concat.simps(2) hd_Cons_tl hd_append2)

    let ?c = "chain ?e' (n # ns2 @ concat nss2) n"
    have "?c \<in> E"
      apply (rule endo_chain_closed, rule endo_edge_fg_plus_fg)
      using \<open>?h' \<noteq> bot\<close> assms unfolding zero_fun_def by blast+
    then have red: "\<And>x. ?c x \<noteq> 0 \<Longrightarrow> ?c (?c x) \<noteq> 0"
      using \<open>pointwise_reduced E\<close> unfolding pointwise_reduced_def comp_def zero_fun_def by simp

    have "chain ?e' (concat nss1 @ ns1 @ n # ns2 @ concat nss2) n (?i (hd ns)) \<noteq> 0"
      using nsdef nss xssdef by metis
    then have "chain ?e' (n # ns2 @ concat nss2) n (chain ?e' (concat nss1 @ ns1) n (?i (hd ns))) \<noteq> 0"
      using chain_append_nonempty[of ?e' "concat nss1 @ ns1" "n # ns1 @ concat nss2" n]
      by (metis append_assoc chain_append_nonempty hd_append2 list.distinct(1) list.sel(1))
    then have "chain ?e' (n # ns2 @ concat nss2) n (chain ?e' (n # ns2 @ concat nss2) n (chain ?e' (concat nss1 @ ns1) n (?i (hd ns)))) \<noteq> 0"
      using red by simp
    then have "chain ?e' (n # ns2) (hd (hd nss2)) (chain ?e' (n # ns2 @ concat nss2) n (chain ?e' (concat nss1 @ ns1) n (?i (hd ns)))) \<noteq> 0"
      using chain_append_not_zero(1)[of "n # ns2 @ concat nss2" "n # ns2" "concat nss2" "edge_fg (h1' + h2')" n
          "chain (edge_fg (h1' + h2')) (n # ns2 @ concat nss2) n (chain (edge_fg (h1' + h2')) (concat nss1 @ ns1) n (inf_fg (h1 + h2) (hd ns)))" E]
      using nss2_ne blub nss xssdef \<open>\<forall>x y. edge_fg (h1' + h2') x y \<in> E\<close> \<open>End_closed E\<close> by simp
    then have "chain ?e' (n # ns2) (hd (hd nss2)) (chain ?e' (n # ns2 @ concat nss2) (hd ((n # ns2) @ [hd (hd nss2)])) (chain ?e' (concat nss1 @ ns1) n (?i (hd ns)))) \<noteq> 0"
      by simp
    then have "chain ?e' (n # ns2 @ concat nss2 @ n # ns2) (hd (hd nss2)) (chain ?e' (concat nss1 @ ns1) n (?i (hd ns))) \<noteq> 0"
      by (subst (asm) chain_append_nonempty[symmetric], simp)
    then have "chain ?e' (n # ns2 @ concat nss2 @ n # ns2) (hd (hd nss2)) (chain ?e' (concat nss1 @ ns1) (hd ((n # ns2 @ concat nss2 @ n # ns2) @ [hd (hd nss2)])) (?i (hd ns))) \<noteq> 0"
      by simp
    then have ne0: "chain ?e' (concat nss1 @ ns1 @ n # ns2 @ concat nss2 @ n # ns2) (hd (hd nss2)) (?i (hd ns)) \<noteq> 0"
      by (subst (asm) chain_append_nonempty[symmetric], simp)
    then have "0 < chain ?e' (concat nss1 @ ns1 @ n # ns2 @ concat nss2 @ n # ns2) (hd (hd nss2)) (?i (hd ns))"
      using gr_zeroI by blast
    also have "... = chain ?e' (concat nss1 @ ns1 @ n # ns2 @ concat nss2 @ n # ns2) (hd (hd nss2)) (?i' (hd ns))"
      using infeq(1) by auto
    also have "... \<le> chain ?e' (concat nss1 @ ns1 @ n # ns2 @ concat nss2 @ n # ns2) (hd (hd nss2)) (?i1' (hd ns))"
      apply (rule pos_endo_mono'_closed[OF inf_fg_le_inf_fg[of h1' h2' "hd ns" E]])
      using nbot True assms apply blast
      using nbot True assms apply blast
      using nbot True assms apply blast
      apply (rule endo_chain_closed)
      using nbot True assms by blast+
    finally have ne00: "chain ?e' (concat nss1 @ ns1 @ n # ns2 @ concat nss2 @ n # ns2) (hd (hd nss2)) (?i1' (hd ns)) \<noteq> 0" by simp

    let ?ns = "concat nss1 @ ns1 @ n # ns2 @ concat nss2 @ n # ns2"
    let ?n = "hd (hd nss2)"
    let ?xss = "xss @ [n # ns2]"

    have "ns1 @ n # ns2 \<in> set xss"
      using nss by simp
    then have "?P (ns1 @ n # ns2) \<or> ?Q (ns1 @ n # ns2)"
      using alternating_props[OF altpq] by blast

    have Y1: "?n \<in> set (map hd xss)"
      using nss nss2_ne by simp

    have Y2: "?ns = concat ?xss"
      using nss by simp

    have Y3: "?n \<in> set (map hd ?xss)"
      using Y1 Y2 by simp

    have "last nss2 = last xss"
      using xssdef nss nss2_ne by simp

    have "\<exists>xss. concat xss = ?ns \<and> xss \<noteq> [] \<and> (\<forall>xs\<in>set xss. xs \<noteq> []) \<and>
                  alternating (segment_fg h1) (segment_fg h2) xss"
      apply (rule split_segments[of ?ns ?N1 ?N2])
      apply simp
      apply simp
      apply (intro conjI)
      using assms nbot nsdef apply (metis dom_fg_plus_fg_iff in_mono)
      using assms dom nss xssdef subgoal
        by (metis set_append set_concat sup.boundedE)
      using \<open>len_segment_fg h1 (ns1 @ n # ns2) \<or> len_segment_fg h2 (ns1 @ n # ns2)\<close> apply auto[1]
      using \<open>len_segment_fg h1 (ns1 @ n # ns2) \<or> len_segment_fg h2 (ns1 @ n # ns2)\<close> apply auto[1]
      using assms(16) assms(17) dom(3) nss(1) xssdef(1) apply auto[1]
      using \<open>len_segment_fg h1 (ns1 @ n # ns2) \<or> len_segment_fg h2 (ns1 @ n # ns2)\<close> apply auto[1]
      by (simp add: True Y2 assms(16) dom(2) xssdef(1))
    then obtain yss where yssdef: "concat yss = ?ns" "yss \<noteq> []" "\<forall>xs\<in>set yss. xs \<noteq> []"
      "alternating (segment_fg h1) (segment_fg h2) yss"
      by auto

    have some_rule: "alternating (segment_fg h1') (segment_fg h2') xs \<Longrightarrow> xs = xs1 @ x1 # x2 # xs2 \<Longrightarrow>
                       segment_fg h1' x1 \<longleftrightarrow> segment_fg h2' x2" for xs xs1 x1 x2 xs2
    proof -
      assume A: "alternating (segment_fg h1') (segment_fg h2') xs" "xs = xs1 @ x1 # x2 # xs2"
      have "alternating (segment_fg h1') (segment_fg h2') xs1"
        using alternating_append1 A by auto
      then show ?thesis
        using A dom(3,4)
        apply (induction xs1 arbitrary: xs rule: alternating_induct'_symmetric[where a=h1' and b=h2'])
        apply simp
        apply simp
        apply (metis Int_commute Int_left_commute inf_bot_right le_iff_inf set_empty)
        apply simp
        subgoal premises prems for a b x y zs xs
        proof -
          have A: "segment_fg b x1 = segment_fg a x2"
            using prems by auto
          show ?thesis
          proof (cases "segment_fg b x1")
            case True
            then have B1: "\<not> segment_fg a x1" using prems
              by (metis Int_assoc inf_bot_right le_iff_inf set_empty)
            from True have B2: "\<not>segment_fg b x2"
              by (metis Int_assoc Int_empty_right A le_iff_inf prems set_empty)
            show ?thesis using B1 B2 by auto
          next
            case False
            then have B1: "segment_fg a x1" using prems
              by (metis (mono_tags, lifting) UnCI alternating_props list.set_intros(1) set_append)
            from A False have "\<not> segment_fg a x2" by blast
            then have "\<not>segment_fg b x1" using prems by auto
            then have B2: "segment_fg b x2"
              using A prems alternating_props[of "segment_fg a" "segment_fg b" "zs @ x1 # x2 # xs2"]
              by auto
            show ?thesis using B1 B2 by auto
          qed
        qed
        done
    qed

    have some_result: "segment_fg h1' (ns1 @ n # ns2) \<longleftrightarrow> segment_fg h2' (hd nss2)"
      apply (rule some_rule[of xss nss1 "ns1 @ n # ns2" "hd nss2" "tl nss2"])
      using xssdef apply simp
      using nss nss2_ne by simp
    then have "segment_fg h1' (n # ns2) \<longleftrightarrow> segment_fg h2' (hd nss2)"
      using nss2_ne apply auto
      using \<open>len_segment_fg h1 (ns1 @ n # ns2) \<or> len_segment_fg h2 (ns1 @ n # ns2)\<close>
      using assms(16) assms(17) dom(1) by auto

    have HHH: "set (n # ns2) \<subseteq> dom_fg h1 \<or> set (n # ns2) \<subseteq> dom_fg h2"
      using \<open>len_segment_fg h1 (ns1 @ n # ns2) \<or> len_segment_fg h2 (ns1 @ n # ns2)\<close> by auto

    have BRUMM: "\<forall>xs \<in> set xss. set xs \<subseteq> dom_fg h1' \<longleftrightarrow> \<not> set xs \<subseteq> dom_fg h2'"
      using nss xssdef dom nss2_ne
      by (metis (no_types, lifting) Int_assoc alternating_props inf_bot_right le_iff_inf set_empty)

    have "\<exists>ys yss. alternating' (segment_fg h1) (segment_fg h2) (butlast xss @ [last xss @ ys] @ yss) (hd nss2) \<and>
               concat nss1 @ ns1 @ n # ns2 @ concat nss2 @ n # ns2 = concat (butlast xss @ [last xss @ ys] @ yss) \<and>
               (\<forall>xs\<in>set xss. xs \<noteq> []) \<and> last xss @ ys \<noteq> [] \<and> (\<forall>xs\<in>set yss. xs \<noteq> []) \<and> ys @ concat yss = n # ns2 \<and> (ys = [] \<or> yss = [])"
      apply (rule split_segments_extend[of "dom_fg h1" "dom_fg h2" xss ?ns "n # ns2" "hd nss2"])
      using xssdef nss \<open>?N1 = ?N1'\<close> \<open>?N2 = dom_fg h2'\<close> dom nsdef nbot nss2_ne HHH apply simp_all
      apply blast
      apply (meson disjoint_iff_not_equal dom(1))
      subgoal premises prems using BRUMM nss nss2_ne by simp
      using \<open>segment_fg h1' (n # ns2) = segment_fg h2' (hd nss2)\<close> by auto
    then obtain zs zss where zss:
      "alternating' (segment_fg h1) (segment_fg h2) (butlast xss @ [last xss @ zs] @ zss) (hd nss2)"
      "concat nss1 @ ns1 @ n # ns2 @ concat nss2 @ n # ns2 = concat (butlast xss @ [last xss @ zs] @ zss)"
      "\<forall>xs\<in>set xss. xs \<noteq> []" "last xss @ zs \<noteq> []" "\<forall>xs\<in>set zss. xs \<noteq> []"
      "zs @ concat zss = n # ns2" "zs = [] \<or> zss = []" "n # ns2 = zs @ concat zss"
      by (metis (no_types, lifting))
    have zss': "alternating (segment_fg h1) (segment_fg h2) (butlast xss @ [last xss @ zs] @ zss)"
      apply (rule alternating'_to_alternating)
      using zss by blast

    let ?zss = "butlast xss @ [last xss @ zs] @ zss"

    have "last xss = last nss2" using nss nss2_ne by simp
    moreover have "butlast xss = nss1 @ (ns1 @ n # ns2) # butlast nss2"
      using nss nss2_ne by (simp add: butlast_append)
    ultimately have WWW: "?zss = nss1 @ (ns1 @ n # ns2) # butlast nss2 @ [last nss2 @ zs] @ zss"
      by simp
    have n_hd: "?n = hd (hd (butlast nss2 @ [last nss2 @ zs] @ zss))"
      by (metis \<open>last xss = last nss2\<close> append_self_conv2 hd_append2 last_in_set
          list.sel(1) nss2_ne(1) snoc_eq_iff_butlast xssdef)
    then have MMM: "?n = hd (concat (butlast nss2 @ [last nss2 @ zs] @ zss))"
      using nss nss2_ne yssdef apply simp by (cases nss2, simp, case_tac list, simp, simp)

    let ?uss = "butlast nss2 @ [last nss2 @ zs] @ zss"

    have "set (map hd xss) = set (map hd (butlast xss @ [last xss @ zs]))"
      using \<open>xss \<noteq> []\<close> nss2_ne \<open>\<forall>xs\<in>set xss. xs \<noteq> []\<close>
      by (induction xss rule: list_nonempty_induct, simp_all)
    then have n_in_hd_zss: "?n \<in> set (map hd ?zss)"
      using Y1 by auto

    have www: "hd (hd (butlast xss @ (last xss @ zs) # zss)) = hd ns"
      by (simp add: bl_xss_ne hdns)

    have mmm: "inf_fg (h1 + h2) (hd ns) \<le> inf_fg h1' (hd (hd (butlast xss @ (last xss @ zs) # zss)))"
      apply (subst www, subst infeq(1)[symmetric])
      apply (rule inf_fg_le_inf_fg)
      using nbot apply simp
      apply (simp add: True)
      using assms by blast

    have ttt: "hd (hd (nss1 @ (ns1 @ zs @ concat zss) # butlast nss2 @ (last nss2 @ zs) # zss)) = hd ns"
      using xssdef nss zss by (metis \<open>hd ns = hd (hd xss)\<close> append_self_conv2 hd_append2 list.sel(1))

    have zss_alt: "alternating (len_segment_fg h1) (len_segment_fg h2) ?zss"
      apply (subst \<open>?N1 = ?N1'\<close>)+
      apply (subst \<open>?N2 = dom_fg h2'\<close>)+
      apply (rule eff_acyclic_chain_length_le_card'[where E=E and n="hd (hd nss2)"])
      using zss' \<open>?N1 = ?N1'\<close> \<open>?N2 = dom_fg h2'\<close> apply simp
      using nbot apply blast
      using assms apply blast
      using assms apply blast
      using assms apply blast
      using assms apply blast
      using assms apply blast
      using assms apply blast
      using assms apply blast
      using assms apply blast
      apply (subst chains'_chain, simp)
      using xssdef zss apply safe
      apply (metis (mono_tags, lifting) alternating_props zss')
      apply (metis (mono_tags, lifting) alternating_props zss')+
      apply (metis (no_types, lifting) append_Nil append_Nil2 bl_xss_ne concat.simps(1) concat.simps(2) concat_append hd_append2 hdns ne00)
      apply (metis (no_types, lifting) append_Nil2 bl_xss_ne concat.simps(1) concat.simps(2) concat_append hd_append2 hdns ne00)
      by (metis (no_types, lifting) append_Nil2 bl_xss_ne concat.simps(1) concat.simps(2) concat_append hd_append2 hdns ne00)

    let ?PP = "alt (len_segment_fg h2) (len_segment_fg h1) (nss1 @ [ns1 @ n # ns2])"
    let ?QQ = "alt (len_segment_fg h1) (len_segment_fg h2) (nss1 @ [ns1 @ n # ns2])"

    have "alternating (len_segment_fg h1) (len_segment_fg h2) (butlast (nss1 @ (ns1 @ n # ns2) # nss2) @ [last (nss1 @ (ns1 @ n # ns2) # nss2) @ zs] @ zss)"
      using zss_alt nss by simp
    then have blub': "alternating (len_segment_fg h1) (len_segment_fg h2) ((nss1 @ [ns1 @ n # ns2]) @ ?uss)"
      using nss WWW by auto
    have uss_alt: "alternating ?PP ?QQ ?uss"
      by (fact alternating_append2[OF blub'])

    have blub': "alternating (segment_fg h1') (segment_fg h2') ((nss1 @ [ns1 @ n # ns2] @ [hd nss2]) @ (tl nss2))"
      using xssdef nss nss2_ne by simp
    have "alternating' (\<lambda>xs. set xs \<subseteq> dom_fg h1') (\<lambda>xs. set xs \<subseteq> dom_fg h2') (butlast (nss1 @ [ns1 @ n # ns2] @ [hd nss2])) (last (nss1 @ [ns1 @ n # ns2] @ [hd nss2]))"
      by (rule alternating_to_alternating'[OF alternating_consequence[OF alternating_append1[OF blub']]], simp_all)
    then have prefix_alt: "alternating' (\<lambda>xs. set xs \<subseteq> dom_fg h1') (\<lambda>xs. set xs \<subseteq> dom_fg h2') (nss1 @ [ns1 @ n # ns2]) (hd nss2)"
      by (simp add: butlast_append)

    have "hd (concat (nss1 @ [ns1 @ n # ns2])) = hd ns"
      using xssdef nss yssdef
      by (metis (no_types, lifting) concat.simps(1) concat.simps(2) concat_append hd_append list.sel(1))
    then have S1: "hd (concat (nss1 @ [ns1 @ n # ns2]) @ [hd (concat (butlast nss2 @ [last nss2 @ zs] @ zss) @ [hd (hd nss2)])]) = hd ns"
      by (metis \<open>len_segment_fg h1 (ns1 @ n # ns2) \<or> len_segment_fg h2 (ns1 @ n # ns2)\<close> append_is_Nil_conv concat.simps(2) concat_append hd_append2)

    have S2: "hd ns = hd (hd (butlast (nss1 @ (ns1 @ n # ns2) # nss2) @ (last nss2 @ zs) # zss))"
      using xssdef nss yssdef bl_xss_ne hdns by auto
    have S3: "hd ns = hd (hd (nss1 @ [ns1 @ n # ns2]))"
      by (metis \<open>hd ns = hd (hd xss)\<close> append_self_conv2 hd_append2 list.sel(1) nss(2))

    have dom_subs: "dom_fg h1 \<subseteq> dom_fg h" "dom_fg h2 \<subseteq> dom_fg h"
      using assms(2) assms(3) by auto

    have hds: "\<forall>ys \<in> set ?zss. hd ys \<in> dom_fg h"
      apply (rule alternatingD[OF zss_alt])
      using dom_subs by fastforce+

    have "\<And>a list. butlast nss2 = a # list \<Longrightarrow> set (hd (butlast nss2)) \<subseteq> dom_fg (h1' + h2')"
      using xssdef nss alternating_props[of "segment_fg h1'" "segment_fg h2'" xss] nss2_ne nbot
      apply simp
      by (metis (no_types, lifting) Un_iff append_butlast_last_id empty_set hd_append2 hd_in_set
          list.sel(1) list.set_intros(1) sup.coboundedI1 sup.coboundedI2 sup_bot.right_neutral)
    then have TOE: "\<And>a list. butlast nss2 = a # list \<Longrightarrow> hd (hd (butlast nss2)) \<in> dom_fg (h1' + h2')"
      using nss2_ne by (metis append_butlast_last_id hd_append2 hd_in_set in_mono list.simps(3))

    have hd_hd_uss_in_h1h2: "hd (hd ?uss) \<in> dom_fg (h1 + h2)"
      apply (cases "butlast nss2")
      using xssdef yssdef nss assms nss2_ne nsdef \<open>h1' + h2' \<noteq> bot\<close>
       apply (metis (no_types, lifting) Un_iff \<open>last xss = last nss2\<close> append_is_Nil_conv
             append_self_conv2 hds list.set_sel(1) list.simps(3) set_append)
      by (metis TOE assms dom(6) hd_append list.simps(3) nbot(1) plus_fg_dom_un)

    have all_tl: "\<forall>x \<in> set xs. P x \<Longrightarrow> \<forall>x \<in> set (tl xs). P x" for xs P
      by (induction xs, simp_all)

    have "chain ?e' ?ns (hd (hd nss2)) = chains ?e' ?zss (hd (hd nss2))"
      apply (subst chain_chains[of ?ns ?zss ?e' "(hd (hd nss2))"], simp_all add: list.set_sel)
      using yssdef zss xssdef zss' concat_append
      apply (metis (no_types, lifting) append.right_neutral append_self_conv2 concat.simps(2))
      by (rule all_tl, metis zss Un_iff in_set_butlastD insert_iff list.set(2) set_append)
    also have "... = chains' (chain ?e') ?zss (hd (hd nss2))"
      using chains'_chains[symmetric, of ?e' ?zss ?n] by auto
    finally have XXX: "chain ?e' ?ns ?n = chains' (chain ?e') ?zss ?n" .

    have alt_cases: "\<not> P z \<Longrightarrow> \<not> Q z \<Longrightarrow> \<not> alt P Q xs z" for P Q xs z
      by (induction xs arbitrary: P Q, auto)

    have blub: "\<And>xs y. xs \<in> set (butlast nss2 @ [last nss2 @ zs] @ zss) \<Longrightarrow>
   (if set xs \<subseteq> dom_fg (alt h2 h1 (nss1 @ [ns1 @ n # ns2])) then cap_fg (alt h2 h1 (nss1 @ [ns1 @ n # ns2])) (hd (xs @ [y])) y
   else if set xs \<subseteq> dom_fg (alt h1 h2 (nss1 @ [ns1 @ n # ns2])) then cap_fg (alt h1 h2 (nss1 @ [ns1 @ n # ns2])) (hd (xs @ [y])) y else 0) =
   (if set xs \<subseteq> dom_fg h1 then cap_fg h1 (hd (xs @ [y])) y else if set xs \<subseteq> dom_fg h2 then cap_fg h2 (hd (xs @ [y])) y else 0)"
    proof (goal_cases)
      case (1 xs y)
      then have **: "xs \<noteq> []"
        apply auto
        using \<open>last nss2 = last xss\<close> zss apply auto[1]
         apply (metis Un_iff \<open>butlast xss = nss1 @ (ns1 @ n # ns2) # butlast nss2\<close>
            in_set_butlastD insert_iff list.set(2) set_append zss(3))
        using zss by blast
      let ?zs = "nss1 @ [ns1 @ n # ns2]"
      have "alt h1 h2 ?zs \<in> {h1,h2}" using alt_in[of ?zs h1 h2] by simp
      then consider (a) "alt h1 h2 ?zs = h1" | (b) "alt h1 h2 ?zs = h2" by blast
      then show ?case
      proof cases
        case a
        from a have "alt h2 h1 ?zs = h2" using alt_comm[of h1 h2 ?zs] by simp
        then show ?thesis
          using 1 a dom ** apply simp
          by (meson disjoint_iff_not_equal hd_in_set in_mono)
      next
        case b
        from b have "alt h2 h1 ?zs = h1" using alt_comm[of h1 h2 ?zs] by simp
        then show ?thesis
          using 1 b dom ** by simp
      qed
    qed

    have BRUM: "hd (hd nss2) = hd (concat (butlast nss2 @ [last nss2 @ zs] @ zss) @ [hd (hd nss2)])"
      using nss2_ne by (simp add: hd_append MMM)

    have AUXAUX:
      "alternating' (segment_fg h1) (segment_fg h2) xss ys \<Longrightarrow> hd ys \<in> dom_fg (alt h2 h1 xss)"
      for xss ys
      by (induction xss rule: alternating'_induct'[where a=h1 and aa=h1 and bb=h2 and b=h2], auto)

    have "0 < chain ?e' ?ns ?n (?i (hd ns))"
      using ne0 nss gr_zeroI by metis
    also have "... = chains' (chain ?e') ?zss ?n (?i (hd ns))"
      using XXX by simp
    also have "... \<le> chains' ?g1 ?zss ?n (?i (hd ns))"
      by (rule alternating_chains'_mono[OF zss_alt X1 X2], simp_all)
    also have "... \<le> chains' ?g2 ?zss ?n (?i (hd ns))"
      by (rule alternating_chains'_mono[OF zss_alt X4 X5], simp_all add: assms)
    also have "... = chains' ?g3 ?zss ?n (?i (hd ns))"
      apply (subst \<open>dom_fg h1 = dom_fg h1'\<close>)
      apply (subst \<open>dom_fg h1 = dom_fg h1'\<close>)
      apply (subst \<open>dom_fg h1 = dom_fg h1'\<close>)
      apply (subst \<open>dom_fg h2 = dom_fg h2'\<close>)
      apply (subst \<open>dom_fg h2 = dom_fg h2'\<close>)
      apply (subst \<open>dom_fg h2 = dom_fg h2'\<close>)
      apply (rule chains'_switch_world[of h1 h2 ?zss "hd nss2" h1' h2' E "?i (hd ns)"])
      using nss xssdef yssdef apply simp_all
      subgoal using nss2_ne zss apply safe using zss by simp_all
      using \<open>?N1 = ?N1'\<close> apply simp
      using assms nss2_ne apply (simp_all (no_asm_simp))
          apply (metis Un_iff in_set_butlastD zss(3) zss(5))
         apply presburger
        apply presburger
       apply blast
      apply (subst S2, rule inf_fg_le_inf_fg)
        apply blast
      using S2 True by presburger
    also have "... \<le> chains' ?g3 ?zss ?n (?i1 (hd ns))"
      apply (rule pos_endo_mono'_closed[OF inf_fg_le_inf_fg])
      using assms apply blast
      using True assms(16) apply blast
        apply blast
       apply (rule endo_chains')
      using assms apply blast
        apply auto[1]
      by (auto simp: assms endo_cap')+
    also have "... = chains' ?g3 ?uss ?n (chains' ?g3 (nss1 @ [ns1 @ n # ns2]) (hd (concat ?uss @ [?n])) (?i1 (hd ns)))"
      apply (rule chains'_append) using WWW apply simp using zss by (smt alternating_props zss')
    also have "... = chains' ?g3 ?uss ?n (chains' ?g3 (nss1 @ [ns1 @ n # ns2]) (hd (concat ?uss @ [?n])) (?i1 (hd (hd (nss1 @ [ns1 @ n # ns2])))))"
      using S3 by simp
    also have "... = chains' ?g3 ?uss ?n (chains' ?g3 (nss1 @ [ns1 @ n # ns2]) (hd (hd nss2)) (?i1 (hd (hd (nss1 @ [ns1 @ n # ns2])))))"
      by (metis (no_types, lifting) append_self_conv2 hd_append2 list.sel(1) MMM)
    also have "... \<le> chains' ?g3 ?uss ?n (inf_fg (alt h2 h1 (nss1 @ [ns1 @ n # ns2])) (hd (hd nss2)))"
      apply (rule pos_endo_mono'_closed[where E=E and f="chains' ?g3 ?uss ?n", OF chains'_cap_fg_inf_fg_le_inf_fg'[of "\<lambda>h1' xs. set xs \<subseteq> dom_fg h1'" h1 h2 _ _ h E]])
      apply (simp only: prefix_alt \<open>?N1 = ?N1'\<close> \<open>?N2 = dom_fg h2'\<close>)
      using assms apply blast+
      using assms apply (simp_all (no_asm) add: zero_fun_def)
      apply (metis Un_iff \<open>butlast xss = nss1 @ (ns1 @ n # ns2) # butlast nss2\<close> in_set_butlastD set_append zss(3))
      using  zss nss 
      subgoal premises prems proof -
        have "alternating (segment_fg h1) (segment_fg h2) ((nss1 @ [ns1 @ n # ns2]) @ butlast nss2 @ [last nss2 @ zs] @ zss)"
          using zss' WWW by simp
        then have "alt (segment_fg h2) (segment_fg h1) (nss1 @ [ns1 @ n # ns2]) (hd (butlast nss2 @ [last nss2 @ zs]))"
          using alternating_append_inner[of "segment_fg h1" "segment_fg h2" "nss1 @ [ns1 @ n # ns2]" "butlast nss2 @ [last nss2 @ zs] @ zss"] nss2_ne
          by (metis (no_types, lifting) append_is_Nil_conv append_self_conv2 hd_append2 list.simps(3))
        then have "segment_fg (alt h2 h1 (nss1 @ [ns1 @ n # ns2])) (hd (butlast nss2 @ [last nss2 @ zs]))"
          by (subst (asm) alt_P_P_hom[of segment_fg h2 h1], simp)
        then show ?thesis using nss2_ne zss(6)
          by (metis (no_types, lifting) append_Nil2 append_butlast_last_id list.set_sel(1) n_hd subsetD zss(7))
      qed
      apply (rule endo_chains'[where E=E], simp_all (no_asm), intro allI conjI impI)
      by (rule endo_cap'[where E=E], simp_all (no_asm) add: zero_fun_def)+
    also have "... \<le> (\<Sum>xs\<in>l_lists' (dom_fg h) (card (dom_fg h) * length ?uss). chain (edge_fg h) (hd (hd ?uss) # xs) ?n (inf_fg (alt h2 h1 (nss1 @ [ns1 @ n # ns2])) (hd (hd nss2))))"
      apply (subst chains'_cong[OF blub[symmetric]], simp)
      apply (rule chains'_cap_inf_le_chain_sum[where E=E])
      apply (rule alternating_consequence[OF uss_alt])
      apply (safe, induction nss1 arbitrary: h1 h2, simp)
      apply auto[1]
      apply simp
      subgoal premises prems for x
      proof -
        have "\<not> (alt (len_segment_fg h2) (len_segment_fg h1) (nss1 @ [ns1 @ n # ns2]) [])"
          by (rule alt_cases, auto)
        then show False using prems by auto
      qed
      apply (induction nss1 arbitrary: h1 h2)
      apply auto[1]
      apply simp
      subgoal premises prems for x
      proof -
        have "\<not> (alt (len_segment_fg h1) (len_segment_fg h2) (nss1 @ [ns1 @ n # ns2]) [])"
          by (rule alt_cases, auto)
        then show False using prems by auto
      qed
      using \<open>h \<noteq> bot\<close> apply blast
      using alt_sum[of h2 h1] \<open>h = h1 + h2\<close> apply (auto simp: algebra_simps)[1]
      subgoal apply simp using zss nss xssdef nss2_ne
        by (metis (no_types, lifting) Un_iff in_set_butlastD insert_iff last_in_set list.set(2) set_append)
      subgoal apply (subst alt_alt_to_alt) using AUXAUX[OF zss(1)] WWW by simp
      subgoal using nss xssdef zss' alternating_props[OF zss'] WWW nsdef \<open>?N1 = ?N1'\<close> \<open>?N2 = dom_fg h2'\<close> \<open>h = h1 + h2\<close> \<open>h \<noteq> bot\<close>
        by (smt UnCI plus_fg_dom_un set_append set_subset_Cons subsetD)
      using "***"(7) assms dom_subs(1) apply blast
      using assms apply blast
      using alt_edge assms
      apply (metis \<open>len_segment_fg h1 (ns1 @ n # ns2) \<or> len_segment_fg h2 (ns1 @ n # ns2)\<close> append_is_Nil_conv concat.simps(1) concat.simps(2))
      using alt_edge assms
      apply (metis \<open>len_segment_fg h1 (ns1 @ n # ns2) \<or> len_segment_fg h2 (ns1 @ n # ns2)\<close> append_is_Nil_conv concat.simps(1) concat.simps(2))
      using assms apply simp_all
      using nss2_ne apply (cases nss2, blast)
      by (metis append_self_conv2 hd_append2 list.sel(1) list.simps(3) n_hd order_refl)
    finally obtain ys where ys: "ys \<in> l_lists' (dom_fg h) (card (dom_fg h) * length (butlast nss2 @ [last nss2 @ zs] @ zss))"
      "chain ?e (hd (hd ?uss) # ys) ?n (inf_fg (alt h2 h1 (nss1 @ [ns1 @ n # ns2])) (hd (concat ?uss @ [?n]))) \<noteq> 0"
      by (smt gr_implies_not_zero sum.not_neutral_contains_not_neutral nss2_ne BRUM)

    have alternating'_append1: "alternating' P Q (xs @ ys) z \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> alternating' P Q xs (hd ys)" for P Q xs ys z
      by (induction xs arbitrary: P Q, auto, cases ys, auto)

    show False
      apply (rule contradict_eff_acyclic_flow[OF \<open>eff_acyclic' h\<close>, where E=E and ns="hd (hd ?uss) # ys" and n="?n"])
      subgoal proof -
        let ?zs = "nss1 @ [ns1 @ n # ns2]"

        have ALT: "alternating' (segment_fg h1) (segment_fg h2) (nss1 @ (ns1 @ n # ns2) # butlast nss2 @ [last nss2 @ zs] @ zss) (hd nss2)"
          using WWW zss by presburger

        have "alternating' (segment_fg h1) (segment_fg h2) ?zs (hd (butlast nss2 @ [last nss2 @ zs] @ zss))"
          apply (rule alternating'_append1[of _ _ ?zs "butlast nss2 @ [last nss2 @ zs] @ zss"])
          using ALT by auto
        then have ALT: "alternating' (segment_fg h1) (segment_fg h2) ?zs (hd (butlast nss2 @ [last nss2 @ zs]))"
          using nss2_ne
          by (metis (no_types, lifting) append_self_conv2 hd_append2 not_Cons_self2)

        have S: "hd (concat (butlast nss2 @ [last nss2 @ zs] @ zss) @ [hd (hd nss2)]) = hd (hd (hd (butlast nss2 @ [last nss2 @ zs] @ zss)) # ys)"
          using nss2_ne by (cases nss2, simp, simp)

        have BRUM2: "hd (hd (butlast nss2 @ [last nss2 @ zs])) = hd (concat (butlast nss2 @ [last nss2 @ zs] @ zss) @ [hd (hd nss2)])"
          using nss2_ne BRUM n_hd zss(7) by auto

        have "0 < chain ?e (hd (hd ?uss) # ys) ?n (inf_fg (alt h2 h1 ?zs) (hd (concat ?uss @ [?n])))"
          using ys gr_zeroI by auto
        also have "... \<le> chain ?e (hd (hd ?uss) # ys) ?n (flow_fg h (hd (concat ?uss @ [?n])))"
          using alternating_inf_fg_flow_fg[OF _ _ _ zss(1)]
          apply simp using n_hd[symmetric] BRUM2[symmetric] apply simp
          apply (rule pos_endo_mono'_closed[where f="chain _ _ _" and E=E, OF alternating_inf_fg_flow_fg[OF _ _ _ ALT]])
          using assms apply blast
          using assms apply blast
            apply (metis \<open>last xss = last nss2\<close> append_Nil append_butlast_last_id hd_append2 list.sel(1) nss2_ne(1) nss2_ne(2) zss(4))
           apply (simp add: assms(10) assms(18) endo_chain_closed_nonempty)
          using assms by blast
        finally show ?thesis 
          using S by simp
      qed
      subgoal using nss2_ne apply (cases nss2, simp, simp, intro conjI)
        using assms(2) hd_hd_uss_in_h1h2 n_hd apply auto[1]
        using ys unfolding l_lists'_def by simp
      subgoal using nss2_ne by (cases nss2, simp, simp)
      using assms by blast+
  qed
qed


text \<open>Case 1 (@{term "h1 = dom_fg h1'"}) of Theorem 3 in @{cite krishna20}\<close>

lemma maintain_eff_acyclic_dom_eq:
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "pointwise_reduced E" "h = h1 + h2" "h \<noteq> bot" "h1' \<noteq> bot" "h1 \<lesssim>\<^sub>S h1'" "dom_fg h1' \<inter> dom_fg h2 = {}"
    "\<forall>n \<in> dom_fg h1' - dom_fg h1. outf_fg h2 n = 0"
    "\<forall>x y. edge_fg h x y \<in> E"
    "eff_acyclic' h" "eff_acyclic' h1" "eff_acyclic' h1'" "eff_acyclic' h2"
    "dom_fg h1 = dom_fg h1'" "End_closed E" "id \<in> E"
    "\<forall>x y. edge_fg h2 x y \<in> E" "\<forall>x y. edge_fg h1 x y \<in> E" "\<forall>x y. edge_fg h1' x y \<in> E" "\<forall>x y. edge_fg (h1' + h2) x y \<in> E"
    "(\<lambda>_. 0) \<in> E" "id \<in> E"
    "\<forall>n\<in>dom_fg h1. \<forall>n'\<in>- dom_fg h1'. \<forall>m\<le>inf_fg h1 n. cap_fg h1 n n' m = cap_fg h1' n n' m"
    "\<forall>n\<in>dom_fg h2. \<forall>n'\<in>- dom_fg h2. \<forall>m\<le>inf_fg h2 n. cap_fg h2 n n' m = cap_fg h2 n n' m" "\<forall>x y. edge_fg (h1 + h2) x y \<in> E"
  shows "\<exists>h'. h' = h1' + h2 \<and> h' \<noteq> bot \<and> eff_acyclic' h' \<and> h \<lesssim>\<^sub>S h'"
proof -
  have *: "h1 \<noteq> bot" "h2 \<noteq> bot" using assms plus_fg_ops_exist by auto
  then have **: "int_fg h1 = int_fg h1'" "\<forall>n \<in> dom_fg h1. \<forall>n' \<in> -dom_fg h1. \<forall>m \<le> inf_fg h1 n. cap_fg h1 n n' m = cap_fg h1' n n' m"
    using assms unfolding subflow_preserving_extension_def contextual_extension_def int_fg_def by (auto intro: fi_cong)

  have nbot: "h1' + h2 \<noteq> bot" "int_fg (h1' + h2) = int_fg (h1 + h2)"
    using assms int_fg_fi_hom[of h1' h2] int_fg_fi_hom[of h1 h2] **
    by (metis int_fg_bot_bot int_fg_bot_bot')+
  then have infeq: "inf_fg (h1' + h2) = inf_fg (h1 + h2)" "int_fg h1' = int_fg h1"
    using int_fg_to_inf_fg ** by auto

  let ?h2' = "h2"
  have ext2: "\<forall>n \<in> dom_fg h2. \<forall>n' \<in> -dom_fg h2. \<forall>m \<le> inf_fg h2 n. cap_fg h2 n n' m = cap_fg ?h2' n n' m"
    by simp

  have ea_h1'h2: "eff_acyclic' (h1' + ?h2')"
  proof (rule ccontr)
    let ?h' = "h1' + h2"
    let ?h = "h1 + h2"
    let ?e' = "edge_fg ?h'"
    let ?e1' = "edge_fg h1'"
    let ?e2' = "edge_fg h2"
    let ?e = "edge_fg h" let ?e1 = "edge_fg h1" let ?e2 = "edge_fg h2"
    let ?f' = "flow_fg ?h'"
    let ?N' = "dom_fg ?h'"
    let ?N1 = "dom_fg h1"
    let ?N2 = "dom_fg h2"
    let ?N1' = "dom_fg h1'"
    let ?N = "dom_fg h" let ?Na = "dom_fg h1" let ?Nb = "dom_fg h2"
    let ?i = "inf_fg ?h"
    let ?i' = "inf_fg ?h'"
    let ?i1 = "inf_fg h1"
    let ?f = "flow_fg (h1 + h2)"
    let ?f1 = "flow_fg h1"
    let ?f1' = "flow_fg h1'"
    let ?i1' = "inf_fg h1'"
    let ?i2' = "inf_fg ?h2'"

    assume "\<not> eff_acyclic' ?h'"
    then have "\<exists>xs y. chain (edge_fg (h1' + h2)) xs y (inf_fg (h1 + h2) (hd xs)) \<noteq> 0 \<and>
                      y \<in> set xs \<and> set xs \<subseteq> dom_fg (h1' + h2)"
      apply (rule eff_acyclic_sourced_path_in_bigraph[of h1' h2 h1 h2 E])
      using assms nbot infeq apply blast+
      using assms unfolding zero_fun_def apply simp
      using infeq apply simp
      using ** assms by blast+
    then obtain ns n where nsdef:
      "chain (edge_fg (h1' + h2)) ns n (inf_fg (h1 + h2) (hd ns)) \<noteq> 0"
      "n \<in> set ns" "set ns \<subseteq> dom_fg (h1' + h2)"
      by blast

    let ?k = "length ns"

    show False
    proof (cases "set ns \<subseteq> dom_fg h1' \<or> set ns \<subseteq> dom_fg h2")
      case True
      then consider (a) "set ns \<subseteq> dom_fg h1'" | (b) "set ns \<subseteq> dom_fg h2"
        by auto
      then show ?thesis
      proof (cases)
        case a
        have "0 < chain ?e1' ns n (?i' (hd ns))"
          using nsdef assms a infeq chain_cong'[OF edge_fg_plus_fg_on1[of h1' h2], of "ns" n] nbot
          by (metis gr_zeroI)
        also have "... \<le> chain ?e1' ns n (?i1' (hd ns))"
          apply (rule chain_mono[OF inf_fg_le_inf_fg[of h1' h2, where E=E], where E=E])
          using nbot assms apply blast
             apply (metis a equals0D hd_in_set nsdef(2) set_empty subset_code(1))
          using assms by blast+
        finally have T: "chain ?e1' ns n (?i1' (hd ns)) \<noteq> 0"
          by simp
        show ?thesis
          using contradict_eff_acyclic[OF \<open>eff_acyclic' h1'\<close> T, where E=E] assms nsdef a 
          by metis
      next
        case b
        have "0 < chain ?e2' ns n (?i' (hd ns))"
          using nsdef assms b infeq chain_cong'[OF edge_fg_plus_fg_on2[of h1' h2], of "ns" n] nbot
          by (metis gr_zeroI)
        also have "... \<le> chain ?e2' ns n (?i2' (hd ns))"
          apply (rule chain_mono[OF inf_fg_le_inf_fg2[of h1' h2, where E=E], where E=E])
          using assms nbot apply blast
          apply (metis b empty_iff hd_in_set list.set(1) nsdef(2) subset_code(1))
          using assms by blast+
        finally have T: "chain ?e2' ns n (?i2' (hd ns)) \<noteq> 0"
          by simp
        show ?thesis
          using contradict_eff_acyclic[OF \<open>eff_acyclic' h2\<close> T, where E=E] assms nsdef b *
          by metis
      qed
    next
      case False
      moreover have dom: "dom_fg h1' \<inter> dom_fg h2 = {}" "ns \<noteq> []"
          "set ns \<subseteq> dom_fg h1' \<union> dom_fg h2" "dom_fg h1' \<inter> dom_fg h2 = {}"
          "?N1 \<inter> ?N2 = {}" "?N1 \<union> ?N2 = ?N"
        using False nsdef ck_lists_props[of ns "dom_fg (h1' + h2)" ?k] nbot
        using assms(6) apply blast
        using nsdef nbot \<open>h = h1 + h2\<close> \<open>h \<noteq> bot\<close> by auto
      ultimately obtain n1 n2 where ***: "n1 \<in> set ns" "n2 \<in> set ns" "n1 \<notin> dom_fg h1'"
        "n2 \<notin> dom_fg h2" "n1 \<noteq> n2" "n1 \<in> dom_fg h2" "n2 \<in> dom_fg h1'"
        by blast
      then have "length ns \<ge> 2"
        using length_ge_2[of ?N1 ?N2 n2 n1 ns] assms dom by blast+
      then have "butlast ns \<noteq> []"
        by (cases ns, simp_all, case_tac list, simp_all)

      show ?thesis
      proof (cases "hd ns \<in> dom_fg h1'")
        case True
        show ?thesis
          using maintain_eff_acyclic_dom_eq'[of E h h1 h2 "h1' + h2" h1' h2 ns n]
          using assms nbot infeq False True nsdef by blast+
      next
        case False
        then have blub: "hd ns \<in> dom_fg h2"
          using dom(2) list.set_sel(1) nbot(1) nsdef(3) by auto
        have bla: "h = h2 + h1" "h2 + h1' \<noteq> bot"
          using assms(2) plus_fg_comm apply blast
          by (simp add: nbot(1) plus_fg_comm)
        show ?thesis
          apply (rule maintain_eff_acyclic_dom_eq'[of E h h2 h1 "h2 + h1'" h2 h1' ns n])
          using assms nbot infeq False False nsdef \<open>\<not> (set ns \<subseteq> dom_fg h1' \<or> set ns \<subseteq> dom_fg h2)\<close> *
            subflow_preserving_extension_refl[of h2] blub bla assms nbot apply blast+
          using nbot assms apply (simp (no_asm) add: algebra_simps)
          using assms nbot infeq False False nsdef \<open>\<not> (set ns \<subseteq> dom_fg h1' \<or> set ns \<subseteq> dom_fg h2)\<close> *
            subflow_preserving_extension_refl[of h2] blub bla assms nbot apply blast+
          using nbot assms apply (simp (no_asm) add: algebra_simps)
          using assms nbot infeq False False nsdef \<open>\<not> (set ns \<subseteq> dom_fg h1' \<or> set ns \<subseteq> dom_fg h2)\<close> * 
            subflow_preserving_extension_refl[of h2] blub bla assms nbot apply blast+
          using nbot assms apply (simp (no_asm) add: algebra_simps)
          using nbot assms infeq apply (simp (no_asm) add: algebra_simps)
          using assms nbot infeq False False nsdef \<open>\<not> (set ns \<subseteq> dom_fg h1' \<or> set ns \<subseteq> dom_fg h2)\<close> *
            subflow_preserving_extension_refl[of h2] blub bla assms nbot apply blast+
          subgoal by (simp add: add.commute nsdef(1))
           apply (simp add: nsdef(2))
          by (simp add: add.commute dom(3) nbot(1))
      qed
    qed
  qed

  have ext': "int_fg h \<lesssim> int_fg (h1' + h2)"
    unfolding contextual_extension_def
    using \<open>h = h1 + h2\<close> nbot \<open>h \<noteq> bot\<close> \<open>dom_fg h1 = dom_fg h1'\<close>
    by simp

  have dom: "dom_fg (h1 + h2) = dom_fg (h1' + h2)"
    by (metis dom_fi_int_fg nbot(2))

  have cap1: "\<forall>n\<in>dom_fg (h1 + h2). \<forall>n'\<in>- dom_fg (h1' + h2). \<forall>m\<le>inf_fg h n.
    cap_fg (h1 + h2) n n' m = cap_fg (h1' + h2) n n' m"
    apply safe
    subgoal for n n' m
      apply (rule cap_fg_eq_cap_fg[of m "h1 + h2" n n' h1 h2 "h1' + h2" h1' h2 E])
      using assms dom  apply blast
      using assms apply blast
      using dom apply blast
      using assms apply blast
      using assms apply blast
      using assms apply blast
      using nbot apply blast
      using assms apply blast
      using assms apply blast
      using assms apply blast
      using assms apply blast
      using assms apply blast
      using assms apply blast
      using assms apply blast
      apply (simp add: assms(2) infeq(1))
      using assms apply blast
      using assms apply blast
      using assms apply blast
      using dom apply blast
      using assms apply blast
      using assms apply blast
      using ea_h1'h2 apply blast
      using assms apply blast
      using assms apply blast
      using assms unfolding zero_fun_def apply blast
      using assms apply blast
      using assms apply blast
      using assms apply blast
      using assms apply blast
      done
    done

  have ext: "h \<lesssim>\<^sub>S (h1' + h2)"
    unfolding subflow_preserving_extension_def
    using ext' assms cap1 
    by (metis Diff_cancel dom empty_iff)

  show ?thesis
    apply (rule exI[where x="h1' + h2"])
    using ea_h1'h2 nbot ext by simp
qed

text \<open>@{cite \<open>lem. 3.39\<close> krishna19a}, required by @{term maintain_eff_acyclic_dom_ne}\<close>

lemma plus_fg_eff_acyclic:
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "h' = h0 + h" "h' \<noteq> bot" "\<forall>n n'. edge_fg h0 n n' = (\<lambda>_. 0)" "eff_acyclic' h"
    "\<forall>x y. edge_fg h' x y \<in> E" "End_closed E" "id \<in> E"
  shows "eff_acyclic' h'"
  unfolding eff_acyclic'_def eff_acyclic_def
proof safe
  fix k ns
  show "1 \<le> k \<Longrightarrow> ns \<in> k_lists (dom_fg h') k
        \<Longrightarrow> chain (edge_fg h') ns (hd ns) (flow_fg h' (hd ns)) = 0"
  proof -
    assume A: "k \<ge> 1" "ns \<in> k_lists (dom_fg h') k"
  
    show "chain (edge_fg h') ns (hd ns) (flow_fg h' (hd ns)) = 0"
    proof (cases "set ns \<subseteq> dom_fg h")
      case True
      then have X: "ns \<in> k_lists (dom_fg h) k" "edge_fg h' = edge_fg h on dom_fg h"
        "flow_fg h' = flow_fg h on dom_fg h"
        using A edge_fg_plus_fg_on2 flow_fg_plus_fg_on2[of h0 h] assms
        unfolding k_lists_def
        by auto
      moreover have B: "ns \<in> k_lists (dom_fg h) k"
        using True A unfolding k_lists_def by blast
      ultimately show ?thesis
        using A assms unfolding eff_acyclic'_def eff_acyclic_def
        apply (subst chain_cong[of _ _ "edge_fg h"])
        using on_eq_superset[OF True edge_fg_plus_fg_on2[of h0 h]] assms
        apply (simp add: k_lists_nonempty(2))
        apply (subst X(3))
        using True A B set_hd_in[of ns "dom_fg h"]
        unfolding k_lists_def
        by auto
    next
      case False
      then obtain n where B1: "n \<in> set ns" "n \<in> -dom_fg h" by auto
      then obtain ns1 ns2 where B2: "ns = ns1 @ n # ns2" using split_list[of n ns] by auto

      let ?e' = "edge_fg h'"

      have C: "n \<in> dom_fg h0"
      proof -
        have "dom_fg h0 \<inter> dom_fg h = {}" "dom_fg h0 \<union> dom_fg h = dom_fg h'"
          using assms by auto
        moreover have "n \<in> dom_fg h'"
          using A B1 unfolding k_lists_def by blast
        ultimately show ?thesis
          using B1 by auto
      qed
      then have "edge_fg h0 n (hd (ns2 @ [hd ns])) = (\<lambda>_. 0)"
        using assms by simp
      then have C: "?e' n (hd (ns2 @ [hd ns])) = (\<lambda>_. 0)"
        using edge_fg_plus_fg_on1[of h0 h] assms C by simp
      have D: "chain ?e' ns (hd ns) =
        chain ?e' (n # ns2) (hd ns) o chain ?e' ns1 (hd ((n # ns2) @ [hd ns]))"
        using B1 B2 chain_append_nonempty[of "edge_fg h'" ns1 "n#ns2" "hd ns"]
        by auto
      then have "chain ?e' ns (hd ns) =
        chain ?e' ns2 (hd ns) o ?e' n (hd (ns2 @ [hd ns])) o chain ?e' ns1 (hd ((n # ns2) @ [hd ns]))"
        using B2 by (cases ns2, auto)
      then have "chain ?e' ns (hd ns) = chain ?e' ns2 (hd ns) o 0 o chain (edge_fg h') ns1 n"
        using C by auto
      then have "chain ?e' ns (hd ns) = (\<lambda>_. 0)"
        using endo_f_0_0_closed[of "chain ?e' ns2 (hd ns)" E] endo_chain_closed[of ?e' E] assms B2
        by fastforce
      then show ?thesis
        by simp
    qed
  qed
qed

text \<open>@{cite \<open>lem. 3.40\<close> krishna19a}, required by @{term maintain_eff_acyclic_dom_ne}\<close>
lemma outf_eq_h0:
  assumes "h' = h0 + h" "h' \<noteq> bot" "\<forall>x y. edge_fg h0 = (\<lambda>_ _ _. 0)"
  shows "\<forall>n' \<in> -dom_fg h'. outf_fg h' n' = outf_fg h n'"
proof
  fix x
  assume A: "x \<in> -dom_fg h'"

  have "outf_fg (h0 + h) x = outf_fg h0 x + outf_fg h x"
    using outf_fg_plus_fg[of h0 h] A assms by simp
  also have "... = (\<Sum>x' \<in> dom_fg h0. edge_fg h0 x' x (flow_fg h0 x')) + outf_fg h x"
    using outf_fg_unfold[of h0 x] A assms by fastforce
  finally show "outf_fg h' x = outf_fg h x"
    using assms by simp
qed

text \<open>@{cite \<open>lem. 3.41\<close> krishna19a}, required by @{term maintain_eff_acyclic_dom_ne}\<close>
lemma cap_outside_eq_h':
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "h' = h0 + h" "h' \<noteq> bot" "\<forall>x y. edge_fg h0 = (\<lambda>_ _ _. 0)" "End_closed E"
    "\<forall>x y. edge_fg h' x y \<in> E" "\<forall>x y. edge_fg h x y \<in> E" "eff_acyclic' h" "id \<in> E" "(\<lambda>_. 0) \<in> E"
  shows "\<forall>n \<in> dom_fg h'. \<forall>n' \<in> -dom_fg h'. \<forall>m \<le> inf_fg h' n.
            cap_fg h' n n' m = (if n \<in> dom_fg h then cap_fg h n n' m else 0)"
proof safe
  fix n n' m
  assume A: "n \<in> dom_fg h'" "n' \<notin> dom_fg h'" "m \<le> inf_fg h' n"

  let ?N' = "dom_fg h'" let ?e' = "edge_fg h'"
  let ?N = "dom_fg h" let ?e = "edge_fg h"
  let ?XS' = "l_lists' ?N' (card ?N')"
  let ?XS = "l_lists' ?N (card ?N)"
  let ?XS1' = "{xs \<in> ?XS'. set xs \<subseteq> ?N}"
  let ?XS2' = "{xs \<in> ?XS'. \<not> (set xs \<subseteq> ?N)}"
  let ?XS1 = "{xs \<in> ?XS1'. length xs < card ?N}"
  let ?XS2 = "{xs \<in> ?XS1'. length xs \<ge> card ?N}"

  show "cap_fg h' n n' m = (if n \<in> dom_fg h then cap_fg h n n' m else 0)"
  proof (cases "n \<in> dom_fg h")
    case True

    have XS: "?XS' = ?XS1' \<union> ?XS2'" "?XS1' \<inter> ?XS2' = {}"
      unfolding l_lists'_def by auto

    have XS2: "?XS1' = ?XS1 \<union> ?XS2" "?XS1 \<inter> ?XS2 = {}"
      unfolding l_lists'_def by auto

    have F1: "finite ?XS1'"
      by simp
    have F2: "finite ?XS2'"
      by simp
    have F3: "finite ?XS1"
      by simp
    have F4: "finite ?XS2"
      by simp

    have Z: "(\<Sum>ns\<in>?XS2'. chain2 ?e' n ns n' m) = 0"
      apply (rule sum.neutral)
    proof
      fix xs
      assume A: "xs \<in> ?XS2'"
      then obtain x where B: "x \<notin> ?N" "x \<in> set xs" by auto
      then have "x \<in> dom_fg h'" using assms A unfolding l_lists'_def by auto
      then have C: "x \<in> dom_fg h0" using B assms by auto

      have E: "?e' x = (\<lambda>_ _. 0)"
        using edge_fg_plus_fg_on1[of h0 h] assms C by simp

      obtain xs1 xs2 where D: "xs = xs1 @ x # xs2"
        using split_list[OF B(2)] by auto
      have "chain2 ?e' n xs n' m = chain ?e' (n # xs) n' m"
        using chain2_chain by metis
      also have "... = chain ?e' (x # xs2) n' (chain ?e' (n # xs1) (hd ((x # xs2) @ [n'])) m)"
        using D chain_append_nonempty[of ?e' "n # xs1" "x #xs2" n' m] by simp
      also have "... = chain ?e' (x # xs2) n' 0"
        by (cases xs2, simp_all add: E)
      also have "... = 0"
        apply (rule endo_f_0_0_closed)
        apply (rule endo_chain_closed[where E=E], simp_all add: assms)
        apply (rule endo_edge_fg_plus_fg)
        using assms by simp_all
      finally show "chain2 ?e' n xs n' m = 0" .
    qed

    have ZZ: "(\<Sum>ns\<in>?XS2. chain2 ?e n ns n' m) = 0"
      apply (rule sum.neutral)
    proof
      fix xs
      assume AA: "xs \<in> ?XS2"

      have "chain2 ?e n xs n' m = chain ?e (n # xs) n' m"
        using chain2_chain by metis
      also have "... \<le> chain ?e (n # xs) n' (inf_fg h' n)"
        by (rule chain_mono[OF A(3), where E=E], simp_all add: assms)
      also have "... \<le> chain ?e (n # xs) n' (inf_fg h n)"
        apply (subst \<open>h' = h0 + h\<close>, rule chain_mono[OF inf_fg_le_inf_fg2[of h0 h]])
        using assms True by simp_all
      also have "... \<le> chain ?e (n # xs) n' (flow_fg h n)"
        apply (rule chain_mono[OF inf_fg_le_flow_fg])
        using assms True by auto
      also have "... \<le> chain ?e (n # xs) n' (flow_fg h (hd (n # xs)))"
        by simp
      also have "... = 0"
        apply (rule eff_acyclic'_chain_eq_0)
        using assms True AA by auto
      finally show "chain2 ?e n xs n' m = 0" by simp
    qed

    have S: "?XS1 = l_lists' ?N (card ?N)"
      using assms unfolding l_lists'_def
      apply auto
      using plus_fg_dom_disj
      by (metis add.right_neutral add_leD2 card_Un_Int card_empty dom_fg_finite not_le)
      
    have "cap_fg h' n n' m = \<delta> n n' m + (\<Sum>ns\<in>?XS'. chain2 ?e' n ns n' m)"
      apply (rule cap_unrolled_closed') using assms True by simp_all
    also have "... = \<delta> n n' m + (\<Sum>ns\<in>?XS1' \<union> ?XS2'. chain2 ?e' n ns n' m)"
      using XS by simp
    also have "... = \<delta> n n' m + ((\<Sum>ns\<in>?XS1'. chain2 ?e' n ns n' m) +
                                 (\<Sum>ns\<in>?XS2'. chain2 ?e' n ns n' m))"
      by (subst sum.union_disjoint[OF F1 F2 XS(2), symmetric], simp)
    also have "... = \<delta> n n' m + (\<Sum>ns\<in>?XS1'. chain2 ?e' n ns n' m)"
      using Z by simp
    also have "... = \<delta> n n' m + (\<Sum>ns\<in>?XS1 \<union> ?XS2. chain2 ?e' n ns n' m)"
      using XS2 by presburger
    also have "... = \<delta> n n' m + (\<Sum>ns\<in>?XS1 \<union> ?XS2. chain2 ?e n ns n' m)"
      apply (simp, rule sum.cong[OF _ chain2_cong_e], simp)
      using edge_fg_plus_fg_on2[of h0 h] assms True unfolding l_lists'_def by auto
    also have "... = \<delta> n n' m + ((\<Sum>ns\<in>?XS1. chain2 ?e n ns n' m) +
                                 (\<Sum>ns\<in>?XS2. chain2 ?e n ns n' m))"
      by (subst sum.union_disjoint[OF F3 F4 XS2(2), symmetric], simp)
    also have "... = \<delta> n n' m + (\<Sum>ns\<in>?XS1. chain2 ?e n ns n' m)"
      using ZZ by simp
    also have "... = \<delta> n n' m + (\<Sum>ns\<in>l_lists' ?N (card ?N). chain2 ?e n ns n' m)"
      using S by simp
    also have "... = cap_fg h n n' m"
      using cap_unrolled_closed'[of "edge_fg h" E "dom_fg h" n n'] assms True by auto
    finally show ?thesis
      using True
      by simp
  next
    case False
    then have D: "n \<in> dom_fg h0"
      using assms A by simp
    then have "edge_fg h0 n = (\<lambda>_ _. 0)"
      using assms by simp
    then have E: "edge_fg h' n = (\<lambda>_ _. 0)"
      using edge_fg_plus_fg_on1[of h0 h] assms D by simp

    have "cap_fg h' n n' m = \<delta> n n' m + (\<Sum>ns\<in>?XS'. chain2 ?e' n ns n' m)"
      apply (rule cap_unrolled_closed') using assms False A by simp_all
    also have "... = (\<Sum>ns\<in>?XS'. chain2 ?e' n ns n' m)"
      using A unfolding \<delta>_def by auto
    also have "... = (\<Sum>ns\<in>?XS'. chain ?e' (n # ns) n' m)"
      by (rule sum.cong, simp, rule chain2_chain)
    also have "... = 0"
      apply (rule sum.neutral, clarsimp)
      apply (case_tac x, simp add: E)
      apply (simp add: E)
      apply (rule endo_f_0_0_closed[where E=E])
       apply (rule endo_chain_closed, simp_all add: assms)
      apply (rule endo_edge_fg_plus_fg)
      using assms by simp_all
    finally show ?thesis
      using False by auto
  qed
qed

text \<open>Case 2 @{term "dom_fg h1 \<subset> dom_fg h1'"} of @{cite \<open>th. 3\<close> krishna20}\<close>

lemma maintain_eff_acyclic_dom_ne:
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes nbot: "h = h1 + h2" "h \<noteq> bot" "h1' \<noteq> bot"
    and dom: "dom_fg h1' \<inter> dom_fg h2 = {}" "dom_fg h1 \<subseteq> dom_fg h1'"
    and edge: "\<forall>n \<in> dom_fg h1' - dom_fg h1. outf_fg h2 n = 0" "\<forall>x y. edge_fg h x y \<in> E"
        "End_closed E" "id \<in> E" "\<forall>x y. edge_fg h2 x y \<in> E" 
        "\<forall>x y. edge_fg h1 x y \<in> E" "\<forall>x y. edge_fg h1' x y \<in> E" "\<forall>x y. edge_fg (h1' + h2) x y \<in> E"
        "(\<lambda>_. 0) \<in> E" "pointwise_reduced E"
    and ea: "eff_acyclic' h" "eff_acyclic' h1" "eff_acyclic' h1'" "eff_acyclic' h2"
      "h1 \<lesssim>\<^sub>S h1'" 
    and cap: "\<forall>n\<in>dom_fg h1. \<forall>n'\<in>- dom_fg h1'. \<forall>m\<le>inf_fg h1 n. cap_fg h1 n n' m = cap_fg h1' n n' m"
    "\<forall>n\<in>dom_fg h2. \<forall>n'\<in>- dom_fg h2. \<forall>m\<le>inf_fg h2 n. cap_fg h2 n n' m = cap_fg h2 n n' m"
  shows "\<exists>h'. h' = h1' + h2 \<and> h' \<noteq> bot \<and> eff_acyclic' h' \<and> h \<lesssim>\<^sub>S h'"
proof -
  let ?h' = "h1' + h2" let ?h = "h1 + h2"
  let ?e' = "edge_fg ?h'" let ?e1' = "edge_fg h1'" let ?e2' = "edge_fg h2"
  let ?e = "edge_fg h" let ?e1 = "edge_fg h1" let ?e2 = "edge_fg h2"
  let ?f' = "flow_fg ?h'" let ?o1' = "outf_fg h1'"
  let ?N' = "dom_fg ?h'" let ?N1 = "dom_fg h1" let ?N2 = "dom_fg h2" let ?N1' = "dom_fg h1'"
  let ?N = "dom_fg h" let ?Na = "dom_fg h1" let ?Nb = "dom_fg h2"
  let ?i = "inf_fg ?h" let ?i' = "inf_fg ?h'" let ?i1 = "inf_fg h1"
  let ?f = "flow_fg (h1 + h2)" let ?f1 = "flow_fg h1" let ?f1' = "flow_fg h1'"
  let ?i1' = "inf_fg h1'" let ?o1 = "outf_fg h1" let ?f2 = "flow_fg h2"

  let ?Nc = "?N1' - ?N1" let ?ec = "\<lambda>n n'. (\<lambda>_. 0)" let ?fc = "\<lambda>n. ?i1' n + ?o1 n"
  let ?hc = "fg ?Nc ?ec ?fc"

  let ?h1'' = "?hc + h1"

  let ?N1'' = "?Nc \<union> ?N1"
  let ?e1'' = "combined ?Nc ?N1 (\<lambda>_ _. 0) ?ec ?e1"
  let ?f1'' = "combined ?Nc ?N1 0 ?fc ?f1"

  have nbot_h1: "h1 \<noteq> bot"
    using nbot by auto

  have E: "?hc \<noteq> bot"
    by (rule fgI, auto)

  have I: "?i1 = ?i1' on ?N1" "?N1 \<subseteq> ?N1'" "?o1 = ?o1' on -?N1'"
    using ea nbot
    unfolding subflow_preserving_extension_def contextual_extension_def
      apply (auto simp: int_fg_def nbot_h1 subsetD)
    by (meson Compl_iff in_mono)

  have X1: "?f1'' = \<lambda>x. ?i1' x + (\<Sum>x' \<in> ?N1''. ?e1'' x' x (?f1'' x')) on ?N1''"
  proof
    fix x
    assume A: "x \<in> ?N1''"
    then show "?f1'' x = ?i1' x + (\<Sum>x' \<in> ?N1''. ?e1'' x' x (?f1'' x'))"
    proof (cases "x \<in> ?Nc")
      case True
      have "?f1'' x = ?i1' x + (\<Sum>x' \<in> ?N1. ?e1'' x' x (?f1'' x')) +
                               (\<Sum>x' \<in> ?Nc. ?e1'' x' x (?f1'' x'))"
        using True outf_fg_unfold[of h1 x] nbot_h1 unfolding combined_def by simp
      then show ?thesis
        by (smt Diff_partition Un_commute add.assoc add.commute dom(2) dom_fg_finite sum.subset_diff)
    next
      case False
      then have A: "x \<in> ?N1"
        using A by blast
      have "?f1'' x = ?i1' x + (\<Sum>x' \<in> ?N1. ?e1'' x' x (?f1'' x')) +
                               (\<Sum>x' \<in> ?Nc. ?e1'' x' x (?f1'' x'))"
        using flow_eq_ne_bot[OF nbot_h1] A I unfolding combined_def by simp
      also have "... = ?i1' x + (\<Sum>x' \<in> ?N1 \<union> ?Nc. ?e1'' x' x (?f1'' x'))"
        using sum.union_disjoint[of ?N1 ?Nc]
        by (smt Diff_partition add.assoc add.commute dom(2) dom_fg_finite sum.subset_diff)
      finally show ?thesis
        by (simp add: Un_commute)
    qed
  qed

  have nbot'': "fg ?N1'' ?e1'' ?f1'' \<noteq> bot"
    using X1 fgI[of ?N1'' ?f1'' ?i1' ?e1''] unfolding combined_def by auto
  have hch1_eq:  "?hc + fg ?N1 ?e1 ?f1 = fg ?N1'' ?e1'' ?f1''"
    apply (rule plus_fg_fg)
    using E nbot_h1 fg_components[of h1]
    by auto
  then have hch1_nbot: "?hc + h1 \<noteq> bot"
    using nbot_h1 fg_components[of h1] nbot''
    by simp
  have hch1_ea: "eff_acyclic' (?hc + h1)"
    apply (rule plus_fg_eff_acyclic[of "?hc + h1" ?hc h1 E], simp_all add: assms hch1_nbot E)
    using E apply auto[1]
    using endo_edge_fg_plus_fg[of E ?hc h1] assms hch1_nbot
    by simp

  have ***: "?hc + h1 = fg ?N1'' ?e1'' ?f1''"
    using fg_components[of h1]  hch1_eq \<open>h1 \<noteq> bot\<close> by simp
  then have *: "inf_fg ?h1'' = restrict ?N1'' 0 ?i1'"
    using inf_fg_fg[of ?N1''] X1 dom_fg_finite 
    by simp

  have **: "outf_fg ?h1'' = outf_fg h1 on -?N1''"
    using outf_eq_h0[of ?h1'' ?hc h1] nbot'' E hch1_nbot
    by auto

  have extfi: "int_fg (?h1'') \<lesssim> int_fg h1'"
    unfolding contextual_extension_def
    by (smt * ** *** Diff_cancel Diff_eq_empty_iff I(3) Un_Diff_cancel Un_commute
        dom(2) dom_fg_fg dom_fi_int_fg inf_fg_int_fg nbot'' nbot(3) outf_fi_int_fg subset_Un_eq)

  have hc_edge: "\<forall>x y. edge_fg ?hc x y \<in> E"
    using E edge by simp

  have cap: "\<forall>n \<in> ?N1''. \<forall>n' \<in> -?N1'. \<forall>m \<le> inf_fg ?h1'' n. cap_fg ?h1'' n n' m = cap_fg h1' n n' m"
  proof (safe, goal_cases)
    case (1 n n' m)
    then have A: "n \<in> ?Nc" by simp
    then have "cap_fg ?h1'' n n' m = 0"
      using cap_outside_eq_h'[of ?h1'' ?hc h1 E] 1 E \<open>End_closed E\<close>
        endo_edge_fg_plus_fg[OF \<open>End_closed E\<close> hch1_nbot hc_edge]
        \<open>eff_acyclic' h1\<close> \<open>\<forall>x y. edge_fg h1 x y \<in> E\<close> \<open>id \<in> E\<close> \<open>(\<lambda>_. 0) \<in> E\<close> hch1_nbot dom
      by (simp, metis (no_types, lifting) ComplI Un_absorb2 compl_sup)
    moreover have "cap_fg h1' n n' m = 0"
    proof -
      have "inf_fg ?h1'' n \<le> inf_fg ?hc n"
        apply (rule inf_fg_le_inf_fg[of ?hc h1 n E])
        using 1 hch1_nbot edge E by simp_all
      then show ?thesis
        using ea 1 * unfolding subflow_preserving_extension_def
        by auto
    qed
    ultimately show ?case
      by simp
  next
    case (2 n n' m)
    then have "cap_fg h1' n n' m = cap_fg h1 n n' m"
      using ea inf_fg_le_inf_fg2[of ?hc h1 n E] edge hch1_nbot
      unfolding subflow_preserving_extension_def 
      by auto
    moreover have "cap_fg ?h1'' n n' m = cap_fg h1 n n' m"
      using cap_outside_eq_h'[of ?h1'' ?hc h1 E] 2 E \<open>End_closed E\<close>
      using endo_edge_fg_plus_fg[OF \<open>End_closed E\<close> hch1_nbot hc_edge]
        \<open>eff_acyclic' h1\<close> \<open>\<forall>x y. edge_fg h1 x y \<in> E\<close> \<open>id \<in> E\<close> \<open>(\<lambda>_. 0) \<in> E\<close> hch1_nbot dom
      apply auto by (smt ComplI Un_absorb2 compl_sup in_mono)
    ultimately show ?case by simp
  qed

  have h1''_ext_h1': "?h1'' \<lesssim>\<^sub>S h1'"
    unfolding subflow_preserving_extension_def
    apply (intro conjI impI)
    using extfi apply simp
    using cap hch1_nbot E apply simp
    using E hch1_nbot by auto

  let ?N1'' = "dom_fg ?h1''"
  let ?e1'' = "edge_fg ?h1''"
  let ?f1'' = "flow_fg ?h1''"

  let ?h'' = "?h1'' + h2"

  let ?N'' = "?N1'' \<union> ?N2"
  let ?e'' = "combined ?N1'' ?N2 (\<lambda>_ _. 0) ?e1'' ?e2"
  let ?f'' = "combined ?N1'' ?N2 0 ?f1'' ?f2"
  let ?i'' = "\<lambda>x. if x \<in> ?N then ?i x else ?i1' x"

  have X2: "?f'' = \<lambda>x. ?i'' x + (\<Sum>x' \<in> ?N''. ?e'' x' x (?f'' x')) on ?N''"
  proof
    fix x
    assume "x \<in> ?N''"
    then have "x \<in> ?N1 \<union> ?N2 \<union> ?Nc"
      using hch1_nbot E by auto
    then consider (a) "x \<in> ?N1" | (b) "x \<in> ?N2" | (c) "x \<in> ?Nc"
      using hch1_nbot plus_fg_dom_un[of ?hc h1] E nbot by blast
    then show "?f'' x = ?i'' x + (\<Sum>x' \<in> ?N''. ?e'' x' x (?f'' x'))"
    proof cases
      case a
      have "?f'' x = ?f1 x"
        unfolding combined_def
        using nbot hch1_nbot E a flow_fg_plus_fg_on2'[of ?hc h1] by auto
      also have "... = ?f x"
        using flow_fg_plus_fg_on1'[of h1 h2 x] \<open>h = h1 + h2\<close> \<open>h \<noteq> bot\<close> a by simp
      also have "... = ?i x + (\<Sum>x' \<in> ?N. ?e x' x (?f x'))"
        using flow_eq_ne_bot[of "h1 + h2"] \<open>h = h1 + h2\<close> \<open>h \<noteq> bot\<close> a by simp
      also have "... = ?i x + (\<Sum>x' \<in> ?N1. ?e x' x (?f x')) + (\<Sum>x' \<in> ?N2. ?e x' x (?f x'))"
        unfolding combined_def
        using nbot hch1_nbot E a flow_fg_plus_fg_on2'[of ?hc h1] a \<open>?N1 \<subseteq> ?N1'\<close> \<open>?N1' \<inter> ?N2 = {}\<close>
        apply auto
        apply (subst sum.union_disjoint[OF dom_fg_finite dom_fg_finite])
        using edge_fg_plus_fg_on1'[of ?hc h1] hch1_nbot a
        by (auto simp: algebra_simps)
      also have "... = ?i x + (\<Sum>x' \<in> ?N1. ?e'' x' x (?f'' x')) + (\<Sum>x' \<in> ?N2. ?e x' x (?f x'))"
        unfolding combined_def
        using nbot hch1_nbot E a edge_fg_plus_fg_on2'[of ?hc h1]
        using flow_fg_plus_fg_on2'[of ?hc h1] a \<open>?N1 \<subseteq> ?N1'\<close> \<open>?N1' \<inter> ?N2 = {}\<close>
          edge_fg_plus_fg_on1'[of h1 h2] flow_fg_plus_fg_on1'[of h1 h2]
        by auto
      also have "... = ?i x + (\<Sum>x' \<in> ?N1. ?e'' x' x (?f'' x')) + (\<Sum>x' \<in> ?N2. ?e'' x' x (?f'' x'))"
        unfolding combined_def
        using nbot hch1_nbot E a edge_fg_plus_fg_on2'[of h1 h2]
        using flow_fg_plus_fg_on2'[of h1 h2] a \<open>?N1 \<subseteq> ?N1'\<close> \<open>?N1' \<inter> ?N2 = {}\<close>
        apply auto
        apply (subst (2) sum.cong[where h="\<lambda>x'. edge_fg h2 x' x (flow_fg h2 x')"])
        using dom by auto
      also have "... = ?i x + (\<Sum>x' \<in> ?N1 \<union> ?N2. ?e'' x' x (?f'' x'))"
        apply (subst sum.union_disjoint[OF dom_fg_finite dom_fg_finite])
        using nbot(1) nbot(2) plus_fg_dom_disj apply blast
        using add.assoc by blast
      also have "... = ?i x + ((\<Sum>x' \<in> ?N1 \<union> ?N2. ?e'' x' x (?f'' x')) + (\<Sum>x' \<in> ?Nc. ?e'' x' x (?f'' x')))"
        unfolding combined_def
        using nbot hch1_nbot E a edge_fg_plus_fg_on1'[of ?hc h1]
        using flow_fg_plus_fg_on1'[of ?hc h1] a \<open>?N1 \<subseteq> ?N1'\<close> \<open>?N1' \<inter> ?N2 = {}\<close>
        by auto
      also have "... = ?i x + (\<Sum>x' \<in> ?N1 \<union> ?N2 \<union> ?Nc. ?e'' x' x (?f'' x'))"
        apply (subst sum.union_disjoint[symmetric])
        using dom by auto
      finally show ?thesis
        using a \<open>h = h1 + h2\<close> \<open>h \<noteq> bot\<close> hch1_nbot E
        apply simp
        apply (rule sum.cong)
        by auto
    next
      case b
      have "?f'' x = ?f2 x"
        unfolding combined_def
        using b hch1_nbot E \<open>?N1 \<subseteq> ?N1'\<close> \<open>?N1' \<inter> ?N2 = {}\<close>
        by auto
      also have "... = ?f x"
        using flow_fg_plus_fg_on2'[of h1 h2 x] \<open>h = h1 + h2\<close> \<open>h \<noteq> bot\<close> b by simp
      also have "... = ?i x + (\<Sum>x' \<in> ?N. ?e x' x (?f x'))"
        using flow_eq_ne_bot[of "h1 + h2"] \<open>h = h1 + h2\<close> \<open>h \<noteq> bot\<close> b by simp
      also have "... = ?i x + (\<Sum>x' \<in> ?N1. ?e x' x (?f x')) + (\<Sum>x' \<in> ?N2. ?e x' x (?f x'))"
        unfolding combined_def
        using nbot hch1_nbot E b flow_fg_plus_fg_on2'[of ?hc h1] \<open>?N1 \<subseteq> ?N1'\<close> \<open>?N1' \<inter> ?N2 = {}\<close>
        apply auto
        apply (subst sum.union_disjoint[OF dom_fg_finite dom_fg_finite])
        using edge_fg_plus_fg_on1'[of ?hc h1] hch1_nbot
        by (auto simp: algebra_simps)
      also have "... = ?i x + (\<Sum>x' \<in> ?N1. ?e'' x' x (?f'' x')) + (\<Sum>x' \<in> ?N2. ?e x' x (?f x'))"
        unfolding combined_def
        using nbot hch1_nbot E b edge_fg_plus_fg_on2'[of ?hc h1]
        using flow_fg_plus_fg_on2'[of ?hc h1] \<open>?N1 \<subseteq> ?N1'\<close> \<open>?N1' \<inter> ?N2 = {}\<close>
          edge_fg_plus_fg_on1'[of h1 h2] flow_fg_plus_fg_on1'[of h1 h2]
        by auto
      also have "... = ?i x + (\<Sum>x' \<in> ?N1. ?e'' x' x (?f'' x')) + (\<Sum>x' \<in> ?N2. ?e'' x' x (?f'' x'))"
        unfolding combined_def
        using nbot hch1_nbot E b edge_fg_plus_fg_on2'[of h1 h2]
        using flow_fg_plus_fg_on2'[of h1 h2] \<open>?N1 \<subseteq> ?N1'\<close> \<open>?N1' \<inter> ?N2 = {}\<close>
        apply auto
        apply (subst (2) sum.cong[where h="\<lambda>x'. edge_fg h2 x' x (flow_fg h2 x')"])
        using dom by auto
      also have "... = ?i x + (\<Sum>x' \<in> ?N1 \<union> ?N2. ?e'' x' x (?f'' x'))"
        apply (subst sum.union_disjoint[OF dom_fg_finite dom_fg_finite])
        using nbot(1) nbot(2) plus_fg_dom_disj apply blast
        using add.assoc by blast
      also have "... = ?i x + ((\<Sum>x' \<in> ?N1 \<union> ?N2. ?e'' x' x (?f'' x')) +
                               (\<Sum>x' \<in> ?Nc. ?e'' x' x (?f'' x')))"
        unfolding combined_def
        using nbot hch1_nbot E edge_fg_plus_fg_on1'[of ?hc h1]
        using flow_fg_plus_fg_on1'[of ?hc h1] \<open>?N1 \<subseteq> ?N1'\<close> \<open>?N1' \<inter> ?N2 = {}\<close>
        by auto
      also have "... = ?i x + (\<Sum>x' \<in> ?N1 \<union> ?N2 \<union> ?Nc. ?e'' x' x (?f'' x'))"
        apply (subst sum.union_disjoint[symmetric])
        using dom by auto
      finally show ?thesis
        using b \<open>h = h1 + h2\<close> \<open>h \<noteq> bot\<close> hch1_nbot E
        apply simp
        apply (rule sum.cong)
        by auto
    next
      case c

      have "outf_fg h2 x = 0"
        using edge c by simp
      then have "(\<Sum>x' \<in> ?N2. ?e2 x' x (?f2 x')) = 0"
        using outf_fg_unfold[of h2 x]
        by (metis Diff_iff c disjoint_iff_not_equal dom(1) nbot(1) nbot(2) plus_fg_ops_exist)
      then have z: "\<And>x'. x' \<in> ?N2 \<Longrightarrow> ?e2 x' x (?f2 x') = 0"
        by simp

      have "?f'' x = ?i1' x + ?o1 x"
        unfolding combined_def
        using nbot hch1_nbot E flow_fg_plus_fg_on1'[of ?hc h1] c by auto
      also have "... = ?i1' x + (\<Sum>x' \<in> ?N1. ?e1 x' x (?f1 x'))"
        apply (subst outf_fg_unfold)
          apply (simp_all add: c nbot_h1)
        using c by blast
      also have "... = ?i1' x + (\<Sum>x' \<in> ?N1. ?e'' x' x (?f'' x'))"
        unfolding combined_def
        using nbot hch1_nbot E flow_fg_plus_fg_on2'[of ?hc h1] edge_fg_plus_fg_on2'[of ?hc h1] c
        by auto
      also have "... = ?i1' x + ((\<Sum>x' \<in> ?N1. ?e'' x' x (?f'' x')) +
                                 (\<Sum>x' \<in> ?Nc. ?e'' x' x (?f'' x')))"
        unfolding combined_def
        using nbot hch1_nbot E edge_fg_plus_fg_on1'[of ?hc h1] c
        by auto
      also have "... = ?i1' x + (\<Sum>x' \<in> ?N1 \<union> ?Nc. ?e'' x' x (?f'' x'))"
        by (subst sum.union_disjoint, simp_all)
      also have "... = ?i1' x + ((\<Sum>x' \<in> ?N1 \<union> ?Nc. ?e'' x' x (?f'' x')) +
                                 (\<Sum>x' \<in> ?N2. ?e'' x' x (?f'' x')))"
        unfolding combined_def
        using nbot hch1_nbot E edge_fg_plus_fg_on1'[of ?hc h1] c \<open>?N1 \<subseteq> ?N1'\<close> \<open>?N1' \<inter> ?N2 = {}\<close> z
        by auto
      also have "... = ?i1' x + (\<Sum>x' \<in> ?N1 \<union> ?Nc \<union> ?N2. ?e'' x' x (?f'' x'))"
        apply (subst sum.union_disjoint[symmetric])
        using dom by auto
      finally show ?thesis
        unfolding combined_def
        using nbot hch1_nbot E flow_fg_plus_fg_on1'[of ?hc h1] c apply auto
        using dom(1) apply blast
        apply (rule sum.cong)
        by auto
    qed
  qed

  have "finite ?N''"
    by simp
  then have h''_nbot: "fg ?N'' ?e'' ?f'' \<noteq> bot"
    using X2 fgI[of ?N'' ?f'' ?i'' ?e''] unfolding combined_def 
    using nbot hch1_nbot by blast

  have h1''h2_eq: "?h1'' + h2 = fg ?N'' ?e'' ?f''"
    apply (subst fg_components[of "?h1''", symmetric], simp add: hch1_nbot)
    apply (subst fg_components[of h2, symmetric])
    using nbot(1) nbot(2) plus_fg_ops_exist apply blast
    apply (rule plus_fg_fg)
    using hch1_nbot fg_components[of "?h1''"] apply simp
    using fg_components[of h2] nbot plus_fg_ops_exist[of h1 h2] apply simp
    using hch1_nbot dom E by auto
  then have h''_nbot: "?h'' \<noteq> bot"
    using hch1_nbot fg_components[of ?h1''] h''_nbot
    by presburger
  have h''_ea: "eff_acyclic' (?h1'' + h2)"
    apply (rule plus_fg_eff_acyclic[of "?h1'' + h2" ?hc "h1 + h2" E])
    apply (simp_all add: assms E algebra_simps)
      apply (metis (no_types, lifting) add.commute add.left_commute h''_nbot)
    using ea(1) nbot(1) apply blast
    apply (rule endo_edge_fg_plus_fg[OF \<open>End_closed E\<close> h''_nbot, simplified algebra_simps])
      apply (rule endo_edge_fg_plus_fg[OF \<open>End_closed E\<close> hch1_nbot, simplified algebra_simps])
    subgoal using E assms by simp
    using assms by blast+

  have "\<exists>h'. h' = h1' + h2 \<and> h' \<noteq> bot \<and> eff_acyclic' h' \<and>
        fg (dom_fg h1' - dom_fg h1) (\<lambda>n n' _. 0) (\<lambda>n. inf_fg h1' n + outf_fg h1 n) + h1 + h2 \<lesssim>\<^sub>S h'"
    apply (rule maintain_eff_acyclic_dom_eq[of E ?h'' ?h1'' h2 h1'])
    using assms h''_nbot h''_ea h1''_ext_h1' hch1_ea apply (simp_all (no_asm))
          apply (metis (no_types, lifting) DiffD1 DiffD2 DiffI UnI2 hch1_nbot plus_fg_dom_un)
         apply (rule endo_edge_fg_plus_fg[of E "?h1''" h2], blast+)
           apply (rule endo_edge_fg_plus_fg[of E "?hc" h1])
    using hch1_nbot apply blast+
    using E apply simp
            apply blast+
    using dom nbot hch1_nbot E apply auto[1]
       apply (rule endo_edge_fg_plus_fg[of E "?hc" h1])
    using hch1_nbot apply blast+
    using E apply simp
        apply blast+
    using cap nbot hch1_nbot E apply simp
         apply (rule endo_edge_fg_plus_fg[of E "?h1''" h2], blast+)
           apply (rule endo_edge_fg_plus_fg[of E "?hc" h1])
    using hch1_nbot apply blast+
    using E apply simp
            apply blast+
    done
  then obtain h' where les1: "h' = h1' + h2" "h' \<noteq> bot" "eff_acyclic' h'"
    "fg (dom_fg h1' - dom_fg h1) (\<lambda>n n' _. 0) (\<lambda>n. inf_fg h1' n + outf_fg h1 n) + h1 + h2 \<lesssim>\<^sub>S h'"
    by auto

  have AUX1: "dom_fg ?h'' = dom_fg ?hc \<union> dom_fg (h1 + h2)"
    using h''_nbot plus_fg_ops_exist(1)[of ?h1'' h2] nbot by auto

  have inf'': "\<forall>x \<in> ?N. inf_fg ?h'' x = ?i x"
  proof
    fix x
    assume A: "x \<in> ?N"

    have B: "outf_fg ?hc x = 0"
      using outf_fg_unfold[of ?hc x] plus_fg_dom_disj[of ?hc "h1 + h2"] h''_nbot A nbot
        plus_fg_ops_exist(1)[of ?hc "h1 + h2"] dom by (auto simp: algebra_simps)

    have C: "inf_fg (h1 + h2) x = inf_fg ?h'' x + outf_fg ?hc x"
      using flow_eq_to_sum[of "h1 + h2" ?hc] h''_nbot A dom nbot by (simp add: algebra_simps)

    show "inf_fg (?hc + h1 + h2) x = inf_fg (h1 + h2) x"
      using B C by simp
  qed

  have les2: "h \<lesssim>\<^sub>S ?h''"
  proof -
    have Y0: "outf_fg ?h'' = outf_fg h on -dom_fg ?h''"
      apply (rule outf_eq_h0[of ?h'' ?hc h])
      using \<open>h = h1 + h2\<close> apply (auto simp: algebra_simps)
      using h''_nbot apply (simp add: algebra_simps)
      using E by simp

    have Y1: "int_fg h \<lesssim> int_fg ?h''"
    proof -
      have WWW: "outf_fg ?hc = (\<lambda>_. 0)"
        using outf_fg_unfold'[OF E] E by auto
      then have MMM: "\<forall>x \<in> dom_fg (h1 + h2). inf_fg (h1 + h2) x = inf_fg ?h'' x"
        using flow_eq_to_sum[of "h1 + h2" ?hc] using \<open>h = h1 + h2\<close> \<open>h \<noteq> bot\<close> h''_nbot
        by (simp add: algebra_simps)

      have "?h'' = ?hc + (h1 + h2)"
        by (simp add: algebra_simps)

      show ?thesis
        unfolding contextual_extension_def
        using h''_nbot I \<open>h = h1 + h2\<close> \<open>h \<noteq> bot\<close> E I nbot hch1_nbot MMM WWW
        apply auto
        by (metis (no_types, lifting) Un_iff inf_fg_int_fg)+
    qed

    have Y2: "\<forall>n \<in> ?N. \<forall>n' \<in> -?N''. \<forall>m \<le> ?i n. cap_fg h n n' m = cap_fg ?h'' n n' m"
    proof (safe, goal_cases)
      case (1 n n' m)
      then have "n \<in> dom_fg ?h''" "n' \<in> -dom_fg ?h''" "m \<le> inf_fg ?h'' n"
        using h''_nbot nbot hch1_nbot inf'' by simp_all
      then show ?case
        using cap_outside_eq_h'[of ?h'' ?hc h E] \<open>h = h1 + h2\<close> E edge h''_nbot
          endo_edge_fg_plus_fg[of E "h1 + h2" ?hc] 1 \<open>eff_acyclic' h\<close> \<open>\<forall>x y. edge_fg h x y \<in> E\<close>
          \<open>id \<in> E\<close> \<open>(\<lambda>_. 0) \<in> E\<close>
        by (simp add: algebra_simps)
    qed

    have Y3:
      "\<forall>n \<in> dom_fg ?h'' - ?N. \<forall>n' \<in> -(dom_fg ?h''). \<forall>m \<le> inf_fg ?h'' n. cap_fg ?h'' n n' m = 0"
    proof (safe, goal_cases)
      case (1 n n' m)
      then have "n \<in> dom_fg ?h''" "n' \<in> -dom_fg ?h''" "m \<le> inf_fg ?h'' n"
        using h''_nbot nbot hch1_nbot inf'' by simp_all
      then show ?case
        using cap_outside_eq_h'[of ?h'' ?hc h E] \<open>h = h1 + h2\<close> E edge h''_nbot
          endo_edge_fg_plus_fg[of E "h1 + h2" ?hc] 1 \<open>eff_acyclic' h\<close> \<open>\<forall>x y. edge_fg h x y \<in> E\<close>
          \<open>id \<in> E\<close> \<open>(\<lambda>_. 0) \<in> E\<close>
        by (simp add: algebra_simps)
    qed

    show ?thesis
      unfolding subflow_preserving_extension_def
      apply (intro conjI)
      using Y1 apply simp
      using Y2 nbot h''_nbot apply simp
      using Y3 by simp
  qed

  show ?thesis
    apply (rule exI[where x="h'"])
    using les1 les2 subflow_preserving_extension_trans[of h ?h'' h'] h''_nbot nbot
    by simp
qed

text \<open>@{cite \<open>th. 3\<close> krishna20}\<close>

lemma maintain_eff_acyclic_dom:
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes nbot: "h = h1 + h2" "h \<noteq> bot" "h1' \<noteq> bot"
    and dom: "dom_fg h1' \<inter> dom_fg h2 = {}"
    and edge: "\<forall>n \<in> dom_fg h1' - dom_fg h1. outf_fg h2 n = 0" "\<forall>x y. edge_fg h x y \<in> E"
        "End_closed E" "id \<in> E" "\<forall>x y. edge_fg h2 x y \<in> E" 
        "\<forall>x y. edge_fg h1 x y \<in> E" "\<forall>x y. edge_fg h1' x y \<in> E" "\<forall>x y. edge_fg (h1' + h2) x y \<in> E"
        "(\<lambda>_. 0) \<in> E" "pointwise_reduced E"
    and ea: "eff_acyclic' h" "eff_acyclic' h1" "eff_acyclic' h1'" "eff_acyclic' h2"
      "h1 \<lesssim>\<^sub>S h1'"
  shows "\<exists>h'. h' = h1' + h2 \<and> h' \<noteq> bot \<and> eff_acyclic' h' \<and> h \<lesssim>\<^sub>S h'"
proof (cases "dom_fg h1 = dom_fg h1'")
  case True
  show ?thesis
    apply (rule maintain_eff_acyclic_dom_eq)
    using True assms unfolding zero_fun_def subflow_preserving_extension_def by blast+
next
  case False
  then have False': "dom_fg h1 \<subseteq> dom_fg h1'"
    using ea unfolding subflow_preserving_extension_def contextual_extension_def by simp
  show ?thesis
    apply (rule maintain_eff_acyclic_dom_ne)
    using False' assms unfolding subflow_preserving_extension_def by blast+
qed

end
