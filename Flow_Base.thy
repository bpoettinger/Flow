\<^marker>\<open>creator Bernhard Pöttinger\<close>

chapter \<open>Flow\<close>
theory Flow_Base
  imports Main Auxiliary Flow_Graph Flow_Interface
begin

paragraph \<open>Summary\<close>
text \<open>This theory established the connection between flow graphs and flow interfaces
introduced by the Flow Framework @{cite krishna20}\<close>

paragraph \<open>Major Definitions\<close>
text \<open>\<^item> @{term inf_fg}: inflow of flow graphs
\<^item> @{term outf_fg}: outflow of flow graphs
\<^item> @{term int_fg}: interface of flow graphs\<close>

paragraph \<open>Major Lemmas\<close>
text \<open>\<^item> @{term int_fg_fi_hom}: relates addition flow graphs and flow interfaces @{cite \<open>lem. 2\<close> krishna20}\<close>

section \<open>Interaction between Flow Graphs and Flow Interfaces\<close>

text \<open>We first define the interface of a flow graph @{cite \<open>p. 316\<close> krishna20}\<close>

definition inf_fg :: "('n,'m) fg \<Rightarrow> ('n \<Rightarrow> 'm::cancel_comm_monoid_add)" where
  "inf_fg h \<equiv> let i = (SOME i. flow_eq h i) in restrict (dom_fg h) 0 i"
         
definition outf_fg :: "('n,'m) fg \<Rightarrow> ('n \<Rightarrow> 'm::cancel_comm_monoid_add)" where
  "outf_fg h \<equiv>
    \<lambda>n. if n \<in> dom_fg h then 0 else (\<Sum>n' \<in> dom_fg h. edge_fg h n' n (flow_fg h n'))"

definition int_fg :: "('n,'m) fg \<Rightarrow> ('n,'m::cancel_comm_monoid_add) fi" where
  "int_fg h \<equiv> if h = bot then bot else fi (dom_fg h) (inf_fg h) (outf_fg h)"

lemma outf_fg_eqI:
  assumes "h1 \<noteq> bot" "h2 \<noteq> bot" "int_fg h1 = int_fg h2"
  shows "outf_fg h1 = outf_fg h2"
proof -
  have "outf_fg h1 = outf_fi (int_fg h1)"
    using assms(1) unfolding int_fg_def outf_fg_def by auto
  also have "... = outf_fi (int_fg h2)"
    using assms by simp
  also have "... = outf_fg h2"
    using assms(2) unfolding int_fg_def outf_fg_def by auto
  finally show ?thesis .
qed

lemma dom_fi_plus_fg[simp]:
  "h1 + h2 \<noteq> bot \<Longrightarrow> dom_fi (int_fg (h1 + h2)) = dom_fg h1 \<union> dom_fg h2"
  unfolding int_fg_def by simp

lemma dom_fi_int_fg[simp]:
  "dom_fi (int_fg h) = dom_fg h"
  unfolding int_fg_def by auto

lemma int_fg_bot_bot[simp]: "int_fg bot = bot"
  unfolding int_fg_def by simp

lemma int_fg_bot_bot'[simp]: "h \<noteq> bot \<Longrightarrow> int_fg h \<noteq> bot"
  unfolding int_fg_def by simp

lemma fg_fi_zero[simp]:
  "int_fg 0 = 0"
  using def_fg_zero_fg
  unfolding zero_fg_def zero_fi_def int_fg_def outf_fg_def
  by (auto intro: fi_cong)

lemma flow_eq_inf_fg:
  assumes "h \<noteq> bot"
  shows "flow_eq h (inf_fg h)"
proof -
  obtain i where "flow_eq h i" using flow_eq_exists assms by auto
  thus "flow_eq h (inf_fg h)"
    using someI[of "flow_eq h" i]
    unfolding inf_fg_def
    by (simp add: flow_eq_outside_irrelevant)
qed

lemma flow_eq_ne_bot:
  assumes "h \<noteq> bot"
  shows "\<forall>n \<in> dom_fg h. flow_fg h n = inf_fg h n + (\<Sum>n' \<in> dom_fg h. edge_fg h n' n (flow_fg h n'))"
proof -
  have "flow_eq h (inf_fg h)" using assms flow_eq_inf_fg by blast
  thus ?thesis using assms fgE' by blast
qed

lemma nbot_fg_to_flow_eq2':
  assumes "h \<noteq> bot"
  shows "flow_eq2' (dom_fg h) (edge_fg h) (flow_fg h) (inf_fg h)"
proof -
  have "flow_eq h (inf_fg h)"
    using flow_eq_inf_fg assms by blast
  then show ?thesis
    using fgE'[of h "inf_fg h"] assms
    unfolding flow_eq2'_def flow_eq'_def
    by simp
qed

lemma outf_fi_plus_fi[simp]:
  assumes "i1 + i2 \<noteq> bot"
  shows "outf_fi (i1 + i2) = (\<lambda>n. outf_fi i1 n + outf_fi i2 n) on -dom_fi (i1 + i2)"
proof -
  have "is_sum_fi i1 i2 (i1 + i2)"
    using assms plus_fi_to_is_sum_fi[of i1 i2] by simp
  thus ?thesis
    unfolding is_sum_fi_def by blast
qed

lemma outf_fi_int_fg[simp]:
  shows "outf_fi (int_fg h) = outf_fg h"
  unfolding int_fg_def outf_fg_def
  by auto

lemma outf_fg_plus_fg[simp]:
  assumes "h1 + h2 \<noteq> bot"
  shows "outf_fg (h1 + h2) = (\<lambda>n. outf_fg h1 n + outf_fg h2 n) on -dom_fg (h1 + h2)"
proof
  fix n
  assume *: "n \<in> -dom_fg (h1 + h2)"

  have "h1 \<noteq> bot" "h2 \<noteq> bot" using assms by auto
  hence disj: "h1 \<noteq> bot" "h2 \<noteq> bot" "dom_fg h1 \<inter> dom_fg h2 = {}"
    "finite (dom_fg h1)" "finite (dom_fg h2)"
    "dom_fg (h1 + h2) = dom_fg h1 \<union> dom_fg h2"
    using assms by simp_all

  have "outf_fg (h1 + h2) n = (if n \<in> dom_fg (h1 + h2) then 0 else
    (\<Sum>n' \<in> dom_fg h1 \<union> dom_fg h2. edge_fg (h1 + h2) n' n (flow_fg (h1 + h2) n')))"
    unfolding outf_fg_def by (simp add: assms)
  also have "... = (\<Sum>n' \<in> dom_fg h1. edge_fg (h1 + h2) n' n (flow_fg (h1 + h2) n'))
                 + (\<Sum>n' \<in> dom_fg h2. edge_fg (h1 + h2) n' n (flow_fg (h1 + h2) n'))"
    using * disj sum.union_disjoint[of "dom_fg h1" "dom_fg h2"
        "\<lambda>n'. edge_fg (h1 + h2) n' n (flow_fg (h1 + h2) n')"] assms
    by simp
  also have "... = (\<Sum>n' \<in> dom_fg h1. edge_fg h1 n' n (flow_fg h1 n'))
                 + (\<Sum>n' \<in> dom_fg h2. edge_fg h2 n' n (flow_fg h2 n'))"
    using flow_fg_plus_fg_on1[of h1 h2] edge_fg_plus_fg_on1[of h1 h2]
      flow_fg_plus_fg_on2[of h1 h2] edge_fg_plus_fg_on2[of h1 h2] assms by simp
  finally show "outf_fg (h1 + h2) n = outf_fg h1 n + outf_fg h2 n"
    unfolding outf_fg_def using * disj
    by simp
qed

lemma flow_eq_to_sum:
  assumes A: "h1 + h2 \<noteq> bot"
  shows "inf_fg h1 = (\<lambda>n. (inf_fg (h1 + h2)) n + outf_fg h2 n) on (dom_fg h1)"
proof safe
  let ?i1 = "inf_fg h1"
  let ?o2 = "outf_fg h2"
  let ?i12 = "inf_fg (h1 + h2)"
  let ?N12 = "dom_fg (h1 + h2)"
  let ?e12 = "edge_fg (h1 + h2)"
  let ?f12 = "flow_fg (h1 + h2)"

  fix n
  assume D: "n \<in> dom_fg h1"

  have nbot: "h1 \<noteq> bot" "h2 \<noteq> bot" using A by auto
  have X: "h1 \<noteq> bot" "h2 \<noteq> bot" using A nbot by simp_all
  hence *: "int_fg h1 \<noteq> bot" "int_fg h2 \<noteq> bot" "int_fg (h1 + h2) \<noteq> bot"
    using A unfolding int_fg_def by simp_all
  have Y: "dom_fg h1 \<inter> dom_fg h2 = {}" "dom_fg h1 \<union> dom_fg h2 = ?N12"
    "finite (dom_fg h2)" "finite (dom_fg h1)"
    using A by auto

  have "?f12 n = ?i12 n + (\<Sum>n' \<in> ?N12. ?e12 n' n (?f12 n'))"
    using * D A flow_eq_ne_bot[of "h1 + h2"] by simp
  hence "flow_fg h1 n = ?i12 n + (\<Sum>n' \<in> dom_fg (h1 + h2). ?e12 n' n (?f12 n'))"
    using flow_fg_plus_fg_on1[of h1 h2]  \<open>n \<in> dom_fg h1\<close> A by auto
  hence "?i1 n + (\<Sum>n' \<in> dom_fg h1. edge_fg h1 n' n (flow_fg h1 n'))
            = ?i12 n + (\<Sum>n' \<in> dom_fg (h1 + h2). edge_fg (h1 + h2) n' n (flow_fg (h1 + h2) n'))"
    using * flow_eq_ne_bot[of h1] \<open>n \<in> dom_fg h1\<close> nbot by auto
  hence "inf_fg h1 n + (\<Sum>n' \<in> dom_fg h1. edge_fg h1 n' n (flow_fg h1 n'))
            = ?i12 n + (\<Sum>n' \<in> dom_fg h1 \<union> dom_fg h2. ?e12 n' n (?f12 n'))"
    using Y by simp
  hence "inf_fg h1 n + (\<Sum>n' \<in> dom_fg h1. edge_fg h1 n' n (flow_fg h1 n'))
            = ?i12 n + (\<Sum>n' \<in> dom_fg h1. ?e12 n' n (?f12 n'))
                     + (\<Sum>n' \<in> dom_fg h2. ?e12 n' n (?f12 n'))"
    using * Y sum.union_disjoint[of "dom_fg h1" "dom_fg h2" "\<lambda>n'. ?e12 n' n (?f12 n')"]
    by (simp add: algebra_simps)
  hence "inf_fg h1 n + (\<Sum>n' \<in> dom_fg h1. edge_fg h1 n' n (flow_fg h1 n'))
            = ?i12 n + (\<Sum>n' \<in> dom_fg h1. edge_fg h1 n' n (flow_fg h1 n'))
                     + (\<Sum>n' \<in> dom_fg h2. ?e12 n' n (?f12 n'))"
    using flow_fg_plus_fg_on1[of h1 h2] edge_fg_plus_fg_on1[of h1 h2] \<open>n \<in> dom_fg h1\<close> A by auto
  hence "inf_fg h1 n = ?i12 n + (\<Sum>n' \<in> dom_fg h2. edge_fg (h1 + h2) n' n (?f12 n'))"
    by (metis (no_types, lifting) add.assoc add.commute add_left_cancel)
  hence "inf_fg h1 n = ?i12 n + (\<Sum>n' \<in> dom_fg h2. edge_fg h2 n' n (flow_fg h2 n'))"
    using flow_fg_plus_fg_on2[of h1 h2] edge_fg_plus_fg_on2[of h1 h2]
      \<open>n \<in> dom_fg h1\<close> A sum.cong by (metis (no_types, lifting))
  thus "inf_fg h1 n = ?i12 n + outf_fg h2 n"
    unfolding outf_fg_def using \<open>n \<in> dom_fg h1\<close> Y by auto
qed

text \<open>The most important statement of the relation between flow graphs and flow interfaces.
@{cite \<open>lem. 2\<close> krishna20}\<close>

lemma int_fg_fi_hom: "int_fg (h1 + h2) = int_fg h1 + int_fg h2"
proof (rule fi_eqI2)
  assume "int_fg (h1 + h2) \<noteq> bot"
  hence A: "h1 + h2 \<noteq> bot" unfolding int_fg_def by auto

  let ?i1 = "inf_fg h1"
  let ?i2 = "inf_fg h2"
  let ?i12 = "inf_fg (h1 + h2)"
  let ?o1 = "outf_fg h1"
  let ?o2 = "outf_fg h2"
  let ?o12 = "outf_fg (h1 + h2)"
  let ?I12 = "int_fg (h1 + h2)"
  let ?I1 = "int_fg h1"
  let ?I2 = "int_fg h2"
  let ?N12 = "dom_fg (h1 + h2)"
  let ?e12 = "edge_fg (h1 + h2)"
  let ?f12 = "flow_fg (h1 + h2)"

  have [simp]: "h1 \<noteq> bot" "h2 \<noteq> bot" using A by auto
  have X: "h1 \<noteq> bot" "h2 \<noteq> bot" using A by simp_all
  hence *: "int_fg h1 \<noteq> bot" "int_fg h2 \<noteq> bot" "int_fg (h1 + h2) \<noteq> bot"
    using A unfolding int_fg_def by simp_all

  have Y: "dom_fg h1 \<inter> dom_fg h2 = {}" "dom_fg h1 \<union> dom_fg h2 = dom_fg (h1 + h2)"
    "finite (dom_fg h2)" "finite (dom_fg h1)"
    using A by auto

  have "?i1 = (\<lambda>n. ?i12 n + ?o2 n) on (dom_fg h1)"
    using flow_eq_to_sum[of h1 h2] A by simp
  hence X1: "inf_fi ?I1 = \<lambda>n. inf_fi ?I12 n + outf_fi ?I2 n on dom_fi ?I1"
    using A Y unfolding int_fg_def apply auto
    by (metis IntI Y(1) empty_iff)

  have "?i2 = (\<lambda>n. ?i12 n + ?o1 n) on (dom_fg h2)"
    using flow_eq_to_sum[of h2 h1] A by (simp add: algebra_simps)
  hence X2: "inf_fi ?I2 = \<lambda>n. inf_fi ?I12 n + outf_fi ?I1 n on dom_fi ?I2"
    using A Y unfolding int_fg_def apply auto
    by (metis IntI Y(1) empty_iff)

  have "?o12 = (\<lambda>n. ?o1 n + ?o2 n) on (-?N12)"
  proof
    fix n
    assume "n \<in> -?N12"
    hence "?o12 n = (\<Sum>n' \<in> ?N12. ?e12 n' n (?f12 n'))"
      unfolding outf_fg_def using Y by simp
    also have "... = (\<Sum>n' \<in> dom_fg h1. edge_fg (h1 + h2) n' n (flow_fg (h1 + h2) n'))
                   + (\<Sum>n' \<in> dom_fg h2. edge_fg (h1 + h2) n' n (flow_fg (h1 + h2) n'))"
      using * Y sum.union_disjoint[of "dom_fg h1" "dom_fg h2" "\<lambda>n'. ?e12 n' n (?f12 n')"]
      by (simp add: algebra_simps)
    also have "... = (\<Sum>n' \<in> dom_fg h1. edge_fg h1 n' n (flow_fg h1 n'))
                   + (\<Sum>n' \<in> dom_fg h2. edge_fg h2 n' n (flow_fg h2 n'))"
      using flow_fg_plus_fg_on1[of h1 h2] edge_fg_plus_fg_on1[of h1 h2]
        flow_fg_plus_fg_on2[of h1 h2] edge_fg_plus_fg_on2[of h1 h2] A by simp
    finally show "?o12 n = ?o1 n + ?o2 n"
      unfolding outf_fg_def using \<open>n \<in> -dom_fg (h1 + h2)\<close> Y by auto
  qed
  hence X3: "outf_fi ?I12 = \<lambda>n. outf_fi ?I1 n + outf_fi ?I2 n on - dom_fi ?I12"
    using A unfolding int_fg_def by simp

  have "is_sum_fi (int_fg h1) (int_fg h2) (int_fg (h1 + h2))"
    unfolding is_sum_fi_def using Y A X1 X2 X3 unfolding int_fg_def by simp
  hence "int_fg h1 + int_fg h2 = int_fg (h1 + h2)"
    using is_sum_fi_to_plus_fi by blast
  thus "int_fg (h1 + h2) = int_fg h1 + int_fg h2"
    by simp
next
  assume A: "int_fg h1 + int_fg h2 \<noteq> bot"
  hence nbot[simp]: "h1 \<noteq> bot" "h2 \<noteq> bot" using A unfolding int_fg_def by auto

  let ?i1 = "inf_fi (int_fg h1)"
  let ?i2 = "inf_fi (int_fg h2)"
  let ?i12 = "inf_fi (int_fg h1 + int_fg h2)"
  let ?o1 = "outf_fi (int_fg h1)"
  let ?o2 = "outf_fi (int_fg h2)"
  let ?o12 = "outf_fi (int_fg h1 + int_fg h2)"
  let ?I12 = "int_fg (h1 + h2)"
  let ?I1 = "int_fg h1"
  let ?I2 = "int_fg h2"
  let ?e2 = "edge_fg h2"
  let ?f2 = "flow_fg h2"
  let ?e1 = "edge_fg h1"
  let ?f1 = "flow_fg h1"
  let ?N1 = "dom_fg h1"
  let ?N2 = "dom_fg h2"

  have X: "h1 \<noteq> bot" "h2 \<noteq> bot" using A by simp_all
  hence *: "int_fg h1 \<noteq> bot" "int_fg h2 \<noteq> bot" using A by auto

  have B: "is_sum_fi (int_fg h1) (int_fg h2) (int_fg h1 + int_fg h2)"
    using A by (simp add: plus_fi_to_is_sum_fi)

  have Y:  "dom_fg h1 \<inter> dom_fg h2 = {}"
    "finite (dom_fg h2)" "finite (dom_fg h1)"
    using A X dom_fi_plus_fi[of "int_fg h1" "int_fg h2"] by auto

  let ?N12 = "dom_fg h1 \<union> dom_fg h2"
  let ?e12 = "combine (dom_fg h1) (dom_fg h2) (\<lambda>_ _. 0) (edge_fg h1) (edge_fg h2)"
  let ?f12 = "combine (dom_fg h1) (dom_fg h2)        0  (flow_fg h1) (flow_fg h2)"

  have "?f12 = (\<lambda>n. ?i12 n + (\<Sum>n' \<in> ?N12. ?e12 n' n (?f12 n'))) on (dom_fg h1)"
  proof
    fix n
    assume "n \<in> dom_fg h1"
    hence "?i1 n = ?i12 n + ?o2 n"
      using B unfolding is_sum_fi_def by simp
    hence "?i1 n = ?i12 n + (\<Sum>n' \<in> dom_fg h2. edge_fg h2 n' n (flow_fg h2 n'))"
      using Y \<open>n \<in> dom_fg h1\<close> unfolding outf_fg_def int_fg_def by auto
    hence "?i1 n + (\<Sum>n' \<in> dom_fg h1. edge_fg h1 n' n (flow_fg h1 n')) =
              ?i12 n + (\<Sum>n' \<in> dom_fg h1. edge_fg h1 n' n (flow_fg h1 n')) +
                       (\<Sum>n' \<in> dom_fg h2. edge_fg h2 n' n (flow_fg h2 n'))"
      by (simp add: algebra_simps)
    hence "?f12 n =
              ?i12 n + (\<Sum>n' \<in> dom_fg h1. edge_fg h1 n' n (flow_fg h1 n')) +
                       (\<Sum>n' \<in> dom_fg h2. edge_fg h2 n' n (flow_fg h2 n'))"
      using \<open>n \<in> dom_fg h1\<close> flow_eq_ne_bot[of h1] unfolding int_fg_def by (simp add: algebra_simps)
    hence "?f12 n = ?i12 n + (\<Sum>n' \<in> dom_fg h1. ?e12 n' n (?f12 n')) +
                             (\<Sum>n' \<in> dom_fg h2. ?e12 n' n (?f12 n'))"
      using Y sum.cong[of ?N2 ?N2 "\<lambda>n'. ?e2 n' n (?f2 n')" "\<lambda>n'. ?e12 n' n (?f12 n')"]
      by fastforce
    thus "?f12 n = ?i12 n + (\<Sum>n' \<in> ?N12. ?e12 n' n (?f12 n'))"
      using Y sum.union_disjoint[of ?N1 ?N2 "\<lambda>n'. ?e12 n' n (?f12 n')"]
      by (simp add: algebra_simps)
  qed
  moreover have "?f12 = (\<lambda>n. ?i12 n + (\<Sum>n' \<in> ?N12. ?e12 n' n (?f12 n'))) on (dom_fg h2)"
  proof
    fix n
    assume "n \<in> dom_fg h2"
    hence "?i2 n = ?i12 n + ?o1 n"
      using B unfolding is_sum_fi_def by simp
    hence "?i2 n = ?i12 n + (\<Sum>n' \<in> dom_fg h1. edge_fg h1 n' n (flow_fg h1 n'))"
      using Y \<open>n \<in> dom_fg h2\<close> unfolding outf_fg_def int_fg_def by auto
    hence "?i2 n + (\<Sum>n' \<in> dom_fg h2. edge_fg h2 n' n (flow_fg h2 n')) =
              ?i12 n + (\<Sum>n' \<in> dom_fg h1. edge_fg h1 n' n (flow_fg h1 n')) +
                       (\<Sum>n' \<in> dom_fg h2. edge_fg h2 n' n (flow_fg h2 n'))"
      by (simp add: algebra_simps)
    hence "?f12 n =
              ?i12 n + (\<Sum>n' \<in> dom_fg h1. edge_fg h1 n' n (flow_fg h1 n')) +
                       (\<Sum>n' \<in> dom_fg h2. edge_fg h2 n' n (flow_fg h2 n'))"
      using \<open>n \<in> ?N2\<close> flow_eq_ne_bot[of h2] Y unfolding int_fg_def by (auto simp: algebra_simps)
    hence "?f12 n = ?i12 n + (\<Sum>n' \<in> dom_fg h1. ?e12 n' n (?f12 n')) +
                             (\<Sum>n' \<in> dom_fg h2. ?e12 n' n (?f12 n'))"
      using Y sum.cong[of ?N2 ?N2 "\<lambda>n'. ?e2 n' n (flow_fg h2 n')" "\<lambda>n'. ?e12 n' n (?f12 n')"]
      by fastforce
    thus "?f12 n = ?i12 n + (\<Sum>n' \<in> ?N12. ?e12 n' n (?f12 n'))"
      using Y sum.union_disjoint[of "dom_fg h1" "dom_fg h2" "\<lambda>n'. ?e12 n' n (?f12 n')"]
      by (simp add: algebra_simps)
  qed
  ultimately have XXXX: "?f12 = (\<lambda>n. ?i12 n + (\<Sum>n' \<in> ?N12. ?e12 n' n (?f12 n'))) on (?N1 \<union> ?N2)"
    by auto
  (* we have a solution to the flow equation and obtain validity of fg _ _ _ *)
  hence XXXXX: "fg ?N12 ?e12 ?f12 \<noteq> bot" by (rule fgI, auto)
  (* we show that the fg _ _ _ we proved validity for is exactly h1 + h2 *)
  hence chain: "fg ?N12 ?e12 ?f12 = h1 + h2" unfolding plus_fg_def using Y by auto
  (* it follows that h1 + h2 \<noteq> nbot *)
  hence C': "h1 + h2 \<noteq> bot" using XXXXX by simp

  have D: "dom_fg (h1 + h2) = dom_fi (int_fg h1 + int_fg h2)" using C' A by auto

  (* we have to show equality of the inflows to h1 + h2 *)
  (* first, show that our explicit solution is a solution (was already done in XXXXX,
     but is hidden behind existential quantifier) *)
  have C: "flow_eq (h1 + h2) ?i12"
    using XXXX flow_eqI[of "dom_fg h1 \<union> dom_fg h2" ?f12 ?i12 ?e12] chain by simp
  (* second, obtain the existentially quantified inflow *)
  have "flow_eq (h1 + h2) (inf_fg (h1 + h2))" by (fact flow_eq_inf_fg[OF C'])
  (* uniqueness implies equality of both variants *)
  hence "inf_fg (h1 + h2) = ?i12 on dom_fg (h1 + h2)"
    using C flow_eq_unique unfolding int_fg_def by simp
  (* the equality we have to prove *)
  hence X1: "?i12 = inf_fi (int_fg (h1 + h2)) on dom_fi (int_fg h1 + int_fg h2)"
    using D unfolding int_fg_def by auto

  have X2: "?o12 = outf_fi (int_fg (h1 + h2)) on -dom_fi (int_fg h1 + int_fg h2)"
    using A C' unfolding int_fg_def by auto

  have X3: "int_fg (h1 + h2) \<noteq> bot" using C' unfolding int_fg_def by simp

  have X4: "dom_fi (int_fg h1 + int_fg h2) = dom_fi (int_fg (h1 + h2))"
    using C' A by auto

  show "int_fg h1 + int_fg h2 = int_fg (h1 + h2)"
    by (fact fi_eqI[OF A X3 X4 X1 X2])
qed

lemma int_fg_plus_cong:
  assumes "int_fg h1 = int_fg h1'"
  shows "int_fg (h1 + h2) = int_fg (h1' + h2)"
  unfolding int_fg_def
  apply auto
    apply (metis assms int_fg_def int_fg_fi_hom plus_fg_dom_un)
  using int_fg_fi_hom[of h1 h2] assms int_fg_fi_hom[of h1' h2, symmetric] apply simp
  by (smt int_fg_def assms dom_fi_int_fg dom_fi_plus_fg int_fg_fi_hom)

lemma outf_fg_unfold:
  assumes "h \<noteq> bot" "n \<notin> dom_fg h"
  shows "outf_fg h n = (\<Sum>n' \<in> dom_fg h. edge_fg h n' n (flow_fg h n'))"
  using assms
  unfolding outf_fg_def dom_fg_def edge_fg_def flow_fg_def
  by auto

lemma outf_fg_unfold':
  assumes "h \<noteq> bot"
  shows "outf_fg h =
    (\<lambda>n. if n \<in> dom_fg h then 0 else (\<Sum>n' \<in> dom_fg h. edge_fg h n' n (flow_fg h n')))"
  using assms
  unfolding outf_fg_def dom_fg_def edge_fg_def flow_fg_def
  by auto

lemma outf_fg_outside_plus:
  assumes "h' = h0 + h" "h' \<noteq> bot" "\<forall>n n'. edge_fg h0 n n' = (\<lambda>_. 0)"
  shows "outf_fg h' = outf_fg h on (-dom_fg h')"
proof
  fix x
  assume A: "x \<in> -dom_fg h'"

  have D: "h0 \<noteq> bot" "h \<noteq> bot"
    using plus_fg_ops_exist assms by auto

  have disj: "dom_fg h0 \<inter> dom_fg h = {}"
    using assms by simp

  show "outf_fg h' x = outf_fg h x"
    using assms A D by (simp, subst outf_fg_unfold, simp_all)
qed

lemma inf_fg_outside_0:
  "inf_fg h = (\<lambda>_. 0) on -dom_fg h"
proof (cases "h = bot")
case True
  then show ?thesis unfolding inf_fg_def by simp
next
case False
  then show ?thesis unfolding inf_fg_def by simp
qed

lemma int_fg_to_inf_fg:
  assumes "int_fg h1 = int_fg h2" "h1 \<noteq> bot"
  shows "inf_fg h1 = inf_fg h2"
proof -
  have *: "h2 \<noteq> bot" using assms by auto
  then have
    "fi (dom_fg h1) (inf_fg h1) (outf_fg h1) = fi (dom_fg h2) (inf_fg h2) (outf_fg h2)"
    using assms unfolding int_fg_def by simp
  then have "inf_fi (fi (dom_fg h1) (inf_fg h1) (outf_fg h1)) =
    inf_fi (fi (dom_fg h2) (inf_fg h2) (outf_fg h2))"
    by simp
  then have "restrict (dom_fg h1) 0 (inf_fg h1) = restrict (dom_fg h2) 0 (inf_fg h2)"
    using inf_fi_fi by simp
  moreover have *: "dom_fg h1 = dom_fg h2"
    using assms by (metis dom_fi_int_fg)
  ultimately show ?thesis
    apply (intro ext)
    apply (case_tac "x \<in> dom_fg h1")
     apply metis
    using inf_fg_outside_0[of h1] inf_fg_outside_0[of h2] * by simp
qed

lemma inf_fg_fg:
  assumes "f = (\<lambda>n. i n + (\<Sum>n' \<in> N. e n' n (f n'))) on N" "finite N"
  shows "inf_fg (fg N e f) = restrict N 0 i"
proof -
  let ?i = "SOME i. flow_eq (fg N e f) i"
  let ?h = "fg N e f"

  have *: "fg N e f \<noteq> bot"
    by (rule fgI[where i=i], simp_all add: assms)
  then have **: "flow_eq (fg N e f) i"
    using flow_eqI[of N f i e] assms by simp
  have ***: "flow_eq ?h (SOME i. flow_eq ?h i)"
    apply (rule someI_ex[of "flow_eq ?h"])
    using ** by blast
  have "i = ?i on N"
    using flow_eq_unique[OF ** ***] * by simp
  then show ?thesis
    unfolding inf_fg_def
    using * by auto
qed

lemma inf_fg_fg':
  assumes "flow_eq2' N e f i" "finite N"
  shows "inf_fg (fg N e f) = restrict N 0 i"
  using assms inf_fg_fg
  unfolding flow_eq2'_def flow_eq'_def
  by blast

lemma inf_fg_fg'':
  assumes "flow_eq (fg N e f) i" "finite N"
  shows "inf_fg (fg N e f) = restrict N 0 i"
  apply (rule inf_fg_fg)
  using fgE'[OF assms(1)] fgI2[OF assms(1) assms(2)] assms
  by auto

lemma inf_fg_int_fg:
  assumes "h \<noteq> bot"
  shows "inf_fi (int_fg h) = inf_fg h"
  using assms
  unfolding int_fg_def
  apply simp
  unfolding inf_fg_def
  by auto

lemma dom_fg_plus_fg_subs1:
  "h1 + h2 \<noteq> bot \<Longrightarrow> dom_fg h1 \<subseteq> dom_fg (h1 + h2)"
  by simp

lemma dom_fg_plus_fg_iff:
  assumes "h = h1 + h2" "h \<noteq> bot" "x \<in> dom_fg h"
  shows "x \<in> dom_fg h2 \<longleftrightarrow> x \<notin> dom_fg h1"
proof -
  have "dom_fg h1 \<inter> dom_fg h2 = {}" "dom_fg h1 \<union> dom_fg h2 = dom_fg h"
    using assms by simp_all
  then show ?thesis
    using assms by blast
qed

lemma plus_fg_not_equal:
  fixes h h1 h2 :: "('a, 'b :: cancel_comm_monoid_add) fg"
  assumes "h = h1 + h2" "h \<noteq> bot" "dom_fg h1 \<noteq> {}"
  shows "h1 \<noteq> h2"
proof (rule ccontr)
  assume "\<not> (h1 \<noteq> h2)"
  then have "dom_fg h1 = dom_fg h2" by simp
  moreover have "dom_fg h1 \<inter> dom_fg h2 = {}" using assms by auto
  ultimately show False using assms by simp
qed

paragraph \<open>Special cases of interfaces of singleton flow graphs\<close>

text \<open>@{cite \<open>lem. 2\<close> krishna19b}\<close>
lemma int_fg_singleton_fi:
  assumes "h \<noteq> bot" "n \<in> dom_fg h" "edge_fg h n n = (\<lambda>_. 0)"
  shows "int_fg (fg {n} (edge_fg h) (flow_fg h)) =
    fi {n} (\<lambda>_. flow_fg h n) (\<lambda>n'. edge_fg h n n' (flow_fg h n))"
proof -
  let ?h = "fg {n} (edge_fg h) (flow_fg h)"
  let ?i = "\<lambda>_. flow_fg h n"

  have feq: "flow_eq ?h ?i" by (rule flow_eqI, auto simp: assms)
  have nbot: "?h \<noteq> bot" using assms def_fg_singleton' by metis
  have "inf_fg ?h = ?i on {n}" using flow_eq_unique[OF flow_eq_inf_fg[OF nbot] feq] nbot by auto

  with assms nbot show ?thesis
    unfolding int_fg_def
    apply auto
    apply (rule fi_eqI)
    using inf_fg_fg''[OF flow_eq_inf_fg[OF nbot]] feq unfolding outf_fg_def by auto
qed

lemma int_fg_singleton:
  assumes "dom_fg h = {n}" "edge_fg h n n = (\<lambda>_. 0)"
  shows "int_fg h = fi {n} (\<lambda>_. flow_fg h n) (\<lambda>n'. edge_fg h n n' (flow_fg h n))" "int_fg h \<noteq> bot"
proof (rule fi_eqI)
  have [simp]: "h \<noteq> bot"
    using assms def_fg_singleton[of h n]
    by simp

  show "int_fg h \<noteq> bot" using assms def_fg_singleton unfolding int_fg_def by auto
  then show "int_fg h \<noteq> bot" .

  show "fi {n} (\<lambda>_. flow_fg h n) (\<lambda>n'. edge_fg h n n' (flow_fg h n)) \<noteq> bot"
    using def_fg_singleton[of h n] assms
    by auto

  show "dom_fi (int_fg h) = dom_fi (fi {n} (\<lambda>_. flow_fg h n) (\<lambda>n'. edge_fg h n n' (flow_fg h n)))"
    using assms by simp

  have "flow_eq h (inf_fg h)" using flow_eq_inf_fg by force
  thus "inf_fi (int_fg h) =
    inf_fi (fi {n} (\<lambda>_. flow_fg h n) (\<lambda>n'. edge_fg h n n' (flow_fg h n))) on dom_fi (int_fg h)"
    using assms fgE'[of h] unfolding int_fg_def by auto

  show " outf_fi (int_fg h) =
    outf_fi (fi {n} (\<lambda>_. flow_fg h n) (\<lambda>n'. edge_fg h n n' (flow_fg h n))) on -dom_fi (int_fg h)"
    unfolding outf_fg_def int_fg_def using assms by simp
qed

lemma int_fg_singleton_id:
  assumes "dom_fg h = {n}" "edge_fg h n n = id"
  shows "int_fg h = fi {n} (\<lambda>_. 0) (\<lambda>n'. edge_fg h n n' (flow_fg h n))"
proof (rule fi_eqI)
  have [simp]: "h \<noteq> bot"
    using assms def_fg_singleton_id[of h n] by simp

  let ?h = "fi {n} (\<lambda>_. 0) (\<lambda>n'. edge_fg h n n' (flow_fg h n))"

  show "int_fg h \<noteq> bot" using assms def_fg_singleton unfolding int_fg_def by auto
  show "?h \<noteq> bot" by auto
  show "dom_fi (int_fg h) = dom_fi ?h" using assms by simp
  have "flow_eq h (inf_fg h)" using flow_eq_inf_fg by force
  thus "inf_fi (int_fg h) = inf_fi ?h on dom_fi (int_fg h)"
    using assms fgE'[of h] unfolding int_fg_def by auto
  show " outf_fi (int_fg h) = outf_fi ?h on -dom_fi (int_fg h)"
    unfolding outf_fg_def int_fg_def using assms by simp
qed

end
