\<^marker>\<open>creator Bernhard Pöttinger\<close>

chapter \<open>Footprints of Modifications to Flow Graphs\<close>
theory Flow_Footprint
imports Flow_Base Flow_Extensions
begin

paragraph \<open>Summary\<close>
text \<open>A theoretical result on the footprint of flow interfaces.\<close>
text \<open>@{cite \<open>def. 7\<close> krishna19b}\<close>

paragraph \<open>Major Definitions\<close>
text \<open>\<^item>  @{text flow_footprint}
\<^item> @{text the_flow_footprint}\<close>

paragraph \<open>Major Theorems\<close>
text \<open>\<^item> @{cite \<open>lem. 4\<close> krishna19b}
\<^item> flow footprints are unique\<close>

section \<open>Flow Footprints\<close>

definition flow_footprint where
  "flow_footprint \<equiv> \<lambda>h h' h1'.
             (\<exists>h1 h2. h = h1 + h2 \<and> h' = h1'  + h2 \<and> int_fg h1 = int_fg h1' \<and>
     (\<forall>h1''. (\<exists>h1 h2. h = h1 + h2 \<and> h' = h1'' + h2 \<and> int_fg h1 = int_fg h1'')
              \<longrightarrow> (dom_fg h1' \<subseteq> dom_fg h1'')))"

definition "the_flow_footprint \<equiv> \<lambda>h h'. (THE h1'. flow_footprint h h' h1')"

text \<open>
The proof structure of @{text in_footprint_iff_changed}@{cite \<open>lem. 4\<close> krishna19b} is:
@{text in_footprint_iff_changed}
- ==> @{text in_footprint_iff_changed1}
- <== @{text in_footprint_iff_changed2}
\<close>

lemma in_footprint_iff_changed1:
  assumes "int_fg h = int_fg h'" "h \<noteq> bot" "h' \<noteq> bot" "n \<in> dom_fg h" "flow_footprint h h' h1'"
    "fg {n} (edge_fg h) (flow_fg h) \<noteq> fg {n} (edge_fg h') (flow_fg h')"
  shows "n \<in> dom_fg h1'"
proof -
  have *: "flow_fg h n \<noteq> flow_fg h' n \<or> edge_fg h n \<noteq> edge_fg h' n"
  proof (rule ccontr, goal_cases)
    case 1
    then have *: "flow_fg h n = flow_fg h' n" "edge_fg h n = edge_fg h' n" by auto
    have "fg {n} (edge_fg h) (flow_fg h) = fg {n} (edge_fg h') (flow_fg h')"
      apply (rule fg_cong) using assms * by auto
    then show ?case using assms by simp
  qed

  obtain h1 h2 where **: "h = h1 + h2" "h' = h1' + h2" "int_fg h1 = int_fg h1'"
    "\<forall>h1''. (\<exists>h1 h2. h = h1 + h2 \<and> h' = h1'' + h2 \<and> int_fg h1 = int_fg h1'')
            \<longrightarrow> (dom_fg h1' \<subseteq> dom_fg h1'')"
    using assms unfolding flow_footprint_def by blast

  have "n \<notin> dom_fg h2"
  proof
    assume AA: "n \<in> dom_fg h2"
    consider (a) "flow_fg h n \<noteq> flow_fg h' n" | (b) "edge_fg h n \<noteq> edge_fg h' n"
      using * by blast
    then show False
    proof cases
      case a
      moreover have "flow_fg h n = flow_fg h' n"
        using ** AA assms flow_fg_plus_fg_on2[of h1 h2] flow_fg_plus_fg_on2[of h1' h2]
        by simp
      ultimately show ?thesis
        by simp
    next
      case b
      moreover have "edge_fg h n = edge_fg h' n"
        using ** AA assms edge_fg_plus_fg_on2[of h1 h2] edge_fg_plus_fg_on2[of h1' h2]
        by simp
      ultimately show ?thesis
        by simp
    qed
  qed
  moreover have "dom_fg h = dom_fg h1 \<union> dom_fg h2" "dom_fg h1 \<inter> dom_fg h2 = {}"
    using assms ** by auto
  ultimately have "n \<in> dom_fg h1"
    using assms by simp
  then show ?thesis
    using assms **
    by (metis dom_fi_int_fg)
qed

lemma in_footprint_iff_changed2:
  assumes "int_fg h = int_fg h'" "h \<noteq> bot" "h' \<noteq> bot" "n \<in> dom_fg h" "flow_footprint h h' h1'"
    "n \<in> dom_fg h1'"
  shows "fg {n} (edge_fg h) (flow_fg h) \<noteq> fg {n} (edge_fg h') (flow_fg h')"
proof
  (* proof by contradiction: we construct a "smaller" h1' which can not exist due to minimality
     of h1'. The false assumption fg {n} ... = fg {n} ... implies that we can move n
     from h1' to h2. *)

  let ?h = "fg {n} (edge_fg h) (flow_fg h)"
  let ?h' = "fg {n} (edge_fg h') (flow_fg h')"

  (* first show that ?h is valid in order to access its components*)
  obtain g1 g2 where J: "h = g1 + g2 \<and> dom_fg g1 = {n} \<and> dom_fg g2 = dom_fg h - {n} \<and>
    edge_fg h = edge_fg g1 on {n} \<and> edge_fg h = edge_fg g2 on dom_fg h - {n} \<and>
    flow_fg h = flow_fg g1 on {n} \<and> flow_fg h = flow_fg g2 on dom_fg h - {n}"
    "g1 \<noteq> bot" "g2 \<noteq> bot"
    using split_fg[of h "{n}" "dom_fg h - {n}"] assms by blast

  have "g1 = fg (dom_fg g1) (edge_fg g1) (flow_fg g1)" by (simp add: J(2))
  have "?h = fg (dom_fg g1) (edge_fg g1) (flow_fg g1)"
    apply (rule fg_cong) using J \<open>g1 \<noteq> bot\<close> by auto
  then have "?h \<noteq> bot" using \<open>g1 \<noteq> bot\<close> by simp
  (* then we can show that the assumption that we obtain from our proof by contradiction
     implies equality of edge and flow on n *)
  moreover assume AA: "?h = ?h'"
  ultimately have EE: "edge_fg h n = edge_fg h' n" "flow_fg h n = flow_fg h' n"
    using fg_eqD[of ?h ?h']
     apply (metis edge_fg_fg singletonI)
    using fg_eqD[of ?h ?h'] 
    by (metis AA \<open>fg {n} (edge_fg h) (flow_fg h) \<noteq> bot\<close> flow_fg_fg singletonI)

  (* unfold the flow footprint assumption *)
  obtain h1 h2 where **: "h = h1 + h2" "h' = h1' + h2" "int_fg h1 = int_fg h1'"
    "\<forall>h1''. (\<exists>h1 h2. h = h1 + h2 \<and> h' = h1'' + h2 \<and> int_fg h1 = int_fg h1'')
            \<longrightarrow> (dom_fg h1' \<subseteq> dom_fg h1'')"
    using assms unfolding flow_footprint_def by blast

  (* some observations *)
  have X: "dom_fg h1 = dom_fg h1'"
    using ** dom_fi_int_fg[of h1] dom_fi_int_fg[of h1']
    by simp

  have "dom_fg h = (dom_fg h1 - {n}) \<union> (dom_fg h2 \<union> {n})"
    "(dom_fg h1 - {n}) \<inter> (dom_fg h2 \<union> {n}) = {}"
    using ** plus_fg_dom_un assms plus_fg_dom_disj by blast+

  (* fact 1: split h into hh1 and hh2 such that n is now part of hh2 instead of hh1 *)
  then obtain hh1 hh2 where C: "h = hh1 + hh2" "dom_fg hh1 = dom_fg h1 - {n}"
      "dom_fg hh2 = dom_fg h2 \<union> {n}"
      "edge_fg h = edge_fg hh2 on dom_fg h2 \<union> {n}" "flow_fg h = flow_fg hh2 on dom_fg h2 \<union> {n}"
      "edge_fg h = edge_fg hh1 on dom_fg h1 - {n}" "flow_fg h = flow_fg hh1 on dom_fg h1 - {n}"
    using split_fg[of h "dom_fg h1 - {n}" "dom_fg h2 \<union> {n}"] assms
    by auto

  have "dom_fg h' = (dom_fg h1 - {n}) \<union> (dom_fg h2 \<union> {n})"
    "(dom_fg h1 - {n}) \<inter> (dom_fg h2 \<union> {n}) = {}"
    using X ** plus_fg_dom_un assms plus_fg_dom_disj by blast+

  (* fact 2: split h' into hh1' and hh2' such that n is now part of hh2 instead of hh1' *)
  then obtain hh1' hh2' where D: "h' = hh1' + hh2'" "dom_fg hh1' = dom_fg h1 - {n}"
      "dom_fg hh2' = dom_fg h2 \<union> {n}"
      "edge_fg h' = edge_fg hh2' on dom_fg h2 \<union> {n}" "flow_fg h' = flow_fg hh2' on dom_fg h2 \<union> {n}"
      "edge_fg h' = edge_fg hh1' on dom_fg h1 - {n}" "flow_fg h' = flow_fg hh1' on dom_fg h1 - {n}"
    using split_fg[of h' "dom_fg h1 - {n}" "dom_fg h2 \<union> {n}"] assms
    by auto

  have E0: "edge_fg h' = edge_fg h2 on (dom_fg h2)" "edge_fg h = edge_fg h2 on (dom_fg h2)"
    "flow_fg h' = flow_fg h2 on (dom_fg h2)" "flow_fg h = flow_fg h2 on (dom_fg h2)"
    using ** assms edge_fg_plus_fg_on2 flow_fg_plus_fg_on2 by blast+

  (* notice that h = h1 + h2 and h' = h1' + h2 imply hh2 = hh2' *)
  have E1: "hh2 = hh2'"
    apply (rule fg_eqI)
    using C D EE apply auto[1]
    using D(1) assms(3) plus_fg_ops_exist apply blast
    using C D EE E0 by auto
  then have E2: "int_fg hh2 = int_fg hh2'"
    by simp

  have "int_fg hh1 + int_fg hh2 = int_fg h"
    by (simp add: C(1) int_fg_fi_hom)
  also have "... = int_fg h'"
    using assms by simp
  also have "... = int_fg hh1' + int_fg hh2'"
    by (simp add: D(1) int_fg_fi_hom)
  (* fact 3: interface have to be equal *)
  finally have E2: "int_fg hh1 = int_fg hh1'"
    using E2 plus_fi_cancel_left[of "int_fg hh1" "int_fg hh2"] int_fg_fi_hom[of hh1 hh2] assms C
    by simp

  (* we collected all facts 1-3 that are required to contradict minimality of h1' *)
  have "h = hh1 + hh2" "h' = hh1' + hh2" "int_fg hh1 = int_fg hh1'" "dom_fg hh1' \<subset> dom_fg h1'"
    using E1 E2 C D ** X assms by auto
  then show False
    using ** by blast
qed

text \<open>@{cite \<open>lem. 4\<close> krishna19b}\<close>

lemma in_footprint_iff_changed:
  assumes "int_fg h = int_fg h'" "h \<noteq> bot" "h' \<noteq> bot"
    "n \<in> dom_fg h" "flow_footprint h h' h1'"
  shows "n \<in> dom_fg h1' \<longleftrightarrow>
    fg {n} (edge_fg h) (flow_fg h) \<noteq> fg {n} (edge_fg h') (flow_fg h')"
  using assms in_footprint_iff_changed1 in_footprint_iff_changed2 by metis

text \<open>Additionally show that flow footprints are unique:\<close>

lemma flow_footprint_unique:
  assumes "flow_footprint h h' h1'" "flow_footprint h h' h1''" "h \<noteq> bot" "h' \<noteq> bot"
  shows "h1' = h1''"
proof -
  obtain h11 h12 where *: "h = h11 + h12" "h' = h1' + h12" "int_fg h11 = int_fg h1'"
    using assms unfolding flow_footprint_def by blast

  obtain h21 h22 where **: "h = h21 + h22" "h' = h1'' + h22" "int_fg h21 = int_fg h1''"
    using assms unfolding flow_footprint_def by blast

  have nbot2: "h12 \<noteq> bot" "h22 \<noteq> bot" using * ** plus_fg_ops_exist assms by auto

  let ?h12 = "fg (dom_fg h12) (edge_fg h12) (flow_fg h12)"
  let ?h22 = "fg (dom_fg h22) (edge_fg h22) (flow_fg h22)"

  have "int_fg (h11 + h12) = int_fg h11 + int_fg h12" using int_fg_fi_hom by metis
  also have "... = int_fg h1' + int_fg h12" using * by simp
  also have "... = int_fg (h1' + h12)" using int_fg_fi_hom by metis
  finally have inbot: "int_fg (h1' + h12) \<noteq> bot" "int_fg h = int_fg h'" using assms * by auto

  let ?X = "{n . n \<in> dom_fg h \<and> fg {n} (edge_fg h) (flow_fg h) \<noteq> fg {n} (edge_fg h') (flow_fg h')}"

  have BLA: "\<And>x. x \<in> dom_fg h1' \<Longrightarrow> x \<in> dom_fg h"
    using assms * plus_fg_dom_un[of h1' h12]
    by (metis Diff_insert_absorb dom_fg_plus_fg_subs1 dom_fi_int_fg subset_Diff_insert)

  have dom1: "dom_fg h1' = ?X"
    using BLA apply auto
    using in_footprint_iff_changed2[OF inbot(2)] assms inbot BLA apply blast
    using * inbot in_footprint_iff_changed1[OF inbot(2) \<open>h \<noteq> bot\<close> \<open>h' \<noteq> bot\<close>] assms by blast

  have BLA: "\<And>x. x \<in> dom_fg h1'' \<Longrightarrow> x \<in> dom_fg h"
    using assms * ** plus_fg_dom_un[of h1'' h22]
    by (metis Diff_insert_absorb dom_fg_plus_fg_subs1 dom_fi_int_fg subset_Diff_insert)

  have dom2: "dom_fg h1'' = ?X"
    using BLA apply auto
    using in_footprint_iff_changed2[OF inbot(2)] assms inbot BLA apply blast
    using * inbot in_footprint_iff_changed1[OF inbot(2) \<open>h \<noteq> bot\<close> \<open>h' \<noteq> bot\<close>] assms by blast

  have dom: "dom_fg h1' = dom_fg h1''" using dom1 dom2 by simp
  then have "dom_fg h12 = dom_fg h' - dom_fg h1'" using assms plus_fg_dom_un[of h1' h12]
      plus_fg_dom_disj[of h1' h12] assms * by blast
  moreover have "dom_fg h22 = dom_fg h' - dom_fg h1''" using assms plus_fg_dom_un[of h1'' h22]
      plus_fg_dom_disj[of h1'' h22] assms ** \<open>dom_fg h1' = dom_fg h1''\<close> ** by blast
  ultimately have dom: "dom_fg h12 = dom_fg h22" using dom by simp

  have X1: "edge_fg h = edge_fg h12 on dom_fg h12" using edge_fg_plus_fg_on2 * assms by auto
  have X2: "edge_fg h = edge_fg h22 on dom_fg h22" using edge_fg_plus_fg_on2 ** assms by auto
  have X3: "flow_fg h = flow_fg h12 on dom_fg h12" using flow_fg_plus_fg_on2 * assms by auto
  have X4: "flow_fg h = flow_fg h22 on dom_fg h22" using flow_fg_plus_fg_on2 ** assms by auto

  have "?h12 = ?h22"
    apply (rule fg_cong)
    using dom X1 X2 X3 X4 by auto
  then have "h12 = h22"
    using nbot2 by auto
  then have "h1' + h12 = h1'' + h12" using * ** by simp
  then show "h1' = h1''" using plus_fg_cancel_right assms * by blast
qed

end
