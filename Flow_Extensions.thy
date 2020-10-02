\<^marker>\<open>creator Bernhard Pöttinger\<close>

chapter \<open>Contextual and Flow-Preserving Extensions of Flow Graphs\<close>
theory Flow_Extensions
  imports Flow_Base Chain
begin

paragraph \<open>Summary\<close>
text \<open>This theory defines two notions of extensions of flow graphs and
proofs the replacement theorem related to the simple extension.
The analogous result for the more difficult the extension can be found in
@{term Effectively_Acyclic_Maintain}.\<close>

paragraph \<open>Major Definitions\<close>
text \<open>
\<^item> @{term contextual_extension}: some condition that enables adding nodes to flow graphs using
  replacement lemma
\<^item> @{term subflow_preserving_extension}: some condition that enables adding nodes to effectively acyclic
  flow graphs using theorem @{term maintain_eff_acyclic_dom}
\<close>

paragraph \<open>Major Lemmas\<close>
text \<open>
\<^item> replacement theorem @{cite \<open>thm. 2\<close> krishna20}\<close>

paragraph \<open>Notation\<close>
text \<open>
\<^item> @{term contextual_extension}: @{text "i1 \<lesssim> i2"}
\<^item> @{term subflow_preserving_extension}: @{text "h1 \<lesssim>\<^sub>S h2"}
\<close>

section \<open>Contextual Extension\<close>

text \<open>@{cite \<open>def. 7\<close> krishna20}\<close>

definition contextual_extension
  :: "('n,'m) fi \<Rightarrow> ('n,'m::cancel_comm_monoid_add) fi \<Rightarrow> bool" ("_ \<lesssim> _")
where
  "contextual_extension \<equiv> \<lambda>i1 i2. dom_fi i1 \<subseteq> dom_fi i2 \<and>
    (inf_fi i1 = inf_fi i2 on dom_fi i1) \<and>
    (outf_fi i1 = outf_fi i2 on -dom_fi i2)"

text \<open>Contextual extension is transitive.\<close>

lemma contextual_extension_trans:
  assumes "i1 \<lesssim> i2" "i2 \<lesssim> i3"
  shows "i1 \<lesssim> i3"
proof -
  have "outf_fi i1 = outf_fi i3 on -dom_fi i3"
  proof
    fix x
    assume A: "x \<in> -dom_fi i3"
    then have B: "x \<in> -dom_fi i2" using assms unfolding contextual_extension_def by auto
    show "outf_fi i1 x = outf_fi i3 x"
      using A B assms unfolding contextual_extension_def by auto
  qed
  then show ?thesis
    using assms unfolding contextual_extension_def by auto
qed

text \<open>Contextual extension is reflexive.\<close>

lemma contextual_extension_refl:
  "i \<lesssim> i"
  unfolding contextual_extension_def
  by simp

text \<open>@{cite \<open>thm. 2\<close> krishna20}\<close>

theorem replacement:
  assumes "i = i1 + i2" "i1 \<lesssim> i1'" "i \<noteq> bot" "i1' \<noteq> bot"
    "dom_fi i1' \<inter> dom_fi i2 = {}" "outf_fi i2 = (\<lambda>_. 0) on (dom_fi i1' - dom_fi i1)"
  shows "\<exists>i'. i' = i1' + i2 \<and> i \<lesssim> i' \<and> i' \<noteq> bot"
proof -
  have *: "is_sum_fi i1 i2 i"
    using assms plus_fi_to_is_sum_fi by blast

  let ?n' = "dom_fi i1' \<union> dom_fi i2"
  let ?i' = "\<lambda>n. if n \<in> dom_fi i1' - dom_fi i1 then inf_fi i1' n else inf_fi i n"
  let ?o' = "\<lambda>n. outf_fi i n"

  have **: "-?n' \<subseteq> -dom_fi i"
    using assms * unfolding is_sum_fi_def contextual_extension_def by auto

  have "outf_fi i = \<lambda>n. outf_fi i1 n + outf_fi i2 n on - dom_fi i"
    using assms * unfolding is_sum_fi_def by auto
  hence **: "outf_fi (i1 + i2) = \<lambda>n. outf_fi i1 n + outf_fi i2 n on -?n'"
    using ** assms by auto

  have "is_sum_fi i1' i2 (fi ?n' ?i' ?o')"
    using assms * plus_fi_ops_exist(2) **
    unfolding is_sum_fi_def contextual_extension_def
    by auto
  then have A: "i1' + i2 = fi ?n' ?i' ?o'"
    using is_sum_fi_to_plus_fi by simp

  have B: "i \<lesssim> fi ?n' ?i' ?o'"
    using assms
    unfolding contextual_extension_def is_sum_fi_def
    by auto

  show ?thesis
    using A B
    by simp
qed

text \<open>0-interface is common starting point for applications of replacement theorem,
0-interface can be shown be extended by almost any interface quite easily:\<close>

lemma zero_lessim_fi:
  assumes "\<forall>x' \<in> -N1. o1 x' = 0" "finite N1"
  shows "0 \<lesssim> fi N1 i1 o1"
  using assms
  unfolding contextual_extension_def zero_fi_def
  by simp


section \<open>Subflow-Preserving Extension\<close>

text \<open>@{cite \<open>def. 13\<close> krishna20}\<close>

definition subflow_preserving_extension ("_ \<lesssim>\<^sub>S _") where
"h \<lesssim>\<^sub>S h' \<equiv> int_fg h \<lesssim> int_fg h' \<and>
(\<forall>n \<in> dom_fg h. \<forall>n' \<in> -dom_fg h'. \<forall>m \<le> inf_fg h n. cap_fg h n n' m = cap_fg h' n n' m) \<and>
(\<forall>n \<in> dom_fg h' - dom_fg h. \<forall>n' \<in> -dom_fg h'. \<forall>m \<le> inf_fg h' n. cap_fg h' n n' m = 0)"

text \<open>Subflow-preserving extension is reflexive:\<close>

lemma subflow_preserving_extension_refl:
  "h \<lesssim>\<^sub>S h"
  unfolding subflow_preserving_extension_def
  using contextual_extension_refl by simp

text \<open>Subflow-preserving extension is transitive:\<close>

lemma subflow_preserving_extension_trans:
  assumes "h1 \<lesssim>\<^sub>S h2" "h2 \<lesssim>\<^sub>S h3" "h1 \<noteq> bot" "h2 \<noteq> bot" "h3 \<noteq> bot"
  shows "h1 \<lesssim>\<^sub>S h3"
proof -
  have x12: "\<forall>n \<in> dom_fg h1. \<forall>n' \<in> -dom_fg h2. \<forall>m \<le> inf_fg h1 n. cap_fg h1 n n' m = cap_fg h2 n n' m"
    and x23: "\<forall>n \<in> dom_fg h2. \<forall>n' \<in> -dom_fg h3. \<forall>m \<le> inf_fg h2 n. cap_fg h2 n n' m = cap_fg h3 n n' m"
    using assms
    unfolding subflow_preserving_extension_def
    by auto

  have dom: "dom_fg h1 \<subseteq> dom_fg h2" "dom_fg h2 \<subseteq> dom_fg h3"
    using assms
    unfolding subflow_preserving_extension_def contextual_extension_def
    by auto

  have infeq: "inf_fg h1 = inf_fg h2 on dom_fg h1"
    using assms inf_fg_int_fg[of h1] inf_fg_int_fg[of h2]
    unfolding subflow_preserving_extension_def contextual_extension_def
    by simp

  have *: "\<forall>n \<in> dom_fg h1. \<forall>n' \<in> -dom_fg h3. \<forall>m \<le> inf_fg h1 n. cap_fg h1 n n' m = cap_fg h3 n n' m"
  proof (safe, goal_cases)
    case (1 n n' m)
    then have "cap_fg h1 n n' m = cap_fg h2 n n' m" using x12 dom by auto
    also have "... = cap_fg h3 n n' m" using x23 infeq dom 1 by auto
    finally show ?case .
  qed

  have **: "\<forall>n \<in> dom_fg h3 - dom_fg h1. \<forall>n' \<in> -dom_fg h3. \<forall>m \<le> inf_fg h3 n. cap_fg h3 n n' m = 0"
  proof (safe, goal_cases)
    case (1 n n' m)
    then show ?case
    proof (cases "n \<in> dom_fg h2")
      case True
      then have N: "n \<in> dom_fg h2 - dom_fg h1" using 1 by blast
      moreover have "n' \<in> -dom_fg h2" using True 1 dom by blast
      moreover have "m \<le> inf_fi (int_fg h2) n"
        using assms dom N 1 unfolding subflow_preserving_extension_def contextual_extension_def
        by (simp add: inf_fg_int_fg)
      ultimately have X1: "cap_fg h2 n n' m = 0"
        using assms dom
        unfolding subflow_preserving_extension_def by (simp add: inf_fg_int_fg)

      from 1 True have "n \<in> dom_fg h2" "n' \<in> -dom_fg h3" by auto
      moreover have "m \<le> inf_fi (int_fg h2) n"
        using assms dom N 1 unfolding subflow_preserving_extension_def contextual_extension_def
        by (simp add: inf_fg_int_fg)
      ultimately have X2: "cap_fg h2 n n' m = cap_fg h3 n n' m" 
        using assms dom unfolding subflow_preserving_extension_def
        by (simp add: inf_fg_int_fg)

      show ?thesis using X1 X2 by simp
    next
      case False
      then show ?thesis 
        using assms dom 1
        unfolding subflow_preserving_extension_def
        by auto
    qed
  qed

  show ?thesis
    using assms contextual_extension_trans * **
    unfolding subflow_preserving_extension_def
    by auto
qed

end
