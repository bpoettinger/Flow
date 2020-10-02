\<^marker>\<open>creator Bernhard Pöttinger\<close>

chapter \<open>Uniqueness of Flows in Effective Acyclic Graphs\<close>
theory Effectively_Acyclic_Uniqueness
imports Effectively_Acyclic
begin

paragraph \<open>Summary\<close>
text \<open>Proof of lemma 5 from @{cite krishna20}: the flow in effectively acyclic flow graphs is
unique.\<close>

section \<open>Uniqueness of effectively acyclic flows, case @{term "card (dom_fg h) >= 1"}\<close>

lemma eff_acyclic_flow_unique':
  fixes E :: "('m \<Rightarrow> 'm :: pos_cancel_comm_monoid_add) set"
  assumes "End_closed E" "flow_eq (fg N e f) i" "eff_acyclic N e f" "finite N"
    "card N \<ge> 1" "\<forall>x y. e x y \<in> E" "(\<lambda>_. 0) \<in> E"
  shows "\<forall>f'. flow_eq (fg N e f') i \<longrightarrow> eff_acyclic N e f' \<longrightarrow> f = f' on N"
proof safe
  fix f' n
  assume A: "flow_eq (fg N e f') i" "eff_acyclic N e f'" "n \<in> N"

  let ?sf = "\<Sum>ns\<in>k_lists N (card N + 1). chain e ns n (f (hd ns))"
  let ?sf' = "\<Sum>ns\<in>k_lists N (card N + 1). chain e ns n (f' (hd ns))"

  have "\<And>ns f. eff_acyclic N e f \<Longrightarrow> flow_eq (fg N e f) i \<Longrightarrow> ns \<in> k_lists N (card N + 1)
    \<Longrightarrow> chain e ns n (f (hd ns)) = 0"
    subgoal for ns f
      by (rule eff_acyclic_chain_0[of N e f ns i E], unfold k_lists_def, simp_all add: assms)
    done
  then have *: "\<And>f. eff_acyclic N e f \<Longrightarrow> flow_eq (fg N e f) i
    \<Longrightarrow> (\<Sum>ns \<in> k_lists N (card N + 1). chain e ns n (f (hd ns))) = 0"
    by auto

  have B1: "f n = i n + (\<Sum>ns\<in>l_lists N (card N + 1). chain e ns n (i (hd ns))) + ?sf"
    by (subst unroll_flow_eq'[of "card N + 1" N e f i E n], auto simp: * assms A)
  then have B1': "f n = i n + (\<Sum>ns\<in>l_lists N (card N + 1). chain e ns n (i (hd ns)))"
    using * assms by simp
  have B2: "f' n = i n + (\<Sum>ns\<in>l_lists N (card N + 1). chain e ns n (i (hd ns))) + ?sf'"
    by (subst unroll_flow_eq'[of "card N + 1" N e f' i E n], auto simp: assms A)
  then have B2': "f' n = i n + (\<Sum>ns\<in>l_lists N (card N + 1). chain e ns n (i (hd ns)))"
    using A * assms by simp

  show "f n = f' n"
    using B1' B2' by simp
qed


text \<open>Lemma 5 from @{cite krishna20}\<close>

lemma eff_acyclic_flow_unique:
  fixes E :: "('m \<Rightarrow> 'm :: pos_cancel_comm_monoid_add) set"
  assumes "End_closed E" "flow_eq (fg N e f) i" "eff_acyclic N e f"
    "finite N" "\<forall>x y. e x y \<in> E" "(\<lambda>_. 0) \<in> E"
  shows "\<forall>f'. flow_eq (fg N e f') i \<longrightarrow> eff_acyclic N e f' \<longrightarrow> f = f' on N"
proof (cases "card N \<ge> 1")
  case True
  then show ?thesis using eff_acyclic_flow_unique' assms by blast
next
  case False
  then have "N = {}" using assms by (meson card_0_eq leI less_one)
  then show ?thesis by auto
qed

end
