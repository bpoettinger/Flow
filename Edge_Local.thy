\<^marker>\<open>creator Bernhard Pöttinger\<close>

chapter \<open>Edge Local Flow\<close>
theory Edge_Local
imports Flow_Base
begin

abbreviation "const E \<equiv> \<forall>e \<in> E. \<exists>a. e = (\<lambda>_. a)"

lemma edge_local:
  assumes "const E" "\<forall>x y. e x y \<in> E" "N \<noteq> {}" "finite N"
  shows "\<exists>f. flow_eq (fg N e f) i \<and> (\<forall>f'. flow_eq (fg N e f') i \<longrightarrow> f = f' on N)"
proof -
  let ?f = "\<lambda>n. i n + (\<Sum>n' \<in> N. (THE a. e n' n = (\<lambda>_. a)))"
  let ?e = "\<lambda>n n' m. (THE a. e n n' = (\<lambda>_. a))"

  have *: "e = ?e"
    by (intro ext, smt assms the_equality)

  have "flow_eq (fg N e ?f) i"
    apply (rule flow_eqI)
    apply (subst (2) *)
    using assms by blast+
  moreover have "\<forall>f'. flow_eq (fg N e f') i \<longrightarrow> ?f = f' on N"
  proof (safe, goal_cases)
    case (1 f' n)
    then have "f' n = i n + (\<Sum>n'\<in>N. e n' n (f' n'))"
      using fgE''[OF 1(1) assms(3)] by simp
    then have "f' n = i n + (\<Sum>n'\<in>N. ?e n' n (f' n'))"
      apply (subst (asm) *) by simp
    then show ?case by simp
  qed
  ultimately show ?thesis
    by blast
qed

end
