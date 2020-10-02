\<^marker>\<open>creator Bernhard Pöttinger\<close>

chapter \<open>PIP: Example\<close>
theory Pip_Example
imports Pip_Shared Pip_Release Pip_Acquire
begin

paragraph \<open>Application of PIP operations\<close>

definition "fold_GrI_repl x \<equiv> ff.fold_GrI x"

theorem replacement':
  assumes "i = i1 + i2" "i1 \<lesssim> i1'" "i \<noteq> bot" "i1' \<noteq> bot"
    "dom_fi i1' \<inter> dom_fi i2 = {}" "outf_fi i2 = (\<lambda>_. 0) on (dom_fi i1' - dom_fi i1)"
  shows "i1 + i2  \<lesssim> i1' + i2 \<and> i1' + i2 \<noteq> bot"
  using replacement assms by blast

lemma NI_GrI_disj:
  "ff.NI g x fs m ix * ff.GrI \<eta> Fs X iX \<Longrightarrow>\<^sub>A ff.NI g x fs m ix * ff.GrI \<eta> Fs X iX * \<up>(x \<notin> X)"
  unfolding ff.NI_def ff.GrI_def ff.N_def ff.Gr_def
  apply sep_auto
  by (smt Set.set_insert assn_times_assoc assn_times_comm finite_insert mod_pure_star_dist
      prod.insert pure_false sngr_same_false)

lemma zero_lessim_fi':
  assumes "\<forall>x' \<in> -dom_fi i. outf_fi i x' = 0" "i \<noteq> bot"
  shows "0 \<lesssim> i"
  using assms
  unfolding contextual_extension_def zero_fi_def
  by auto

lemma fold_GrI_repl_rule:
  assumes "x \<notin> X" "outf_fi ix = (\<lambda>_. 0) on -dom_fi ix" "outf_fi iX x = {#}"
  shows "<ff.GrI \<eta> Fs X iX * ff.NI g x fs m ix>
   fold_GrI_repl x
   <\<lambda>_. ff.GrI (\<eta>(x := g)) (Fs(x := fs)) ({x} \<union> X) (iX + ix) * \<up>(x \<notin> X \<and> iX + ix \<noteq> bot)>"
  using assms
  unfolding fold_GrI_repl_def apply simp
  apply (rule cons_pre_rule[OF ent_frame_fwd[OF ff.peek_NI]], frame_inference+, clarsimp)
  apply (rule cons_pre_rule[OF ent_frame_fwd[OF ff.GrI_dom]], frame_inference+, clarsimp)
  using replacement'[of iX 0 iX ix, OF _ zero_lessim_fi'[of ix]] apply auto
  apply (sep_auto heap: ff.fold_GrI_rule simp: algebra_simps)
  by (rule ff.GrI_cong, simp_all add: algebra_simps)

definition alloc_node :: "int \<Rightarrow> fields ref Heap" where
"alloc_node q0 \<equiv> do {
  n \<leftarrow> ref (Fields None q0 q0 {#});
  ff.close_NI n ({#} :: int multiset);
  fold_GrI_repl n;
  return n
}"

lemma alloc_correct:
  assumes "q0 \<ge> 0" "outf_fi i = (\<lambda>_. 0) on -dom_fi i"
  shows "<ff.GrI \<eta> Fs X i>
    alloc_node q0
    <\<lambda>x. \<exists>\<^sub>Aix. ff.GrI (\<eta>(x := None))
      (\<lambda>x'. if x = x' then Fields None q0 q0 {#} else Fs x') (X \<union> {x}) (i + ix) *
      \<up>(i + ix \<noteq> bot \<and> ix = fi {x} (\<lambda>_. 0) (\<lambda>_. 0) \<and> x \<notin> dom_fi i)>"
   apply (rule cons_pre_rule[OF ent_frame_fwd[OF ff.GrI_dom]])
    apply frame_inference+
  apply clarsimp
  using assms
  unfolding alloc_node_def
  apply (sep_auto heap: ff.close_NI_rule)
   apply (rule cons_pre_rule)
    apply (rule NI_GrI_disj)
   apply (rule cons_pre_rule[OF ent_frame_fwd[OF ff.GrI_dom]])
     apply frame_inference+
   apply (sep_auto heap: ff.close_NI_rule fold_GrI_repl_rule)+
  by (rule ff.GrI_cong, auto)

definition pip_example where
"pip_example \<equiv> do {
  a \<leftarrow> alloc_node 1;
  b \<leftarrow> alloc_node 2;
  acquire a b;
  c \<leftarrow> alloc_node 3;
  acquire b c;
  release a b;
  acquire c a;

  return (a,b,c)
}"

lemma no_infl_no_outfl_plus_fg:
  assumes "finite X1" "finite X2" "X1 \<inter> X2 = {}"
  shows "fi X1 (\<lambda>_. 0) (\<lambda>_. 0) + fi X2 (\<lambda>_. 0) (\<lambda>_. 0) = fi (X1 \<union> X2) (\<lambda>_. 0) (\<lambda>_. 0)"
  apply (rule is_sum_fi_to_plus_fi)
  using assms unfolding is_sum_fi_def by auto

lemma pip_example_correct:
  shows "<ff.GrI Map.empty Fs0 {} 0 * \<up>(\<phi> 0)>
    pip_example
    <\<lambda>(a,b,c). (\<exists>\<^sub>AFs i \<eta>. ff.GrI \<eta> Fs {a,b,c} i *
               \<up>(\<eta> = Map.empty(c \<mapsto> b, a \<mapsto> c) \<and>
                 i = fi {a,b,c} (\<lambda>_. 0) (\<lambda>_. 0) \<and> \<phi> i))>"
  unfolding pip_example_def
  apply (sep_auto heap: alloc_correct acquire_correct release_correct
         simp: no_infl_no_outfl_plus_fg zero_fi_def \<phi>_def)
  by (rule ff.GrI_cong, auto simp: no_infl_no_outfl_plus_fg insert_commute)

end
