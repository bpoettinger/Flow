\<^marker>\<open>creator Bernhard Pöttinger\<close>

chapter \<open>PIP Invariant\<close>
theory Pip_Invariant
imports Pip_Shared
begin

paragraph \<open>Summary\<close>
text \<open>This theory proves that in our PIP data structure the current priorities are an upper
bound of the default priorities of default priorities of predecessors.\<close>

definition path where
"path Fs x y \<equiv> \<exists>xs. hd xs = x \<and> last xs = y \<and> (\<forall>i \<in> {0..length xs - 1}. fields_y (Fs (xs!i)) = Some (xs!(i+1)))"

lemma edge_flow_iff1:
  assumes "x \<in> X" "H \<noteq> bot" "dom_fg H = X" "H \<noteq> bot"
  shows "ff.Gr \<eta> Fs X H \<Longrightarrow>\<^sub>A ff.Gr \<eta> Fs X H * \<up>(\<exists>m. \<gamma> (\<eta> x) x (Fs x) m \<and> flow_fg H x = m \<and>
    edge_fg H x = (\<lambda>y m. if Some y = fields_y (Fs x) then {# Max_mset (m + {# fields_q0 (Fs x) #}) #} else {#}))"
  apply (rule ent_trans[OF ff.Gr_dom])
  apply (rule ent_trans[OF ent_frame_fwd[OF ff.unfold_N[of x X H]]])
  using assms apply simp
  using assms apply simp
  apply frame_inference+
  apply (cases "Fs x")
  apply sep_auto
    apply (subst flow_fg_plus_fg_on1')
  using assms apply simp
  using assms plus_fg_ops_exist dom_fg_fg apply blast
  using assms plus_fg_ops_exist apply (metis flow_fg_fg singletonI)
  using assms unfolding fields_y_def apply clarsimp
    apply (subst edge_fg_plus_fg_on1')
  using assms plus_fg_ops_exist apply blast
  using assms plus_fg_ops_exist dom_fg_fg apply blast
  apply (subst edge_fg_fg)
  using assms plus_fg_ops_exist apply blast
   apply simp
   apply (rule ext, simp)
  apply (case_tac "Fs x", auto simp: fields_q0_def split: fields.splits)[1]
  apply sep_auto
  apply (rule ent_trans[OF ff.fold_N[where g="\<eta> x"]])
      apply simp
     apply (metis ab_semigroup_add_class.add.commute assms(2) dom_fg_fg dom_fg_plus_fg1 plus_fg_ops_exist)
  apply (metis ab_semigroup_add_class.add.commute assms(2))
   apply simp
  apply (rule ff.Gr_cong)
  using assms by auto

lemma sum_insert_multiset:
  assumes "finite X" "a \<in> X"
  shows "f a \<subseteq># sum f X"
proof -
  have "sum f (insert a (X - {a})) = f a + sum f (X - {a})"
    by (rule sum.insert, simp_all add: assms)
  then show ?thesis
    using le_iff_add insert_absorb[of a X] assms
    by auto
qed

lemma onI:
  assumes "\<And>x. x \<in> X \<Longrightarrow> f x = g x"
  shows "f = g on X"
  using assms by blast

lemma path_flow:
  assumes "xs \<noteq> []" "\<forall>i \<in> {0..<length xs}. fields_y (Fs (xs!i)) = Some ((xs @ [y])!(i+1))"
    "set xs \<subseteq> X" "y \<in> X" "H \<noteq> bot" "X = dom_fg H"
  shows "ff.Gr \<eta> Fs X H \<Longrightarrow>\<^sub>A ff.Gr \<eta> Fs X H * \<up>(fields_q (Fs (hd xs)) \<le> fields_q (Fs y))"
  using assms
  apply (induction xs rule: list_nonempty_induct)
  subgoal for x
   apply (rule_tac ent_trans[OF edge_flow_iff1[where x=x]], simp, simp, simp, simp)
    apply (rule_tac ent_trans[OF ent_frame_fwd[OF edge_flow_iff1[where x=y]]], simp, simp, simp, simp)
    apply (frame_inference)+
    apply clarsimp
    subgoal premises prems for a b
    proof -
      have "{#fields_q (Fs x)#} = {#Max (insert (fields_q0 (Fs x)) (set_mset (flow_fg H x)))#}"
        using prems by (cases "Fs x", simp split: prod.splits add: fields_q_def fields_q0_def)
      also have "... = edge_fg H x y (flow_fg H x)"
        using prems by (cases "\<eta> x", simp, cases "Fs x", simp)
      also have "... \<subseteq># (\<Sum>x \<in> dom_fg H. edge_fg H x y (flow_fg H x))"
        apply (rule sum_insert_multiset[where f="\<lambda>x. edge_fg H x y (flow_fg H x)" and a=x])
        using prems by auto
      also have "... \<subseteq># inf_fg H y + (\<Sum>x \<in> dom_fg H. edge_fg H x y (flow_fg H x))"
        by simp
      also have "... = flow_fg H y"
        using flow_eq_ne_bot[of H] prems by (cases xs, auto)
      finally have "fields_q (Fs x) \<in># flow_fg H y"
        by simp
      then have "fields_q (Fs x) \<le> Max (insert (fields_q0 (Fs y)) (set_mset (flow_fg H y)))"
        by simp
      also have "... = fields_q (Fs y)"
        using prems by (cases "Fs y", simp split: prod.splits add: fields_q_def fields_q0_def)
      finally show ?thesis .
  qed
  done
  subgoal for x xs
   apply (rule_tac ent_trans[OF edge_flow_iff1[where x=x]], simp, simp, simp, simp)
    apply (rule_tac ent_trans[OF ent_frame_fwd[OF edge_flow_iff1[where x="hd xs" and X=X and H=H]]], simp)
        apply (meson basic_trans_rules(31) hd_in_set)
        apply simp
        apply simp
    apply simp
      apply (frame_inference+)
    apply clarsimp
    subgoal premises prems for a b
    proof -
      have *: "(\<lambda>i. fields_y (Fs (xs ! i))) = \<lambda>i. Some ((xs @ [y]) ! (Suc i)) on {0..<length xs}"
        using prems(3) by force

      then have "fields_y (Fs ((x # xs) ! 0)) = Some ((xs @ [y]) ! 0)"
        using atLeastLessThan_iff prems by blast
      then have S: "fields_y (Fs x) = Some (hd xs)"
        by (simp add: hd_conv_nth prems(1))

      have "{#fields_q (Fs x)#} = {#Max (insert (fields_q0 (Fs x)) (set_mset (flow_fg H x)))#}"
        using prems by (cases "Fs x", simp split: prod.splits add: fields_q_def fields_q0_def)
      also have "... = edge_fg H x (hd xs) (flow_fg H x)"
        using prems S by (cases "\<eta> x", simp, cases "Fs x", simp add: fields_q0_def fields_y_def)
      also have "... \<subseteq># (\<Sum>x \<in> dom_fg H. edge_fg H x (hd xs) (flow_fg H x))"
        using sum_insert_multiset[where f="\<lambda>x. edge_fg H x (hd xs) (flow_fg H x)" and a=x]
        using prems by auto
      also have "... \<subseteq># inf_fg H (hd xs) + (\<Sum>x \<in> dom_fg H. edge_fg H x (hd xs) (flow_fg H x))"
        by simp
      also have "... = flow_fg H (hd xs)"
        using flow_eq_ne_bot[of H] prems by (cases xs, auto)
      finally have "fields_q (Fs x) \<in># flow_fg H (hd xs)"
        by simp
      then have "fields_q (Fs x) \<le> Max (insert (fields_q0 (Fs (hd xs))) (set_mset (flow_fg H (hd xs))))"
        by simp
      also have "... = fields_q (Fs (hd xs))"
        using prems by (cases "Fs (hd xs)", simp split: prod.splits add: fields_q_def fields_q0_def)
      also have "... \<le> fields_q (Fs y)"
        using prems(2)[OF *] prems by blast
      finally show ?thesis .
    qed
    done
  done

lemma path_flow':
  assumes "xs \<noteq> []" "\<forall>i \<in> {0..<length xs}. fields_y (Fs (xs!i)) = Some ((xs @ [y])!(i+1))"
    "set xs \<subseteq> X" "y \<in> X" "H \<noteq> bot" "X = dom_fg H"
  shows "ff.Gr \<eta> Fs X H \<Longrightarrow>\<^sub>A ff.Gr \<eta> Fs X H * \<up>(fields_q0 (Fs (hd xs)) \<le> fields_q (Fs y))"
proof -
  have X: "\<gamma> (\<eta> (hd xs)) (hd xs) (Fs (hd xs)) m \<Longrightarrow> fields_q0 (Fs (hd xs)) \<le> fields_q (Fs (hd xs))"
    for xs m
  proof -
    assume A: "\<gamma> (\<eta> (hd xs)) (hd xs) (Fs (hd xs)) m"

    have "fields_q0 (Fs (hd xs)) \<le> Max_mset ({#fields_q0 (Fs (hd xs))#} + m)"
      by simp
    also have "... = fields_q (Fs (hd xs))"
      using assms A by (cases "Fs (hd xs)", simp split: prod.splits add: fields_q_def fields_q0_def)
    finally show ?thesis .
  qed

  show ?thesis
    apply (rule ent_trans[OF path_flow[of xs]])
    using assms apply blast
    using assms apply blast
    using assms apply blast
    using assms apply blast
    using assms apply blast
    using assms apply blast
    apply (simp only: ent_pure_pre_iff, intro impI)
    apply (rule ent_trans[OF ff.unfold_N[where x="hd xs"]])
    using assms apply auto[1]
    using assms apply simp
    apply auto[1]
     apply (rule order_trans[OF X])
     apply simp
     apply simp
    apply sep_auto
    subgoal for m h'
    apply (rule ent_frame_fwd[OF ff.fold_N])
         defer
         defer
    defer
         defer
         apply frame_inference+
        apply sep_auto
    apply (rule ff.Gr_cong)
    using assms hd_in_set apply blast
    using assms apply simp
    using assms apply simp
    using assms apply simp
    using assms apply simp
    using assms apply simp
    subgoal
      by (metis ab_semigroup_add_class.add.commute assms(5) assms(6)
          dom_fg_fg dom_fg_plus_fg1 plus_fg_ops_exist)
    using assms subgoal
      by (metis plus_fg_comm)
    using assms apply simp
    done
  done
qed

abbreviation "paths Fs X y \<equiv>
  { xs | xs. xs \<noteq> []
       \<and> (\<forall>i \<in> {0..length xs}. fields_y (Fs (xs!i)) = Some ((xs @ [y])!(i+1)))
       \<and> set xs \<subseteq> X }"

lemma upper_bound:
  assumes "finite P" "X = dom_fg H" "y \<in> X" "P \<subseteq> paths Fs X y" "H \<noteq> bot"
  shows "ff.Gr \<eta> Fs X H \<Longrightarrow>\<^sub>A ff.Gr \<eta> Fs X H *
    \<up>(fields_q (Fs y) \<ge>
      Max ({fields_q0 (Fs (hd xs)) | xs. xs \<in> P } \<union> {fields_q0 (Fs y)}))"
  using assms
proof (induction P rule: finite_induct)
  case empty
  show ?case
    apply (rule ent_trans[OF ff.unfold_N[where x=y]])
    using empty apply simp
    using empty apply simp
    apply (intro ent_ex_preI)
    unfolding fields_q0_def fields_q_def
    apply (cases "Fs y")
    apply sep_auto
    apply (rule ent_trans[OF ff.fold_N[where g="\<eta> y"]])
    apply simp
    subgoal premises prems for h' x3 x4
    proof -
      let ?h1 = "fg {y} (\<lambda>_. edge y (Fields (\<eta> y) (Max (insert x3 (set_mset x4))) x3 x4)) (\<lambda>_. x4)"
      have "dom_fg ?h1 = {y}"
        using empty prems plus_fg_ops_exist[of ?h1 h'] by simp
      moreover have "dom_fg H = dom_fg ?h1 \<union> dom_fg h'"
        using empty prems plus_fg_dom_un by blast
      moreover have "dom_fg ?h1 \<inter> dom_fg h' = {}"
        using empty prems plus_fg_dom_disj by blast
      ultimately show ?thesis
        using empty by blast
    qed
    using assms apply (simp add: algebra_simps)
    apply simp
    apply (rule ff.Gr_cong)
    using assms by auto
next
  case (insert xs F)
  show ?case 
    apply (rule ent_trans[OF path_flow'[of xs Fs y]])
    using insert apply simp
    using insert apply simp
    using insert apply simp
    using insert apply simp
    using insert apply simp
    using insert apply simp
    apply (rule ent_frame_fwd[OF insert.IH])
    using insert apply simp
    using insert apply simp
    using insert apply simp
    using insert apply simp
    apply frame_inference
    using insert by simp
qed

end
