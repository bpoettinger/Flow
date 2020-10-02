\<^marker>\<open>creator Bernhard Pöttinger\<close>

chapter \<open>Pip: Acquire\<close>
theory Pip_Acquire
imports Pip_Shared
begin

paragraph \<open>Verification of PIP acquire operation\<close>

lemma search23:
  fixes i1 i2 i3 :: "('a,'b :: cancel_comm_monoid_add) fi"
  assumes "i1 + i2 + i3 \<noteq> bot"
  shows "i1 + i2 \<noteq> bot" "i1 + i3 \<noteq> bot" "i2 + i3 \<noteq> bot"
proof -
  show "i1 + i2 \<noteq> bot" using plus_fi_ops_exist(1)[of "i1 + i2" i3] using assms by simp
  have "i1 + i3 + i2 \<noteq> bot" using assms  by (simp add: algebra_simps)
  then show "i1 + i3 \<noteq> bot" using plus_fi_ops_exist(1)[of "i1 + i3" i2] by (simp add: algebra_simps)
  have "i2 + i3 + i1 \<noteq> bot" using assms  by (simp add: algebra_simps)
  then show "i2 + i3 \<noteq> bot" using plus_fi_ops_exist(1)[of "i2 + i3" i1] by (simp add: algebra_simps)
qed

lemma Max_sup_in:
  assumes "finite B" "A \<subseteq> B" "Max B \<in> A"
  shows "Max A = Max B"
  using assms
  by (meson Max.coboundedI Max_eqI in_mono infinite_super)

lemma XD1:
  assumes "ixs + fi {xa} (\<lambda>_. add_mset t (m - {#f#})) (\<lambda>n. if n = xa then {#} else edge xa (Fields (\<eta> xa) (max q0 (Max (insert t (set_mset (m - {#f#}))))) q0 m) n m) \<noteq> bot"
    and "\<eta> xa \<noteq> Some xa" "Max (insert q0 (set_mset m)) = max q0 (Max (insert t (set_mset (m - {#f#}))))"
  shows "fi {xa} (\<lambda>_. add_mset t (m - {#f#})) (\<lambda>y. if Some y = \<eta> xa then {#Max_mset (add_mset t (m - {#f#}) + {#q0#})#} else {#}) + ixs \<noteq> bot"
proof -
  have "fi {xa} (\<lambda>_. add_mset t (m - {#f#})) (\<lambda>y. if Some y = \<eta> xa then {#Max_mset (add_mset t (m - {#f#}) + {#q0#})#} else {#}) =
        fi {xa} (\<lambda>_. add_mset t (m - {#f#})) (\<lambda>n. if n = xa then {#} else edge xa (Fields (\<eta> xa) (max q0 (Max (insert t (set_mset (m - {#f#}))))) q0 m) n m)"
    apply (rule fi_cong)
    using assms by (simp_all split: fields.splits)
  then show ?thesis
    using assms by (simp add: algebra_simps)
qed

lemma XD2:
  assumes "ixs + fi {xa} (\<lambda>_. add_mset t (m - {#f#})) (\<lambda>n. if n = xa then {#} else edge xa (Fields None (Max (insert x3 (set_mset m))) x3 m) n m) \<noteq> bot"
  shows "fi {xa} (\<lambda>_. add_mset t (m - {#f#})) (\<lambda>y. {#}) + ixs \<noteq> bot"
proof -
  have "fi {xa} (\<lambda>_. add_mset t (m - {#f#})) (\<lambda>n. if n = xa then {#} else edge xa (Fields None (Max (insert x3 (set_mset m))) x3 m) n m) =
        fi {xa} (\<lambda>_. add_mset t (m - {#f#})) (\<lambda>y. {#})"
    by (rule fi_cong, simp_all)
  then show ?thesis
    using assms by (simp add: algebra_simps)
qed

lemma XD3:
  assumes "N1 = N2" "\<forall>n \<in> N1. i1 n = i2 n" "\<forall>n \<in> -N1. o1 n = o2 n"
  shows "if1 + fi N1 i1 o1 = fi N2 i2 o2 + if1"
  using assms
  apply (simp add: algebra_simps)
  apply (rule arg_cong[OF fi_cong])
  by (simp_all add: algebra_simps)

lemma XD4:
  assumes "fi {xb} (\<lambda>_. mm) (\<lambda>y. edge xb (Fs xb) y mm) + i' +
       fi {xa} (\<lambda>_. add_mset t (m - {#f#})) (\<lambda>n. if n = xa then {#} else edge xa (Fields (Some xb) (Max (insert q0 (set_mset m))) q0 m) n m) \<noteq>
       bot" and "xa \<noteq> xb"
  shows "fi {xa} (\<lambda>_. add_mset t (m - {#f#})) (\<lambda>y. if y = xb then {#Max_mset (add_mset t (m - {#f#}) + {#q0#})#} else {#}) + i' \<noteq> bot"
proof -
  let ?f = "Max (insert q0 (set_mset m))"
  let ?t = "max q0 (Max (insert t (set_mset (m - {#f#}))))"

  let ?ia = "fi {xa} (\<lambda>_. add_mset t (m - {#f#})) (\<lambda>n. if n = xa then {#} else edge xa (Fields (Some xb) (Max (insert q0 (set_mset m))) q0 m) n m)"
  let ?ia' = "fi {xa} (\<lambda>_. add_mset t (m - {#f#})) (\<lambda>y. if y = xb then {#Max_mset (add_mset t (m - {#f#}) + {#q0#})#} else outf_fi (fi {xa} (\<lambda>_. add_mset t (m - {#f#})) (\<lambda>n. if n = xa then {#} else edge xa (Fields (Some xb) (Max (insert q0 (set_mset m))) q0 m) n m)) y)"
  let ?ia'' = "fi {xa} (\<lambda>n. if n = xa then add_mset t (m - {#f#}) else {#}) (\<lambda>n. if n = xb then {#max q0 (Max (insert t (set_mset (m - {#f#}))))#} else outf_fi (fi {xa} (\<lambda>_. add_mset t (m - {#f#})) (\<lambda>n. if n = xa then {#} else edge xa (Fields (Some xb) (Max (insert q0 (set_mset m))) q0 m) n m)) n)"

  let ?ia4 = "fi {xa} (\<lambda>_. add_mset t (m - {#f#})) (\<lambda>y. if y = xb then {#Max_mset (add_mset t (m - {#f#}) + {#q0#})#} else {#})"
  have ia4_ia': "?ia4 = ?ia'"
    by (rule fi_cong, auto)

  let ?ib = "fi {xb} (\<lambda>_. mm) (\<lambda>y. edge xb (Fs xb) y mm)"
  let ?ib'' = "fi {xb}
   (\<lambda>n. add_mset (max q0 (Max (insert t (set_mset (m - {#f#})))))
        (inf_fi (fi {xa} (\<lambda>_. add_mset t (m - {#f#})) (\<lambda>n. if n = xa then {#} else edge xa (Fields (Some xb) (Max (insert q0 (set_mset m))) q0 m) n m) + fi {xb} (\<lambda>_. mm) (\<lambda>y. edge xb (Fs xb) y mm)) n))
   (\<lambda>n. if n = xb then {#} else edge xb (Fs xb) n mm)"

  have X: "?ia' = ?ia''"
    by (rule fi_cong, auto)
  have XX: "(?ia + ?ib) + i' \<noteq> bot"
    using assms by (simp add: algebra_simps)
  have Y: "?ia + ?ib = ?ia'' + ?ib''"
    apply (rule adjust_interface'[of ?ia ?ib xa xb "{#?t#}", symmetric, simplified])
     apply (fact plus_fi_ops_exist(1)[OF XX]) using assms by simp
  then have Z: "(?ia'' + i') + ?ib'' \<noteq> bot"
    using XX by (simp add: algebra_simps)
  then have "?ia'' + i' \<noteq> bot"
    using plus_fi_ops_exist(1) by auto
  then show ?thesis
    using X assms by (simp add: ia4_ia')
qed

lemma onI:
  assumes "\<And>x. x \<in> X \<Longrightarrow> f x = g x"
  shows "f = g on X"
  using assms by blast

lemma plus_fi_cancel_left:
  assumes "i2 = i2'"
  shows "i1 + i2 = i1 + i2'"
  using assms by simp

lemma plus_fi_cancel_rigtht:
  assumes "i1 = i1'"
  shows "i1 + i2 = i1' + i2"
  using assms by simp

lemmas plus_fi_cancel = plus_fi_cancel_left plus_fi_cancel_right



lemma update_correct:
  fixes i ix ixs :: "(fields ref, int multiset) fi"
  assumes "finite (dom_fi i)" "V \<subseteq> dom_fi i" "x \<notin> xs"
    and "i = ixs + fi {x}
      (\<lambda>_. inf_fi ix x - {# f #} + (if t \<ge>0 then {# t #} else {#})) (outf_fi ix)"
    and "i \<noteq> bot" "f < t"
    and "\<forall>x \<in> V. t \<in># fields_qs (Fs x)"
    and "\<forall>x' \<in> dom_fi i. case \<eta> x' of Some y \<Rightarrow> y \<in> {x} \<union> xs | _ \<Rightarrow> True"
    and "t \<ge> 0"
  shows "<ff.NI (\<eta> x) x (Fs x) m ix * ff.GrI \<eta> Fs xs ixs>
    update x f t
    <\<lambda>_. \<exists>\<^sub>AFs'. ff.GrI \<eta> Fs' ({x} \<union> xs) i>"
  using assms
  apply (induction V arbitrary: f Fs m ix ixs xs \<eta> rule: finite_induct_reverse[where F="dom_fi i" and a=x])

  (* base case*)
    apply (rule cons_pre_rule[OF ent_frame_fwd[OF ff.peek_NI]])
      apply frame_inference+

  subgoal for a F f Fs m ix ixs xs \<eta>
    apply (rule cons_pre_rule[OF ent_frame_fwd[OF ff.GrI_dom]])
      apply frame_inference+
    apply clarsimp

    apply (subst update.simps)
    apply (sep_auto simp: pip_simps heap: ll_simps ff.fold_GrI_rule[where g="\<eta> a"] split: fields.splits if_splits dest: in_diffD XD1)
    apply (intro ff.GrI_cong[of "insert a (dom_fi ixs)"] onI)
         apply simp
    apply simp
       apply auto[1]
      apply (rule XD3[symmetric])
        apply simp
       apply simp
    apply simp
   apply (sep_auto simp: pip_simps heap: ll_simps ff.fold_GrI_rule[where g="\<eta> a"] split: fields.splits dest: XD2)
   apply (rule ff.GrI_cong[OF _ eq_on_refl])
      apply simp
    apply simp
    apply (simp add: algebra_simps, rule arg_cong[OF fi_cong], simp, simp, simp)

  subgoal premises prems for q0 ia x
  proof -
    have "t \<in># m" "f < t"
      using prems by auto
    then have "Max (insert q0 (set_mset m)) = max q0 (Max (insert t (set_mset (m - {#f#}))))"
      apply (cases "m = {#}", simp, simp)
      by (smt Max.insert_remove Max.remove at_most_one_mset_mset_diff diff_single_trivial finite_set_mset max_def more_than_one_mset_mset_diff)
    then show ?thesis
      using prems by simp
  qed
  done

  (* Step case! *)
  subgoal for a F' f Fs m ix ixs xs \<eta>

    apply (rule cons_pre_rule[OF ent_frame_fwd[OF ff.GrI_dom]])
      apply frame_inference+

    apply (subst update.simps)
    apply (sep_auto simp: pip_simps heap: ll_simps ff.fold_GrI_rule split: fields.splits if_splits dest: in_diffD XD1)
    apply (intro ff.GrI_cong[of "insert a (dom_fi ixs)"] onI)
         apply simp
    apply simp
       apply auto[1]
      apply (rule XD3[symmetric])
        apply simp
       apply simp
    apply simp
   apply (sep_auto simp: pip_simps heap: ll_simps ff.fold_GrI_rule[where g="\<eta> a"] split: fields.splits dest: XD2)
   apply (rule ff.GrI_cong[OF _ eq_on_refl])
      apply simp
    apply simp
    apply (simp add: algebra_simps, rule arg_cong[OF fi_cong], simp, simp, simp)

   apply (case_tac "a \<in> F'")
   (* re-encounter some node *)
  subgoal premises prems for q0 xb
  proof -
    have "t \<in># m" "f < t"
      using prems by auto
    then have "Max (insert q0 (set_mset m)) = max q0 (Max (insert t (set_mset (m - {#f#}))))"
      apply (cases "m = {#}", simp, simp)
      by (smt Max.insert_remove Max.remove at_most_one_mset_mset_diff diff_single_trivial finite_set_mset max_def more_than_one_mset_mset_diff)
    then show ?thesis
      using prems by simp
  qed

  (* an actual step *)
  apply (sep_auto simp: pip_simps heap: ll_simps ff.fold_GrI_rule[where g="\<eta> a"] split: fields.splits dest: XD4)
  subgoal premises prems for q0 xb i' mm
  proof -
    let ?i1 = "fi {xb} (\<lambda>_. mm) (\<lambda>y. edge x (Fs x) y mm)"

    let ?f = "Max (insert q0 (set_mset m))"
    let ?t = "max q0 (Max (insert t (set_mset (m - {#f#}))))"

    have S: "?t = t"
      by (smt prems Max.insert_not_elem Max.insert_remove Max.remove Max_singleton at_most_one_mset_mset_diff finite_set_mset max_def more_than_one_mset_mset_diff)

    have "Max (insert q0 (set_mset m)) \<noteq> t"
      using prems S by simp
    then have SS: "Max (insert q0 (set_mset m)) < t"
      by (smt Max.insert_remove Max_in Max_insert S at_most_one_mset_mset_diff empty_not_insert finite_set_mset max_def more_than_one_mset_mset_diff prems set_mset_add_mset_insert singletonD)

    have tge0: "?t \<ge> 0" using prems by auto

    let ?ia = "fi {a} (\<lambda>_. add_mset t (m - {#f#})) (\<lambda>n. if n = a then {#} else edge a (Fields (Some xb) (Max (insert q0 (set_mset m))) q0 m) n m)"
    let ?ia2 = "fi {a} (\<lambda>_. add_mset t (m - {#f#})) (\<lambda>y. if y = xb then {#Max_mset (add_mset t (m - {#f#}) + {#q0#})#} else {#})"
    let ?ia3 = " fi {a} (\<lambda>n. if n = a then add_mset t (m - {#f#}) else {#})
      (\<lambda>n. if n = xb then {#max q0 (Max (insert t (set_mset (m - {#f#}))))#} else outf_fi (fi {a} (\<lambda>_. add_mset t (m - {#f#})) (\<lambda>n. if n = a then {#} else edge a (Fields (Some xb) (Max (insert q0 (set_mset m))) q0 m) n m)) n)"

    have ia2_ia3: "?ia2 = ?ia3" by (rule fi_cong, auto)

    let ?ib = "fi {xb} (\<lambda>_. mm) (\<lambda>y. edge xb (Fs xb) y mm)"
    let ?ib2 = "fi {xb} (\<lambda>_. inf_fi (fi {xb} (\<lambda>_. mm) (\<lambda>y. edge xb (Fs xb) y mm)) xb + (if 0 \<le> max q0 (Max (insert t (set_mset (m - {#f#})))) then {#max q0 (Max (insert t (set_mset (m - {#f#}))))#} else {#}) - {#Max (insert q0 (set_mset m))#}) (outf_fi (fi {xb} (\<lambda>_. mm) (\<lambda>y. edge xb (Fs xb) y mm)))"
    let ?ib3 = "fi {xb} (\<lambda>n. add_mset (max q0 (Max (insert t (set_mset (m - {#f#}))))) ((if n = xb then mm else {#}) - (if n = a then {#} else if n = a then {#} else edge a (Fields (Some xb) (Max (insert q0 (set_mset m))) q0 m) n m)))
      (\<lambda>n. if n = xb then {#} else edge xb (Fs xb) n mm)"

    have ib2_ib3: "?ib2 = ?ib3" apply (rule fi_cong) using tge0 S prems by (auto simp: algebra_simps)

    have nbot_iaibi': "(?ia + ?ib) + i' \<noteq> bot"
      using prems by (simp add: algebra_simps)
    have nbot_iaib: "?ia + ?ib \<noteq> bot"
      using plus_fi_ops_exist(1)[OF nbot_iaibi'] by simp

    have nbot_ia_ibi': "?ia + (?ib + i') \<noteq> bot"
      using prems by (simp add: algebra_simps)

    have nbot_ib_iai': "?ib + (?ia + i') \<noteq> bot"
      using prems by (simp add: algebra_simps)

    have nbot_ib_i'ia: "?ib + (i' + ?ia) \<noteq> bot"
      using prems by (simp add: algebra_simps)

    have iaib_ia2ib2: "?ia + ?ib = ?ia2 + ?ib2"
      using adjust_interface_mset'[of ?ia ?ib a xb "{#?t#}", OF nbot_iaib] ib2_ib3 ia2_ia3 prems
      by (simp add: algebra_simps)
    then have nbot_ia2ib2: "?ia2 + ?ib2 + i' \<noteq> bot"
      using nbot_iaibi' by (simp add: algebra_simps)

    have nbot_ib_i'ia2: "?ib2 + (i'  + ?ia2) \<noteq> bot"
      using prems iaib_ia2ib2 by (simp add: algebra_simps)

    have nbot: "?i1 \<noteq> bot" "i' \<noteq> bot" "?ib + i' \<noteq> bot" "i' + ?ia \<noteq> bot" "i' + ?ia2 \<noteq> bot"
      using plus_fi_ops_exist(1)[OF nbot_iaib] plus_fi_ops_exist(2)[OF nbot_iaib]
        plus_fi_ops_exist(2)[OF nbot_ia_ibi'] plus_fi_ops_exist(2)[OF nbot_ib_i'ia]
        plus_fi_ops_exist(2)[OF nbot_ib_i'ia2] 
      by auto

    have *: "(?ib + ?ia) + i' \<noteq> bot"
      using prems by (simp add: algebra_simps)
    then have "?ib + ?ia \<noteq> bot"
      using plus_fi_ops_exist[OF *] by simp
    then have "inf_fi ?ib xb = inf_fi (?ib + ?ia) xb + outf_fi ?ia xb"
      using unfold_inf_fi[of ?ib ?ia xb] by simp

    have "{xb} \<union> insert a (dom_fi ixs - {xb}) = dom_fi i"
      using prems nbot by simp

    show ?thesis
      apply (subst S)+
      using prems iaib_ia2ib2 tge0 nbot
      apply (sep_auto heap: ent_star_mono[OF _ ff.GrI_cong] cons_rule[OF _ _
       prems(1)[of xb "insert a (dom_fi ixs - {xb})" _ _ _ "\<lambda>y. if y = a then Fields (Some xb) t q0 (add_mset t (m - {#f#})) else Fs y"]]
        simp: tge0 algebra_simps iaib_ia2ib2 nbot intro!: fi_cong ff.GrI_cong split: fields.splits)
      using S apply (simp add: algebra_simps)
      apply simp
      using S apply (simp add: algebra_simps)
      using S apply (simp add: algebra_simps)
      using SS apply simp
       apply (auto split: fields.splits)[1]
      apply (simp split: option.splits)
      apply (smt Un_iff dom_fi_fi dom_fi_plus_fi(1) fiI finite.emptyI finite_insert nbot(5) option.inject prems(9) singletonD)
      using nbot by simp
  qed
  done

  using assms apply simp
  done



lemma inf_fi_plus_fi1:
  assumes "x \<in> N1" "fi N1 i1 o1 + fi N2 i2 o2 \<noteq> bot"
  shows "inf_fi (fi N1 i1 o1 + fi N2 i2 o2) x = i1 x - o2 x"
proof -
  let ?i1 = "fi N1 i1 o1"
  let ?i2 = "fi N2 i2 o2"

  have "is_sum_fi ?i1 ?i2 (?i1 + ?i2)"
    using assms by (simp add: plus_fi_to_is_sum_fi)
  then have "inf_fi ?i1 = \<lambda>n. inf_fi (?i1 + ?i2) n + outf_fi ?i2 n on dom_fi ?i1"
    unfolding is_sum_fi_def by auto
  then have "i1 x = inf_fi (?i1 + ?i2) x + o2 x"
    using assms plus_fi_ops_exist[of ?i1 ?i2] dom_fi_plus_fi[of ?i1 ?i2] by auto
  then show ?thesis by simp
qed

lemma inf_fi_plus_fi2:
  assumes "x \<in> N2" "fi N1 i1 o1 + fi N2 i2 o2 \<noteq> bot"
  shows "inf_fi (fi N1 i1 o1 + fi N2 i2 o2) x = i2 x - o1 x"
proof -
  let ?i1 = "fi N1 i1 o1"
  let ?i2 = "fi N2 i2 o2"

  have "is_sum_fi ?i1 ?i2 (?i1 + ?i2)"
    using assms by (simp add: plus_fi_to_is_sum_fi)
  then have "inf_fi ?i2 = \<lambda>n. inf_fi (?i1 + ?i2) n + outf_fi ?i1 n on dom_fi ?i2"
    unfolding is_sum_fi_def by auto
  then have "i2 x = inf_fi (?i1 + ?i2) x + o1 x"
    using assms plus_fi_ops_exist[of ?i1 ?i2] dom_fi_plus_fi[of ?i1 ?i2] by auto
  then show ?thesis by simp
qed


lemmas pip_simps' = pip_simps fields_y'_def

lemma acquire_correct:
  assumes "p \<in> X" "r \<in> X" "p \<noteq> r" " \<eta> r = None" "i \<noteq> bot" "\<forall>x \<in> X. case \<eta> x of Some y \<Rightarrow> y \<in> X | _ \<Rightarrow> True"
  shows "<ff.GrI \<eta> Fs X i> acquire p r <\<lambda>_. \<exists>\<^sub>AFs'. ff.GrI (case \<eta> r of None \<Rightarrow> \<eta>(r := Some p) | _ \<Rightarrow> \<eta>(p := Some r)) Fs' X i>"
  unfolding acquire_def
  apply (rule cons_pre_rule[OF ent_frame_fwd[OF ff.GrI_dom]], frame_inference+)
  apply (sep_auto simp: pip_simps' heap: ll_simps split: fields.splits)
  using assms apply simp
  using assms apply simp
  apply (sep_auto simp: pip_simps' heap: ll_simps split: fields.splits)
  using assms apply simp
  using assms apply simp
  using assms dom_fi_plus_fi(2) apply fastforce
  apply (sep_auto simp: pip_simps' heap: ll_simps split: fields.splits)
  using assms apply simp
    apply (sep_auto simp: pip_simps' heap: ll_simps ff.fold_GrI_rule[where g="Some p"] split: fields.splits)
  subgoal premises prems for m i'a x3 x4
  proof -
    let ?ir = "fi {r} (\<lambda>_. x4) (\<lambda>y. {#})"
    let ?ir' = "fi {r} (inf_fi (fi {r} (\<lambda>_. x4) (\<lambda>y. {#}))) (\<lambda>n. if n = p then {#Max_mset (x4 + {#x3#})#} else outf_fi (fi {r} (\<lambda>_. x4) (\<lambda>y. {#})) n)"
    let ?ir2 = "fi {r} (\<lambda>_. x4) (\<lambda>y. if y = p then {#Max_mset (x4 + {#x3#})#} else {#})"
    let ?ip = "fi {p} (\<lambda>_. m) (\<lambda>y. edge p (Fs p) y m)"
    let ?ip' = "fi {p} (\<lambda>n. inf_fi (fi {r} (\<lambda>_. x4) (\<lambda>y. {#}) + fi {p} (\<lambda>_. m) (\<lambda>y. edge p (Fs p) y m)) n + {#Max_mset (x4 + {#x3#})#}) (outf_fi (fi {p} (\<lambda>_. m) (\<lambda>y. edge p (Fs p) y m)))"

    have ir'_ir2: "?ir' = ?ir2"
      by (rule fi_cong, auto)

    have "(?ir + ?ip) + i'a \<noteq> bot" using assms prems by (simp add: algebra_simps)
    then have nbot: "?ir + ?ip \<noteq> bot" using plus_fi_ops_exist(1) by blast
    have "?ir' + ?ip' = ?ir + ?ip" using assms adjust_interface'[of ?ir ?ip r p "{#Max_mset (x4 + {#x3#})#}", OF nbot] by simp
    then have "?ir' + (?ip' + i'a) \<noteq> bot" using prems assms by (simp add: algebra_simps)
    then have "?ip' + (?ir' + i'a) \<noteq> bot" by (simp add: algebra_simps)
    then have "?ir' + i'a \<noteq> bot" using plus_fi_ops_exist(2) by blast
    with prems ir'_ir2 show False by simp
  qed
     apply (cases "Fs r", simp)
    apply (cases "Fs r", simp)
   apply simp

  subgoal for m i'a x3 x4 ia

    apply (rule cons_rule[OF _ _ update_correct[where V="{}"], of _ "\<lambda>y. if y = r then Some p else \<eta> y"_ "\<lambda>x. if x = r then Fields (Some p) (Max (insert x3 (set_mset x4))) x3 x4 else Fs x"])
    using assms apply (simp add: algebra_simps)
              apply (rule ent_star_mono[OF ent_refl])
              apply (rule ff.GrI_cong)
                 apply simp
    apply (simp add: assms)
               apply simp
    apply simp
                 apply (rule ent_ex_preI)
                 apply (rule_tac x=Fs' in ent_ex_postI)
             apply (rule ff.GrI_cong _ eq_on_refl)
    apply (intro onI)
                    apply simp
               apply simp
    using assms search23 apply (auto simp: algebra_simps)[1]
             apply simp
            apply simp
           apply simp
    using assms apply simp
    subgoal premises prems
    proof -
      let ?ip = "fi {p} (\<lambda>_. m) (\<lambda>y. edge p (Fs p) y m)"
      let ?ip' = "fi {p} (\<lambda>_. inf_fi (fi {p} (\<lambda>_. m) (\<lambda>y. edge p (Fs p) y m)) p - {#- 1#} + (if 0 \<le> Max (insert x3 (set_mset x4)) then {#Max (insert x3 (set_mset x4))#} else {#})) (outf_fi (fi {p} (\<lambda>_. m) (\<lambda>y. edge p (Fs p) y m)))"
      let ?ip2 = "fi {p} (\<lambda>n. inf_fi (fi {r} (\<lambda>_. x4) (\<lambda>y. {#}) + fi {p} (\<lambda>_. m) (\<lambda>y. edge p (Fs p) y m)) n + {#Max_mset (x4 + {#x3#})#}) (outf_fi (fi {p} (\<lambda>_. m) (\<lambda>y. edge p (Fs p) y m)))"

      let ?ir = "fi {r} (\<lambda>_. x4) (\<lambda>y. {#})"
      let ?ir' = "fi {r} (\<lambda>_. x4) (\<lambda>y. if y = p then {#Max_mset (x4 + {#x3#})#} else {#})"
      let ?ir2 = "fi {r} (inf_fi (fi {r} (\<lambda>_. x4) (\<lambda>y. {#}))) (\<lambda>n. if n = p then {#Max_mset (x4 + {#x3#})#} else outf_fi (fi {r} (\<lambda>_. x4) (\<lambda>y. {#})) n)"

      have "(?ir + ?ip) + i'a \<noteq> bot" using assms prems by (simp add: algebra_simps)
      then have nbot: "?ir + ?ip \<noteq> bot" using plus_fi_ops_exist(1) by blast

      have B: "-1 \<notin># m"
        using assms prems by (cases "Fs p", auto)

      have A1: "?ip' = ?ip2"
        apply (rule fi_cong)
        apply simp
        using assms prems apply simp
         apply (intro conjI)
        apply clarsimp
          apply (subst inf_fi_plus_fi2, simp)
        using nbot apply blast
          apply (simp add: B diff_single_trivial)
         apply (smt Max_ge finite_insert finite_set_mset insertI1)
        by blast

      have A2: "?ir' = ?ir2"
        by (rule fi_cong, auto)
    
      have "?ir2 + ?ip2 = ?ir + ?ip"
        using assms adjust_interface'[of ?ir ?ip r p "{#Max_mset (x4 + {#x3#})#}", OF nbot]
        by simp
      then show ?thesis
        using A1 A2 by (simp add: algebra_simps)
    qed
    subgoal premises prems
    proof -
      let ?ip = "fi {p} (\<lambda>_. m) (\<lambda>y. edge p (Fs p) y m)"
      let ?ip' = "fi {p} (\<lambda>_. inf_fi (fi {p} (\<lambda>_. m) (\<lambda>y. edge p (Fs p) y m)) p - {#- 1#} + (if 0 \<le> Max (insert x3 (set_mset x4)) then {#Max (insert x3 (set_mset x4))#} else {#})) (outf_fi (fi {p} (\<lambda>_. m) (\<lambda>y. edge p (Fs p) y m)))"
      let ?ip2 = "fi {p} (\<lambda>n. inf_fi (fi {r} (\<lambda>_. x4) (\<lambda>y. {#}) + fi {p} (\<lambda>_. m) (\<lambda>y. edge p (Fs p) y m)) n + {#Max_mset (x4 + {#x3#})#}) (outf_fi (fi {p} (\<lambda>_. m) (\<lambda>y. edge p (Fs p) y m)))"

      let ?ir = "fi {r} (\<lambda>_. x4) (\<lambda>y. {#})"
      let ?ir' = "fi {r} (\<lambda>_. x4) (\<lambda>y. if y = p then {#Max_mset (x4 + {#x3#})#} else {#})"
      let ?ir2 = "fi {r} (inf_fi (fi {r} (\<lambda>_. x4) (\<lambda>y. {#}))) (\<lambda>n. if n = p then {#Max_mset (x4 + {#x3#})#} else outf_fi (fi {r} (\<lambda>_. x4) (\<lambda>y. {#})) n)"

      have "(?ir + ?ip) + i'a \<noteq> bot" using assms prems by (simp add: algebra_simps)
      then have nbot: "?ir + ?ip \<noteq> bot" using plus_fi_ops_exist(1) by blast

      have B: "-1 \<notin># m"
        using assms prems by (cases "Fs p", auto)

      have A1: "?ip' = ?ip2"
        using assms prems
        by (smt B Max_ge add_mset_add_single diff_empty diff_single_trivial fiI fi_cong finite.emptyI finite_insert finite_set_mset inf_fi_fi inf_fi_plus_fi2 insertI1 nbot set_mset_add_mset_insert)

      have A2: "?ir' = ?ir2"
        by (rule fi_cong, auto)
    
      have "?ir2 + ?ip2 = ?ir + ?ip"
        using assms adjust_interface'[of ?ir ?ip r p "{#Max_mset (x4 + {#x3#})#}", OF nbot]
        by simp
      then show ?thesis
        using A1 A2 prems assms by (auto simp: algebra_simps)
    qed
       apply (case_tac x4, simp, simp)
      apply simp
    using assms apply (auto split: option.splits)[1]
    by (case_tac x4, simp, simp)







  apply (sep_auto simp: pip_simps' heap: ll_simps split: fields.splits)
  using assms apply simp
    apply (sep_auto simp: pip_simps' heap: ll_simps ff.fold_GrI_rule[where g="Some r"] split: fields.splits)
  subgoal premises prems for i'a x3 x4 y x3a x4a
  proof -
    let ?ir = "fi {r} (\<lambda>_. x4) (\<lambda>ya. if ya = y then {#Max_mset (x4 + {#x3#})#} else {#})"
    let ?ir2 = "fi {r} (inf_fi (fi {r} (\<lambda>_. x4) (\<lambda>ya. if ya = y then {#Max_mset (x4 + {#x3#})#} else {#})))
     (\<lambda>n. if n = p then {#Max_mset (x4 + {#x3#})#} else outf_fi (fi {r} (\<lambda>_. x4) (\<lambda>ya. if ya = y then {#Max_mset (x4 + {#x3#})#} else {#})) n)"
    let ?ip = "fi {p} (\<lambda>_. x4a) (\<lambda>y. if Some y = \<eta> p then {#Max_mset (x4a + {#x3a#})#} else {#})"
    let ?ip' = "fi {p} (\<lambda>_. x4a) (\<lambda>y. if y = r then {#Max_mset (x4a + {#x3a#})#} else {#})"
    let ?ip2 = "fi {p} (\<lambda>n. inf_fi (fi {r} (\<lambda>_. x4) (\<lambda>ya. if ya = y then {#Max_mset (x4 + {#x3#})#} else {#}) + fi {p} (\<lambda>_. x4a) (\<lambda>y. if Some y = \<eta> p then {#Max_mset (x4a + {#x3a#})#} else {#})) n + {#Max_mset (x4 + {#x3#})#})
     (outf_fi (fi {p} (\<lambda>_. x4a) (\<lambda>y. if Some y = \<eta> p then {#Max_mset (x4a + {#x3a#})#} else {#})))"

    have ir'_ir2: "?ip' = ?ip2"
      apply (rule fi_cong)
      using prems assms by auto

    have "(?ir + ?ip) + i'a \<noteq> bot" using assms prems by (simp add: algebra_simps)
    then have nbot: "?ir + ?ip \<noteq> bot" using plus_fi_ops_exist(1) by blast
    have "?ir2 + ?ip2 = ?ir + ?ip" using assms adjust_interface'[of ?ir ?ip r p "{#Max_mset (x4 + {#x3#})#}", OF nbot] by simp
    then have "?ir2 + (?ip' + i'a) \<noteq> bot" using prems assms by (simp add: algebra_simps)
    then have "?ip' + i'a \<noteq> bot" using plus_fi_ops_exist(2) by blast
    with prems ir'_ir2 show False by simp
  qed
     apply (cases "Fs r", simp)
    apply (cases "Fs r", simp)
   apply simp

  subgoal for i'a x3 x4 y x3a x4a ia

    apply (rule cons_rule[OF _ _ update_correct[where V="{}"], of _ "\<lambda>y. if y = p then Some r else \<eta> y"_ "\<lambda>x. if x = p then Fields (Some r) (Max (insert x3 (set_mset x4))) x3 x4 else Fs x" _ 
        "fi {r} (\<lambda>_. x4) (\<lambda>ya. if ya = y then {#Max_mset (x4 + {#x3#})#} else {#})" _
        "fi {p} (\<lambda>_. x4a) (\<lambda>y. if y = r then {#Max_mset (x4a + {#x3a#})#} else {#}) + i'a"])
    using assms apply (simp add: algebra_simps)
                 apply (rule ent_ex_preI)
                 apply (rule_tac x=Fs' in ent_ex_postI)
             apply (rule ff.GrI_cong _ eq_on_refl)
    apply (intro onI)
                    apply simp
               apply simp
    using assms search23 apply (auto simp: algebra_simps)[1]
    using assms by (auto simp: algebra_simps)
  done

end
