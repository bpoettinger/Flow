\<^marker>\<open>creator Bernhard Pöttinger\<close>

chapter \<open>PIP: Release\<close>
theory Pip_Release
imports Pip_Shared
begin

paragraph \<open>Verification of PIP release operation\<close>

(* attempt to avoid explicit applications plus_fi_ops_exists, elimination rules *)

lemma search23:
  fixes i1 i2 i3 :: "('a,'b :: cancel_comm_monoid_add) fi"
  assumes "i1 + (i2 + i3) \<noteq> bot"
  shows "i1 + i2 \<noteq> bot" "i1 + i3 \<noteq> bot" "i2 + i3 \<noteq> bot"
proof -
  show "i1 + i2 \<noteq> bot" using plus_fi_ops_exist(1)[of "i1 + i2" i3] using assms by (simp add: algebra_simps)
  have "i1 + i3 + i2 \<noteq> bot" using assms  by (simp add: algebra_simps)
  then show "i1 + i3 \<noteq> bot" using plus_fi_ops_exist(1)[of "i1 + i3" i2] by (simp add: algebra_simps)
  have "i2 + i3 + i1 \<noteq> bot" using assms  by (simp add: algebra_simps)
  then show "i2 + i3 \<noteq> bot" using plus_fi_ops_exist(1)[of "i2 + i3" i1] by (simp add: algebra_simps)
qed

lemma search23':
  fixes i1 i2 i3 :: "('a,'b :: cancel_comm_monoid_add) fi"
  assumes "i1 + i2 + i3 \<noteq> bot"
  shows "i1 + i2 \<noteq> bot" "i1 + i3 \<noteq> bot" "i2 + i3 \<noteq> bot"
proof -
  show "i1 + i2 \<noteq> bot" using plus_fi_ops_exist(1)[of "i1 + i2" i3] using assms by (simp add: algebra_simps)
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
  assumes "finite (dom_fi i)" "V \<subseteq> dom_fi i"
    and "f \<in># inf_fi ix x" "\<forall>x \<in> V. f \<notin># fields_qs (Fs x)"
    and "x \<notin> xs"
    and "i = ixs + fi {x}
      (\<lambda>_. inf_fi ix x - {# f #} + (if t \<ge>0 then {# t #} else {#})) (outf_fi ix)"
    and "i \<noteq> bot" "f > t" 
    and "\<forall>x' \<in> {x} \<union> xs. case \<eta> x' of Some y \<Rightarrow> y \<in> {x} \<union> xs | _ \<Rightarrow> True"
  shows "<ff.NI (\<eta> x) x (Fs x) m ix * ff.GrI \<eta> Fs xs ixs>
    update x f t
    <\<lambda>_. \<exists>\<^sub>AFs'. ff.GrI \<eta> Fs' ({x} \<union> xs) i>"
  using assms
  apply (induction V arbitrary: t Fs m ix ixs xs \<eta> rule: finite_induct_reverse[where F="dom_fi i" and a=x])

  (* base case*)
    apply (rule cons_pre_rule[OF ent_frame_fwd[OF ff.peek_NI]])
      apply frame_inference+
    apply clarsimp
  subgoal for x F t Fs m ix ixs xs \<eta> unfolding fields_qs_def by (cases "Fs x", auto)

  (* Step case! *)
  subgoal for xa F' t Fs m ix ixs xs \<eta>

    (* get domain of graph *)
    apply (rule cons_pre_rule[OF ent_frame_fwd[OF ff.GrI_dom]])
      apply frame_inference+
    apply clarsimp

    (* unfold function definition*)
    apply (subst update.simps)

    (* non-recursive case 1 *)
    apply (sep_auto simp: pip_simps heap: ll_simps split: fields.splits dest: in_diffD XD1)
    apply (intro ff.GrI_cong onI)
         apply simp
    apply simp
       apply auto[1]
      apply (rule XD3[symmetric])
        apply simp
    apply simp
    apply simp
    (* non-recursive case 2 *)
   apply (sep_auto simp: pip_simps heap: ll_simps split: fields.splits dest: XD2)
   apply (rule ff.GrI_cong[OF _ eq_on_refl])
      apply simp
    apply simp
    apply (simp add: algebra_simps, rule arg_cong[OF fi_cong], simp, simp, simp)

   apply (case_tac "xa \<in> F'")
   (* re-encounter some node *)
    apply (auto)[1]

  (* recursive case for t \<ge> 0 *)
  apply (sep_auto simp: pip_simps heap: ll_simps split: fields.splits dest: XD4)
  subgoal premises prems for q0 xb i' mm
  proof -
    let ?i1 = "fi {xb} (\<lambda>_. mm) (\<lambda>y. edge x (Fs x) y mm)"

    (* related to termination, involves non-trivial arguments *)
    have "m \<noteq> {#}" using prems by auto
    then have neq: "max q0 (Max (set_mset m)) \<noteq> max q0 (Max (insert t (set_mset (m - {#f#}))))"
      using prems by simp
    then have Z: "Max_mset m \<noteq> Max_mset (m - {#f#} + {#t#})" by simp
    have ZZ: "Max (set_mset m) = f" using Max_mset_add_remove[OF \<open>f \<in># m\<close> \<open>t < f\<close> Z[symmetric]] by simp

    have T: "Max_mset (m - {#f#} + {#t#}) \<le> Max_mset m" by (fact Max_mset_add_remove_le[OF \<open>f \<in># m\<close> \<open>t < f\<close>])

    have SS: "max q0 f \<le> f"
    proof (rule ccontr)
      assume "\<not> max q0 f \<le> f"
      then have "f < q0" by simp
      then have "Max (set_mset m) < q0" "Max_mset (m - {#f#} + {#t#}) < q0" using ZZ T by auto
      then have "max q0 (Max (set_mset m)) = max q0 (Max (insert t (set_mset (m - {#f#}))))"
        by (smt add_mset_add_single set_mset_add_mset_insert)
      then show False using neq by simp
    qed
    then have S: "Max (insert q0 (set_mset m)) = f"
      using \<open>m \<noteq> {#}\<close> ZZ by simp

    have SSS: "q0 < f"
      by (smt T ZZ add_mset_add_single neq set_mset_add_mset_insert)

    have LT': "Max_mset (m - {#f#} + {#t#}) < Max_mset m"
      by (fact Max_mset_add_remove_lt[OF \<open>f \<in># m\<close> \<open>t < f\<close> Z[symmetric]])
    then have LT: "max q0 (Max_mset (m - {#f#} + {#t#})) < Max_mset m"
      by (smt add_mset_add_single neq set_mset_add_mset_insert)

    let ?f = "Max (insert q0 (set_mset m))"
    let ?t = "max q0 (Max (insert t (set_mset (m - {#f#}))))"

    have tge0: "?t \<ge> 0" using prems by auto

    (* fake-interface manipulation of ?ia and ?ib, should be automated *)

    let ?ia = "fi {xa} (\<lambda>_. add_mset t (m - {#f#})) (\<lambda>n. if n = xa then {#} else edge xa (Fields (Some xb) (Max (insert q0 (set_mset m))) q0 m) n m)"
    let ?ia2 = "fi {xa} (\<lambda>_. add_mset t (m - {#f#})) (\<lambda>y. if y = xb then {#Max_mset (add_mset t (m - {#f#}) + {#q0#})#} else {#})"
    let ?ia3 = "fi {xa} (inf_fi (fi {xa} (\<lambda>_. add_mset t (m - {#f#})) (\<lambda>n. if n = xa then {#} else edge xa (Fields (Some xb) (Max (insert q0 (set_mset m))) q0 m) n m)))
     (\<lambda>n. if n = xb then {#max q0 (Max (insert t (set_mset (m - {#f#}))))#} else outf_fi (fi {xa} (\<lambda>_. add_mset t (m - {#f#})) (\<lambda>n. if n = xa then {#} else edge xa (Fields (Some xb) (Max (insert q0 (set_mset m))) q0 m) n m)) n)"

    have ia2_ia3: "?ia2 = ?ia3" by (rule fi_cong, auto)

    let ?ib = "fi {xb} (\<lambda>_. mm) (\<lambda>y. edge xb (Fs xb) y mm)"
    let ?ib2 = "fi {xb} (\<lambda>_. inf_fi (fi {xb} (\<lambda>_. mm) (\<lambda>y. edge xb (Fs xb) y mm)) xb + (if 0 \<le> max q0 (Max (insert t (set_mset (m - {#f#})))) then {#max q0 (Max (insert t (set_mset (m - {#f#}))))#} else {#}) - {#f#}) (outf_fi (fi {xb} (\<lambda>_. mm) (\<lambda>y. edge xb (Fs xb) y mm)))"
    let ?ib3 = "fi {xb}
     (\<lambda>n. inf_fi (fi {xb} (\<lambda>_. mm) (\<lambda>y. edge xb (Fs xb) y mm)) n - outf_fi (fi {xa} (\<lambda>_. add_mset t (m - {#f#})) (\<lambda>n. if n = xa then {#} else edge xa (Fields (Some xb) (Max (insert q0 (set_mset m))) q0 m) n m)) n +
           {#max q0 (Max (insert t (set_mset (m - {#f#}))))#})
     (outf_fi (fi {xb} (\<lambda>_. mm) (\<lambda>y. edge xb (Fs xb) y mm)))"

    have ib2_ib3: "?ib2 = ?ib3" apply (rule fi_cong) using tge0 S prems by auto

    (* this stuff about the existence of flow interfaces should be automated,
       no idea how to, some idas provided some improvement, this stuff is remaining *)

    have nbot_iaibi': "(?ia + ?ib) + i' \<noteq> bot"
      using prems by (simp add: algebra_simps)
    have nbot_iaib: "?ia + ?ib \<noteq> bot"
      using plus_fi_ops_exist(1)[OF nbot_iaibi'] by simp

    have iaib_ia2ib2: "?ia + ?ib = ?ia2 + ?ib2"
      using adjust_interface_mset'[of ?ia ?ib xa xb "{#?t#}"] ib2_ib3 ia2_ia3 nbot_iaib prems by simp
    then have nbot_ia2ib2: "?ia2 + ?ib2 + i' \<noteq> bot"
      using nbot_iaibi' by (simp add: algebra_simps)

    have nbot_ib_i'ia2: "?ib2 + (i'  + ?ia2) \<noteq> bot"
      using prems iaib_ia2ib2 by (simp add: algebra_simps)

    have nbot: "?i1 \<noteq> bot" "i' \<noteq> bot" "?ib + i' \<noteq> bot" "i' + ?ia \<noteq> bot" "i' + ?ia2 \<noteq> bot"
      using prems nbot_ib_i'ia2 by (auto elim!: search23 search23' simp: prems algebra_simps)

    (* again part of termination *)

    have *: "(?ib + ?ia) + i' \<noteq> bot"
      using prems by (simp add: algebra_simps)
    then have "?ib + ?ia \<noteq> bot"
      using plus_fi_ops_exist[OF *] by simp
    then have "inf_fi ?ib xb = inf_fi (?ib + ?ia) xb + outf_fi ?ia xb"
      using unfold_inf_fi[of ?ib ?ia xb] by simp
    then have f_in_mm: "f \<in># mm"
      apply (simp split: if_splits)
      using prems apply simp
      using S by (metis (no_types, lifting) union_single_eq_member)

    have SSSS: "\<forall>x \<in># m - {#f#}. x < f"
      using ZZ LT' by auto

    show ?thesis
      apply (subst (1) S)
      using prems iaib_ia2ib2 f_in_mm tge0 SSS nbot SSSS
      apply (sep_auto heap: ent_star_mono[OF _ ff.GrI_cong] cons_rule[OF _ _
       prems(1)[of _ xb "\<lambda>y. if y = xa then Fields (Some xb) (max q0 (Max (insert t (set_mset (m - {#f#}))))) q0 (add_mset t (m - {#f#})) else Fs y" "insert xa (dom_fi ixs - {xb})"]]
        simp: tge0 algebra_simps iaib_ia2ib2 nbot intro!: fi_cong ff.GrI_cong split: fields.splits)
    apply (auto split: option.splits simp: nbot algebra_simps)
    done
  qed


 (* recursive case for t < 0, symmetric to above case, in certain aspects nastier than
    above case due to multiset reasoning, case should be eliminated by avoiding the case split
    caused by sep_auto *)
    apply (subst update.simps)
  apply (sep_auto simp: pip_simps heap: ll_simps ff.fold_GrI_rule[where g="\<eta> xa"] split: fields.splits dest: in_diffD XD1 intro: XD2 XD3)
  subgoal premises prems for q0
  proof -
    have "fi {xa} (\<lambda>_. m - {#f#}) (\<lambda>y. if Some y = \<eta> xa then {#Max_mset (m - {#f#} + {#q0#})#} else {#}) =
          fi {xa} (\<lambda>_. m - {#f#}) (\<lambda>n. if n = xa then {#} else edge xa (Fields (\<eta> xa) (Max (insert q0 (set_mset (m - {#f#})))) q0 m) n m)"
      by (rule fi_cong, auto simp: prems)
    then show ?thesis using prems by (simp add: algebra_simps)
  qed
  apply simp
      apply auto[1]
   apply (rule ent_ex_postI)
  apply (rule ff.GrI_cong[OF _ eq_on_refl])
     apply simp
    apply simp
  subgoal premises prems for q0 xb
  proof -
    let ?i1 = "fi {xa} (\<lambda>_. m - {#f#}) (\<lambda>n. if n = xa then {#} else edge xa (Fields (\<eta> xa) (Max (insert q0 (set_mset (m - {#f#})))) q0 m) n m)"
    let ?i2 = "fi {xa} (\<lambda>_. m - {#f#}) (\<lambda>y. if Some y = \<eta> xa then {#Max_mset (m - {#f#} + {#q0#})#} else {#})"
    have "?i1 = ?i2" by (rule fi_cong, auto simp: prems)
    then show ?thesis by (simp add: algebra_simps)
  qed


  apply (sep_auto simp: pip_simps heap: ll_simps ff.fold_GrI_rule[where g="\<eta> xa"] split: fields.splits)
  subgoal premises prems for q0
  proof -
    have "fi {xa} (\<lambda>_. m - {#f#}) (\<lambda>y. {#}) =
          fi {xa} (\<lambda>_. m - {#f#}) (\<lambda>n. if n = xa then {#} else edge xa (Fields None (Max (insert q0 (set_mset m))) q0 m) n m)"
      by (rule fi_cong, auto simp: prems)
    then show ?thesis using prems by (simp add: algebra_simps)
  qed
  apply simp
  apply simp
    apply (rule ent_ex_postI)
  apply clarsimp
   apply (rule ff.GrI_cong[OF _ eq_on_refl])
      apply simp
    apply simp
  apply (simp add: algebra_simps, rule arg_cong[OF fi_cong], simp, simp, simp)
  apply (sep_auto simp: pip_simps heap: ll_simps ff.fold_GrI_rule[where g="\<eta> xa"] split: fields.splits)
  subgoal premises prems for x3 x i' mm
  proof -
    let ?i1 = "fi {xa} (\<lambda>_. m - {#f#}) (\<lambda>n. if n = xa then {#} else edge xa (Fields (Some x) (Max (insert x3 (set_mset m))) x3 m) n m)"
    let ?i2 = "fi {x} (\<lambda>_. mm) (\<lambda>y. edge x (Fs x) y mm)"

    let ?i1'' = "fi {xa} (\<lambda>_. m - {#f#}) (\<lambda>y. if y = x then {#Max_mset (m - {#f#} + {#x3#})#} else {#})"

    let ?i1' = "fi {xa} (inf_fi (fi {xa} (\<lambda>_. m - {#f#}) (\<lambda>n. if n = xa then {#} else edge xa (Fields (Some x) (Max (insert x3 (set_mset m))) x3 m) n m)))
   (\<lambda>n. if n = x then {#Max_mset (m - {#f#} + {#x3#})#} else outf_fi (fi {xa} (\<lambda>_. m - {#f#}) (\<lambda>n. if n = xa then {#} else edge xa (Fields (Some x) (Max (insert x3 (set_mset m))) x3 m) n m)) n)"
    let ?i2' = "fi {x}
     (\<lambda>n. inf_fi (fi {xa} (\<lambda>_. m - {#f#}) (\<lambda>n. if n = xa then {#} else edge xa (Fields (Some x) (Max (insert x3 (set_mset m))) x3 m) n m) + fi {x} (\<lambda>_. mm) (\<lambda>y. edge x (Fs x) y mm)) n +
           {#Max_mset (m - {#f#} + {#x3#})#})
     (outf_fi (fi {x} (\<lambda>_. mm) (\<lambda>y. edge x (Fs x) y mm)))"

    have A: "?i1' = ?i1''"
      apply (rule fi_cong)
        apply simp
       apply simp
      by simp

    have "?i1 + ?i2 + i' \<noteq> bot" using prems by (simp add: algebra_simps)
    then have E: "?i1 + ?i2 \<noteq> bot" using search23'[of ?i1 ?i2 i'] by simp

    have B: "?i1' + ?i2' = ?i1 + ?i2"
      apply (rule adjust_interface'[of ?i1 ?i2 xa x "{#Max_mset (m - {#f#} + {#x3#})#}"])
      using E apply simp
        apply simp
       apply simp
      using prems by blast

    have "?i1' + ?i2' + i' \<noteq> bot" using prems E B by (simp add: algebra_simps)
    then have "?i1'' + i' \<noteq> bot" using search23'[of ?i1' ?i2' i'] A by simp
    then show ?thesis using prems by (simp add: algebra_simps)
  qed

    apply simp
  apply simp
  subgoal premises prems for q0 xb i' i1 mm xaa
  proof -
    have S: "Max (insert q0 (set_mset m)) = f"
    proof -
      have "Max (insert q0 (set_mset m)) \<noteq> Max (insert q0 (set_mset (m - {#f#})))" using prems by blast
      show ?thesis
      proof (rule ccontr)
        let ?S = "insert q0 (set_mset m)"
        let ?m = "Max ?S"
        assume "?m \<noteq> f"
        then have "?m \<ge> f" "?m \<in> ?S" using \<open>f \<in># m\<close>
          by (simp, meson Max_in finite_insert finite_set_mset insert_not_empty)
        then have *: "?m > f" using \<open>Max (insert q0 (set_mset m)) \<noteq> f\<close> by linarith
        then have **: "?m \<in> insert q0 (set_mset (m - {#f#}))"
          by (smt \<open>Max (insert q0 (set_mset m)) \<in> insert q0 (set_mset m)\<close> insert_DiffM2 insert_iff mset_right_cancel_elem prems)
        moreover have X: "insert q0 (set_mset (m - {#f#})) \<subseteq> insert q0 (set_mset m)" using \<open>f \<in># m\<close>
          by (metis insert_DiffM insert_mono set_mset_add_mset_insert subset_insertI)
        have "Max (insert q0 (set_mset (m - {#f#}))) = ?m"
          apply (rule Max_sup_in[OF _ X]) using ** by auto
        then show False using prems by simp
      qed
    qed

    let ?ia = "fi {xa} (\<lambda>_. m - {#f#}) (\<lambda>n. if n = xa then {#} else edge xa (Fields (Some xb) (Max (insert q0 (set_mset m))) q0 m) n m)"
    let ?ia' = "fi {xa} (\<lambda>_. m - {#f#}) (\<lambda>y. if y = xb then {#Max_mset (m - {#f#} + {#q0#})#} else {#})"
    let ?ia'' = "fi {xa} (inf_fi (fi {xa} (\<lambda>_. m - {#f#}) (\<lambda>n. if n = xa then {#} else edge xa (Fields (Some xb) (Max (insert q0 (set_mset m))) q0 m) n m)))
   (\<lambda>n. if n = xb then {#Max_mset (m - {#f#} + {#q0#})#} else outf_fi (fi {xa} (\<lambda>_. m - {#f#}) (\<lambda>n. if n = xa then {#} else edge xa (Fields (Some xb) (Max (insert q0 (set_mset m))) q0 m) n m)) n)"

    let ?ib = "fi {xb} (\<lambda>_. mm) (\<lambda>y. edge xb (Fs xb) y mm)"
    let ?ib'' = "fi {xb}
   (\<lambda>n. inf_fi (fi {xa} (\<lambda>_. m - {#f#}) (\<lambda>n. if n = xa then {#} else edge xa (Fields (Some xb) (Max (insert q0 (set_mset m))) q0 m) n m) + fi {xb} (\<lambda>_. mm) (\<lambda>y. edge xb (Fs xb) y mm)) n +
         {#Max_mset (m - {#f#} + {#q0#})#})
   (outf_fi (fi {xb} (\<lambda>_. mm) (\<lambda>y. edge xb (Fs xb) y mm)))"

    have "?ia + ?ib + i' \<noteq> bot" using prems by (simp add: algebra_simps)
    then have nbot: "?ib + i' \<noteq> bot" "?ia + ?ib \<noteq> bot" "?ia + i' \<noteq> bot" using search23' by blast+

    let ?ib3 = "fi {xb} (\<lambda>_. add_mset (Max (insert q0 (set_mset (m - {#f#})))) mm - {#f#}) (\<lambda>n. if n = xb then {#} else edge xb (Fs xb) n mm)"
    let ?ib4 = "fi {xb} (\<lambda>_. inf_fi (fi {xb} (\<lambda>_. mm) (\<lambda>y. edge xb (Fs xb) y mm)) xb + (if 0 \<le> Max (insert q0 (set_mset (m - {#f#}))) then {#Max (insert q0 (set_mset (m - {#f#})))#} else {#}) - {#f#})
     (outf_fi (fi {xb} (\<lambda>_. mm) (\<lambda>y. edge xb (Fs xb) y mm)))"

    let ?t = "Max (insert q0 (set_mset (m - {#f#})))"
    have G: "0 \<le> ?t"
      apply (rule order_trans[OF _ Max_ge[of _ q0]])
      using prems by auto

    have L: "Max (insert q0 (set_mset (m - {#f#}))) < f"
    proof -
      have "Max (insert q0 (set_mset m)) \<noteq> Max (insert q0 (set_mset (m - {#f#})))"
        using prems by blast

      show ?thesis
      proof (rule ccontr)
        let ?m = "Max (insert q0 (set_mset (m - {#f#})))"
        assume "\<not> Max (insert q0 (set_mset (m - {#f#}))) < f"
        then have X: "?m \<ge> f" by linarith
        then have "?m \<in> insert q0 (set_mset m)"
          by (metis Max_in empty_not_insert finite_set_mset insertCI insertE insert_DiffM prems(2) set_mset_add_mset_insert)
        with X show False
          by (smt Max.coboundedI S finite.insertI finite_set_mset prems)
      qed
    qed
    then have notin: "f \<notin># m - {#f#}"
      by auto

    have MM: "mm = add_mset (Max (insert q0 (set_mset m))) (inf_fi (?ib + ?ia) xb)"
      using prems unfold_inf_fi[of ?ib ?ia xb] nbot by (simp add: algebra_simps)
    then have F: "f \<in># mm" using S by (metis (no_types, lifting) union_single_eq_member)

    let ?ia4 = "fi {xa} (inf_fi (fi {xa} (\<lambda>_. m - {#f#}) (\<lambda>n. if n = xa then {#} else edge xa (Fields (Some xb) (Max (insert q0 (set_mset m))) q0 m) n m)))
   (\<lambda>n. if n = xb then {#Max (insert q0 (set_mset (m - {#f#})))#} else outf_fi (fi {xa} (\<lambda>_. m - {#f#}) (\<lambda>n. if n = xa then {#} else edge xa (Fields (Some xb) (Max (insert q0 (set_mset m))) q0 m) n m)) n)"
    let ?ib4 = "fi {xb}
   (\<lambda>n. inf_fi (fi {xb} (\<lambda>_. mm) (\<lambda>y. edge xb (Fs xb) y mm)) n - outf_fi (fi {xa} (\<lambda>_. m - {#f#}) (\<lambda>n. if n = xa then {#} else edge xa (Fields (Some xb) (Max (insert q0 (set_mset m))) q0 m) n m)) n +
         {#Max (insert q0 (set_mset (m - {#f#})))#})
   (outf_fi (fi {xb} (\<lambda>_. mm) (\<lambda>y. edge xb (Fs xb) y mm)))"

    have T: "?ia4 + ?ib4 = ?ia + ?ib"
      apply (rule adjust_interface_mset'[of ?ia ?ib xa xb "{#?t#}"])
      using nbot apply simp
        apply simp
       apply simp
      using prems by blast

    have A: "?ia4 = ?ia'" by (rule fi_cong, auto)

    have BB: "?ib3 = ?ib4"
      apply (rule fi_cong, simp)
      using nbot G prems S apply simp
      by simp

    have X: "?ia' + ?ib3 = ?ia + ?ib"
      using T A BB by (simp add: algebra_simps)

    have "?ia' + ?ib4 + i' \<noteq> bot"
      using T A nbot prems by (auto simp: algebra_simps)
    then have nbot': "i' + ?ia' \<noteq> bot"
      using search23[of ?ia' ?ib4 i'] by (simp add: algebra_simps)

    have D: "dom_fi (?ib + i') = dom_fi i' \<union> {xb}" "dom_fi i' \<union> {xb} = dom_fi ixs" "dom_fi (i' + ?ia') = dom_fi i' \<union> {xa}"
      using nbot prems nbot' by (auto simp: algebra_simps)

    show ?thesis
      apply (subst S)
      apply (rule cons_rule[OF _ _
       prems(1)[of _ xb "\<lambda>y. if y = xa then Fields (Some xb) (Max (set_mset (m - {#f#} + {# q0 #}))) q0 (m - {#f#}) else Fs y" "insert xa (dom_fi ixs - {xb})"]])
                 apply (simp add: algebra_simps prems)
                 apply (rule ent_star_mono[OF ent_refl ff.GrI_cong])
                    apply simp
                   apply simp
                  apply simp
                 apply simp
      subgoal
        apply (rule ent_ex_preI)
        apply (rule_tac x=Fs' in ent_ex_postI)
        apply (rule ff.GrI_cong)
           apply simp
          apply simp
        using D apply auto[1]
        using prems X G by (simp add: algebra_simps)
      using F apply simp
      using prems notin apply (auto split: fields.splits)[1]
      using X G prems apply (simp add: algebra_simps)
      using X G prems apply (simp add: algebra_simps)
      using X G prems apply (simp add: algebra_simps)
      using L apply blast
      using D apply (simp add: algebra_simps prems)
      apply auto[1]
      using prems apply (auto split: option.splits)[1]
      by (metis (no_types) Un_Diff_cancel Un_insert_left Un_insert_right ab_semigroup_add_class.add.commute insert_absorb2 insert_iff prems)
  qed
  done

  using assms apply simp

  done


lemmas pip_simps' = pip_simps fields_y'_def

lemma release_correct:
  assumes "p \<in> X" "r \<in> X" "p \<noteq> r" " \<eta> r = Some p" "i \<noteq> bot"
    and "\<forall>x \<in> X. case \<eta> x of Some y \<Rightarrow> y \<in> X | _ \<Rightarrow> True"
  shows "<ff.GrI \<eta> Fs X i>
    release p r
    <\<lambda>_. \<exists>\<^sub>AFs'. ff.GrI (\<eta>(r := None)) Fs' X i>"
    unfolding release_def
  apply (rule cons_pre_rule[OF ent_frame_fwd[OF ff.GrI_dom]], frame_inference+)
  apply (sep_auto simp: pip_simps' heap: ll_simps split: fields.splits)
  using assms apply simp
  using assms apply simp
  apply (sep_auto simp: pip_simps' heap: ll_simps split: fields.splits)
  using assms apply simp
  using assms apply simp
  using assms dom_fi_plus_fi(2) apply fastforce
  apply (sep_auto simp: pip_simps' heap: ll_simps split: fields.splits)
  subgoal premises prems for m i'a x3 x4
  proof -
    let ?ir = "fi {r} (\<lambda>_. x4) (\<lambda>y. if Some y = \<eta> r then {#Max_mset (x4 + {#x3#})#} else {#})"
    let ?ir' = "fi {r} (inf_fi (fi {r} (\<lambda>_. x4) (\<lambda>y. if Some y = \<eta> r then {#Max_mset (x4 + {#x3#})#} else {#}))) (\<lambda>n. if n = p then 0 else outf_fi (fi {r} (\<lambda>_. x4) (\<lambda>y. if Some y = \<eta> r then {#Max_mset (x4 + {#x3#})#} else {#})) n)"
    let ?ir2 = "fi {r} (\<lambda>_. x4) (\<lambda>y. {#})"
    let ?ip = "fi {p} (\<lambda>_. m) (\<lambda>y. edge p (Fs p) y m)"
    let ?ip' = "fi {p} (\<lambda>n. inf_fi (fi {r} (\<lambda>_. x4) (\<lambda>y. if Some y = \<eta> r then {#Max_mset (x4 + {#x3#})#} else {#}) + fi {p} (\<lambda>_. m) (\<lambda>y. edge p (Fs p) y m)) n + {#}) (outf_fi (fi {p} (\<lambda>_. m) (\<lambda>y. edge p (Fs p) y m)))"

    have ir'_ir2: "?ir' = ?ir2"
      apply (rule fi_cong, auto)
      using assms prems by auto

    have "(?ir + ?ip) + i'a \<noteq> bot" using assms prems by (simp add: algebra_simps)
    then have nbot: "?ir + ?ip \<noteq> bot" using plus_fi_ops_exist(1) by blast
    have "?ir2 + ?ip' = ?ir + ?ip" using assms adjust_interface'[of ?ir ?ip r p 0, OF nbot] ir'_ir2 by simp
    then have "?ir2 + (?ip' + i'a) \<noteq> bot" using prems assms by (simp add: algebra_simps)
    then have "?ip' + (?ir2 + i'a) \<noteq> bot" by (simp add: algebra_simps)
    then have "?ir2 + i'a \<noteq> bot" using plus_fi_ops_exist(2) by blast
    with prems show False by simp
  qed
     apply (cases "Fs r", simp)
    apply (cases "Fs r", simp)
   apply simp

  subgoal for m i'a x3 x4

    apply (rule cons_rule[OF _ _ update_correct[where V="{}"]])
    using assms apply (simp add: algebra_simps, frame_inference)

                 apply (rule ent_ex_preI)
                 apply (rule_tac x=Fs' in ent_ex_postI)
                 apply (rule ff.GrI_cong _ eq_on_refl)
                    apply simp
               apply simp
              apply blast
             apply simp
            apply simp
    apply simp
    subgoal premises prems proof -
      let ?ip = "fi {p} (\<lambda>_. m) (\<lambda>y. edge p (Fs p) y m)"
      let ?ir = "fi {r} (\<lambda>_. x4) (\<lambda>y. if Some y = \<eta> r then {#Max_mset (x4 + {#x3#})#} else {#})"
      have nbot: "?ip + ?ir \<noteq> bot" using prems search23 assms by (simp add: algebra_simps)

      have "outf_fi ?ir p = {#Max_mset (x4 + {#x3#})#}" using assms by simp
      then have "inf_fi ?ip p = inf_fi (?ip + ?ir) p + {#Max_mset (x4 + {#x3#})#}"
        using nbot unfold_inf_fi[of ?ip ?ir p] by simp
      then show ?thesis
        by (smt ab_semigroup_add_class.add.commute add.right_neutral add_diff_cancel_right'
            mset_contains_eq set_mset_add_mset_insert union_mset_add_mset_right)
    qed
         apply simp
    using assms apply simp
    subgoal premises prems proof -
      let ?ip = "fi {p} (\<lambda>_. m) (\<lambda>y. edge p (Fs p) y m)"
      let ?ip2 = "fi {p} (\<lambda>_. m - {#Max (insert x3 (set_mset x4))#}) (\<lambda>n. if n = p then {#} else edge p (Fs p) n m)"
      let ?ip3 = "fi {p} (\<lambda>n. inf_fi (fi {p} (\<lambda>_. m) (\<lambda>y. edge p (Fs p) y m)) n - outf_fi (fi {r} (\<lambda>_. x4) (\<lambda>y. if Some y = \<eta> r then {#Max_mset (x4 + {#x3#})#} else {#})) n + {#}) (outf_fi (fi {p} (\<lambda>_. m) (\<lambda>y. edge p (Fs p) y m)))"
      have A: "?ip2 = ?ip3" by (rule fi_cong, auto simp: prems assms)

      let ?ir = "fi {r} (\<lambda>_. x4) (\<lambda>y. if Some y = \<eta> r then {#Max_mset (x4 + {#x3#})#} else {#})"
      let ?ir2 = "fi {r} (\<lambda>_. x4) (\<lambda>y. {#})"
      let ?ir3 = "fi {r} (inf_fi (fi {r} (\<lambda>_. x4) (\<lambda>y. if Some y = \<eta> r then {#Max_mset (x4 + {#x3#})#} else {#}))) (\<lambda>n. if n = p then {#} else outf_fi (fi {r} (\<lambda>_. x4) (\<lambda>y. if Some y = \<eta> r then {#Max_mset (x4 + {#x3#})#} else {#})) n)"
      have B: "?ir2 = ?ir3" by (rule fi_cong, auto simp: prems assms)

      have *: "(?ip + ?ir) + i'a \<noteq> bot" using prems assms by (simp add: algebra_simps)

      have "?ip + ?ir = ?ip2 + ?ir2"
        using adjust_interface_mset'[of ?ir ?ip r p "{#}"] A B prems assms plus_fi_ops_exist(1)[OF *]
        by (simp add: algebra_simps)
      with assms prems show ?thesis
        by (simp add: algebra_simps)
    qed
    subgoal premises prems proof -
      let ?ip = "fi {p} (\<lambda>_. m) (\<lambda>y. edge p (Fs p) y m) "
      let ?ir = "fi {r} (\<lambda>_. x4) (\<lambda>y. if y = p then {#Max_mset (x4 + {#x3#})#} else {#})"
      have *: "(?ip + ?ir) + i'a \<noteq> bot" using prems assms by (simp add: algebra_simps)
      show ?thesis using plus_fi_ops_exist(1)[OF *] assms prems by simp
    qed
           apply (smt Max_ge finite_insert finite_set_mset insertI1)
    subgoal premises prems proof -
      let ?ip = "fi {p} (\<lambda>_. m) (\<lambda>y. edge p (Fs p) y m)"
      let ?ir = "fi {r} (\<lambda>_. x4) (\<lambda>y. if Some y = \<eta> r then {#Max_mset (x4 + {#x3#})#} else {#})"
      have "?ip + ?ir \<noteq> bot" using prems search23 assms by (simp add: algebra_simps)
      with assms prems show ?thesis by (auto split: option.splits)
    qed
  done
  done


end
