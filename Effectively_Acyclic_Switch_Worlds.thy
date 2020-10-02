\<^marker>\<open>creator Bernhard Pöttinger\<close>

chapter \<open>"Switching Worlds"\<close>
theory Effectively_Acyclic_Switch_Worlds
imports Effectively_Acyclic
begin

section \<open>Summary\<close>
text \<open>@{term chains'_switch_world} transfers a convoluted path from a flow graph
@{term "hh1 + hh2"} to a flow graph @{term "hh1' + hh2'"} which are connected by subflow-
preserving extensions @{term "hh1 \<lesssim>\<^sub>S hh1'"} and @{term "hh2 \<lesssim>\<^sub>S hh2'"} (the extensions are
already unfolded and the required parts are explicitly stated as assumptions).\<close>

lemma chains'_switch_world:
  assumes "alternating' (segment_fg hh1) (segment_fg hh2) xss ys" "\<forall>xs \<in> set xss. xs \<noteq> []"
    "dom_fg hh1 = dom_fg hh1'" "dom_fg hh2 = dom_fg hh2'"
    "dom_fg (hh1 :: ('x,'a :: pos_cancel_comm_monoid_add) fg) \<inter> dom_fg hh2 = {}"
    "\<forall>n \<in> dom_fg hh1. \<forall>n' \<in> -dom_fg hh1. \<forall>m \<le> inf_fg hh1 n. cap_fg hh1 n n' m = cap_fg hh1' n n' m"
    "\<forall>n \<in> dom_fg hh2. \<forall>n' \<in> -dom_fg hh2. \<forall>m \<le> inf_fg hh2 n. cap_fg hh2 n n' m = cap_fg hh2' n n' m"
    "hh1 + hh2 \<noteq> bot" "End_closed E" "\<forall>x y. edge_fg hh1 x y \<in> E" "\<forall>x y. edge_fg hh2 x y \<in> E"
    "m \<le> inf_fg hh1 (hd (hd xss))" "id \<in> E" "\<forall>x y. edge_fg (hh1 + hh2) x y \<in> E" "(\<lambda>_. 0) \<in> E"
  shows "chains' (alt_cap_fg hh1' hh2') xss (hd ys) m = chains' (alt_cap_fg hh1 hh2) xss (hd ys) m"
  using assms
proof (induction xss arbitrary: m
       rule: alternating'_induct'_symmetric'[where a=hh1 and aa=hh1' and bb=hh2' and b=hh2])
  case (empty)
  then show ?case by simp
next
  case (base hh1 hh2 hh1' hh2' xs)
  then have "hd xs \<in> dom_fg hh1" "hd ys \<in> -dom_fg hh1" "m \<le> inf_fg hh1 (hd xs)"
      apply (simp add: in_mono)
     apply (meson ComplI base.hyps(2) base.prems(4) disjoint_iff_not_equal hd_in_set in_mono)
    using base.prems(11) by auto
  then have "cap_fg hh1 (hd xs) (hd ys) m = cap_fg hh1' (hd xs) (hd ys) m"
    using base by metis
  then show ?case
    using base by simp
next
  case (step hh1 hh2 hh1' hh2' xs ys' zss)
  then have "hd xs \<in> dom_fg hh1" "hd ys' \<in> -dom_fg hh1" "m \<le> inf_fg hh1 (hd xs)"
      apply (metis (mono_tags, hide_lams) leI length_greater_0_conv less_one set_hd_in zero_less_iff_neq_zero)
     apply (meson ComplI disjoint_iff_not_equal list.set_sel(1) step.hyps(3) step.prems(4) subset_iff)
    using step.prems(11) by auto
  then have "cap_fg hh1 (hd xs) (hd ys') m = cap_fg hh1' (hd xs) (hd ys') m"
    using step by meson
  then have *: "cap' (card (dom_fg hh1')) (dom_fg hh1') (edge_fg hh1') (hd xs) (hd ys') m =
                cap' (card (dom_fg hh1')) (dom_fg hh1') (edge_fg hh1) (hd xs) (hd ys') m"
    using step by simp

  have bla: "alternating' (segment_fg hh2) (segment_fg hh1) (ys' # zss) ys"
    using step by simp

  then have bla2: "alternating' (segment_fg hh2') (segment_fg hh1') (ys' # zss) ys"
    using step by simp

  have chains_eq: "chains' (alt_cap_fg hh1 hh2) (ys' # zss) =
       chains' (alt_cap_fg hh2 hh1) (ys' # zss)"
    apply (intro ext)
    apply (rule alternating_chains'_cong[OF bla])
    apply auto
    by (metis Int_assoc Int_empty_right inf_sup_absorb le_iff_sup set_empty step.prems(4))+

  have chains_eq2: "chains' (alt_cap_fg hh1' hh2') (ys' # zss) =
       chains' (alt_cap_fg hh2' hh1') (ys' # zss)"
    apply (intro ext)
    apply (rule alternating_chains'_cong[OF bla2])
    apply auto
    by (metis inf_sup_absorb inf_sup_distrib2 le_iff_sup set_empty step.prems(2)
        step.prems(3) step.prems(4) sup_bot.right_neutral)+

  have "cap' (card (dom_fg hh1')) (dom_fg hh1') (edge_fg hh1) (hd xs) (hd ys') m \<le>
        cap' (card (dom_fg hh1')) (dom_fg hh1') (edge_fg hh1) (hd xs) (hd ys')
          (inf_fg hh1 (hd (hd (xs # ys' # zss))))"
    apply (rule pos_endo_mono'_closed[OF \<open>m \<le> inf_fg hh1 (hd (hd (xs # ys' # zss)))\<close>, where E=E])
     apply (rule endo_cap')
    using step dom_fg_finite[of hh1'] by blast+
  also have "... \<le> inf_fg hh2 (hd ys')"
    apply simp
    apply (subst \<open>dom_fg hh1 = dom_fg hh1'\<close>[symmetric])+
    apply (rule cap'_fg_inf_fg_fg_le_inf_fg[simplified, of "hh1 + hh2" hh1 hh2 xs E "hd ys'"])
    using step apply blast
    using step apply blast
    using step apply blast
    using step apply blast
    using step apply blast
    using step apply blast
    using step apply blast
    using step apply blast
    using step apply blast
    using step apply blast
    using step apply blast 
    using step(3) by auto (* why doesn't blast prove this? *)
  finally have blabla:
    "cap' (card (dom_fg hh1')) (dom_fg hh1') (edge_fg hh1) (hd xs) (hd ys') m \<le> inf_fg hh2 (hd ys')" .

  show ?case
    using chains_eq2 subst chains_eq step.IH[simplified] step *
    apply simp
    apply (rule step.IH[simplified])
    apply blast
    apply blast
    apply blast
    using step(6,7,8) Int_commute apply auto[1]
    apply blast
    apply blast
          apply (simp only: \<open>hh1 + hh2 \<noteq> bot\<close> algebra_simps)
    apply blast
    apply blast
    apply blast
    using blabla apply blast
     apply blast
    by (simp add: algebra_simps)
qed

text \<open>Analogous the previous lemma for a slightly different setup:
- alternating' vs. alternating
- chains' vs. chain

It was easier to copy and adjust the proof instead of building adapters for the above differences.\<close>

lemma chains'_switch_world_chain:
  assumes "alternating (\<lambda>x. x \<in> dom_fg hh1) (\<lambda>x. x \<in> dom_fg hh2) xs" "xs \<noteq> []"
    "dom_fg hh1 = dom_fg hh1'" "dom_fg hh2 = dom_fg hh2'"
    "dom_fg (hh1 :: ('x,'a :: pos_cancel_comm_monoid_add) fg) \<inter> dom_fg hh2 = {}"
    "\<forall>n \<in> dom_fg hh1. \<forall>n' \<in> -dom_fg hh1. \<forall>m \<le> inf_fg hh1 n. cap_fg hh1 n n' m = cap_fg hh1' n n' m"
    "\<forall>n \<in> dom_fg hh2. \<forall>n' \<in> -dom_fg hh2. \<forall>m \<le> inf_fg hh2 n. cap_fg hh2 n n' m = cap_fg hh2' n n' m"
    "hh1 + hh2 \<noteq> bot" "End_closed E" "\<forall>x y. edge_fg hh1 x y \<in> E" "\<forall>x y. edge_fg hh2 x y \<in> E"
    "m \<le> inf_fg hh1 (hd xs)" "id \<in> E" "\<forall>x y. edge_fg (hh1 + hh2) x y \<in> E" "(\<lambda>_. 0) \<in> E"
    "y \<notin> dom_fg hh1" "y \<notin> dom_fg hh2"
  shows "chain (alt_cap_hd_fg hh1' hh2') xs y m = chain (alt_cap_hd_fg hh1 hh2) xs y m"
  using assms
proof (induction xs arbitrary: m rule:
       alternating_induct'_symmetric'[where a=hh1 and aa=hh1' and bb=hh2' and b=hh2])
  case (empty)
  then show ?case by simp
next
  case (base hh1 hh2 hh1' hh2' x)
  then show ?case by simp
next
  case (step hh1 hh2 hh1' hh2' x y' zs)
  then have "x \<in> dom_fg hh1" "y' \<in> -dom_fg hh1" "m \<le> inf_fg hh1 x"
    apply simp
    apply auto[1]
    using step
    apply (metis ComplI One_nat_def Suc_leI disjoint_iff_not_equal length_greater_0_conv set_hd_in)
    using step by simp_all
  then have "cap_fg hh1 x y' m = cap_fg hh1' x y' m"
    using step by simp
  then have *: "cap' (card (dom_fg hh1')) (dom_fg hh1') (edge_fg hh1') x y' m =
                cap' (card (dom_fg hh1')) (dom_fg hh1') (edge_fg hh1) x y' m"
    using step by simp

  have L: "cap (dom_fg hh1') (edge_fg hh1) x y' m \<le> inf_fg hh2 (hd (y' # zs))"
    using cap'_fg_le_inf_fg_le_inf_fg[of "hh1 + hh2" hh1 hh2 "[x]" E y' m] step by simp

  have S:
    "(\<lambda>x y. if x \<in> dom_fg hh2' then cap_fg hh2 x y else if x \<in> dom_fg hh1 then cap_fg hh1 x y else 0) =
     (\<lambda>x y. if x \<in> dom_fg hh1' then cap_fg hh1 x y else if x \<in> dom_fg hh2 then cap_fg hh2 x y else 0)"
    apply (intro ext)
    using \<open>dom_fg hh2 = dom_fg hh2'\<close> \<open>dom_fg hh1 = dom_fg hh1'\<close> \<open>dom_fg hh1 \<inter> dom_fg hh2 = {}\<close> by auto

  have "chain (alt_cap_hd_fg hh1' hh2') (x # y' # zs) y m =
        chain (alt_cap_hd_fg hh1' hh2') (y' # zs) y (cap_fg hh1' x y' m)"
    using step by simp
  also have "... = chain (alt_cap_hd_fg hh1' hh2') (y' # zs) y (cap (dom_fg hh1') (edge_fg hh1) x y' m)"
    using * by simp
  also have "... = chain (alt_cap_hd_fg hh2 hh1) (y' # zs) y (cap (dom_fg hh1') (edge_fg hh1) x y' m)"
    apply (subst alt_cap_hd_fg_sym')
    using step apply simp
    apply (subst step.IH)
    using step L apply blast
    using step L apply blast
    using step L apply blast
    using step L apply blast
    using step L apply blast
    using step L apply blast
    using step L apply (simp only: algebra_simps)
    using step L apply blast
    using step L apply blast
    using step L apply blast
    using step L apply blast
    using step L apply blast
    using step L apply blast
    using step L apply (simp only: algebra_simps)
    using step L apply blast+
    done
  finally show ?case
    using step S by simp
qed

end
