\<^marker>\<open>creator Bernhard Pöttinger\<close>

theory FF
  imports Flow_Base Flow_Extensions "Separation_Logic_Imperative_HOL.Sep_Main"
begin

paragraph \<open>Summary\<close>
text \<open>This theory introduces a locale that provides general infrastructure to
embed the Flow Framework into a Separation Logic. See section 3 in @{cite krishna20}.
\<close>

section \<open>The Framework\<close>

locale FF =
  fixes \<gamma> :: "'a \<Rightarrow> 'n ref \<Rightarrow> 'n :: heap \<Rightarrow> 'm :: cancel_comm_monoid_add \<Rightarrow> bool"
    and \<phi> :: "('n ref, 'm) fi \<Rightarrow> bool"
    and edges :: "'n ref \<Rightarrow> 'n \<Rightarrow> 'n ref \<Rightarrow> 'm \<Rightarrow> 'm"
  assumes edges_not_refl: "\<And>x fs g m. \<gamma> g x fs m \<Longrightarrow>  edges x fs x = (\<lambda>_. 0)"
begin

lemma int_fg_fg:
  assumes "\<gamma> g x fs m"
  shows "int_fg (fg {x} (\<lambda>_. edges x fs) (\<lambda>_. m)) = fi {x} (\<lambda>_. m) (\<lambda>y. edges x fs y m)"
proof -
  let ?e = "\<lambda>_ y. edges x fs y"
  let ?f = "\<lambda>_. m"
  let ?h = "fg {x} ?e ?f"

  have *: "?h \<noteq> bot"
    using def_fg_singleton' edges_not_refl assms by metis
  have **: "flow_eq ?h ?f"
    apply (rule flow_eqI) using edges_not_refl assms by auto
  show ?thesis
    unfolding int_fg_def inf_fg_def outf_fg_def
    using * ** apply auto
    apply (rule fi_cong, auto)
    by (metis (mono_tags, lifting) dom_fg_fg flow_eq_unique singletonI someI_ex)
qed

subsection \<open>Flow Graph Abstractions\<close>

text \<open>Our framework abstracts heap objects as nodes. The underlying heap object induces
a singleton flow graph. Each node has to satisfy the node-local invariant $\gamma$.\<close>

definition N :: "'a \<Rightarrow> 'n ref \<Rightarrow> 'n \<Rightarrow> 'm \<Rightarrow> ('n ref, 'm) fg \<Rightarrow> assn" where
"N g x fs m h \<equiv>
  x \<mapsto>\<^sub>r fs * \<up>(\<gamma> g x fs m \<and> h \<noteq> bot \<and> h = fg {x} (\<lambda>_. edges x fs) (\<lambda>_. m))"

text \<open>Graphs compose multiple nodes. The nodes' singleton flow graphs have to
make up a valid flow graph again.\<close>

definition
  Gr :: "('n ref \<Rightarrow> 'a) \<Rightarrow> ('n ref \<Rightarrow> 'n) \<Rightarrow> 'n ref set \<Rightarrow> ('n ref, 'm) fg \<Rightarrow> assn"
where
  "Gr \<eta> Fs X h \<equiv>
    \<exists>\<^sub>AH M. (\<Prod>x \<in> X. N (\<eta> x) x (Fs x) (M x) (H x)) *
           \<up>(finite X \<and> h \<noteq> bot \<and> h = (\<Sum>x \<in> X. H x))"

text \<open>Some useful entailments for our graph/node abstractions:\<close>

lemma decomp_Gr:
  assumes "xs1 \<inter> xs2 = {}" "dom_fg h = xs1 \<union> xs2"
  shows "Gr \<eta> Fs (xs1 \<union> xs2) h \<Longrightarrow>\<^sub>A
    \<exists>\<^sub>Ah1 h2. Gr \<eta> Fs xs1 h1 * Gr \<eta> Fs xs2 h2 * \<up>(h \<noteq> bot \<and> h = h1 + h2)"
  apply (unfold Gr_def)
  apply (simp)
  apply (intro ent_ex_preI)
  subgoal for H M
    using assms split_sum[of H xs1 xs2] finiteUn[OF dom_fg_finite assms(2)] apply simp
    apply clarsimp
    apply (rule ent_ex_postI[of _ _ "sum H xs1"])
    apply (rule ent_ex_postI[of _ _ "sum H xs2"])
    apply (rule ent_ex_postI[of _ _ H])
    apply (rule ent_ex_postI[of _ _ M])
    apply (rule ent_ex_postI[of _ _ H])
    apply (rule ent_ex_postI[of _ _ M])
    apply (auto simp: prod.union_disjoint assms)
    done
  done

lemma ent_prod_cong: 
  assumes "finite X" "\<And>x. x \<in> X \<Longrightarrow> P x \<Longrightarrow>\<^sub>A P' x"
  shows "(\<Prod>x \<in> X. P x) \<Longrightarrow>\<^sub>A (\<Prod>x \<in> X. P' x)"
  using assms
  apply (induction X rule: finite_induct)
   apply simp
  apply sep_auto
  apply (rule ent_star_mono)
  using assms apply auto
  done

lemma comp_Gr:
  assumes "xs1 \<inter> xs2 = {}" "finite xs1" "finite xs2" "h = h1 + h2" "h \<noteq> bot"
  shows "Gr \<eta>1 Fs1 xs1 h1 * Gr \<eta>2 Fs2 xs2 h2 \<Longrightarrow>\<^sub>A
    Gr (\<lambda>x. if x \<in> xs1 then \<eta>1 x else \<eta>2 x)
       (\<lambda>x. if x \<in> xs1 then Fs1 x else Fs2 x) (xs1 \<union> xs2) h"
  apply (unfold Gr_def)
  apply clarsimp
  apply (intro ent_ex_preI)
  subgoal for H2 M2 H1 M1
    apply clarsimp
    apply (rule ent_trans[of _ "\<Prod>x\<in>xs1 \<union> xs2.
      N ((\<lambda>x. if x \<in> xs1 then \<eta>1 x else \<eta>2 x) x)
        x
        ((\<lambda>x. if x \<in> xs1 then Fs1 x else Fs2 x) x)
        ((\<lambda>x. if x \<in> xs1 then M1 x else M2 x) x) ((\<lambda>x. if x \<in> xs1 then H1 x else H2 x) x)"])
    using assms apply (simp add: prod.union_disjoint)
     apply (rule ent_star_mono[OF ent_refl ent_prod_cong])
    using assms apply simp
    using assms apply sep_auto
    apply (intro ent_ex_postI[of _ _ "\<lambda>x. if x \<in> xs1 then H1 x else H2 x"])
    apply (intro ent_ex_postI[of _ _ "\<lambda>x. if x \<in> xs1 then M1 x else M2 x"])
    apply clarsimp
    using assms apply (simp)
    apply (subst (1) sum.cong[where h="\<lambda>x. restrict xs1 (H2 x) H1 x"], simp, simp)
    apply (subst (2) sum.cong[where h="\<lambda>x. restrict xs1 (H2 x) H1 x"], simp, simp)
    using assms apply blast
    by (rule sum.union_disjoint[symmetric], simp_all add: assms)
  done

lemma sing_N_Gr: "N (\<eta> x) x fs m h \<Longrightarrow>\<^sub>A Gr \<eta> (\<lambda>_. fs) {x} h"
  apply (unfold N_def Gr_def)
  by sep_auto

lemma sing_Gr_N:
  "Gr \<eta> Fs {x} h \<Longrightarrow>\<^sub>A \<exists>\<^sub>Am. N (\<eta> x) x (Fs x) m h *
    \<up>(\<gamma> (\<eta> x) x (Fs x) m \<and> h \<noteq> bot \<and> h = fg {x} (\<lambda>_. edges x (Fs x)) (\<lambda>_. m))"
  apply (unfold N_def Gr_def)
  by sep_auto

lemma peek_N:
  shows "N g x fs m h \<Longrightarrow>\<^sub>A N g x fs m h * \<up>(h = fg {x} (\<lambda>_. edges x fs) (\<lambda>_. m))"
  unfolding N_def by sep_auto

lemma unfold_N:
  assumes "x \<in> X" "X = dom_fg h"
  shows "Gr \<eta> Fs X h \<Longrightarrow>\<^sub>A
    \<exists>\<^sub>Am h1 h'. Gr \<eta> Fs (X - {x}) h' * N (\<eta> x) x (Fs x) m h1 *
      \<up>(h = h1 + h' \<and> \<gamma> (\<eta> x) x (Fs x) m \<and> h1 = fg {x} (\<lambda>_. edges x (Fs x)) (\<lambda>_. m))"
proof -
  have *: "X = insert x X" using assms by auto
  show ?thesis
    apply (subst *)
    apply (rule ent_trans[OF decomp_Gr[of "{x}" "X - {x}" h], simplified])
    using assms * apply simp
    apply (intro ent_ex_preI, clarsimp)
    apply (rule ent_trans[OF ent_frame_fwd[OF sing_Gr_N[where x=x]]])
      apply frame_inference+
    apply clarsimp
    apply (intro ent_ex_preI, clarsimp)
    apply (rule_tac x=m in ent_ex_postI)
    apply (rule ent_ex_postI)
    apply (rule_tac x=h2 in ent_ex_postI)
    apply (rule ent_trans[OF ent_frame_fwd[OF peek_N]])
    by frame_inference+
qed

lemma Gr_cong:
  assumes "X = X'" "\<eta> = \<eta>' on X" "Fs = Fs' on X" "h = h'" "h \<noteq> bot"
  shows "Gr \<eta> Fs X h \<Longrightarrow>\<^sub>A Gr \<eta>' Fs' X' h'"
  unfolding Gr_def using assms by sep_auto

lemma fold_N:
  assumes "x \<notin> X" "X = dom_fg h" "h + h1 \<noteq> bot" "\<gamma> g x fs m"
  shows "Gr \<eta> Fs X h * N g x fs m h1 \<Longrightarrow>\<^sub>A
    Gr (\<lambda>y. if y = x then g else \<eta> y) (\<lambda>y. if y = x then fs else Fs y) ({x} \<union> X) (h1 + h)"
  apply (rule ent_trans[OF ent_frame_fwd[OF sing_N_Gr]])
  using assms apply simp
    apply frame_inference+
  apply (rule ent_trans[OF comp_Gr])
  using assms apply simp_all
  by (rule Gr_cong, auto simp: algebra_simps)

lemma dom_fi_plus_fg_iterated:
  fixes H :: "'n ref \<Rightarrow> ('n ref,'b :: cancel_comm_monoid_add) fg"
  assumes "finite X" "sum H X \<noteq> bot"
  shows "dom_fg (sum H X) = (\<Union>x \<in> X. dom_fg (H x))"
  using assms
  apply (induction X rule: finite_induct)
   apply simp_all
  using plus_fg_ops_exist by blast

lemma Gr_dom:
  "Gr \<eta> Fs X H \<Longrightarrow>\<^sub>A Gr \<eta> Fs X H * \<up>(finite X \<and> dom_fg H = X)"
proof -
  have X: "finite X \<Longrightarrow> (\<Prod>x\<in>X. N (\<eta> x) x (Fs x) (M x) (Ha x)) \<Longrightarrow>\<^sub>A
    (\<Prod>x\<in>X. N (\<eta> x) x (Fs x) (M x) (Ha x)) * \<up>(\<forall>x \<in> X. dom_fg (Ha x) = {x})" for M Ha
    apply (induction X rule: finite_induct)
    by (sep_auto simp: mod_star_conv N_def)+

  show ?thesis
    unfolding Gr_def
    apply (intro ent_ex_preI, clarsimp)
    apply (rule ent_trans[OF X])
     apply simp
    subgoal for Ha M
      using dom_fi_plus_fg_iterated[of X Ha] by sep_auto
    done
qed

lemma Gr_emp: "emp \<Longrightarrow>\<^sub>A \<exists>\<^sub>AFs. Gr \<eta> Fs {} 0"
  apply (unfold Gr_def)
  using def_fg_zero_fg by sep_auto

lemma repl:
  assumes "xs1' \<inter> xs2 = {}" "finite xs1'" "finite xs2" "int_fg h1 = int_fg h1'"
    "h = h1 + h2" "h \<noteq> bot"
  shows "Gr \<eta> Fs1 xs1' h1' * Gr \<eta> Fs2 xs2 h2 \<Longrightarrow>\<^sub>A
    Gr \<eta> (\<lambda>x. if x \<in> xs1' then Fs1 x else Fs2 x) (xs1' \<union> xs2) (h1' + h2) *
    \<up>(int_fg h = int_fg (h1' + h2))"
proof -
  have "int_fg (h1 + h2) = int_fg h1 + int_fg h2" by (rule int_fg_fi_hom)
  also have "... = int_fg h1' + int_fg h2" using assms by simp
  also have "... = int_fg (h1' + h2)" by (rule int_fg_fi_hom[symmetric])
  finally have H: "int_fg h = int_fg (h1' + h2)" using assms by simp
  then have nbot': "h1' + h2 \<noteq> bot" using assms by auto

  show ?thesis
    apply sep_auto
     apply (simp add: H)
    apply (rule ent_trans[OF comp_Gr], simp_all add: assms)
    using nbot' apply simp
    by sep_auto
qed

lemma open_N:
  shows "N g x fs m h \<Longrightarrow>\<^sub>A
    x \<mapsto>\<^sub>r fs * \<up>(h \<noteq> bot \<and> \<gamma> g x fs m \<and> h = fg {x} (\<lambda>_. edges x fs) (\<lambda>_. m))"
  unfolding N_def by sep_auto

lemma close_N:
  assumes "\<gamma> g x fs m"
  shows "x \<mapsto>\<^sub>r fs \<Longrightarrow>\<^sub>A N g x fs m (fg {x} (\<lambda>_. edges x fs) (\<lambda>_. m))"
  using assms unfolding N_def apply sep_auto
  using assms def_fg_singleton'[of "\<lambda>_ y. edges x fs y" x "\<lambda>_. m"] edges_not_refl[of g x fs m]
  by metis

subsection \<open>Flow Interface\<close>

text \<open>Building on top of the flow graph abstraction we introduce another level of abstraction:
flow interfaces.\<close>

definition NI :: "'a \<Rightarrow> 'n ref \<Rightarrow> 'n \<Rightarrow> 'm \<Rightarrow> ('n ref, 'm) fi \<Rightarrow> assn" where
"NI g x fs m i \<equiv> \<exists>\<^sub>Ah. N g x fs m h * \<up>(i \<noteq> bot \<and> i = int_fg h)"

definition
  GrI :: "('n ref \<Rightarrow> 'a) \<Rightarrow> ('n ref \<Rightarrow> 'n) \<Rightarrow> 'n ref set \<Rightarrow> ('n ref, 'm) fi \<Rightarrow> assn"
where
  "GrI \<eta> Fs X i \<equiv> \<exists>\<^sub>Ah. Gr \<eta> Fs X h * \<up>(i = int_fg h)"

text \<open>Lifting the generally useful entailments to flow interfaces:\<close>

lemma decomp_GrI:
  assumes "xs1 \<inter> xs2 = {}" "dom_fi i = xs1 \<union> xs2"
  shows "GrI \<eta> Fs (xs1 \<union> xs2) i \<Longrightarrow>\<^sub>A
    \<exists>\<^sub>Ai1 i2. GrI \<eta> Fs xs1 i1 * GrI \<eta> Fs xs2 i2 * \<up>(i \<noteq> bot \<and> i = i1 + i2)"
  apply (unfold GrI_def)
  apply (rule ent_ex_preI)
  apply clarsimp
  apply (rule ent_trans[OF decomp_Gr])
  using assms apply simp
  using assms apply simp
  apply (intro ent_ex_preI)
  subgoal for h h1 h2
  apply (rule ent_ex_postI[of _ _ "int_fg h1"])
  apply (rule ent_ex_postI[of _ _ "int_fg h2"])
  apply (rule ent_ex_postI[of _ _ h2])
    apply (rule ent_ex_postI[of _ _ h1])
    using int_fg_fi_hom by sep_auto
  done

lemma comp_GrI:
  assumes "xs1 \<inter> xs2 = {}" "finite xs1" "finite xs2" "i = i1 + i2" "i \<noteq> bot"
  shows "GrI \<eta>1 Fs1 xs1 i1 * GrI \<eta>2 Fs2 xs2 i2 \<Longrightarrow>\<^sub>A
    GrI (\<lambda>x. if x \<in> xs1 then \<eta>1 x else \<eta>2 x) (\<lambda>x. if x \<in> xs1 then Fs1 x else Fs2 x) (xs1 \<union> xs2) i"
  apply (unfold GrI_def)
  apply clarsimp
  apply (intro ent_ex_preI)
  apply clarsimp
  subgoal for h2 h1
    using assms int_fg_fi_hom[symmetric,of h1 h2]
    apply auto
    apply (rule ent_ex_postI[of _ _ "h1+h2"])
    apply sep_auto
    apply (rule comp_Gr[of xs1 xs2 "h1 + h2" h1 h2 \<eta>1 Fs1 \<eta>2 Fs2])
    apply auto
    done
  done

lemma sing_GrI_NI: "GrI \<eta> Fs {x} i \<Longrightarrow>\<^sub>A \<exists>\<^sub>Am. NI (\<eta> x) x (Fs x) m i * \<up>(\<gamma> (\<eta> x) x (Fs x) m)"
  unfolding GrI_def NI_def Gr_def N_def
  by sep_auto

lemma sing_NI_GrI:
  shows "NI (\<eta> x) x fs m i \<Longrightarrow>\<^sub>A GrI \<eta> (\<lambda>_. fs) {x} i"
  unfolding NI_def GrI_def using sing_N_Gr by sep_auto

lemma GrI_emp: "emp \<Longrightarrow>\<^sub>A \<exists>\<^sub>AFs. GrI \<eta> Fs {} 0"
  unfolding GrI_def
  by (rule ent_trans[OF Gr_emp], sep_auto)

lemma repli:
  assumes "xs1' \<inter> xs2 = {}" "finite xs1'" "finite xs2"
  shows "GrI \<eta>1 Fs1 xs1' i1 * GrI \<eta>2 Fs2 xs2 i2 * \<up>(i \<noteq> bot \<and> i = i1 + i2 \<and> i1 = i2) \<Longrightarrow>\<^sub>A
    GrI (\<lambda>x. if x \<in> xs1' then \<eta>1 x else \<eta>2 x) (\<lambda>x. if x \<in> xs1' then Fs1 x else Fs2 x) (xs1' \<union> xs2) i"
  using assms
  apply (unfold GrI_def)
  apply clarsimp
  apply (intro ent_ex_preI)
  apply clarsimp
  subgoal for h2 h1
    using assms int_fg_fi_hom[symmetric,of h1 h2]
    apply simp
    apply (rule ent_ex_postI[of _ _ "h1+h2"])
    apply sep_auto
    apply (rule comp_Gr)
    apply auto
    done
  done

lemma unfold_GrI:
  assumes "x \<in> xs" "xs = dom_fi i"
  shows "GrI \<eta> Fs xs i \<Longrightarrow>\<^sub>A
    (\<exists>\<^sub>Aix ixs m. NI (\<eta> x) x (Fs x) m ix * GrI \<eta> Fs (xs - {x}) ixs *
                 \<up>(\<gamma> (\<eta> x) x (Fs x) m \<and> i \<noteq> bot \<and> ix + ixs = i))"
proof -
  have A: "xs = {x} \<union> (xs - {x})"
    using assms by blast
  show ?thesis
    apply (subst A)
    apply (rule ent_trans[OF decomp_GrI], blast)
    using assms A apply simp
  apply (intro ent_ex_preI, clarsimp)
    apply (rule ent_trans[OF ent_frame_fwd[OF sing_GrI_NI[where x=x]]])
      apply frame_inference+
    by sep_auto
qed

lemma GrI_cong:
  assumes "\<eta>1 = \<eta>2 on X1" "Fs1 = Fs2 on X1" "X1 = X2" "i1 = i2"
  shows "GrI \<eta>1 Fs1 X1 i1 \<Longrightarrow>\<^sub>A GrI \<eta>2 Fs2 X2 i2"
  using assms
  unfolding GrI_def Gr_def
  by sep_auto

lemma NI_cong:
  assumes "g = g'" "fs = fs'" "m = m'" "i = i'"
  shows "NI g x fs m i \<Longrightarrow>\<^sub>A NI g' x fs' m' i'"
  using assms unfolding NI_def by sep_auto

lemma NI_dom: "NI g x fs m i \<Longrightarrow>\<^sub>A NI g x fs m i * \<up>(dom_fi i = {x})"
  unfolding NI_def N_def by sep_auto

lemma GrI_dom: "GrI \<eta> Fs X i \<Longrightarrow>\<^sub>A GrI \<eta> Fs X i * \<up>(dom_fi i = X \<and> finite X \<and> i \<noteq> bot)"
  unfolding GrI_def
  apply (clarsimp, intro ent_ex_preI, clarsimp)
  using Gr_dom apply sep_auto
  unfolding Gr_def
  by (metis (mono_tags, lifting) int_fg_bot_bot' mod_ex_dist mod_pure_star_dist)

lemma foldi:
  assumes "x \<notin> xs" "finite xs" "i \<noteq> bot" "i = ix + ixs"
  shows "NI g x fs m ix * GrI \<eta> Fs xs ixs \<Longrightarrow>\<^sub>A GrI (\<lambda>n. if n \<in> {x} then g else \<eta> n) (\<lambda>n. if n \<in> {x} then fs else Fs n) ({x} \<union> xs) i"
proof -
  show ?thesis
    apply (rule ent_trans[OF ent_frame_fwd[OF sing_NI_GrI]])
      apply frame_inference+
    apply (rule ent_trans[OF comp_GrI])
    using assms apply (simp_all add: algebra_simps)
    by (rule GrI_cong, simp_all)
qed

(*lemma N_\<eta>_cong:
  assumes "\<eta> x = \<eta>' x"
  shows "N \<eta> x h \<Longrightarrow>\<^sub>A N \<eta>' x h"
  using assms
  unfold_GrIng N_def
  by sep_auto

lemma NI_\<eta>_cong:
  assumes "\<eta> x = \<eta>' x"
  shows "NI \<eta> x i \<Longrightarrow>\<^sub>A NI \<eta>' x i"
  using assms
  unfold_GrIng NI_def N_def
  by sep_auto

lemma GrI_\<eta>_cong:
  assumes "\<eta> = \<eta>' on X"
  shows "GrI \<eta> X i \<Longrightarrow>\<^sub>A GrI \<eta>' X i"
  using assms
  unfold_GrIng GrI_def Gr_def
  apply sep_auto
  by (rule sep_prod_cong[OF N_\<eta>_cong], simp)*)

subsection \<open>SL Ghost Commands\<close>

text \<open>We additionally introduce ghost commands that enable us to trigger the above entailments
in our SL-proofs by placing the ghost commands in the program text.\<close>

definition "sing_NI_GrI x \<equiv> return ()"
definition "sing_GrI_NI x \<equiv> return ()"
definition "ghost_diff x y \<equiv> return ()"
definition "preserve_interface2 x y b \<equiv> b"
definition extends :: "('a,'b) fi \<Rightarrow> ('a,'b) fi \<Rightarrow> unit Heap" where "extends i1 i2 \<equiv> return ()"
definition "open_N x \<equiv> return ()"
definition "close_N x c \<equiv> return ()"
definition "open_NI x \<equiv> return ()"
definition "close_NI x c \<equiv> return ()"
definition "fold_GrI x \<equiv> return ()"
definition "unfold_GrI x \<equiv> return ()"
definition "peek_NI x \<equiv> return ()"


lemma sing_NI_GrI_rule:
  "<NI (\<eta> x) x fs m i> sing_NI_GrI x <\<lambda>_. GrI \<eta> (\<lambda>_. fs) {x} i>"
  unfolding sing_NI_GrI_def
  using sing_NI_GrI by sep_auto

lemma sing_GrI_NI_rule:
  "<GrI \<eta> Fs {x} i> sing_GrI_NI x <\<lambda>_. \<exists>\<^sub>Am. NI (\<eta> x) x (Fs x) m i>"
  unfolding sing_GrI_NI_def
  by (rule cons_pre_rule[OF sing_GrI_NI], sep_auto)

lemma diff_NI_rule: "<NI g1 x1 fs1 m1 i1 * NI g2 x2 fs2 m2 i2> ghost_diff x1 x2 <\<lambda>_. NI g1 x1 fs1 m1 i1 * NI g2 x2 fs2 m2 i2 * \<up>(x1 \<noteq> x2)>"
  unfolding ghost_diff_def NI_def N_def by sep_auto

lemma ent_diff_NI: "NI g1 x1 fs1 m1 i1 * NI g2 x2 fs2 m2 i2 \<Longrightarrow>\<^sub>A NI g1 x1 fs1 m1 i1 * NI g2 x2 fs2 m2 i2 * \<up>(x1 \<noteq> x2)"
  unfolding ghost_diff_def NI_def N_def by sep_auto

lemma preserve_interface_rule:
  assumes "<NI g1 x1 fs1 m1 i1 * NI g2 x2 fs2 m2 i2 * P> b <\<lambda>z. NI g1' x1 fs1' m1' i1' * NI g2' x2 fs2' m2' i2' * P' z>" "i1 + i2 = i1' + i2'"
  shows "<NI g1 x1 fs1 m1 i1 * NI g2 x2 fs2 m2 i2 * P> preserve_interface2 x1 x2 b <\<lambda>z. NI g1' x1 fs1' m1' i1' * NI g2' x2 fs2' m2' i2' * P' z * \<up>(i1 + i2 = i1' + i2')>"
  unfolding preserve_interface2_def using assms by sep_auto

lemma extends_rule:
  assumes "dom_fi i1 \<subseteq> dom_fi i2" "inf_fi i1 = inf_fi i2 on dom_fi i1" "outf_fi i1 = outf_fi i2 on -dom_fi i2"
  shows "<emp> extends i1 i2 <\<lambda>_. \<up>(i1 \<lesssim> i2)>"
  using assms unfolding extends_def contextual_extension_def by sep_auto

lemma close_N_rule:
  assumes "\<gamma> g x fs m"
  shows "<x \<mapsto>\<^sub>r fs> close_N x m <\<lambda>_. N g x fs m (fg {x} (\<lambda>_. edges x fs) (\<lambda>_. m))>"
  unfolding close_N_def N_def
  using assms
  apply sep_auto
  subgoal premises prems for a b
  proof -
    have "fg {x} (\<lambda>_. edges x fs) (\<lambda>_. m) \<noteq> bot"
      apply (rule fgI[where i="\<lambda>_. m"])
      using assms edges_not_refl by auto
    then show ?thesis
      using prems by simp
  qed
  done

lemma open_NI_rule:
  "<NI g x fs m i> open_NI x <\<lambda>_. x \<mapsto>\<^sub>r fs * \<up>(i \<noteq> bot \<and> \<gamma> g x fs m \<and> i = fi {x} (\<lambda>_. m) (\<lambda>y. edges x fs y m))>"
  unfolding open_N_def open_NI_def NI_def N_def
  apply sep_auto
  using int_fg_fg by simp

lemma peek_NI:
  "NI g x fs m i \<Longrightarrow>\<^sub>A NI g x fs m i * \<up>(i \<noteq> bot \<and> \<gamma> g x fs m \<and> i = fi {x} (\<lambda>_. m) (\<lambda>y. edges x fs y m))"
  unfolding open_N_def open_NI_def NI_def N_def
  apply sep_auto
  using int_fg_fg by simp

lemma peek_NI_rule:
  "<NI g x fs m i> peek_NI x <\<lambda>_. NI g x fs m i * \<up>(i \<noteq> bot \<and> \<gamma> g x fs m \<and> i = fi {x} (\<lambda>_. m) (\<lambda>y. edges x fs y m))>"
  using peek_NI unfolding peek_NI_def by sep_auto

lemma close_NI_rule:
  assumes "\<gamma> g x fs m"
  shows "<x \<mapsto>\<^sub>r fs> close_NI x m <\<lambda>_. \<exists>\<^sub>Ai. NI g x fs m i * \<up>(i \<noteq> bot \<and> i = fi {x} (\<lambda>_. m) (\<lambda>y. edges x fs y m))>"
  unfolding close_NI_def close_N_def NI_def N_def
  using assms
  apply (sep_auto)
  using assms def_fg_singleton'[of "\<lambda>_ y. edges x fs y" x "\<lambda>_. m"] edges_not_refl[of g x fs m] apply metis
  using int_fg_fg apply simp
  by (subst int_fg_fg, simp_all)

lemma fold_GrI_rule:
  assumes "i1 + i2 \<noteq> bot" "x \<notin> X" "finite X"
  shows "<NI g x fs m i1 * GrI \<eta> Fs X i2>
    fold_GrI x
    <\<lambda>_. GrI (\<lambda>y. if y \<in> {x} then g else \<eta> y)
             (\<lambda>y. if y \<in> {x} then fs else Fs y) ({x} \<union> X) (i1 + i2)>"
  unfolding fold_GrI_def
  apply sep_auto
  apply (rule ent_frame_fwd[OF sing_NI_GrI], frame_inference)
  apply (rule comp_GrI[of "{x}" X "i1 + i2" i1 i2 "\<lambda>_. g" "\<lambda>_. fs" \<eta> Fs, simplified])
  using assms by auto

lemma unfold_GrI_rule:
  assumes "x \<in> X" "X = dom_fi i"
  shows "<GrI \<eta> Fs X i> unfold_GrI x <\<lambda>_. \<exists>\<^sub>Ai' i1 m. NI (\<eta> x) x (Fs x) m i1 * \<up>(i1 \<noteq> bot \<and> i' \<noteq> bot \<and> i1 = fi {x} (\<lambda>_. m) (\<lambda>y. edges x (Fs x) y m) \<and> \<gamma> (\<eta> x) x (Fs x) m \<and> i = i1 + i') * GrI \<eta> Fs (X - {x}) i'>"
  apply (rule cons_pre_rule[OF unfold_GrI[where x=x]])
  using assms apply simp
  using assms apply simp
  apply sep_auto
  apply (rule cons_pre_rule[OF ent_frame_fwd[OF peek_NI]])
  apply frame_inference+
  unfolding unfold_GrI_def
  by sep_auto

end

end

