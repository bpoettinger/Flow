theory Pip_Shared
imports Flow_Base FF "HOL-Library.Multiset"
begin

datatype fields = Fields "fields ref option" "int" "int" "int multiset"

definition "fields_y fs \<equiv> case fs of Fields y _ _ _ \<Rightarrow> y"
definition "fields_q fs \<equiv> case fs of Fields _ q _ _ \<Rightarrow> q"
definition "fields_q0 fs \<equiv> case fs of Fields _ _ q0 _ \<Rightarrow> q0"
definition "fields_qs fs \<equiv> case fs of Fields _ _ _ qs \<Rightarrow> qs"

definition "fields_y' fs y \<equiv> case fs of Fields _ q q0 qs \<Rightarrow> Fields y q q0 qs"
definition "fields_q' fs q \<equiv> case fs of Fields y _ q0 qs \<Rightarrow> Fields y q q0 qs"
definition "fields_q0' fs q0 \<equiv> case fs of Fields y q _ qs \<Rightarrow> Fields y q q0 qs"
definition "fields_qs' fs qs \<equiv> case fs of Fields y q q0 _ \<Rightarrow> Fields y q q0 qs"

instantiation multiset :: (countable) countable
begin
instance
proof (standard, goal_cases)
  case 1
  let ?multiset_to_list = "\<lambda>X. (SOME xs. mset xs = X)"

  obtain list_to_nat :: "'a list \<Rightarrow> nat"
    where "inj list_to_nat"
    by blast
  moreover have "inj ?multiset_to_list"
  proof (rule injI)
    fix X Y
    assume "(SOME xs. mset xs = X) = (SOME xs. mset xs = Y)"
    moreover have "mset (SOME xs. mset xs = X) = X" "mset (SOME xs. mset xs = Y) = Y"
      using some_eq_ex[symmetric, of "\<lambda>xs. mset xs = X"] ex_mset[of X]
            some_eq_ex[symmetric, of "\<lambda>xs. mset xs = Y"] ex_mset[of Y] by simp_all
    ultimately show "X = Y"
      by presburger
  qed
  ultimately have "inj (list_to_nat o ?multiset_to_list)"
    using inj_compose by blast
  then show ?case
    by blast
qed
end
instance multiset :: (heap) heap ..
instance fields :: countable by countable_datatype
instance fields :: heap ..

fun Max' :: "int set \<Rightarrow> int" where
"Max' X = (if X = {} then 0 else Max X)"

fun Max'_mset :: "int multiset \<Rightarrow> int" where
"Max'_mset X = Max' (set_mset X)"

fun \<gamma> :: "fields ref option \<Rightarrow> fields ref \<Rightarrow> fields \<Rightarrow> int multiset \<Rightarrow> bool" where
"\<gamma> \<eta> x (Fields y q q0 qs) m = (q0 \<ge> 0 \<and> (\<forall>q'\<in>set_mset qs. q' \<ge> 0) \<and>
                finite (set_mset qs) \<and> 
                m = qs \<and> Max'_mset ({#q0#} + qs) = q \<and>
                \<eta> = y \<and> \<eta> \<noteq> Some x)"

definition \<phi> where
"\<phi> i \<equiv> i \<noteq> bot \<and> inf_fi i = (\<lambda>_. {#}) \<and> outf_fi i = (\<lambda>_. {#})"

fun edge :: "fields ref \<Rightarrow> fields \<Rightarrow> fields ref \<Rightarrow> (int multiset \<Rightarrow> int multiset)" where
"edge x (Fields y q q0 qs) z =
  (\<lambda>m. if Some z = y then {# Max_mset (m + {# q0 #}) #} else {#})"

lemma edge_refl_0[simp]:
  assumes "Some x \<noteq> fields_y fs"
  shows "edge x fs x = (\<lambda>_. {#})"
  using assms 
  unfolding fields_y_def by (auto split: fields.splits)

lemma fg_singleton_valid_no_refl_edge[simp]:
  assumes "Some x \<noteq> fields_y fs"
  shows "fg {x} (\<lambda>_. edge x fs) fl \<noteq> bot"
proof -
  have X: "edge x fs x = (\<lambda>_. {#})" using assms by simp
  thus ?thesis by (rule def_fg_singleton')
qed

interpretation ff: FF \<gamma> \<phi> edge
proof (standard, goal_cases)
  case (1 x fs)
  then show ?case
    apply (cases fs)
    using fg_singleton_valid_no_refl_edge
    unfolding fields_y_def
    by auto
qed

definition "adjust_interface x y \<equiv> return ()"

lemma adjust_interface':
  assumes "ix + iy \<noteq> bot" "dom_fi ix = {x}" "dom_fi iy = {y}" "x \<noteq> y"
  shows "fi {x} (inf_fi ix) (\<lambda>n. if n = y then a else outf_fi ix n) +
    fi {y} (\<lambda>n. inf_fi (ix + iy) n + a) (outf_fi iy) = ix + iy"
proof -
  let ?ix' = "fi {x} (inf_fi ix) (\<lambda>n. if n = y then a else outf_fi ix n)"
  let ?iy' = "fi {y} (\<lambda>n. inf_fi (ix + iy) n + a) (outf_fi iy)"

  have *: "is_sum_fi ix iy (ix + iy)"
    using plus_fi_to_is_sum_fi[of ix iy "ix + iy"] assms by simp
  then have A: "\<forall>n \<in> dom_fi ix. inf_fi ix n = inf_fi (ix + iy) n + outf_fi iy n"
    using assms unfolding is_sum_fi_def by auto
  have **: "is_sum_fi ?ix' ?iy' (ix + iy)"
    using assms A
    unfolding is_sum_fi_def
    by simp
  show ?thesis
    by (fact is_sum_fi_to_plus_fi[OF **])
qed

text \<open>If the existence of an interface sum is assumed and the domain provides minus,
  then @{text adjust_interface} can be simplified.\<close>
lemma adjust_interface_mset':
  assumes "ix + iy \<noteq> bot" "dom_fi ix = {x}" "dom_fi iy = {y}" "x \<noteq> y"
  shows "fi {x} (inf_fi ix) (\<lambda>n. if n = y then a else outf_fi ix n) +
         fi {y} (\<lambda>n. inf_fi iy n - outf_fi ix n + a) (outf_fi iy) = ix + iy"
proof -
  let ?ix' = "fi {x} (inf_fi ix) (\<lambda>n. if n = y then a else outf_fi ix n)"
  let ?iy' = "fi {y} (\<lambda>n. inf_fi (ix + iy) n + a) (outf_fi iy)"

  have *: "is_sum_fi ix iy (ix + iy)"
    using plus_fi_to_is_sum_fi[of ix iy "ix + iy"] assms by simp
  then have A: "\<forall>n \<in> dom_fi ix. inf_fi ix n = inf_fi (ix + iy) n + outf_fi iy n"
    using assms unfolding is_sum_fi_def by auto
  have "\<forall>n \<in> dom_fi iy. inf_fi iy n = inf_fi (ix + iy) n + outf_fi ix n"
    using assms * unfolding is_sum_fi_def by simp
  then have B: "\<forall>n \<in> dom_fi iy. inf_fi (ix + iy) n = inf_fi iy n - outf_fi ix n"
    by simp
  have C: "fi {y} (\<lambda>n. inf_fi (ix + iy) n + a) (outf_fi iy) =
    fi {y} (\<lambda>n. inf_fi iy n - outf_fi ix n + a) (outf_fi iy)"
    by (rule fi_cong, auto simp: B assms)
  have **: "is_sum_fi ?ix' ?iy' (ix + iy)"
    using assms A
    unfolding is_sum_fi_def
    by simp
  show ?thesis
    using is_sum_fi_to_plus_fi[OF **] C by simp
qed

lemma adjust_interface_rule:
  assumes "ix + iy \<noteq> bot" "x \<noteq> y" "dom_fi ix = {x}" "dom_fi iy = {y}"
  shows "<ff.NI gx x fsx mx ix * ff.NI gy y fsy my iy>
    adjust_interface x y
    <\<lambda>_. ff.NI gx x fsx mx ix * ff.NI gy y fsy my iy * \<up>(ix + iy =
            fi {x} (inf_fi ix) (\<lambda>n. if n = y then a else outf_fi ix n) +
            fi {y} (\<lambda>n. inf_fi (ix + iy) n + a) (outf_fi iy))>"
  unfolding adjust_interface_def apply sep_auto
  using assms adjust_interface'[of ix iy x y] by simp


\<comment> \<open>We use Ref.change to simulate single field updates while storing all fields together,
    i.e. all unrelated fields are read to rewrite them together with the changed field.\<close>
abbreviation fields_change where
"fields_change setter x \<equiv> Ref.change (\<lambda>fs. setter fs x)"

abbreviation fields_lookup where
"fields_lookup getter fs \<equiv> do {
    fs' \<leftarrow> Ref.lookup fs;
    return (getter fs') }"

partial_function (heap) update :: "fields ref \<Rightarrow> int \<Rightarrow> int \<Rightarrow> unit Heap" where
"update n from to = do {
    ff.open_NI n;
    q0 \<leftarrow> fields_lookup fields_q0 n;
    qs \<leftarrow> fields_lookup fields_qs n;
    let qs' = qs - {# from #} + (if to \<ge> 0 then {# to #} else {#}) in do {
    fields_change fields_qs' qs' n;
    from \<leftarrow> fields_lookup fields_q n;
    fields_change fields_q' (Max_mset (qs' + {#q0#})) n;
    to \<leftarrow> fields_lookup fields_q n;
    y \<leftarrow> fields_lookup fields_y n;
    ff.close_NI n qs';

    if from \<noteq> to
      then (case y of
        Some y' \<Rightarrow> do {
            ff.unfold_GrI y';
            ff.fold_GrI n;
            update y' from to 
          }
        | _ \<Rightarrow> do {
          ff.fold_GrI n
        })
      else ff.fold_GrI n
  }
}"

definition acquire :: "fields ref \<Rightarrow> fields ref \<Rightarrow> unit Heap" where
"acquire p r = do {
    ff.unfold_GrI p;
    ff.unfold_GrI r;
    ff.open_NI r;

    rqs \<leftarrow> fields_lookup fields_qs r;
    ry \<leftarrow> fields_lookup fields_y r;

    (if ry = None
      then do {
        fields_change fields_y' (Some p) r;
        rq \<leftarrow> fields_lookup fields_q r;
        ff.close_NI r rqs;
        ff.fold_GrI r;
        update p (-1) rq }
      else do {
        ff.close_NI r rqs;
        ff.open_NI p;
        fields_change fields_y' (Some r) p;
        pq \<leftarrow> fields_lookup fields_q p;
        pqs \<leftarrow> fields_lookup fields_qs p;
        ff.close_NI p pqs;
        ff.fold_GrI p;
        update r (-1) pq})
  }"

definition release :: "fields ref \<Rightarrow> fields ref \<Rightarrow> unit Heap" where
"release p r = do {
    ff.unfold_GrI p;
    ff.unfold_GrI r;
    ff.open_NI r;
    rq \<leftarrow> fields_lookup fields_q r;
    rqs \<leftarrow> fields_lookup fields_qs r;
    fields_change fields_y' None r;
    ff.close_NI r rqs;
    ff.fold_GrI r;
    update p rq (-1)
  }"

lemma ent_prod_cong:
  assumes "finite X" "\<And>x. x \<in> X \<Longrightarrow> P x \<Longrightarrow>\<^sub>A P' x"
  shows "(\<Prod>x \<in> X. P x) \<Longrightarrow>\<^sub>A (\<Prod>x \<in> X. P' x)"
  using assms
  apply (induction X rule: finite_induct)
   apply sep_auto
  apply (subst prod.insert, simp, simp)
  apply (subst prod.insert, simp, simp)
  by (rule ent_star_mono, simp, simp)


lemma finite_induct_reverse'_aux0: "a \<in> F \<Longrightarrow> insert a (F - F') = F - (F' - {a})"
  by blast

lemma finite_induct_reverse'_aux1: "finite X \<Longrightarrow> card X > 0 \<Longrightarrow> X \<noteq> {}"
  by auto

lemma finite_induct_reverse'_aux2:
  assumes "finite X" "x \<in> X" "card (X - {x}) = 0" shows "X = {x}"
proof -
  have "card (X - {x}) = 0" using assms by simp
  then have "card X = 1" using assms card_Suc_Diff1 by fastforce
  then show ?thesis using assms by (metis card_eq_0_iff finite_Diff insert_Diff)
qed

lemma finite_induct_reverse':
  assumes "finite F'" "F' \<subseteq> F" "\<And>a F. a \<in> F \<Longrightarrow> P a F"
    "\<And>x F'. F' \<subseteq> F \<Longrightarrow> x \<in> F \<Longrightarrow> (\<And>y. y \<in> F \<Longrightarrow> P y (insert x F')) \<Longrightarrow> P x F'" "a \<in> F'"
  shows "P a (F - F')"
  using assms
proof (induction "card (F' - {a})" arbitrary: a F')
  case 0
  have *: "insert a (F - {a}) = F" using \<open>a \<in> F'\<close> \<open>F' \<subseteq> F\<close> by blast
  have **: "F' = {a}"
    by (fact finite_induct_reverse'_aux2[OF \<open>finite F'\<close> \<open>a \<in> F'\<close> \<open>0 = card (F' - {a})\<close>[symmetric]])
  show ?case
    apply (rule "0"(5))
      apply blast
    using 0 apply blast
    apply (subst **, subst *, rule "0"(4), blast)
    done
next
  case (Suc x)

  have F: "finite (F' - {a})"
    using \<open>finite F'\<close> finite_Diff by blast

  have "F' - {a} \<noteq> {}" using \<open>Suc x = card (F' - {a})\<close> finite_induct_reverse'_aux1[OF F] by simp
  with \<open>F' \<subseteq> F\<close> have "F - (F' - {a}) \<noteq> F" by blast
  then have "F - (F' - {a}) \<subset> F" by blast

  show ?case
    apply (rule Suc(6))
       apply blast
    using Suc apply blast
    subgoal for y
    apply (subst finite_induct_reverse'_aux0[of a F F'])
      using Suc apply blast
      apply (cases "y \<in> F' \<and> y \<noteq> a")
    apply (rule Suc(1)[of "F' - {a}" y])
    using \<open>Suc x = card (F' - {a})\<close> F apply simp
    using \<open>finite F'\<close> apply simp
    using Suc apply blast
    using Suc apply blast
    using Suc apply blast
     apply simp
  proof-
    assume "y \<in> F" "\<not> (y \<in> F' \<and> y \<noteq> a)"
    then have A: "y \<in> F - (F' - {a})" by simp
    show "P y (F - (F' - {a}))"
      by (fact Suc(5)[OF A])
  qed
  done
qed


lemma finite_induct_reverse [consumes 2, case_names base step]:
  assumes "finite F" "F' \<subseteq> F" "\<And>a F. a \<in> F \<Longrightarrow> P a F"
    "\<And>x F'. F' \<subseteq> F \<Longrightarrow> x \<in> F \<Longrightarrow> (\<And>y. y \<in> F \<Longrightarrow> P y (insert x F')) \<Longrightarrow> P x F'" "a \<in> F"
  shows "P a F'"
proof (cases "a \<in> F - F'")
  case True
  obtain F'' where *: "F' = F - F''" "F'' \<subseteq> F" "finite F''" using assms by auto
  have "P a (F - F'')"
    apply (rule finite_induct_reverse'[of F'' F P a])
    using * assms True by blast+
  then show ?thesis
    using * by simp
next
  case False
  show ?thesis
    apply (rule assms(3))
    using False assms by simp
qed


lemmas pip_simps = fields_q_def fields_qs_def fields_qs'_def fields_q'_def fields_q0_def
                   fields_y_def Ref.change_def
lemmas ll_simps = ff.open_NI_rule ff.close_NI_rule ff.sing_NI_GrI_rule ff.sing_GrI_NI_rule
                  ff.preserve_interface_rule[where P=emp and P'="\<lambda>_. emp"]
                  ff.diff_NI_rule ff.extends_rule ff.extends_rule ff.unfold_GrI_rule
                  ff.fold_GrI_rule

lemma Max_mset_add_remove:
  assumes "x \<in># X" "y < x" "Max_mset ((X - {# x #}) + {# y #}) \<noteq> Max_mset X"
  shows "Max_mset X = x"
proof (rule ccontr)
  assume A: "Max_mset X \<noteq> x"
  then have B: "Max_mset X > x" using \<open>x \<in># X\<close> using Max_ge le_neq_trans by auto
  moreover have C: "Max_mset X \<in># X" using Max_in assms by blast

  have D: "y < Max_mset X"
    using B assms by simp

  have "Max_mset (X - {#x#}) = Max_mset X" using B assms
    using A C by (metis Max_eqI Max_ge finite_set_mset in_diffD insert_DiffM insert_noteq_member)
  then have "Max_mset ((X - {#x#}) + {#y#}) = Max_mset X"
    using A C D assms by (metis Max_insert add_cancel_left_right add_mset_eq_singleton_iff
        finite_set_mset insert_DiffM less_imp_le max_def set_mset_add_mset_insert
        set_mset_eq_empty_iff union_mset_add_mset_right)
  then show False
    using assms by simp
qed

lemma Max_mset_add_remove_lt:
  assumes "x \<in># X" "y < x" "Max_mset ((X - {# x #}) + {# y #}) \<noteq> Max_mset X"
  shows "Max_mset ((X - {# x #}) + {# y #}) < Max_mset X"
proof -
  have "Max_mset X = x"
    using assms Max_mset_add_remove by auto
  show ?thesis
  proof (rule ccontr)
    assume "\<not> Max_mset (X - {#x#} + {#y#}) < Max_mset X"
    then have "Max_mset (X - {#x#} + {#y#}) \<ge> Max_mset X"
      using leI by blast
    then obtain z where "z \<in># X - {#x#} + {#y#}" "z \<ge> Max_mset X"
      by (metis Max_in empty_eq_union finite_set_mset multi_self_add_other_not_self
          set_mset_eq_empty_iff)
    then have *: "z \<ge> x" using assms by (simp add: \<open>Max_mset X = x\<close>)
    then have "z \<in># X" by (metis \<open>z \<in># X - {#x#} + {#y#}\<close> assms leD mset_contains_eq
          mset_right_cancel_elem union_iff)
    then have "Max_mset ((X - {# x #}) + {# y #}) = Max_mset X" using * assms
      by (metis (no_types, lifting) Max_ge Max_in \<open>Max_mset X = x\<close> \<open>z \<in># X - {#x#} + {#y#}\<close>
          empty_eq_union finite_set_mset leD more_than_one_mset_mset_diff mset_right_cancel_elem
          neq_iff set_mset_eq_empty_iff)
    then show False
      using assms by simp
  qed
qed

lemma Max_mset_add_remove_le:
  assumes "x \<in># X" "y < x"
  shows "Max_mset ((X - {# x #}) + {# y #}) \<le> Max_mset X"
proof -
  have "Max_mset ((X - {# x #}) + {# y #}) = Max_mset ((X + {# y #}) - {# x #})"
    using assms by simp
  also have "... \<le> Max_mset (X + {# y #})"
    by (metis assms Max_ge Max_in diff_union_single_conv2 empty_eq_union finite_set_mset in_diffD
        multi_self_add_other_not_self set_mset_eq_empty_iff)
  also have "... = Max_mset X"
    by (metis assms Max_ge Max_in add_right_imp_eq antisym diff_single_trivial zero_diff
        diff_union_single_conv2 finite_set_mset leD mset_right_cancel_elem multi_drop_mem_not_eq)
  finally show ?thesis .
qed




lemma dom_fg_plus_fg1:
  assumes nbot: "h1 + h2 \<noteq> bot"
  shows "dom_fg h1 = dom_fg (h1 + h2) - dom_fg h2"
  using plus_fg_dom_un[OF nbot] plus_fg_dom_disj[OF nbot] by auto



end
