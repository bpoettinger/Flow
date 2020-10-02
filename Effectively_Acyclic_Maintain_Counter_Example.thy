\<^marker>\<open>creator Bernhard Pöttinger\<close>

chapter \<open>Counter-Example for Theorem 3\<close>
theory Effectively_Acyclic_Maintain_Counter_Example
  imports Effectively_Acyclic "HOL-Library.Multiset"
begin

paragraph \<open>Summary\<close>
text \<open>This theory provides a counter-example for theorem 3 in @{cite krishna20}\<close>

text \<open>We use flow graphs h = h1 + h2 and h' = h1' + h2.\<close>

text \<open>We introduce the following hack to obtain a pos_cancel_comm_monoid_add multiset.
  Regarding @{term "x \<subseteq># y"} it is, however it is not regarding @{term "x \<le> y"} of multisets.
  I have no clue how to use the first variant with my existing formalization. I think I have
  to include the endomorphism stuff in context pos_cancel_comm_monoid_add. Unfortunately,
  it uses extensively Function Algebras that seem to not be applicable in this context as
  it constrains the type class of its type parameter and our context does not provide this
  information for its type parameter.\<close>

instance multiset :: (preorder) pos_cancel_comm_monoid_add
  sorry

lemma aux':
  fixes m :: "nat multiset"
  shows "m \<le> {#2#} \<Longrightarrow> m = {#} \<or> m = {#2#}"
  sorry (* related to our type-class issue, next lemma shows that this works for
            the intended less-relation... *)

lemma aux'':
  fixes m :: "nat multiset"
  shows "m \<subseteq># {#2#} \<Longrightarrow> m = {#} \<or> m = {#2#}"
  using multi_nonempty_split by auto

text \<open>Edge function\<close>

fun f' :: "nat set \<Rightarrow> nat multiset \<Rightarrow> nat multiset" where
"f' R X = {# x + 1 | x \<in># X . x \<notin> R #}"

text \<open>Inflows {inf of h, inf1 of h1, inf2 of h2\<close>

fun inf :: "nat \<Rightarrow> nat multiset" where
"inf 0 = {# 0 #}" |
"inf _ = {#}"

fun inf1 :: "nat \<Rightarrow> nat multiset" where
"inf1 0 = {# 0 #}" |
"inf1 k = (if k = 2 then {#2#} else {#})"

fun inf2 :: "nat \<Rightarrow> nat multiset" where
"inf2 k = (if k = 1 then {#1#} else {#})"

text \<open>Flows flow of h, flow' of h'\<close>

fun flow :: "nat \<Rightarrow> nat multiset" where
"flow k = {# k #}"

fun flow' :: "nat \<Rightarrow> nat multiset" where
"flow' x = (if x = 0 then {# 0, 3 #} else {# x #})"

text \<open>Edges edges of h, edges' of h'\<close>

fun edges :: "nat \<Rightarrow> nat \<Rightarrow> nat multiset \<Rightarrow> nat multiset" where
"edges x y = (
    if x = 0 \<and> y = 1 then f' {3} else
    if x = 1 \<and> y = 2 then f' {2} else
    if x = 2 \<and> y = 0 then f' {2} else
    (\<lambda>_. 0)
  )"

fun edges' :: "nat \<Rightarrow> nat \<Rightarrow> nat multiset \<Rightarrow> nat multiset" where
"edges' x y = (
    if x = 0 \<and> y = 1 then f' {3} else
    if x = 1 \<and> y = 2 then f' {2} else
    if x = 2 \<and> y = 0 then f' {} else
    (\<lambda>_. 0)
  )"

text \<open>Define flow graphs using the above raw definitions\<close>

abbreviation "h \<equiv> fg {0,1,2} edges flow"
abbreviation "h' \<equiv> fg {0,1,2} edges' flow'"
abbreviation "h1 \<equiv> fg {0,2} edges flow"
abbreviation "h1' \<equiv> fg {0,2} edges' flow'"
abbreviation "h2 \<equiv> fg {1} edges flow :: (nat, nat multiset) fg"

text \<open>Prove for each of the defined flow graphs that the supposed inflow and flow actually solve
the flow equation.\<close>

lemma flow_exists: "flow_eq (fg {0,1,2} edges flow) inf"
  by (rule flow_eqI, auto simp: numeral_2_eq_2)

lemma flow_exists': "flow_eq (fg {0,1,2} edges' flow') inf"
  by (rule flow_eqI, auto simp: numeral_2_eq_2)

lemma flow_exists1: "flow_eq (fg {0,2} edges flow) inf1"
  by (rule flow_eqI, auto simp: numeral_2_eq_2)

lemma flow_exists1': "flow_eq (fg {0,2} edges' flow') inf1"
  by (rule flow_eqI, auto simp: numeral_2_eq_2)

lemma flow_exists2: "flow_eq (fg {1} edges flow) inf2"
  by (rule flow_eqI, auto simp: numeral_2_eq_2)

text \<open>Prove that each of the defined flow graphs is a valid flow graph (kind of redundant
considering the proofs for the flow equations...)\<close>

lemma fg_exists: "h \<noteq> bot"
  using fgI2[OF flow_exists] by auto

lemma fg_exists': "h' \<noteq> bot"
  using fgI2[OF flow_exists'] by auto

lemma fg_exists1: "h1 \<noteq> bot"
  using fgI2[OF flow_exists1] by auto

lemma fg_exists1': "h1' \<noteq> bot"
  using fgI2[OF flow_exists1'] by auto

lemma fg_exists2: "h2 \<noteq> bot"
  using fgI2[OF flow_exists2] by auto

text \<open>Prove that the indeed h = h1 + h2 and h' = h1' + h2 (as supposed to)\<close>

lemma fg_sum_eq: "h1 + h2 = h"
  by (rule plus_fg_fg'[OF fg_exists1 fg_exists2], auto)

lemma fg_sum_eq': "h1' + h2 = h'"
  by (rule plus_fg_fg'[OF fg_exists1' fg_exists2], auto)

text \<open>Prove that h1' extends h1 subflow-preservingly\<close>

lemma aux:
  "m \<le> {# 2 #} \<Longrightarrow> {#x \<in># fold_mset (add_mset \<circ> Suc) {#} {#x \<in># m. x \<noteq> 2#}. x \<noteq> 3#} = {#x \<in># fold_mset (add_mset \<circ> Suc) {#} m. x \<noteq> 3#}"
  apply (rule multiset_eqI)
  using aux'[of m] apply auto
  by (metis (mono_tags, lifting) comp_def comp_fun_commute.fold_mset_single comp_fun_commute_mset_image count_single eval_nat_numeral(3))

lemma ctx: "h1 \<lesssim>\<^sub>S h1'"
  using fg_exists1 fg_exists1' inf_fg_int_fg[of h1] inf_fg_int_fg[of h1']
        inf_fg_fg''[OF flow_exists1] inf_fg_fg''[OF flow_exists1'] outf_fg_unfold'[OF fg_exists1]
        outf_fg_unfold'[OF fg_exists1'] aux
  unfolding subflow_preserving_extension_def contextual_extension_def
  apply clarsimp
  unfolding image_mset_def
  by (smt aux' filter_empty_mset filter_mset_add_mset fold_mset_empty inf1.simps(2) numeral_2_eq_2)

text \<open>Define the set E of allowed edge functions by introducing the
closure over all f' and id and 0\<close>

inductive_set E :: "(nat multiset \<Rightarrow> nat multiset) set" where
id[intro]: "id \<in> E" |
zero[intro]: "(\<lambda>_. {#}) \<in> E" |
base[intro]: "finite R \<Longrightarrow> f' R \<in> E" |
plus[intro]: "f1 \<in> E \<Longrightarrow> f2 \<in> E \<Longrightarrow> f1 + f2 \<in> E" |
comp[intro]: "f1 \<in> E \<Longrightarrow> f2 \<in> E \<Longrightarrow> f1 o f2 \<in> E"

text \<open>We have to prove that E is a closed set of endomorphisms:\<close>

lemma endo_E': "e \<in> E \<Longrightarrow> e \<in> End"
  by (induction rule: E.induct, auto simp: endo_def)

lemma endo_E: "E \<subseteq> End"
  using endo_E' by auto

lemma End_closed_E: "End_closed E"
  unfolding End_closed_def
  using endo_E' by auto

text \<open>We have to prove that E is a reduced set of functions.\<close>

text \<open>For some reason we introduce an abbreviation for reduced functions.\<close>
abbreviation "reduced' e \<equiv> (\<exists>x. e x \<noteq> 0) \<longrightarrow> (\<exists>x. e (e x) \<noteq> 0)"

text \<open>All f' are reduced\<close>
lemma reduced_f':
  shows "finite R \<Longrightarrow> reduced' ((f' :: nat set \<Rightarrow> nat multiset \<Rightarrow> nat multiset) R)"
proof
  assume A: "finite R" "\<exists>x. f' R x \<noteq> {#}"
  show "\<exists>x. f' R (f' R x) \<noteq> {#}"
  proof (cases "R = {}")
    case True
    then have "f' R (f' R {#(0 :: nat)#}) = {#2#}"
      by simp
    then show ?thesis
      by (metis add_mset_not_empty)
  next
    case False
    then have "Max R \<in> R"
      using A by simp
    then have *: "(Max R) + 1 \<notin> R"
      by (metis A(1) Max_ge add.right_neutral add_le_cancel_left not_one_le_zero)
    then have **: "(Max R) + 2 \<notin> R"
      by (metis A(1) Max_ge add.comm_neutral add_le_cancel_left eq_numeral_Suc linorder_not_le zero_less_Suc)

    have "f' R (f' R {#(Max R) + 1#}) = {#(Max R) + 3#}"
      using * ** by simp
    then show ?thesis
      by (metis empty_not_add_mset)
  qed
qed

text \<open>Sums of functions from E are reduced.\<close>
lemma reduced_E_plus:
  assumes "f1 \<in> E" "f2 \<in> E" "reduced' f1" "reduced' f2" "\<forall>x. (f1 + f2) ((f1 + f2) x) = {#}"
  shows "\<forall>x. (f1 + f2) x = {#}"
proof -
  have "\<forall>x. f1 (f1 x) = {#} \<and> f2 (f2 x) = {#}"
  proof
    fix x
    have "{#} = (f1 + f2) ((f1 + f2) x)"
      using assms by simp
    also have "... = f1 ((f1 + f2) x) + f2 ((f1 + f2) x)"
      by simp
    also have "... = f1 (f1 x) + f1 (f2 x) + f2 (f1 x) + f2 (f2 x)"
      using assms endo_E' unfolding endo_def by simp
    finally show "f1 (f1 x) = {#} \<and> f2 (f2 x) = {#}"
      by auto
  qed
  then have "\<forall>x. f1 x = {#}" "\<forall>x. f2 x = {#}"
    using assms by auto
  then  show "\<forall>x. (f1 + f2) x = {#}"
    by auto
qed

text \<open>Some auxiliary development\<close>
lemma E_mono:
  assumes "e \<in> E" "x \<subseteq># x'"
  shows "e x \<subseteq># e x'"
  using assms
  by (induction arbitrary: x x', auto simp: image_mset_subseteq_mono multiset_filter_mono mset_subset_eq_mono_add)

text \<open>Some auxiliary development\<close>
lemma E_not_zero: "e \<in> E \<Longrightarrow> e \<noteq> 0 \<Longrightarrow> \<exists>x. x \<noteq> 0 \<and> (\<forall>x' \<ge> x. \<exists>y \<ge> x'. y \<in># e {#x'#})"
proof (induction rule: E.induct)
case id
  then show ?case by auto
next
  case zero
  then show ?case by simp
next
  case (base R)
  then show ?case
  proof (cases "R = {}")
    case True
    show ?thesis 
      by (rule exI[where x="1"], auto simp: True)
  next
    case False
    then have "Max R \<in> R"
      using base by simp
    then have *: "\<forall>x' > Max R. x' \<notin> R"
      using base False Max_less_iff by auto
    show ?thesis
      apply (rule exI[where x="Max R + 1"], simp)
      using "*" Suc_le_lessD by blast
  qed
next
  case (plus f1 f2)
  then have "f1 \<noteq> 0 \<or> f2 \<noteq> 0"
    by auto
  then consider (a) "f1 \<noteq> 0" | (b) "f2 \<noteq> 0" by blast
  then show ?case
  proof cases
    case a
    then obtain x where "x \<noteq> 0" "\<forall>x'\<ge>x. \<exists>y\<ge>x'. y \<in># f1 {#x'#}" using plus by blast
    then show ?thesis
      apply (cases "f2 = 0", auto)
      by (rule exI[where x="x"], auto)
  next
    case b
    then obtain x where "x \<noteq> 0" "\<forall>x'\<ge>x. \<exists>y\<ge>x'. y \<in># f2 {#x'#}" using plus by blast
    then show ?thesis
      apply (cases "f1 = 0", auto)
      by (rule exI[where x="x"], auto)
  qed
next
  case (comp f1 f2)
  then have "f1 \<noteq> 0" by auto
  moreover have "f2 \<noteq> 0"
    using comp
    by (meson End_closed_End endo_E' endo_f_0_0_closed_comp)
  ultimately obtain x1 x2 where *: "x1 \<noteq> 0" "\<forall>x'\<ge>x1. \<exists>y\<ge>x'. y \<in># f1 {#x'#}"
    "x2 \<noteq> 0" "\<forall>x'\<ge>x2. \<exists>y\<ge>x'. y \<in># f2 {#x'#}" using comp by blast

  let ?x = "max x1 x2"

  have bla: "\<forall>x'\<ge>max x1 x2. \<exists>y\<ge>x'. y \<in># (f1 \<circ> f2) {#x'#}"
  proof safe
    fix x'
    assume A: "max x1 x2 \<le> x'"
    then have "x' \<ge> x2" by simp
    then obtain y where Y: "y \<ge> x'" "y \<in># f2 {#x'#}" using * by blast
    then have X: "{#y#} \<subseteq># f2 {#x'#}" by simp
    have X2: "f1 {#y#} \<subseteq># f1 (f2 {#x'#})" by (fact E_mono[OF comp(1) X])
  
    have AA: "y \<ge> x1" using A Y by simp
    then obtain y2 where ZZ: "y2 \<ge> y" "y2 \<in># f1 {#y#}" using * by blast
    then have Z: "y2 \<in># f1 (f2 {#x'#})" using X2 mset_subset_eqD by metis
    show "\<exists>y\<ge>x'. y \<in># (f1 \<circ> f2) {#x'#}"
      apply (rule exI[where x="y2"])
      using Z ZZ Y by auto
  qed

  show ?case
    apply (rule exI[where x="?x"])
    using * bla by auto
qed

text \<open>Compositions of functions in E are reduced\<close>
lemma reduced_E_comp:
  assumes "f1 \<in> E" "f2 \<in> E" "reduced' f1" "reduced' f2" "\<exists>x. (f1 o f2) x \<noteq> 0"
  shows "\<exists>x. (f1 o f2) ((f1 o f2) x) \<noteq> {#}"
proof -
  obtain x where *: "f1 (f2 x) \<noteq> 0"
    using assms by auto
  then have A1: "f1 \<noteq> 0" by auto
  have A2: "f2 \<noteq> 0" using End_closed_E assms by auto

  obtain x1 x2 where *: "x2 \<noteq> 0" "x2 \<noteq> 0" "\<forall>x' \<ge> x1. \<exists>y \<ge> x'. y \<in># f1 {#x'#}" "\<forall>x' \<ge> x2. \<exists>y \<ge> x'. y \<in># f2 {#x'#}"
    using E_not_zero[OF assms(1) A1] E_not_zero[OF assms(2) A2] by auto

  let ?x = "max x1 x2"

  have *: "?x \<noteq> 0" "\<forall>x' \<ge> ?x. \<exists>y \<ge> x'. y \<in># f1 {#x'#}" "\<forall>x' \<ge> ?x. \<exists>y \<ge> x'. y \<in># f2 {#x'#}"
    using * by auto

  have "?x \<ge> ?x" by simp
  then obtain y1 where B1: "y1 \<ge> ?x" "y1 \<in># f2 {#?x#}" using * by blast
  then have B2: "{#y1#} \<subseteq># f2 {#?x#}" by simp
  then have B22: "f1 {#y1#} \<subseteq># f1 (f2 {#?x#})" using E_mono[OF assms(1) B2] by simp
  then have "y1 \<ge> ?x" using B1 by simp
  then obtain y2 where B2: "y2 \<ge> y1" "y2 \<in># f1 {#y1#}" using * by blast
  then have B22': "{#y2#} \<subseteq># f1 {#y1#}" by simp
  have B3: "{#y2#} \<subseteq># f1 (f2 {#?x#})" using subset_mset.order.trans[OF B22' B22] by simp
  then have B3': "f2 {#y2#} \<subseteq># f2 (f1 (f2 {#?x#}))" using E_mono[OF assms(2) B3]
    unfolding comp_def by simp
  then have "y2 \<ge> ?x" using B1 B2 order_trans by blast
  then obtain y3 where B3: "y3 \<ge> y2" "y3 \<in># f2 {#y2#}" using * by blast
  then have B7: "{#y3#} \<subseteq># f2 {#y2#}" by simp
  then have B33: "{#y3#} \<subseteq># f2 (f1 (f2 {#?x#}))" using subset_mset.order.trans[OF B7 B3'] by simp
  then have B5: "f1 {#y3#} \<subseteq># f1 (f2 (f1 (f2 {#?x#})))" using E_mono[OF assms(1) B33]
    unfolding comp_def by simp
  have "y3 \<ge> ?x" using B3(1) \<open>max x1 x2 \<le> y2\<close> order.trans by blast
  then obtain y4 where B4: "y4 \<ge> y3" "y4 \<in># f1 {#y3#}" using * by blast
  then have B6: "y4 \<in># f1 (f2 (f1 (f2 {#?x#})))" using B5 by (simp add: mset_subset_eqD)
  show ?thesis unfolding comp_def
    apply (rule exI[where x="{#?x#}"])
    using B6 by auto
qed

text \<open>All functions in E are reduced\<close>
lemma reduced_E': "e \<in> E \<Longrightarrow> \<forall>x. e (e x) = 0 \<Longrightarrow> \<forall>x. e x = 0"
  apply (induction rule: E.induct, simp, simp)
  using reduced_f' apply blast
  using reduced_E_plus apply blast
  using reduced_E_comp by blast

text \<open>Obtain the actual reduced predicate.\<close>
lemma reduced_E: "reduced E"
  using reduced_E'
  unfolding reduced_def comp_def zero_fun_def
  by metis

text \<open>Prove that all edge functions that occur in our flow graphs are allowed by E.\<close>
lemma edge_in: "\<forall>x y. edge_fg h x y \<in> E" using fg_exists by auto
lemma edge_in2: "\<forall>x y. edge_fg h2 x y \<in> E" using fg_exists2 by auto
lemma edge_in1: "\<forall>x y. edge_fg h1 x y \<in> E" using fg_exists1 by auto
lemma edge_in1': "\<forall>x y. edge_fg h1' x y \<in> E" using fg_exists1' by auto
lemma edge_in': "\<forall>x y. edge_fg h' x y \<in> E" using fg_exists' by auto

lemma k_lists_h_3_unfold':
  "k_lists {0,1,2} 3 = {
    [0,0,0], [0,0,1], [0,0,2],
    [0,1,0], [0,1,1], [0,1,2],
    [0,2,0], [0,2,1], [0,2,2],
    [1,0,0], [1,0,1], [1,0,2],
    [1,1,0], [1,1,1], [1,1,2],
    [1,2,0], [1,2,1], [1,2,2],
    [2,0,0], [2,0,1], [2,0,2],
    [2,1,0], [2,1,1], [2,1,2],
    [2,2,0], [2,2,1], [2,2,2]
}"
  unfolding k_lists_def
  apply auto
  by (smt insert_iff insert_subset length_0_conv length_Suc_conv list.set(2) numeral_3_eq_3 singletonD)

lemma k_lists_h_3_unfold:
  "k_lists {0,Suc 0, Suc (Suc 0)} 3 = {
    [0,0,0], [0,0,1], [0,0,2],
    [0,1,0], [0,1,1], [0,1,2],
    [0,2,0], [0,2,1], [0,2,2],
    [1,0,0], [1,0,1], [1,0,2],
    [1,1,0], [1,1,1], [1,1,2],
    [1,2,0], [1,2,1], [1,2,2],
    [2,0,0], [2,0,1], [2,0,2],
    [2,1,0], [2,1,1], [2,1,2],
    [2,2,0], [2,2,1], [2,2,2]
}"
  using k_lists_h_3_unfold'
  apply (subst (asm) numeral_2_eq_2)
  by simp

lemma k_lists_h1'_1_unfold: "k_lists (dom_fg h1') 1 = {[0], [2]}"
  unfolding k_lists_def
  using fg_exists1'
  apply auto
  by (metis empty_iff length_0_conv length_Suc_conv set_ConsD set_empty subset_empty subset_insert)

lemma k_lists_h_1_unfold: "k_lists (dom_fg h) 1 = {[1],[2],[0]}"
  unfolding k_lists_def
  using fg_exists
  apply auto
  by (metis empty_iff length_0_conv length_Suc_conv set_ConsD set_empty subset_empty subset_insert)

lemma k_lists_h_2_unfold: "k_lists (dom_fg h) 2 = {[0,0], [0,1], [0,2], [1,0], [1,1], [1,2], [2,0], [2,1], [2,2]}"
  unfolding k_lists_def
  using fg_exists
  apply auto
  by (smt insertE insert_subset length_0_conv length_Suc_conv list.set(2) numeral_2_eq_2 singletonD)

lemma k_lists_h1'_2_unfold: "k_lists (dom_fg h1') 2 = {[0,0], [0,2], [2,0], [2,2]}"
  unfolding k_lists_def
  using fg_exists1'
  apply auto
  by (smt insertE insert_subset length_0_conv length_Suc_conv list.set(2) numeral_2_eq_2 singletonD)

text \<open>Prove effective acyclicity of all flow graphs\<close>

lemma pigeonhole_split_list_length_le:
  assumes "length as \<ge> card N + 1" "set as \<subseteq> N" "finite N"
  shows "\<exists>x xs ys zs. as = xs @ x # ys @ x # zs \<and> length ys < card N"
  using assms
proof (induction "length as" arbitrary: as rule: nat_less_induct)
  case 1
  obtain x xs ys zs where *: "as = xs @ x # ys @ x # zs"
    using pigeonhole_split_list[of N as] 1 by auto
  then show ?case
  proof (cases "length ys < card N")
    case True
    then show ?thesis using * by blast
  next
    case False
    then have X: "\<And>m x. m < length as \<Longrightarrow> m = length x \<Longrightarrow> card N + 1 \<le> length x \<Longrightarrow> set x \<subseteq> N \<Longrightarrow>
      finite N \<Longrightarrow> (\<exists>xa xs ys zs. x = xs @ xa # ys @ xa # zs \<and> length ys < card N)"
      using 1 by blast
    from False have A: "length (x # ys) < length as" using * by simp
    moreover have B: "length (x # ys) \<ge> card N + 1" using * False 1 by simp
    moreover have C: "set (x # ys) \<subseteq> N" using 1 * by simp
    ultimately show ?thesis using * 1 X[OF A _ B C]
      by (metis append.assoc append_Cons)
  qed
qed

text \<open>Obviously I have not the slightest clue how to efficiently \<close>

lemma ea_aux:
  assumes "k \<ge> 1" "k \<le> 3" "xs \<in> k_lists (dom_fg h) k"
  shows "chain (edge_fg h) xs (hd xs) (flow_fg h (hd xs)) = {#}"
  using assms
      apply (cases "k = 0")
       apply simp
      apply (cases "k = 1")
      using k_lists_h_1_unfold fg_exists apply simp
       apply (intro conjI)
         apply (clarsimp, cases xs, simp, simp)+
      apply (cases "k = 2")
       defer
      using k_lists_h_2_unfold fg_exists apply simp
       apply (clarsimp split: if_splits simp: numeral_2_eq_2)
       apply (intro conjI)
        apply safe
          apply (cases "k = 3")
      using k_lists_h_3_unfold fg_exists apply simp
           apply (clarsimp split: if_splits nat.splits simp: numeral_2_eq_2)
           apply (cases xs)
            apply simp
           apply safe
      apply simp_all
          apply (cases "k = 3")
      using k_lists_h_3_unfold fg_exists apply simp
           apply (clarsimp split: if_splits nat.splits simp: numeral_2_eq_2)
           apply (cases xs)
            apply simp
           apply safe
      apply simp_all
          apply (cases "k = 3")
      using k_lists_h_3_unfold fg_exists apply simp
           apply (clarsimp split: if_splits nat.splits simp: numeral_2_eq_2)
           apply (cases xs)
            apply simp
           apply safe
      apply simp_all
          apply (cases "k = 3")
      using k_lists_h_3_unfold fg_exists apply simp
           apply (clarsimp split: if_splits nat.splits simp: numeral_2_eq_2)
           apply (cases xs)
            apply simp
           apply safe
      apply simp_all
      using k_lists_h_2_unfold fg_exists apply simp
       apply (clarsimp split: if_splits simp: numeral_2_eq_2)
       apply (intro conjI)
        apply safe
      by simp_all

lemma ea_aux1':
  assumes "k \<ge> 1" "k \<le> 2" "xs \<in> k_lists (dom_fg h1') k"
  shows "chain (edge_fg h1') xs (hd xs) (flow_fg h1' (hd xs)) = {#}"
  using assms
      apply (cases "k = 0")
       apply simp
      apply (cases "k = 1")
      using k_lists_h1'_1_unfold fg_exists1' apply simp
       apply (intro conjI)
         apply (clarsimp, cases xs, simp, simp)+
      apply (cases "k = 2")
       defer
      apply linarith
      using k_lists_h1'_2_unfold fg_exists1' apply simp
       apply (clarsimp split: if_splits simp: numeral_2_eq_2)
       apply (intro conjI)
        apply safe
      by simp_all

lemma chainE:
  assumes "chain f xs y z = a" "f = g on set xs"
  shows "chain g xs y z = a"
  using assms
  apply (induction xs rule: induct_list012, auto)
  by (smt chain_cong set_ConsD)

lemma ea1': "eff_acyclic' h1'"
  unfolding eff_acyclic'_def eff_acyclic_def
proof (safe, goal_cases)
  case (1 k ns)
  then show ?case
  proof (cases "k \<ge> 3")
    case True
    then obtain n ns1 ns2 ns3 where ns: "ns = ns1 @ n # ns2 @ n # ns3" "length ns2 < card (dom_fg h1')"
      using pigeonhole_split_list_length_le[of "dom_fg h1'" ns] 1 fg_exists1' unfolding k_lists_def by auto
    then have "chain edges' (n # ns2) n (flow_fg h1' n) = 0"
      using ea_aux1'[of "length (n # ns2)" "n # ns2"] fg_exists1' True 1 
        fg_exists' fg_sum_eq' chain_cong'[OF edge_fg_plus_fg_on1[of h1' h2], symmetric]
      apply (auto split: if_splits simp: numeral_2_eq_2 k_lists_def)
      by (erule chainE, auto)+
    then have "chain edges' (n # ns3) (hd ns) (chain edges' (n # ns2) n (flow_fg h1' n)) = {#}"
      apply simp
      apply (rule endo_f_0_0_closed[of "chain _ _ _", where E=E])
       apply (rule endo_chain_closed)
         apply auto
      using End_closed_E by blast+
    then have "chain edges' (n # ns2 @ n # ns3) (hd ns) (flow_fg h1' n) = {#}"
      using chain_append'[where xs="n#ns2"]
      by (smt append_Cons list.discI list.sel(1))
    then have **: "chain (edge_fg h1') (n # ns2 @ n # ns3) (hd ns) (flow_fg h1' n) = {#}"
      apply (subst (asm) chain_cong'[where g="edge_fg h1'" and N="{0,2}"], simp add: fg_exists1')
       apply (metis "1"(2) dom_fg_fg fg_exists1' k_lists_dom le_sup_iff ns(1) set_append)
      by simp
    have *: "hd (ns1 @ [n]) = hd ns" using ns by (simp add: hd_append)
    have "chain (edge_fg h1') (ns1 @ n # ns2 @ n # ns3) (hd ns) (flow_fg h1' (hd ns)) \<le>
      chain (edge_fg h1') (n # ns2 @ n # ns3) (hd ns) (flow_fg h1' n)"
      apply (subst chain_append_nonempty[where xs="ns1"], simp)
      apply (rule order_trans)
       apply (rule pos_endo_mono'_closed[where f="chain _ _ _" and E=E])
      apply (subst *[symmetric])
      apply (rule chain_flow_fg_le_flow_fg[of h1' E n ns1])
               apply (simp add: fg_exists1')
              apply (simp add: End_closed_E)
      using edge_in1' apply blast
      using 1 ns unfolding k_lists_def apply (simp add: fg_exists1 fg_exists1' list.sel(1))
      using 1 ns unfolding k_lists_def apply (simp add: fg_exists1 fg_exists1' list.sel(1))
          apply (simp add: E.id)
         apply (simp add: E.zero)
        apply (simp add: E.id End_closed_E edge_in1' endo_chain_closed)
              apply (simp add: End_closed_E)
      apply simp
      done
    then show ?thesis
      using ns ** by simp
  next
    case False
    then have "k \<le> 2" by simp
    with 1 show ?thesis
      using ea_aux1' by blast
  qed
qed

lemma ea: "eff_acyclic' h"
  unfolding eff_acyclic'_def eff_acyclic_def
proof (safe, goal_cases)
  case (1 k ns)
  then show ?case
  proof (cases "k \<ge> 4")
    case True
    then obtain n ns1 ns2 ns3 where ns: "ns = ns1 @ n # ns2 @ n # ns3" "length ns2 < card (dom_fg h)"
      using pigeonhole_split_list_length_le[of "dom_fg h" ns] 1 fg_exists unfolding k_lists_def by auto
    then have "chain edges (n # ns2) n (flow_fg h n) = 0"
      using ea_aux[of "length (n # ns2)" "n # ns2"] fg_exists True 1 
        fg_exists' fg_sum_eq'
      unfolding k_lists_def
      apply simp
      apply (erule chainE)
      by auto
    then have "chain edges (n # ns3) (hd ns) (chain edges (n # ns2) n (flow_fg h n)) = {#}"
      apply simp
      apply (rule endo_f_0_0_closed[of "chain _ _ _", where E=E])
       apply (rule endo_chain_closed)
         apply auto
      using End_closed_E by blast+
    then have "chain edges (n # ns2 @ n # ns3) (hd ns) (flow_fg h n) = {#}"
      using chain_append'[where xs="n#ns2"]
      by (smt append_Cons list.discI list.sel(1))
    then have **: "chain (edge_fg h) (n # ns2 @ n # ns3) (hd ns) (flow_fg h n) = {#}"
      apply (subst (asm) chain_cong'[where g="edge_fg h" and N="{0,1,2}"], simp add: fg_exists)
        apply (metis One_nat_def edge_fg_fg fg_exists insertCI)
      using ns 1 fg_exists unfolding k_lists_def by auto
    have *: "hd (ns1 @ [n]) = hd ns" using ns by (simp add: hd_append)
    have bruteforce: "fg {0, Suc 0, 2} edges flow = h"
      by simp
    have "chain (edge_fg h) (ns1 @ n # ns2 @ n # ns3) (hd ns) (flow_fg h (hd ns)) \<le>
      chain (edge_fg h) (n # ns2 @ n # ns3) (hd ns) (flow_fg h n)"
      apply (subst chain_append_nonempty[where xs="ns1"], simp)
      apply (rule order_trans)
       apply (rule pos_endo_mono'_closed[where f="chain _ _ _" and E=E])
         apply (subst *[symmetric])
      apply (subst bruteforce)+
         apply (rule chain_flow_fg_le_flow_fg[of h E n ns1])
      using fg_exists apply blast
              apply (simp add: End_closed_E)
      using edge_in apply blast
            apply (metis "1"(2) Diff_insert_absorb UnCI insertI1 k_lists_dom list.simps(15) ns(1) set_append subset_Diff_insert)
      apply (metis "1"(2) k_lists_dom le_sup_iff ns(1) set_append)
          apply (simp add: E.id)
         apply (simp add: E.zero)
      apply (metis E.id End_closed_E bruteforce edge_in endo_chain_closed)
              apply (simp add: End_closed_E)
      by simp
    then show ?thesis
      using ns ** by simp
  next
    case False
    then have "k \<le> 3" by simp
    with 1 show ?thesis
      using ea_aux by blast
  qed
qed

lemma eff_acyclic'_plus_fg1:
  fixes h h1 h2
  assumes "eff_acyclic' h" "h = h1 + h2" "h \<noteq> bot"
  shows "eff_acyclic' h1"
  using assms edge_fg_plus_fg_on1[of h1 h2] flow_fg_plus_fg_on1[of h1 h2]
  unfolding eff_acyclic'_def eff_acyclic_def k_lists_def
  apply auto
  apply (subst chain_cong'[where g="edge_fg (h1 + h2)" and N="dom_fg h1"])
    apply simp
   apply simp
  by (metis dom_fg_plus_fg_subs1 hd_in_set le_simps(3) length_greater_0_conv plus_fg_dom_un subset_eq)

lemma eff_acyclic'_plus_fg2:
  fixes h h1 h2
  assumes "eff_acyclic' h" "h = h1 + h2" "h \<noteq> bot"
  shows "eff_acyclic' h2"
  using assms eff_acyclic'_plus_fg1
  using add.commute by blast

lemma ea1: "eff_acyclic' h1" and ea2: "eff_acyclic' h2"
  using ea eff_acyclic'_plus_fg2 eff_acyclic'_plus_fg1
  by (metis fg_exists fg_sum_eq)+

text \<open>Prove that h' is not an effectively acyclic flow graph.\<close>
lemma ea': "\<not> (eff_acyclic' h')"
proof
  let ?ns = "[0,1,2]"
  let ?N = "dom_fg h'" let ?e = "edge_fg h'" let ?f = "flow_fg h'"
  have k: "?ns \<in> k_lists ?N 3"
    using fg_exists' unfolding k_lists_def by simp

  assume A: "eff_acyclic' h'"
  have *: "chain ?e ?ns (hd ?ns) (?f (hd ?ns)) = {#}"
    apply (rule eff_acyclic'_chain_eq_0_plus_fg[of h' h' 0])
    using fg_exists' End_closed_E edge_in' A by auto

  have "chain edges' ?ns (hd ?ns) (flow' (hd ?ns)) = {# 3 #}" by simp
  with * fg_exists' show False by simp
qed

text \<open>Assuming theorem 3 from @{cite krishna20} we derive False from our example flow graphs:
on the one hand the theorem claims that flow graph h1'+h2 us effectively acyclic,
while on the other hand we showed that it is not effectively acyclic.\<close>

lemma maintain_eff_acyclic_dom:
  assumes T: "\<And>h h1 h1' h2 :: (nat, nat multiset) fg. \<And>E.
           h = h1 + h2 \<Longrightarrow> h \<noteq> bot \<Longrightarrow> h1' \<noteq> bot \<Longrightarrow> dom_fg h1' \<inter> dom_fg h2 = {} \<Longrightarrow>
           \<forall>n \<in> dom_fg h1' - dom_fg h1. outf_fg h2 n = 0 \<Longrightarrow> \<forall>x y. edge_fg h x y \<in> E \<Longrightarrow>
           End_closed E \<Longrightarrow> id \<in> E \<Longrightarrow> \<forall>x y. edge_fg h2 x y \<in> E \<Longrightarrow>
           \<forall>x y. edge_fg h1 x y \<in> E \<Longrightarrow> \<forall>x y. edge_fg h1' x y \<in> E \<Longrightarrow>
           (\<lambda>_. 0) \<in> E \<Longrightarrow> reduced E \<Longrightarrow> eff_acyclic' h \<Longrightarrow> eff_acyclic' h1 \<Longrightarrow> eff_acyclic' h1' \<Longrightarrow>
           eff_acyclic' h2 \<Longrightarrow> h1 \<lesssim>\<^sub>S h1' \<Longrightarrow>
           \<exists>h'. h' = h1' + h2 \<and> h' \<noteq> bot \<and> eff_acyclic' h' \<and> h \<lesssim>\<^sub>S h'"
  shows False
proof -
  have "\<exists>h'. h' = h1' + h2 \<and> h' \<noteq> bot \<and> eff_acyclic' h' \<and> h \<lesssim>\<^sub>S h'"
    apply (rule T[OF fg_sum_eq[symmetric] fg_exists fg_exists1' _ _ edge_in End_closed_E
        _ edge_in2 edge_in1 edge_in1' _ reduced_E ea ea1 ea1' ea2 ctx])
    using fg_exists1 fg_exists1' fg_exists2 assms id_def by auto
  then obtain h'' where "h'' = h1' + h2" "h'' \<noteq> bot" "eff_acyclic' h''" "h \<lesssim>\<^sub>S h''"
    by blast
  with ea' fg_sum_eq' show False by simp
qed

end
