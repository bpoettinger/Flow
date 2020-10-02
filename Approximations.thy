\<^marker>\<open>creator Bernhard Pöttinger\<close>

chapter \<open>Approximations\<close>
theory Approximations
imports Chain
begin

paragraph \<open>Summary\<close>
text \<open>This theory contains many approximations of terms involving flows, inflows, outflows,
capacities,... These approximations will be used to prove that terms are not 0 by relating
them to smaller terms that are known to be greater than 0.\<close>

paragraph \<open>Major Definitions\<close>
text \<open>
-@{term segment_fg}: analogous definition to segment to describe path segments of convoluted
  paths in flow graphs
- @{term len_segment_fg}: extends@{term segment_fg} by imposing an upper bound on the path segments
- @{term alt_cap_fg}: capacity function to be used along convoluted paths
- @{term alt_cap_hd_fg}: same as @{term alt_cap_fg} but determines current subgraph based on head instead of subset
  relation\<close>

abbreviation "segment_fg h ys \<equiv> set ys \<subseteq> dom_fg h \<and> ys \<noteq> []"
abbreviation "len_segment_fg h ys \<equiv> set ys \<subseteq> dom_fg h \<and> ys \<noteq> [] \<and> length ys \<le> card (dom_fg h)"
abbreviation "alt_cap_fg h1 h2 xs y \<equiv> (
  if set xs \<subseteq> dom_fg h1 then cap_fg h1 (hd (xs @ [y])) y else
  if set xs \<subseteq> dom_fg h2 then cap_fg h2 (hd (xs @ [y])) y else
  0)"
abbreviation "alt_cap_hd_fg h1 h2 x y \<equiv> (
  if x \<in> dom_fg h1 then cap_fg h1 x y else
  if x \<in> dom_fg h2 then cap_fg h2 x y else
  0)"

lemma alt_cap_hd_sym: "dom_fg h1 \<inter> dom_fg h2 = {} \<Longrightarrow> alt_cap_hd_fg h1 h2 x y = alt_cap_hd_fg h2 h1 x y"
  by auto

lemma alt_cap_hd_fg_sym':
  shows "dom_fg h1 \<inter> dom_fg h2 = {} \<Longrightarrow> alt_cap_hd_fg h1 h2 = alt_cap_hd_fg h2 h1"
  by (intro ext, auto)

section \<open>Unrolling the flow equation\<close>

text \<open>@{cite \<open>lem. 6\<close> krishna19b}: expand the flow equation into sums over finitely many paths.
  Later we will be able to prove that the second big-sum (the one involving flow f) is 0 in certain
  contexts, therefore, we will be able to straight-forwardly calculate the flow given a graph and
  inflow (because this representation of the flow equation then is no longer recursively defined!).\<close>

lemma unroll_flow_eq:
  assumes "l \<ge> 1" "flow_eq2' N e f i" "\<forall>x y. e x y \<in> E" "End_closed E" "n \<in> N" "finite N"
    "(\<lambda>_. 0) \<in> E"
  shows "f n = i n + (\<Sum>ns \<in> l_lists N l. (chain e ns n) (i (hd ns)))
                   + (\<Sum>ns \<in> k_lists N l. (chain e ns n) (f (hd ns)))"
  using assms
proof (induction l rule: nat_induct_at_least)
  case base
  have "l_lists N (Suc 0) = {}" unfolding l_lists_def by auto
  moreover have "k_lists N (Suc 0) = {[l] | l. l \<in> N}" unfolding k_lists_def
  proof (standard,goal_cases)
    case 1
    then show ?case by (auto, case_tac x, auto)
  next
    case 2 then show ?case by auto
  qed
  moreover have "f n = i n + (\<Sum>n'\<in>N. e n' n (f n'))"
    using base unfolding flow_eq2'_def flow_eq'_def by simp
  ultimately show ?case
    using base by (auto intro: sum.reindex_cong[symmetric,where l="\<lambda>x. [x]"] inj_onI)
next
  case (Suc l)
  have *: "(\<lambda>n. i n + (\<Sum>n'\<in>N. e n' n (f n'))) = f on N"
    using Suc unfolding flow_eq2'_def flow_eq'_def by simp

  have **: "(\<Sum>ns\<in>k_lists N l. chain e ns n (f (hd ns))) =
            (\<Sum>ns\<in>k_lists N l. chain e ns n (i (hd ns) + (\<Sum>n'\<in>N. e n' (hd ns) (f n'))))"
    unfolding k_lists_def
    using * Suc
    by (auto simp: set_hd_in)

  have ***: "(\<Sum>ns\<in>k_lists N l. chain e ns n (i (hd ns)   + (\<Sum>n'\<in>N. e n' (hd ns) (f n')))) =
             (\<Sum>ns\<in>k_lists N l. chain e ns n (i (hd ns))) + (\<Sum>ns\<in>k_lists N l. chain e ns n (\<Sum>n'\<in>N. e n' (hd ns) (f n')))"
  proof -
    have "(\<Sum>ns\<in>k_lists N l. chain e ns n (i (hd ns) + (\<Sum>n'\<in>N. e n' (hd ns) (f n')))) =
          (\<Sum>ns\<in>k_lists N l. chain e ns n (i (hd ns)) + chain e ns n (\<Sum>n'\<in>N. e n' (hd ns) (f n')))"
      apply (rule sum.cong[OF _ endo_sum_closed], simp)
      apply (rule endo_chain_closed_nonempty)
      using Suc unfolding k_lists_def by (auto simp add: id_def)
    then show ?thesis
      by (simp add: sum.distrib)
  qed
    
  have "f n = i n + (\<Sum>ns\<in>l_lists N l. chain e ns n (i (hd ns)))
                          + (\<Sum>ns\<in>k_lists N l. chain e ns n (f (hd ns)))"
    using Suc by simp
  also have "... = i n + (\<Sum>ns\<in>l_lists N l. chain e ns n (i (hd ns)))
                       + (\<Sum>ns\<in>k_lists N l. chain e ns n (i (hd ns)))
                       + (\<Sum>ns\<in>k_lists N l. chain e ns n (\<Sum>n'\<in>N. e n' (hd ns) (f n')))"
    using ** *** by (simp add: algebra_simps)
  also have "... = i n + (\<Sum>ns\<in>l_lists N (Suc l). chain e ns n (i (hd ns)))
                       + (\<Sum>ns\<in>k_lists N l. chain e ns n (\<Sum>n'\<in>N. e n' (hd ns) (f n')))"
    using l_lists_k_lists_union[of l N] sum.union_disjoint[symmetric, of "l_lists N l" _
          "\<lambda>ns. chain e ns n (i (hd ns))"] l_lists_k_lists_disjoint[of l N]
          Suc l_lists_finite[of N l] k_lists_finite[of N l]
    by (auto simp: algebra_simps)
  also have "... = i n + (\<Sum>ns\<in>l_lists N (Suc l). chain e ns n (i (hd ns)))
                       + (\<Sum>ns\<in>k_lists N l. \<Sum>n'\<in>N. chain e ns n (e n' (hd ns) (f n')))"
    apply (simp, rule sum.cong, simp)
    using assms
    apply (auto elim!: endo_iterated_sum_closed[where E=E]
           intro!: endo_chain_closed_nonempty simp: k_lists_def)
    using Suc.hyps not_one_le_zero by blast
  also have "... = i n + (\<Sum>ns\<in>l_lists N (Suc l). chain e ns n (i (hd ns)))
                       + (\<Sum>ns\<in>k_lists N l. \<Sum>n'\<in>N. chain e (n'#ns) n (f n'))"
    apply (simp, rule sum.cong, simp, rule sum.cong, simp)
    subgoal for ns n
      using Suc apply (cases ns, auto) using k_lists_nonempty[of l ns N] by simp
    done
  also have "... = i n + (\<Sum>ns\<in>l_lists N (Suc l). chain e ns n (i (hd ns)))
                       + (\<Sum>(ns,n')\<in>k_lists N l \<times> N. chain e (n'#ns) n (f n'))"
    by (auto simp: sum.cartesian_product)
  also have "... = i n + (\<Sum>ns\<in>l_lists N (Suc l). chain e ns n (i (hd ns)))
                       + (\<Sum>ns\<in>k_lists N (Suc l). chain e ns n (f (hd ns)))"
    using k_lists_x_Suc[of l N] Suc
    apply (auto split: prod.splits)
    apply (rule sum.reindex_cong[symmetric, of "\<lambda>(ns,n). n#ns"])
      apply (auto intro: inj_onI)
    subgoal for ns
  proof -
    assume "ns \<in> k_lists N (Suc l)"
    then have *: "length (tl ns) = l" "hd ns \<in> N" "set (tl ns) \<subseteq> N" "ns \<noteq> []"
      unfolding k_lists_def apply (auto simp: set_hd_in)
      by (metis Suc.hyps \<open>ns \<in> k_lists N (Suc l)\<close> k_lists_nonempty(2) le_SucI list.set_sel subsetD)
    then have "tl ns \<in> k_lists N l" unfolding k_lists_def by simp
    then have "(hd ns)#(tl ns) \<in> (\<lambda>x. case x of (ns, n) \<Rightarrow> n # ns) ` (k_lists N l \<times> N)"
      using *(2) by auto
    then show "ns \<in> (\<lambda>x. case x of (ns, n) \<Rightarrow> n # ns) ` (k_lists N l \<times> N)"
      using *(4) by simp
  qed
  done
  finally show ?case .
qed

text \<open>Adapter lemma to @{thm unroll_flow_eq} for @{const flow_eq} of @{const flow_eq2'}\<close>

lemma unroll_flow_eq':
  assumes "l \<ge> 1" "flow_eq (fg N e f) i" "\<forall>x y. e x y \<in> E"
    "End_closed E" "n \<in> N" "finite N" "(\<lambda>_. 0) \<in> E"
  shows "f n = i n + (\<Sum>ns \<in> l_lists N l. (chain e ns n) (i (hd ns)))
                   + (\<Sum>ns \<in> k_lists N l. (chain e ns n) (f (hd ns)))"
  using assms
  apply transfer
  apply (auto split: if_splits)
  apply (rule unroll_flow_eq)
  by (auto simp: flow_eq2'_def)

section \<open>Simple Approximations between Nodes\<close>

text \<open>For each node its inflow is less equal its flow.\<close>

lemma inf_fg_le_flow_fg:
  fixes h :: "('n,'m :: pos_cancel_comm_monoid_add) fg"
  assumes "h \<noteq> bot" "n \<in> dom_fg h"
  shows "inf_fg h n \<le> flow_fg h n"
proof -
  have "flow_fg h n = inf_fg h n + (\<Sum>n'\<in>dom_fg h. edge_fg h n' n (flow_fg h n'))"
    using flow_eq_ne_bot[of h] assms by simp
  then show ?thesis
    using le_iff_add by blast
qed

text \<open>The inflow to a subgraph is greater equal the inflow to its supergraph (because it
additionally receives inflow from its sibling subgraphs when considered on its own)\<close>

lemma inf_fg_le_inf_fg:
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "h1 + h2 \<noteq> bot" "x \<in> dom_fg h1" "\<forall>x y. edge_fg h1 x y \<in> E"
  shows "inf_fg (h1 + h2) x \<le> inf_fg h1 x"
proof -
  have "inf_fg h1 x = inf_fg (h1 + h2) x + outf_fg h2 x"
    using flow_eq_to_sum[of h1 h2] assms by simp
  then show ?thesis
    by (simp add: le_iff_add)
qed

text \<open>Same as @{thm inf_fg_le_inf_fg} but for second summand.\<close>

lemma inf_fg_le_inf_fg2:
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "h1 + h2 \<noteq> bot" "x \<in> dom_fg h2" "\<forall>x y. edge_fg h2 x y \<in> E"
  shows "inf_fg (h1 + h2) x \<le> inf_fg h2 x"
  using inf_fg_le_inf_fg[of h2 h1 x E] assms by (simp add: algebra_simps)

text \<open>The flow to outside nodes along single edges is less equal the total outflow.\<close>

lemma edge_fg_flow_fg_le_outf_fg:
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "h \<noteq> bot" "x \<in> dom_fg h" "y \<in> -dom_fg h" "\<forall>x y. edge_fg h x y \<in> E"
  shows "edge_fg h x y (flow_fg h x) \<le> outf_fg h y"
proof -
  have "edge_fg h x y (flow_fg h x) \<le> (\<Sum>n'\<in>dom_fg h. edge_fg h n' y (flow_fg h n'))"
    apply (rule sum_insert_pos_monoid) using assms by auto
  also have "... = outf_fg h y"
    apply (rule outf_fg_unfold[symmetric])
    using assms by auto
  finally show ?thesis .
qed

text \<open>The outflow from h1 to a node in h2  is less equal h2's inflow to that node\<close>

lemma outf_fg_le_inf_fg:
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "h \<noteq> bot" "h = h1 + h2" "x \<in> dom_fg h2" "\<forall>x y. edge_fg h1 x y \<in> E"
  shows "outf_fg h1 x \<le> inf_fg h2 x"
proof -
  have "inf_fg h2 x = inf_fg h x + outf_fg h1 x"
    by (metis add.commute assms flow_eq_to_sum)
  then show ?thesis
    by (simp add: add_increasing)
qed

section \<open>Approximations of Chains\<close>

text \<open>chain2 can be approximated by capacities that contain the chain.\<close>

lemma chain2_le_cap'':
  fixes E :: "('b \<Rightarrow> 'b :: pos_cancel_comm_monoid_add) set"
  assumes "set xs \<subseteq> N" "length xs < k" "x \<in> N" "finite N" "\<forall>x y. e x y \<in> E" "End_closed E"
  shows "chain2 e x xs y z \<le> cap' k N e x y z"
proof -
  have "cap' k N e x y z = \<delta> x y z + (\<Sum>ns\<in>l_lists' N k. chain2 e x ns y) z"
    using cap'_unrolled_closed[of e E N x k y] assms by simp
  then have **: "cap' k N e x y z = \<delta> x y z + (\<Sum>ns\<in>l_lists' N k. chain2 e x ns y z)"
    by (subst (asm) plus_fun_apply_iterated[OF l_lists'_finite[OF \<open>finite N\<close>]], simp)
  have *: "xs \<in> l_lists' N k"
    using assms unfolding l_lists'_def by simp
  have "chain2 e x xs y z \<le> (\<Sum>ns\<in>l_lists' N k. chain2 e x ns y z)"
    by (fact sum_insert_pos_monoid[OF l_lists'_finite[OF \<open>finite N\<close>] *])
  also have "... \<le> \<delta> x y z + (\<Sum>ns\<in>l_lists' N k. chain2 e x ns y z)"
    by (simp add: add_increasing)
  finally show ?thesis
    using ** unfolding plus_fun_def by simp
qed

text \<open>chain can be approximated by capacities that contain the chain.\<close>

lemma chain_le_cap':
  fixes e :: "'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b :: pos_cancel_comm_monoid_add"
  assumes "set xs \<subseteq> N" "xs \<noteq> []" "length xs \<le> k" "finite N" "\<forall>x y. e x y \<in> E" "x \<le> x'"
    "End_closed E" "(\<lambda>_. 0) \<in> E" "id \<in> E"
  shows "chain e xs y x \<le> cap' k N e (hd (xs @ [y])) y x'"
proof -
  have "chain e xs y x = chain2 e (hd xs) (tl xs) y x"
    using chain_chain2 assms by metis
  also have "... \<le> cap' k N e (hd xs) y x"
    apply (rule chain2_le_cap''[of "tl xs" N k "hd xs" e E y x])
    using assms apply simp_all
      apply (simp add: list.set_sel(2) subset_iff)
     apply (metis diff_Suc_less le_neq_implies_less length_greater_0_conv less_imp_diff_less)
    by auto
  also have "... \<le> cap' k N e (hd xs) y x'"
    apply (rule pos_endo_mono'_closed[OF \<open>x \<le> x'\<close>])
    using assms by (auto elim: endo_cap')
  finally show ?thesis
    using assms by simp
qed

lemma chain_flow_fg_le_flow_fg:
  fixes E :: "('m \<Rightarrow> 'm :: pos_cancel_comm_monoid_add) set"
  assumes "h \<noteq> bot" "End_closed E" "\<forall>x y. edge_fg h x y \<in> E" "y \<in> dom_fg h" "set xs \<subseteq> dom_fg h"
    "id \<in> E" "(\<lambda>_. 0) \<in> E"
  shows "chain (edge_fg h) xs y (flow_fg h (hd (xs @ [y]))) \<le> flow_fg h y"
proof (cases xs)
case Nil
  then show ?thesis by simp
next
  case (Cons a xs)
  then have *: "flow_fg h y =
    inf_fg h y + (\<Sum>ns\<in>l_lists (dom_fg h) (length (a # xs)). chain (edge_fg h) ns y (inf_fg h (hd ns)))
               + (\<Sum>ns\<in>k_lists (dom_fg h) (length (a # xs)). chain (edge_fg h) ns y (flow_fg h (hd ns)))"
    using unroll_flow_eq[of "length (a # xs)" "dom_fg h" "edge_fg h" "flow_fg h" "inf_fg h" E y] assms
      nbot_fg_to_flow_eq2'[of h] by simp
  have "chain (edge_fg h) (a # xs) y (flow_fg h (hd (a # xs))) \<le> (\<Sum>ns\<in>k_lists (dom_fg h) (length (a # xs)). chain (edge_fg h) ns y (flow_fg h (hd ns)))"
    apply (rule sum_insert_pos_monoid[OF k_lists_finite[OF dom_fg_finite], of "a # xs" h "length (a # xs)"])
    using assms Cons unfolding k_lists_def
    by blast
  also have "... \<le> flow_fg h y"
    using * by (simp add: add_increasing)
  finally show ?thesis
    using Cons by simp
qed

lemma cap'_superset_iterations:
  fixes E :: "('b \<Rightarrow> 'b :: pos_cancel_comm_monoid_add) set"
  assumes "finite N'" "N \<subseteq> N'" "k \<le> k'" "End_closed E" "\<forall>x y. e x y \<in> E" "x \<in> N"
  shows "cap' k N e x y z \<le> cap' k' N' e x y z"
  using assms
proof (induction N' rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert a F)
  have fin: "finite N"
    using assms finite_subset by blast
  have fin2: "finite (insert a F)"
    using insert by simp

  have "cap' k N e x y z = (\<delta> x y + (\<Sum>ns \<in> l_lists' N k. chain2 e x ns y)) z"
    apply (subst cap'_unrolled_closed) using assms fin by auto
  also have "... = \<delta> x y z + (\<Sum>ns \<in> l_lists' N k. chain2 e x ns y) z"
    by simp
  also have "... = \<delta> x y z + (\<Sum>ns \<in> l_lists' N k. chain2 e x ns y z)"
    by (subst plus_fun_apply_iterated[OF l_lists'_finite[OF fin]], simp)
  also have "... \<le> \<delta> x y z + (\<Sum>ns \<in> l_lists' (insert a F) k'. chain2 e x ns y z)"
    by (rule add_left_mono[OF sum_mono2[OF l_lists'_finite[OF fin2] l_lists'_mono[OF \<open>N \<subseteq> insert a F\<close> \<open>k \<le> k'\<close>]]], simp)
  also have "... = \<delta> x y z + (\<Sum>ns \<in> l_lists' (insert a F) k'. chain2 e x ns y) z"
    using plus_fun_apply_iterated[OF l_lists'_finite[OF fin2]] by metis
  also have "... = cap' k' (insert a F) e x y z"
    apply (subst cap'_unrolled_closed) using insert fin2 by auto
  finally show ?case by simp
qed
  
lemma cap_superset:
  fixes E :: "('b \<Rightarrow> 'b :: pos_cancel_comm_monoid_add) set"
  assumes "finite N'" "N \<subseteq> N'" "k \<le> k'" "End_closed E" "\<forall>x y. e x y \<in> E" "x \<in> N"
  shows "cap N e x y \<le> cap N' e x y"
  using assms
  by (meson cap'_superset_iterations card_mono le_funI)

lemma alternating_chains'_mono:
  assumes "alternating P Q xss"
      "\<And>xs y x x'. P xs \<Longrightarrow> x \<le> x' \<Longrightarrow> f xs y x \<le> g xs y x'"
      "\<And>xs y x x'. Q xs \<Longrightarrow> x \<le> x' \<Longrightarrow> f xs y x \<le> g xs y x'" "u \<le> v"
  shows "chains' f xss y u \<le> chains' g xss y v"
  using assms
proof (induction xss arbitrary: P Q f g u v)
  case Nil
  then show ?case by simp
next
  case (Cons xs xss)
  then show ?case
    by (cases xss, auto)
qed








lemma chain_inf_fg_le_flow_fg:
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "h \<noteq> bot" "End_closed E" "\<forall>x y. edge_fg h x y \<in> E"
    "set xs \<subseteq> dom_fg h" "y \<in> dom_fg h" "id \<in> E" "(\<lambda>_. 0) \<in> E"
  shows "chain (edge_fg h) xs y (inf_fg h (hd (xs @ [y]))) \<le> flow_fg h y"
proof (cases "length xs \<ge> 1")
  case True
  have kl: "xs \<in> k_lists (dom_fg h) (length xs)"
    unfolding k_lists_def using assms by simp

  have *: "flow_eq2' (dom_fg h) (edge_fg h) (flow_fg h) (inf_fg h)"
    using \<open>h \<noteq> bot\<close> nbot_fg_to_flow_eq2' by metis

  let ?f = "\<Sum>ns\<in>l_lists (dom_fg h) (length xs). chain (edge_fg h) ns y (inf_fg h (hd ns))"
  let ?g = "\<Sum>ns\<in>k_lists (dom_fg h) (length xs). chain (edge_fg h) ns y (flow_fg h (hd ns))"

  have flw: "flow_fg h y = inf_fg h y + ?f + ?g"
    apply (rule unroll_flow_eq[of "length xs" "dom_fg h" "edge_fg h" "flow_fg h" "inf_fg h" E y])
    using assms * True by auto

  have "chain (edge_fg h) xs y (inf_fg h (hd (xs @ [y]))) \<le> chain (edge_fg h) xs y (flow_fg h (hd (xs @ [y])))"
    apply (rule chain_mono[OF inf_fg_le_flow_fg]) using assms by (simp_all add: set_hd_in)
  also have "... \<le> (\<Sum>ns\<in>k_lists (dom_fg h) (length xs). chain (edge_fg h) ns y (flow_fg h (hd (ns @ [y]))))"
    by (fact sum_insert_pos_monoid[OF k_lists_finite[OF dom_fg_finite] kl])
  also have "... = ?g"
    apply (rule sum.cong, simp)
    using assms True unfolding k_lists_def
    by (auto simp: hd_append assms)
  also have "... \<le> (inf_fg h y + ?f) + ?g"
    by (simp add: add_increasing)
  finally show ?thesis
    using flw by simp
next
  case False
  then have "xs = []" by (metis One_nat_def Suc_leI length_greater_0_conv)
  then show ?thesis using inf_fg_le_flow_fg assms by simp
qed

lemma chain_inf_fg_le_flow_fg':
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "h \<noteq> bot" "End_closed E" "\<forall>x y. edge_fg h x y \<in> E" "y \<in> dom_fg h" "k \<ge> 1" "id \<in> E" "(\<lambda>_. 0) \<in> E"
  shows "inf_fg h y + (\<Sum>xs \<in> l_lists (dom_fg h) k. chain (edge_fg h) xs y (inf_fg h (hd (xs @ [y])))) \<le> flow_fg h y"
proof -
  have *: "flow_eq2' (dom_fg h) (edge_fg h) (flow_fg h) (inf_fg h)"
    using \<open>h \<noteq> bot\<close> nbot_fg_to_flow_eq2' by metis

  let ?f = "\<Sum>ns\<in>l_lists (dom_fg h) k. chain (edge_fg h) ns y (inf_fg h (hd ns))"
  let ?f' = "\<Sum>ns\<in>l_lists (dom_fg h) k. chain (edge_fg h) ns y (inf_fg h (hd (ns @ [y])))"
  let ?g = "\<Sum>ns\<in>k_lists (dom_fg h) k. chain (edge_fg h) ns y (flow_fg h (hd ns))"
  let ?h = "inf_fg h y"

  have flw: "flow_fg h y = ?h + ?f + ?g"
    apply (rule unroll_flow_eq[of k "dom_fg h" "edge_fg h" "flow_fg h" "inf_fg h" E y])
    using assms * by auto

  have "?h + ?f' = ?h + ?f"
    apply (subst sum.cong, simp)
    using assms unfolding l_lists_def
    by (auto simp: hd_append assms)
  also have "...\<le> ?h + ?f + ?g"
    using le_iff_add by blast
  finally show ?thesis
    using flw by auto
qed

lemma chain_inf_fg_le_inf_fg:
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "h \<noteq> bot" "End_closed E" "\<forall>x y. edge_fg h1 x y \<in> E" "set xs \<subseteq> dom_fg h1"
    "y \<in> dom_fg h2" "h = h1 + h2" "xs \<noteq> []" "id \<in> E" "(\<lambda>_. 0) \<in> E"
  shows "chain (edge_fg h1) xs y (inf_fg h1 (hd (xs @ [y]))) \<le> inf_fg h2 y"
  using assms
proof (induction xs rule: induct_list012) (* cases actually... *)
  case 1
  then show ?case by simp
next
  case (2 x)
  have "edge_fg h1 x y (inf_fg h1 x) \<le> edge_fg h1 x y (flow_fg h1 x)"
    apply (rule pos_endo_mono'_closed[OF inf_fg_le_flow_fg, where E=E]) using 2 by auto
  also have "... \<le> outf_fg h1 y"
    apply (rule edge_fg_flow_fg_le_outf_fg) using assms 2 apply auto
    by (simp_all add: dom_fg_plus_fg_iff)
  also have "... \<le> inf_fg h2 y"
    apply (rule outf_fg_le_inf_fg) using assms 2 by auto
  finally show ?case by simp
next
  case (3 x y' zs)

  let ?xs = "x # y' # zs"
  let ?e1 = "edge_fg h1"
  let ?i1 = "inf_fg h1"
  let ?f1 = "flow_fg h1"

  have "chain ?e1 ?xs y (?i1 (hd (butlast ?xs @ [last ?xs]))) = ?e1 (last ?xs) y (chain ?e1 (butlast ?xs) (last ?xs) (?i1 (hd ((butlast ?xs) @ [last ?xs]))))"
    by (rule chain_append1, simp)
  also have "... \<le> ?e1 (last ?xs) y (?f1 (last ?xs))"
    apply (rule pos_endo_mono'_closed[OF chain_inf_fg_le_flow_fg, of h1 E "butlast ?xs" "last ?xs" "?e1 (last ?xs) y" E])
    using 3 unfolding id_def by (auto, simp add: in_set_butlastD subset_code(1))
  also have "... \<le> outf_fg h1 y"
    apply (rule edge_fg_flow_fg_le_outf_fg) using assms 3 apply auto
    by (simp_all add: dom_fg_plus_fg_iff)
  also have "... \<le> inf_fg h2 y"
    apply (rule outf_fg_le_inf_fg) using assms 3 by auto
  finally show ?case
    by simp
qed

lemma cap'_unrolled_closed':
  assumes "finite N" "x \<in> N" "End_closed E" "\<forall>x y. e x y \<in> E" "id \<in> E" "(\<lambda>_. 0) \<in> E"
  shows "cap' k N e x y = \<delta> x y + (\<Sum>ns \<in> l_lists' N k. chain e (x # ns) y)"
proof -
  have "cap' k N e x y = \<delta> x y + (\<Sum>ns\<in>l_lists' N k. chain2 e x ns y)"
    using cap'_unrolled_closed[of e E N x k y] assms
    unfolding \<delta>_def
    by auto
  then show ?thesis
    by (simp, subst sum.cong[OF _ chain2_chain'], simp_all)
qed

lemma Cons_l_lists'_le_l_lists: "x \<in> N \<Longrightarrow> (Cons x) ` l_lists' N k \<subseteq> l_lists N (k + 1)"
  unfolding l_lists_def l_lists'_def image_def
  by auto

lemma cap'_inf_le_flow_eq:
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "flow_eq2' N e f i" "\<forall>x y. e x y \<in> E" "End_closed E" "k \<ge> 1" "finite N" "x \<in> N" "y \<in> N"
    "id \<in> E" "(\<lambda>_. 0) \<in> E"
  shows "cap' k N e x y (i x) \<le> f y"
proof -
  have S: "f y = i y + (\<Sum>ns\<in>l_lists N (k + 1). chain e ns y (i (hd ns))) + (\<Sum>ns\<in>k_lists N (k + 1). chain e ns y (f (hd ns)))"
    using unroll_flow_eq[of "k + 1" N e f i E y] assms by simp

  have "cap' k N e x y (i x) = \<delta> x y (i x) + (\<Sum>ns\<in>l_lists' N k. chain e (x # ns) y (i x))"
    using cap'_unrolled_closed'[of N x E e k y] assms
    unfolding \<delta>_def
    apply auto
    using plus_fun_apply_iterated[OF l_lists'_finite[where X=N and l=k]] by metis
  also have "... = \<delta> x y (i x) + (\<Sum>ns\<in>(Cons x) ` l_lists' N k. chain e ns y (i (hd ns)))"
    apply (simp, rule sum.reindex_cong[where l=tl])
    unfolding l_lists'_def
      apply (auto intro: inj_onI)
    unfolding image_def by fastforce
  also have "... \<le> i y + (\<Sum>ns\<in>(Cons x) ` l_lists' N k. chain e ns y (i (hd ns)))"
    unfolding \<delta>_def by (simp add: add_right_mono)
  also have "... \<le> i y + (\<Sum>ns\<in>l_lists N (k + 1). chain e ns y (i (hd ns)))"
    apply (rule add_left_mono[OF sum_mono2[OF l_lists_finite[OF \<open>finite N\<close>] Cons_l_lists'_le_l_lists]])
    using assms by auto
  also have "... \<le> f y"
    using S le_iff_add by blast
  finally show ?thesis .
qed

lemma cap'_inf_fg_le_flow_fg:
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "h \<noteq> bot" "\<forall>x y. edge_fg h x y \<in> E" "End_closed E" "x \<in> dom_fg h"
    "y \<in> dom_fg h" "k \<ge> 1" "id \<in> E" "(\<lambda>_. 0) \<in> E"
  shows "cap' k (dom_fg h) (edge_fg h) x y (inf_fg h x) \<le> flow_fg h y"
proof -
  have T: "flow_eq2' (dom_fg h) (edge_fg h) (flow_fg h) (inf_fg h)"
    using assms nbot_fg_to_flow_eq2' by blast
  show ?thesis
    apply (rule cap'_inf_le_flow_eq[OF T, of E])
    using assms by simp_all
qed

lemma cap_fg_inf_fg_le_flow_fg:
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "h \<noteq> bot" "\<forall>x y. edge_fg h x y \<in> E" "End_closed E" "x \<in> dom_fg h"
    "y \<in> dom_fg h" "id \<in> E" "(\<lambda>_. 0) \<in> E"
  shows "cap_fg h x y (inf_fg h x) \<le> flow_fg h y"
  apply (rule cap'_inf_fg_le_flow_fg[where E=E], simp_all add: assms)
  by (metis Suc_leI assms(5) card_gt_0_iff dom_fg_finite equals0D)

lemma l_lists_to_double_sum:
  assumes "finite X" "k \<ge> 1"
  shows "(\<Sum>xs \<in> l_lists X (k + 1). f xs) = (\<Sum>x \<in> X. f [x] + (\<Sum>xs \<in> l_lists X k. f (xs @ [x])))"
proof -
  have *: "l_lists {} (k + 1) = {}"
    unfolding l_lists_def by simp

  let ?X1 = "{ns @ [n] |ns n. (ns, n) \<in> l_lists X k \<times> X}"
  let ?X0 = "{[n'] |n'. n' \<in> X}"

  have eq: "?X1 = {n # ns | ns n. (ns, n) \<in> l_lists X k \<times> X}"
    unfolding l_lists_def
    apply auto
    subgoal for ns n
      apply (rule exI[where x="tl ns @ [n]"])
      apply (rule exI[where x="hd ns"])
      apply auto
        apply (metis Suc_le_lessD length_greater_0_conv list.exhaust_sel)
       apply (metis Suc_le_lessD in_mono length_greater_0_conv list.set_sel(2))
      by (simp add: set_hd_in)
    subgoal for ns n
      apply (rule exI[where x="butlast (n # ns)"])
      apply (rule exI[where x="last ns"])
      apply auto
      by (simp add: in_mono in_set_butlastD)
    done

  have "?X1 = (\<lambda>(xs,x). xs @ [x]) ` (l_lists X k \<times> X)"
    unfolding l_lists_def
    by auto
  then have F1: "finite ?X1"
    using finite_imageI[OF finite_cartesian_product[OF l_lists_finite[OF \<open>finite X\<close>, of k] \<open>finite X\<close>], of "\<lambda>(xs,x). xs @ [x]"]
    unfolding l_lists_def
    by simp
  have "?X0 = (\<lambda>x. [x]) ` X"
    by auto
  then have F0: "finite ?X0"
    using finite_imageI[OF \<open>finite X\<close>]
    by auto

  have "\<forall>xs \<in> ?X0. length xs = 1"
    by auto
  moreover have "\<forall>xs \<in> ?X1. length xs \<ge> 2"
    unfolding l_lists_def by auto
  ultimately have D: "?X1 \<inter> ?X0 = {}"
    by fastforce

  have "(\<Sum>xs \<in> l_lists X (k + 1). f xs) = (\<Sum>xs \<in> ?X1 \<union> ?X0. f xs)"
    using assms l_lists_x_Suc[of k X] eq by simp
  also have "... = (\<Sum> xs \<in> ?X1. f xs) + (\<Sum>xs \<in> ?X0. f xs)"
    by (rule sum.union_disjoint[OF F1 F0 D])
  also have "... = (\<Sum>(x,xs) \<in> X \<times> l_lists X k. f  (xs @ [x])) + (\<Sum>xs \<in> ?X0. f xs)"
    apply (subst sum.reindex_cong[where l="\<lambda>(x,xs). xs @ [x]" and B="X \<times> l_lists X k"])
    by (auto intro: inj_onI)
  also have "... = (\<Sum>x \<in> X. \<Sum>xs \<in> l_lists X k. f (xs @ [x])) + (\<Sum>xs \<in> ?X0. f xs)"
    by (subst sum.cartesian_product, simp)
  also have "... = (\<Sum>x \<in> X. \<Sum>xs \<in> l_lists X k. f (xs @ [x])) + (\<Sum>x \<in> X. f [x])"
    apply (subst sum.reindex_cong[where l="\<lambda>x. [x]" and A="?X0" and B=X])
    by (auto intro: inj_onI)
  also have "... = (\<Sum>x \<in> X. f [x] + (\<Sum>xs \<in> l_lists X k. f (xs @ [x])))"
    by (metis (no_types, lifting) add.commute sum.cong sum.distrib)
  finally show ?thesis .
qed

lemma cap_fg_inf_fg_le_outf_fg:
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "h \<noteq> bot" "x \<in> dom_fg h" "y \<in> -dom_fg h" "End_closed E"
    "\<forall>x y. edge_fg h x y \<in> E" "dom_fg h \<noteq> {}" "id \<in> E" "(\<lambda>_. 0) \<in> E"
  shows "cap_fg h x y (inf_fg h x) \<le> outf_fg h y"
proof -
  have D1: "card (dom_fg h) \<ge> 1"
    using assms by (simp add: Suc_leI card_gt_0_iff)
  then obtain k where *[simp]: "k + 1 = card (dom_fg h)"
    using le_add_diff_inverse2 by blast

  have "cap_fg h x y (inf_fg h x) = (\<Sum>xs\<in>l_lists' (dom_fg h) (card (dom_fg h)). chain2 (edge_fg h) x xs y (inf_fg h x))"
    using cap_unrolled_closed[of "edge_fg h" E "dom_fg h" x y] assms plus_fun_apply_iterated[OF l_lists'_finite[OF dom_fg_finite]] *
    unfolding \<delta>_def
    by auto
  also have "... = (\<Sum>xs\<in>l_lists' (dom_fg h) (card (dom_fg h)). chain (edge_fg h) (x # xs) y (inf_fg h x))"
    by (subst sum.cong[OF _ chain2_chain], simp_all)
  also have "... = (\<Sum>xs\<in>Cons x ` l_lists' (dom_fg h) (card (dom_fg h)). chain (edge_fg h) xs y (inf_fg h (hd xs)))"
    apply (rule sum.reindex_cong[where l=tl])
    unfolding l_lists'_def
      apply (auto intro: inj_onI)
    unfolding image_def by fastforce
  also have "... \<le> (\<Sum>xs\<in>l_lists (dom_fg h) (card (dom_fg h) + 1). chain (edge_fg h) xs y (inf_fg h (hd xs)))"
    apply (rule sum_mono2[OF l_lists_finite[OF dom_fg_finite] Cons_l_lists'_le_l_lists])
    using assms by auto
  also have "... = (\<Sum>x \<in> dom_fg h. edge_fg h x y (inf_fg h x) + (\<Sum>xs \<in> l_lists (dom_fg h) (card (dom_fg h)). chain (edge_fg h) (xs @ [x]) y (inf_fg h (hd (xs @ [x])))))"
    by (subst l_lists_to_double_sum[OF dom_fg_finite D1], simp)
  also have "... = (\<Sum>x \<in> dom_fg h. edge_fg h x y (inf_fg h x) + (\<Sum>xs \<in> l_lists (dom_fg h) (card (dom_fg h)). edge_fg h x y (chain (edge_fg h) xs x (inf_fg h (hd (xs @ [x]))))))"
    by (metis (no_types, lifting) chain.simps(2) chain_append_nonempty hd_append2 impossible_Cons le_numeral_extra(3) list.sel(1) list.size(3) sum.cong)
  also have "... = (\<Sum>x \<in> dom_fg h. edge_fg h x y (inf_fg h x + (\<Sum>xs \<in> l_lists (dom_fg h) (card (dom_fg h)). chain (edge_fg h) xs x (inf_fg h (hd (xs @ [x]))))))"
    apply (rule sum.cong, simp)
    subgoal for x
      apply (subst fun_dist_right''[symmetric, OF l_lists_finite[OF dom_fg_finite], where g="edge_fg h x y" and E=E])
      using assms apply simp_all
      by (rule endo_sum_closed[symmetric, where E=E], simp_all add: assms)
    done
  also have "... \<le> (\<Sum>x \<in> dom_fg h. edge_fg h x y (flow_fg h x))"
    apply (rule sum_mono)
    subgoal for x
      apply (rule pos_endo_mono'_closed[OF chain_inf_fg_le_flow_fg'[of h E x "card (dom_fg h)"]])
      using assms D1 by auto
    done
  also have "... = outf_fg h y"
    apply (rule outf_fg_unfold[symmetric])
    using assms by auto
  finally show ?thesis .
qed

lemma cap'_fg_inf_fg_fg_le_inf_fg:
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "h \<noteq> bot" "h = h1 + h2" "xs \<noteq> []" "\<forall>x y. edge_fg h x y \<in> E" "End_closed E"
    "\<forall>x y. edge_fg h1 x y \<in> E" "\<forall>x y. edge_fg h2 x y \<in> E" "id \<in> E" "(\<lambda>_. 0) \<in> E"
     "id \<in> E" "set xs \<subseteq> dom_fg h1" "y \<in> dom_fg h2"
   shows "cap_fg h1 (hd xs) y (inf_fg h1 (hd xs)) \<le> inf_fg h2 y"
proof -
  have "cap_fg h1 (hd xs) y (inf_fg h1 (hd xs)) \<le> outf_fg h1 y"
    apply (rule cap_fg_inf_fg_le_outf_fg)
    using assms apply auto
    using plus_fg_dom_disj by fastforce
  also have "... \<le> inf_fg h2 y"
    apply (rule outf_fg_le_inf_fg[of h])
    using assms by auto
  finally show ?thesis .
qed

lemma cap'_fg_inf_fg_fg_le_inf_fg2:
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "h \<noteq> bot" "h = h1 + h2" "xs \<noteq> []" "\<forall>x y. edge_fg h x y \<in> E" "End_closed E"
    "\<forall>x y. edge_fg h1 x y \<in> E" "\<forall>x y. edge_fg h2 x y \<in> E"
     "id \<in> E" "set xs \<subseteq> dom_fg h1" "y \<in> dom_fg h2" "(\<lambda>_. 0) \<in> E"
   shows "cap_fg h1 (hd xs) y (inf_fg h (hd xs)) \<le> inf_fg h2 y"
proof -
  have "cap_fg h1 (hd xs) y (inf_fg (h1 + h2) (hd xs)) \<le> cap_fg h1 (hd xs) y (inf_fg h1 (hd xs))"
    apply (rule pos_endo_mono'_closed[OF inf_fg_le_inf_fg])
    using assms apply simp_all
    using hd_in_set apply blast
    using assms by (auto elim: endo_cap')
  also have "... \<le> inf_fg h2 y"
    apply (rule cap'_fg_inf_fg_fg_le_inf_fg)
    using assms by auto
  finally show ?thesis using assms by simp
qed

lemma alternating_chains'_cong:
  assumes "alternating' P Q xss ys" "\<And>xs y. P xs \<Longrightarrow> f xs y = g xs y" "\<And>xs y. Q xs \<Longrightarrow> f xs y = g xs y"
  shows "chains' f xss y a = chains' g xss y a"
  using assms by (induction xss arbitrary: a P Q rule: induct_list012, auto)

lemma alternating_chains_cong:
  assumes "alternating P Q xss" "\<And>xs y. P xs \<Longrightarrow> f xs y = g xs y" "\<And>xs y. Q xs \<Longrightarrow> f xs y = g xs y"
  shows "chains' f xss y a = chains' g xss y a"
  using assms by (induction xss arbitrary: a P Q rule: induct_list012, auto)

lemma chains'_cap_fg_inf_fg_le_inf_fg':
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "alternating' (P h1) (P h2) xss ys" "h \<noteq> bot" "h = h1 + h2" "xss \<noteq> []"
    "\<forall>x y. edge_fg h x y \<in> E" "End_closed E" "\<forall>x y. edge_fg h1 x y \<in> E"
    "\<forall>x y. edge_fg h2 x y \<in> E" "xss \<noteq> []" "\<forall>xs \<in> set xss. xs \<noteq> []"
    "\<And>xs. P h1 xs \<Longrightarrow> set xs \<subseteq> dom_fg h1" "\<And>xs. P h2 xs \<Longrightarrow> set xs \<subseteq> dom_fg h2"
    "id \<in> E" "hd ys \<in> dom_fg (alt h2 h1 xss)" "(\<lambda>_. 0) \<in> E"
  shows "chains' (alt_cap_fg h1 h2) xss (hd ys) (inf_fg h1 (hd (hd xss)))
    \<le> inf_fg (alt h2 h1 xss) (hd ys)"
  using assms
proof (induction xss rule: alternating'_induct'_symmetric[where a=h1 and b=h2])
  case (empty h1 h2)
  then show ?case by simp
next
  case (base h1 h2 xs)
  then show ?case
    apply simp
    apply (rule cap'_fg_inf_fg_fg_le_inf_fg[simplified, where h=h and E=E])
    using assms by simp_all
next
  case (step h1 h2 xs ys' zss)
  then have swp: "h2 + h1 = h1 + h2"
    by (simp add: algebra_simps)

  have eq: "\<And>xsa ya. xsa \<noteq> [] \<Longrightarrow> alt_cap_fg h1 h2 xsa ya = alt_cap_fg h2 h1 xsa ya"
    apply (case_tac "set xsa \<subseteq> dom_fg h1")
     apply (case_tac "set xsa \<subseteq> dom_fg h2")
      apply simp_all
    using plus_fg_dom_disj[of h1 h2] \<open>h = h1 + h2\<close> \<open>h \<noteq> bot\<close>
    by (meson disjoint_iff_not_equal hd_in_set subset_code(1))

  from step show ?case
    apply simp
    apply (rule order_trans)
     apply (rule pos_endo_mono'_closed[OF cap'_fg_inf_fg_fg_le_inf_fg, simplified, where E=E])
    apply blast
    apply blast
    apply blast
    apply blast
    apply blast
    apply blast
    apply blast
    unfolding id_def apply blast
    apply (fold id_def)
         apply auto[1]
       apply (meson hd_in_set subsetD)
       apply (meson hd_in_set subsetD)
       apply (meson hd_in_set subsetD)
      apply (rule endo_chains')
        apply simp_all
     apply (intro conjI impI allI)
       apply (rule endo_cap', simp_all)
       apply (rule endo_cap', simp_all)
       apply (rule endo_cap', simp_all)
    apply (subst chains'_cong[where g="alt_cap_fg h2 h1"])
     apply (subgoal_tac "xsa \<noteq> []")
    using eq apply auto[1]
     apply auto[1]
    using step.IH[simplified swp] unfolding id_def by auto
qed

lemma cap'_fg_le_inf_fg_le_inf_fg:
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "h \<noteq> bot" "h = h1 + h2" "xs \<noteq> []" "\<forall>x y. edge_fg h x y \<in> E" "End_closed E"
    "\<forall>x y. edge_fg h1 x y \<in> E" "\<forall>x y. edge_fg h2 x y \<in> E" "id \<in> E"
    "set xs \<subseteq> dom_fg h1" "y \<in> dom_fg h2" "m \<le> inf_fg h1 (hd xs)" "(\<lambda>_. 0) \<in> E"
   shows "cap_fg h1 (hd xs) y m \<le> inf_fg h2 y"
proof -
  have "cap_fg h1 (hd xs) y m \<le> cap_fg h1 (hd xs) y (inf_fg h1 (hd xs))"
    apply (rule pos_endo_mono'_closed[OF \<open>m \<le> inf_fg h1 (hd xs)\<close>, where E=E])
     apply (rule endo_cap')
    using assms dom_fg_finite by blast+
  also have "... \<le> inf_fg h2 y"
    apply (rule cap'_fg_inf_fg_fg_le_inf_fg[where h=h and E=E])
    using assms by blast+
  finally show ?thesis .
qed

lemma alternating_inf_fg_flow_fg:
  fixes h1 h2 :: "('a,'b :: pos_cancel_comm_monoid_add) fg"
  assumes "h = h1 + h2" "h \<noteq> bot" "ys \<noteq> []"
  shows "alternating' (segment_fg h1) (segment_fg h2) xss ys \<Longrightarrow> inf_fg (alt h2 h1 xss) (hd ys) \<le> flow_fg h (hd ys)"
proof (induction xss rule: alternating'_induct'[where a=h1 and aa=h1 and b=h2 and bb=h2])
  case emptyP
  then show ?case
    using inf_fg_le_flow_fg[of h1 "hd ys"] flow_fg_plus_fg_on1'[of h1 h2 "hd ys"] plus_fg_ops_exist[of h1 h2] assms
    by force
next
  case emptyQ
  then show ?case
    using inf_fg_le_flow_fg[of h2 "hd ys"] flow_fg_plus_fg_on2'[of h1 h2 "hd ys"] plus_fg_ops_exist[of h1 h2] assms
    by force
next
  case (baseP xs)
  then show ?case
    using inf_fg_le_flow_fg[of h2 "hd ys"] flow_fg_plus_fg_on2'[of h1 h2 "hd ys"] plus_fg_ops_exist[of h1 h2] assms
    by force
next
  case (baseQ xs)
  then show ?case 
    using inf_fg_le_flow_fg[of h1 "hd ys"] flow_fg_plus_fg_on1'[of h1 h2 "hd ys"] plus_fg_ops_exist[of h1 h2] assms
    by force
next
  case (stepP x y' zs)
  then show ?case by simp
next
  case (stepQ x y' zs)
  then show ?case by simp
qed

abbreviation "alt_chain h1 h2 \<equiv> \<lambda>xs y. if set xs \<subseteq> dom_fg h1 then chain (edge_fg h1) xs y else chain (edge_fg h2) xs y"

lemma chains'_chain_inf_fg_le_inf_fg:
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "alternating' (segment_fg h1) (segment_fg h2) xss ys" "xss \<noteq> []" "h1 + h2 \<noteq> bot" "\<forall>x y. edge_fg h1 x y \<in> E"
    "End_closed E" "\<forall>x y. edge_fg h2 x y \<in> E" "(\<lambda>_. 0) \<in> E" "id \<in> E"
  shows "chains' (alt_chain h1 h2) xss (hd ys) (inf_fg h1 (hd (hd xss))) \<le> inf_fg (alt h2 h1 xss) (hd ys)"
  using assms
proof (induction xss rule: alternating'_induct'_symmetric'[where a=h1 and b=h2 and aa=h1 and bb=h2])
  case (empty a b)
  then show ?case by simp
next
  case (base h1 h2 h1 h2 xs)
  then show ?case apply simp
    using chain_inf_fg_le_inf_fg[of "h1 + h2" E h1 xs "hd ys" h2] base apply simp
    using hd_in_set by blast
next
  case (step h1 h2 h1 h2 xs ys' zss)

  have D: "dom_fg h1 \<inter> dom_fg h2 = {}" "dom_fg h1 \<noteq> {}" "dom_fg h2 \<noteq> {}"
    using step by auto
  then have S: "\<And>xs y. xs \<in> set (ys' # zss) \<Longrightarrow> (if set xs \<subseteq> dom_fg h1 then chain (edge_fg h1) xs y else chain (edge_fg h2) xs y) =
        (if set xs \<subseteq> dom_fg h2 then chain (edge_fg h2) xs y else chain (edge_fg h1) xs y)"
    using step apply auto
      apply (meson \<open>dom_fg h1 \<inter> dom_fg h2 = {}\<close> disjoint_iff_not_equal hd_in_set in_mono)
     apply (smt D alternating'_props disjoint_eq_subset_Compl inf.absorb_iff1 set_empty subset_trans)
    by (metis (no_types, lifting) alternating'_props in_mono)

  from step show ?case
    apply simp
    apply (rule order_trans[where y="chains' _ _ _ (inf_fg h2 (hd ys'))", OF pos_endo_mono'_closed[where f="chains' _ _ _" and E=E]])
    using  chain_inf_fg_le_inf_fg[of "h1 + h2" E h1 xs "hd ys'" h2] step hd_in_set apply (auto simp: algebra_simps)[1]
       apply blast
      apply (rule endo_chains'[OF \<open>End_closed E\<close>], auto simp: step intro!: endo_chain_closed)
    apply (subst chains'_cong[OF S], simp)
    by (simp add: algebra_simps step)
qed

lemma cap'_empty:
  shows "cap' k {} e x y = \<delta> x y"
  by (cases k, auto)

text \<open>an approximation with cap (sum k\_i) is too coarse, we need a slightly finer variant\<close>

lemma chains'_cap_inf_le_chain_sum:
  fixes h h1 h2 :: "('a,'b :: pos_cancel_comm_monoid_add) fg"
  assumes "alternating (segment_fg h1) (segment_fg h2) xss" 
    "h \<noteq> bot" "h = h1 + h2" "xss \<noteq> []" "\<forall>xs \<in> set xss. xs \<noteq> []" "y \<in> dom_fg (alt h2 h1 xss)"
    "\<forall>xs \<in> set xss. set xs \<subseteq> dom_fg h" "dom_fg h \<noteq> {}" "\<forall>x y. edge_fg h x y \<in> E" "\<forall>x y. edge_fg h1 x y \<in> E" "\<forall>x y. edge_fg h2 x y \<in> E" "End_closed E"
    "id \<in> E" "(\<lambda>_. 0) \<in> E" "z \<le> inf_fg h1 (hd (hd xss))"
  shows "chains' (alt_cap_fg h1 h2) xss y z \<le> (\<Sum>xs \<in> l_lists' (dom_fg h) (card (dom_fg h) * length xss). chain (edge_fg h) ((hd (hd xss)) # xs) y z)"
  using assms
proof (induction xss arbitrary: y z rule: alternating_induct'_symmetric[where a=h1 and b=h2])
  case empty
  then show ?case by simp
next
  case (base h1 h2 xs)
  then have "y \<in> dom_fg h2" by simp
  moreover have "hd xs \<in> dom_fg h1" using base hd_in_set by blast
  ultimately have N: "hd xs \<noteq> y" using base plus_fg_dom_disj[of h1 h2] by blast

  from base show ?case apply simp
    apply (subst cap'_unrolled_closed[OF _ dom_fg_finite])
    apply blast
    using hd_in_set apply blast
      apply (simp_all add: \<delta>_def N)
    apply (subst plus_fun_apply_iterated[OF l_lists'_finite[OF dom_fg_finite]])
    apply (subst chain2_chain)
    apply (subst sum.cong, simp, rule chain_cong''[OF edge_fg_plus_fg_on1[of h1 h2], symmetric], simp)
    unfolding l_lists'_def apply simp
    using hd_in_set apply blast
    apply (rule order_trans[OF sum_mono2[OF l_lists'_finite[where X="dom_fg (h1 + h2)" and l="card (dom_fg (h1 + h2))", OF dom_fg_finite]]], simp)
    unfolding l_lists'_def
      apply (smt Collect_mono Un_upper1 add.right_neutral card_Un_Int card_empty dom_fg_finite less_add_same_cancel1 less_trans not_gr_zero plus_fg_dom_disj subset_trans)
    by simp_all
next
  case (step h1 h2 xs ys zss)

  have D: "dom_fg h1 \<inter> dom_fg h2 = {}"
    using step by simp

  have **: "h2 + h1 = h1 + h2"
    using step by (simp add: ac_simps)

  have E: "\<And>xs. xs \<noteq> [] \<Longrightarrow> set xs \<subseteq> dom_fg h1 \<Longrightarrow> set xs \<subseteq> dom_fg h2 \<Longrightarrow> False"
  proof (goal_cases)
    case (1 xs)
    then have "xs = []" using D
      by (meson disjoint_iff_not_equal hd_in_set subset_code(1))
    then show ?case using 1 by simp
  qed

  from step have "hd xs \<in> dom_fg h1" using hd_in_set by blast
  moreover have ysh2: "hd ys \<in> dom_fg h2" using hd_in_set step by blast
  ultimately have DD: "hd xs \<noteq> hd ys" using D by auto

  let ?l' = "\<lambda>xs. (dropWhile (\<lambda>x. x \<noteq> hd ys) xs, takeWhile (\<lambda>x. x \<noteq> hd ys) xs)"

  have inj: "inj ?l'" by (intro injI, metis Pair_inject takeWhile_dropWhile_id)

  have subs: "(Cons (hd ys) ` l_lists' (dom_fg h2 \<union> dom_fg h1) (card (dom_fg h2 \<union> dom_fg h1) + card (dom_fg h2 \<union> dom_fg h1) * length zss)) \<times> l_lists' (dom_fg h1) (card (dom_fg h1)) \<subseteq>
        ?l' ` l_lists' (dom_fg h1 \<union> dom_fg h2) (card (dom_fg h1 \<union> dom_fg h2) + (card (dom_fg h1 \<union> dom_fg h2) + card (dom_fg h1 \<union> dom_fg h2) * length zss))"
  proof -
    show ?thesis
      unfolding l_lists'_def
      using dom_fg_finite[of h1] dom_fg_finite[of h2] plus_fg_dom_disj[of h1 h2] \<open>h = h1 + h2\<close> \<open>h \<noteq> bot\<close>
      unfolding image_def
      apply (auto simp: card_Un_disjoint algebra_simps \<open>hd ys \<in> dom_fg h2\<close>)
      subgoal for a b
        apply (rule exI[where x="a @ hd ys # b"], auto simp: \<open>hd ys \<in> dom_fg h2\<close>)
         apply (induction a, simp, simp)
        using D ysh2 apply blast
        apply (induction a, simp, simp)
        using D ysh2 by blast
      done
  qed

  from step show ?case
    apply simp
    apply (subst chains'_cong[where g="alt_cap_fg h2 h1"])
     apply clarsimp
    subgoal for xs a using E[of xs] by blast
    apply (rule order_trans[OF step.IH, simplified])
    using "**" apply presburger
    using "**" apply presburger
         apply blast
         apply blast
         apply blast
             apply blast
    using "**" apply presburger
         apply blast
         apply blast
         apply blast
         apply blast
    using "**" apply presburger
     apply (rule order_trans[OF pos_endo_mono'_closed[OF \<open>z \<le> inf_fg h1 (hd (hd (xs # ys # zss)))\<close>]])
    apply (rule endo_cap'[where E=E], simp_all add: id_def)
     apply (rule cap'_fg_inf_fg_fg_le_inf_fg[where h="h1 + h2" and E=E], simp_all add: id_def)
     apply (meson hd_in_set in_mono)
    apply (subst cap'_unrolled_closed[OF _ dom_fg_finite, where E=E])
    apply blast
       apply (meson hd_in_set in_mono)
      apply blast
    unfolding \<delta>_def using DD apply simp
    apply (subst (2) sum.cong, simp)
    apply (subst plus_fun_apply_iterated[OF l_lists'_finite[OF dom_fg_finite]])
     apply (rule fun_dist_right''[OF l_lists'_finite[OF dom_fg_finite], where E=E])
      apply (rule endo_chain_closed)
    subgoal premises prems for x using \<open>\<forall>x y. edge_fg (h1 + h2) x y \<in> E\<close> by (simp add: algebra_simps)
       apply blast
      apply (simp add: id_def)
    apply blast
    apply (subst chain2_chain)
    apply (subst sum.cong[OF _ sum.cong], simp, simp)
     apply (subst (2) chain_cong''[OF edge_fg_plus_fg_on2[of h2], symmetric])
    subgoal premises prems using \<open>h \<noteq> bot\<close> \<open>h = h1 + h2\<close> by (simp add: algebra_simps)
      subgoal unfolding l_lists'_def apply simp by (meson hd_in_set in_mono)
       apply (subst chain_append'[symmetric, where ys="hd ys # _", simplified], simp)
      apply (subst (2) sum.reindex_cong[symmetric, where l="Cons (hd ys)"])
         apply (intro inj_onI, simp, simp, simp)
      apply (subst sum.cartesian_product)
      apply (rule order_trans[OF sum_reindex_cong_mono[OF subs inj]])
         apply (auto split: prod.splits)[1]
      apply (rule l_lists'_finite[OF finite_UnI[OF dom_fg_finite dom_fg_finite]])
       apply simp
      using "**" by fastforce
qed

lemma cap_le_cap:
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "a \<le> a'" "h = h1 + h2" "h \<noteq> bot" "End_closed E" "\<forall>x y. edge_fg (h1 + h2) x y \<in> E"
    "\<forall>x y. edge_fg h1 x y \<in> E" "x \<in> dom_fg h1" "id \<in> E" "(\<lambda>_. 0) \<in> E"
  shows "cap_fg h1 x y a \<le> cap_fg h x y a'"
proof -
  let ?N1 = "dom_fg h1" let ?e1 = "edge_fg h1"
  let ?N = "dom_fg (h1 + h2)" let ?e = "edge_fg (h1 + h2)"

  have "x \<in> dom_fg (h1 + h2)"
    using assms by simp

  have "cap_fg h1 x y a = \<delta> x y a + (\<Sum>ns\<in>l_lists' ?N1 (card ?N1). chain2 ?e1 x ns y) a"
    using cap'_unrolled_closed[OF _ dom_fg_finite \<open>x \<in> dom_fg h1\<close> \<open>End_closed E\<close>] assms by simp
  also have "... = \<delta> x y a + (\<Sum>ns\<in>l_lists' ?N1 (card ?N1). chain ?e1 (x # ns) y a)"
    by (subst plus_fun_apply_iterated[OF l_lists'_finite[OF dom_fg_finite]], subst chain2_chain, simp)
  also have "... = \<delta> x y a + (\<Sum>ns\<in>l_lists' ?N1 (card ?N1). chain ?e (x # ns) y a)"
    apply (simp, rule sum.cong)
     apply (simp, subst chain_cong'[OF edge_fg_plus_fg_on1])
    using assms unfolding l_lists'_def by simp_all
  also have "... \<le> \<delta> x y a + (\<Sum>ns\<in>l_lists' ?N (card ?N). chain ?e (x # ns) y a)"
    apply (rule add_left_mono[OF sum_mono2[OF l_lists'_finite[OF dom_fg_finite]]])
    unfolding l_lists'_def using assms card_mono[OF dom_fg_finite dom_fg_plus_fg_subs1] apply fastforce
    by simp
  also have "... \<le> \<delta> x y a + (\<Sum>ns\<in>l_lists' ?N (card ?N). chain2 ?e x  ns y) a"
    by (subst plus_fun_apply_iterated[OF l_lists'_finite[OF dom_fg_finite]], subst chain2_chain, simp)
  also have "... = cap_fg (h1 + h2) x y a"
    using cap'_unrolled_closed[OF _ dom_fg_finite \<open>x \<in> dom_fg (h1 + h2)\<close> \<open>End_closed E\<close>] assms by simp
  also have "... \<le> cap_fg (h1 + h2) x y a'"
    apply (rule pos_endo_mono'_closed[OF \<open>a \<le> a'\<close>, where E=E])
     apply (rule endo_cap')
    using assms by simp_all
  finally show ?thesis using assms by simp
qed

lemma fold_endo_closed:
  assumes "set fs \<subseteq> E" "f \<in> E" "End_closed E"
  shows "fold (o) fs f \<in> E"
  using assms
proof (induction fs arbitrary: f)
case Nil
  then show ?case by simp
next
  case (Cons g fs)
  then have "(\<lambda>a. g (f a)) \<in> E"
    unfolding endo_def End_closed_def comp_def
    by simp
  then show ?case
    using Cons
    unfolding End_closed_def endo_def comp_def
    by simp
qed

lemma chains_le_fold:
  fixes f :: "'n list \<Rightarrow> ('m \<Rightarrow> 'm :: pos_cancel_comm_monoid_add)"
  assumes "\<forall>ms \<in> set mss. chain e ms m \<le> f ms" "\<forall>ms \<in> set mss. hd ms = m"
    "\<forall>x y. e x y \<in> E" "\<forall>x. f x \<in> E" "End_closed E" "\<forall>ms \<in> set mss. ms \<noteq> []"
  shows "chains e mss m \<le> fold (o) (map f mss) id"
  using assms
proof (induction mss rule: induct_list012)
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 x y zs)
  have "chains e (y # zs) (hd x) \<circ> chain e x (hd y) \<le> fold (\<circ>) (map f zs) (f y) \<circ> f x"
    apply (rule pos_endo_mono_closed)
        apply (subst "3"(4), simp)
    using 3 apply fastforce
    using 3(2,3) apply simp
    using endo_chains_closed_nonempty [of e E "y # zs" "hd x"] 3 apply simp
    using endo_chains_closed_nonempty [of e E "y # zs" "hd x"] 3 apply simp
    apply (rule fold_endo_closed)
    using 3 by auto
  also have "... = fold (\<circ>) (map f zs) (f y \<circ> f x)"
    using fold_cons[of "map f zs" "f y" "f x"] by simp
  finally show ?case
    by (auto simp: comp_def 3, fold comp_def, simp)
qed

end
