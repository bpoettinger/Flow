\<^marker>\<open>creator Bernhard Pöttinger\<close>

theory Effectively_Acyclic
imports Flow_Base Approximations Flow_Extensions Pigeonhole Alternating
begin

paragraph \<open>Summary\<close>

text \<open>This theory defines effective acyclicity of flow graphs and provides some lemmas to apply it
more efficiently.\<close>

paragraph \<open>Major Definitions\<close>
text \<open>
- @{term eff_acyclic}: a flow graph is effectively acyclic if the flow along each cycle within the flow
  graph is 0. Enables us to compute flows as we can eliminate the recursive nature of the flow
  equation by unrolling it far enough and all recursive terms will contain cycles (i.e. become
  irrelevant due to effective acyclicity.)
\<close>

section \<open>Effective Acyclicity\<close>

text \<open>@{cite \<open>def. 11\<close> krishna20}\<close>

definition eff_acyclic where
"eff_acyclic N e f \<equiv> \<forall>k \<ge> 1. \<forall>ns \<in> k_lists N k. chain e ns (hd ns) (f (hd ns)) = 0"

text \<open>Convenience definition for @{term eff_acyclic} for flow graphs instead of its components:\<close>

definition eff_acyclic' where
"eff_acyclic' h \<equiv> eff_acyclic (dom_fg h) (edge_fg h) (flow_fg h)"

subsection \<open>Prove that a path has no flow due to effective acyclicity\<close>

text \<open>@{term eff_acyclic_chain_0}: Paths longer than @{term "card N + 1"} definitely contain a cycle,
therefore have flow 0 in effectively acyclic context.\<close>

lemma eff_acyclic_chain_0:
  fixes f :: "'n \<Rightarrow> 'm :: pos_cancel_comm_monoid_add"
  assumes "eff_acyclic N e f" "length ns \<ge> card N + 1" "set ns \<subseteq> N" "finite N"
          "flow_eq (fg N e f) i" "End_closed E" "\<forall>x y. e x y \<in> E" "(\<lambda>_. 0) \<in> E"
  shows "chain e ns n (f (hd ns)) = 0"
proof -
  obtain xs ys zs a where **: "ns = xs @ [a] @ ys @ [a] @ zs"
    using assms pigeonhole_split_list[of N ns] by auto
  then have "set ns = set xs \<union> {a} \<union> set ys \<union> set zs"
    by auto
  then have inn: "set xs \<subseteq> N" "set ys \<subseteq> N" "set zs \<subseteq> N" "a \<in> N"
    using assms ** by blast+
  then have "[a] @ ys \<in> k_lists N (length ys + 1)"
    unfolding k_lists_def by simp
  then have zero: "chain e ([a] @ ys) a (f a) = 0"
    using assms
    unfolding eff_acyclic_def k_lists_def
    by (metis (no_types, lifting) \<open>[a] @ ys \<in> k_lists N (length ys + 1)\<close> assms(1) eff_acyclic_def
        hd_append2 impossible_Cons le_add2 le_numeral_extra(3) list.sel(1) list.size(3))
  then have ***: "chain e ns n = chain e ([a] @ ys @ [a] @ zs) n o chain e xs a"
    using ** chain_append[of "[a] @ ys @ [a] @ zs" e xs n] by simp
  then have "chain e ns n = chain e (a # zs) n o chain e (a # ys) a o chain e xs a"
    using *** chain_append[of "a # zs" e "a # ys" n] by auto
  moreover have B: "chain e xs a (f (hd (xs @ [a]))) \<le> f a"
  proof (cases xs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons aa list)
    have "xs \<in> k_lists N (length xs)"
      using inn unfolding k_lists_def by simp
    then have A: "chain e xs a (f (hd xs)) \<le> (\<Sum>xs\<in>k_lists N (length xs). chain e xs a (f (hd xs)))"
      using sum_insert_pos_monoid[of "k_lists N (length xs)" xs "\<lambda>xs. chain e xs a (f (hd xs))"] inn
        k_lists_finite[of N "length xs"] assms by simp
    have "f a = (\<Sum>ns\<in>k_lists N (length xs). chain e ns a (f (hd ns))) +
                (i a + (\<Sum>ns\<in>l_lists N (length xs). chain e ns a (i (hd ns))))"
      using unroll_flow_eq'[of "length xs" N e f i E a]
        assms inn Cons by (auto simp: algebra_simps)
    then have B: "(\<Sum>ns\<in>k_lists N (length xs). chain e ns a (f (hd ns))) \<le> f a"
      using le_iff_add by auto
    have "chain e xs a (f (hd xs)) \<le> f a" using order_trans[OF A B] .
    then show ?thesis using Cons by simp
  qed
  ultimately have "chain e ns n (f (hd ns)) =
    (chain e (a # zs) n o chain e (a # ys) a o chain e xs a) (f (hd ns))"
    using pos_endo_mono_closed by simp
  also have "... \<le> (chain e (a # zs) n o chain e (a # ys) a) (f a)"
    apply (subst **, subst hd_append, cases xs)
    apply simp_all
    using pos_endo_mono'_closed[OF B, of "chain e (a # zs) n o chain e (a # ys) a", simplified] **
    by (metis B chain_mono assms(6) assms(7) hd_append2 list.sel(1) list.sel(2)
        list.sel(3) not_Cons_self2)
  also have "... = chain e (a # zs) n 0"
    using zero by simp
  also have "... = 0"
    apply (subst endo_f_0_0_closed[of "chain e (a # zs) n"])
    using assms by (auto intro!: endo_chain_closed_nonempty[where E=E])
  finally show ?thesis
    by simp
qed

text \<open>Adapter for @{thm eff_acyclic_chain_0} for flow graphs instead of components.\<close>

lemma eff_acyclic'_chain_eq_0:
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "eff_acyclic' h" "set xs \<subseteq> dom_fg h" "xs \<noteq> []" "End_closed E"
    "\<forall>x y. edge_fg h x y \<in> E" "length xs \<ge> card (dom_fg h) + 1" "h \<noteq> bot" "(\<lambda>_. 0) \<in> E"
  shows "chain (edge_fg h) xs x (flow_fg h (hd xs)) = 0"
proof -
  obtain i where *: "flow_eq h i"
    using \<open>h \<noteq> bot\<close> flow_eq_exists by blast
  have "chain (edge_fg h) xs x (flow_fg h (hd xs)) = 0"
    apply (rule eff_acyclic_chain_0[of "dom_fg h" "edge_fg h" "flow_fg h" xs i E x])
    using assms * unfolding eff_acyclic'_def by simp_all
  then show ?thesis
    using assms by simp
qed

text \<open>Same as @{text contradict_eff_acyclic_flow} but with inflow as initial flow this time
instead of flow.\<close>

text \<open>If a path is not distinct then there is a cycle in there and in an effectively acyclic
context this implies that there is no flow along this path.\<close>

lemma chain_eff_acylic_zero_not_distinct_flow:
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "eff_acyclic' h" "set ns \<subseteq> dom_fg h" "h \<noteq> bot" "id \<in> E" "ns \<noteq> []"
    "End_closed E" "\<forall>x y. edge_fg h x y \<in> E" "\<not> distinct ns" "m \<le> flow_fg h (hd ns)" "(\<lambda>_. 0) \<in> E"
  shows "chain (edge_fg h) ns n m = 0"
proof -
  let ?e = "edge_fg h"
  let ?f = "flow_fg h"

  obtain ns1 ns2 ns3 n0 where ns: "ns = ns1 @ n0 # ns2 @ n0 # ns3"
    using assms not_distinct_decomp[of "ns"] by auto

  have "set ns \<subseteq> dom_fg h" using assms by simp
  then have dom: "set ns1 \<subseteq> dom_fg h" "set ns2 \<subseteq> dom_fg h" "set ns3 \<subseteq> dom_fg h" "n0 \<in> dom_fg h"
    using ns by auto

  have "n0 # ns2 \<in> k_lists (dom_fg h) (length (n0 # ns2))"
    unfolding k_lists_def using ns dom by simp
  then have "chain ?e (n0 # ns2) (hd (n0 # ns2)) (?f (hd (n0 # ns2))) = 0"
    using assms unfolding eff_acyclic'_def eff_acyclic_def by force
  then have "chain ?e (n0 # ns3) n (chain ?e (n0 # ns2) (hd ((n0 # ns3) @ [n])) (?f (hd ((n0 # ns3) @ [n])))) = 0"
    apply simp
    apply (rule endo_f_0_0_closed[where f="chain ?e (n0 # ns3) n" and E=E])
    by (rule endo_chain_closed, auto simp: assms)
  then have **: "chain (edge_fg h) (n0 # ns2 @ n0 # ns3) n (flow_fg h (hd (n0 # ns2))) = 0"
    by (subst (asm) chain_append_nonempty[symmetric], simp)

  have *: "chain ?e ns1 n0 (?f (hd (ns1 @ [n0]))) \<le> ?f n0"
    apply (rule chain_flow_fg_le_flow_fg)
    using assms dom by auto

  have "chain ?e ns n m \<le> chain ?e ns n (?f (hd ns))"
    apply (rule order_trans[OF pos_endo_mono'_closed[OF \<open>m \<le> ?f (hd ns)\<close>]])
    by (rule endo_chain_closed[where E=E], auto simp: assms)
  also have "... = chain ?e (n0 # ns2 @ n0 # ns3) n (chain ?e ns1 n0 (?f (hd (ns1 @ [n0]))))"
    apply (simp add: chain_append_nonempty ns)
    by (metis append_self_conv2 hd_append2 list.sel(1))
  also have "... \<le> chain ?e (n0 # ns2 @ n0 # ns3) n (?f n0)"
    apply (rule pos_endo_mono'_closed[OF *, where E=E])
    by (rule endo_chain_closed, auto simp: assms)
  also have "... = 0" using ** by simp

  finally show ?thesis using ns by simp
qed

text \<open>A specialized variant of the previous lemma @{thm chain_eff_acylic_zero_not_distinct_flow}:
initial flow inflow instead of arbitrary flow.\<close>

lemma chain_eff_acylic_zero_not_distinct:
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "eff_acyclic' h" "set ns \<subseteq> dom_fg h" "h \<noteq> bot" "id \<in> E" "(\<lambda>_. 0) \<in> E" "ns \<noteq> []"
    "End_closed E" "\<forall>x y. edge_fg h x y \<in> E" "\<not> distinct ns" "m \<le> inf_fg h (hd ns)"
  shows "chain (edge_fg h) ns n m = 0"
proof -
  have *: "m \<le> flow_fg h (hd ns)"
    using inf_fg_le_flow_fg[of h "hd ns"] assms by force
  show ?thesis
    apply (rule chain_eff_acylic_zero_not_distinct_flow)
    using assms * chain_eff_acylic_zero_not_distinct_flow by auto
qed

text \<open>Another special case of @{thm chain_eff_acylic_zero_not_distinct_flow} for convoluted paths.\<close>

lemma chains_eff_acylic_zero_not_distinct:
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "\<not> distinct (concat xss)" "eff_acyclic' h" "z \<le> flow_fg h (hd (hd xss))"
    "\<forall>xs \<in> set xss. xs \<noteq> []" "set (concat xss) \<subseteq> dom_fg h" "\<forall>x y. edge_fg h x y \<in> E"
    "End_closed E" "h \<noteq> bot" "xss \<noteq> []" "id \<in> E" "(\<lambda>_. 0) \<in> E"
  shows "chains (edge_fg h) xss y z = 0"
proof -
  have "hd (hd xss) = hd (concat xss)" using assms
    by (metis concat.simps(2) hd_Cons_tl hd_append2 hd_in_set)
  then have "chain (edge_fg h) (concat xss) y z = 0"
    using chain_eff_acylic_zero_not_distinct_flow[of h "concat xss" E z y] assms by simp
  moreover have "chains (edge_fg h) xss y z = chain (edge_fg h) (concat xss) y z"
    using chain_concat_chains assms by metis
  ultimately show ?thesis by simp
qed

lemma eff_acyclic'_chain_eq_0_plus_fg: (* replace/simplify *)
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "eff_acyclic' h1" "h = h1 + h2" "set xs \<subseteq> dom_fg h1" "xs \<noteq> []" "h \<noteq> bot"
  shows "chain (edge_fg h) xs (hd xs) (flow_fg h (hd xs)) = 0"
proof -
  let ?k = "length xs"
  let ?N1 = "dom_fg h1" let ?f1 = "flow_fg h1" let ?e1 = "edge_fg h1"
  let ?N = "dom_fg h" let ?f = "flow_fg h" let ?e = "edge_fg h"

  have "xs \<in> k_lists ?N1 ?k"
    using assms unfolding k_lists_def by simp
  then have "chain ?e1 xs (hd xs) (?f1 (hd xs)) = 0"
    using assms add_leD2 unfolding eff_acyclic'_def eff_acyclic_def
    by (metis One_nat_def Suc_leI assms(1) eff_acyclic'_def eff_acyclic_def length_greater_0_conv)
  then show ?thesis
    apply (subst chain_cong[of xs ?e ?e1])
    using on_eq_superset[OF \<open>set xs \<subseteq> ?N1\<close> edge_fg_plus_fg_on1[of h1 h2]] assms apply simp
    using on_eq_superset[OF \<open>set xs \<subseteq> ?N1\<close> flow_fg_plus_fg_on1[of h1 h2]] assms by simp
qed

subsection \<open>Paths with cycles can not have flow in effective acyclic flow graph\<close>

text \<open>A path that contains its destination node has no flow in an effectively acyclic context.\<close>

lemma contradict_eff_acyclic_flow:
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "eff_acyclic' h" "chain (edge_fg h) ns n (flow_fg h (hd ns)) \<noteq> 0" "set ns \<subseteq> dom_fg h" 
    "n \<in> set ns" "h \<noteq> bot" "End_closed E" "\<forall>x y. edge_fg h x y \<in> E" "(\<lambda>_. 0) \<in> E" "id \<in> E"
  shows "False"
proof -
  let ?e = "edge_fg h"
  let ?f = "flow_fg h"
  let ?N = "dom_fg h"
  let ?i = "inf_fg h"

  have "ns \<noteq> []"
    using assms by auto

  obtain ns1 ns2 where *: "ns = ns1 @ n # ns2" "set ns1 \<subseteq> ?N" "set (n # ns2) \<subseteq> ?N"
    using split_list[of n ns] assms(3,4) by auto
  then have **: "n # ns2 \<in> k_lists (dom_fg h) (length (n # ns2))" "length (n # ns2) \<ge> 1"
    unfolding k_lists_def by auto
  then have "chain (edge_fg h) (n # ns2) (hd (n # ns2)) (flow_fg h (hd (n # ns2))) = 0"
    using assms(1) unfolding eff_acyclic_def eff_acyclic'_def by blast
  moreover have "0 \<noteq> chain ?e (n # ns2) n (?f n)"
  proof -
    have ***: "hd (ns @ [n]) = hd (ns1 @ [n])"
      using * by (simp add: hd_append)
    have "0 < chain ?e (n # ns2) n (chain ?e ns1 n (?f (hd ns)))"
      using assms
      apply (subst (asm) \<open>ns = ns1 @ n # ns2\<close>,
             subst (asm) chain_append_nonempty[where xs="ns1" and ys="n # ns2"], simp)
      using not_gr_zero by blast
    also have "... = chain ?e (n # ns2) n (chain ?e ns1 n (?f (hd (ns @ [n]))))"
      using \<open>ns \<noteq> []\<close> by simp
    also have "... \<le> chain ?e (n # ns2) n (?f n)"
      apply (subst ***)
      apply (rule chain_mono[OF chain_flow_fg_le_flow_fg, of h E])
      using assms * by simp_all
    finally show ?thesis
      by simp
  qed
  ultimately show False
    by simp
qed

lemma contradict_eff_acyclic:
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "eff_acyclic' h" "chain (edge_fg h) ns n (inf_fg h (hd ns)) \<noteq> 0" "set ns \<subseteq> dom_fg h"
    "n \<in> set ns" "h \<noteq> bot" "End_closed E" "\<forall>x y. edge_fg h x y \<in> E" "(\<lambda>_. 0) \<in> E" "id \<in> E"
  shows "False"
proof -
  have "0 < chain (edge_fg h) ns n (inf_fg h (hd ns))"
    using assms gr_zeroI by blast
  also have "... \<le> chain (edge_fg h) ns n (flow_fg h (hd ns))"
    apply (auto intro!: pos_endo_mono'_closed[OF inf_fg_le_flow_fg, where E=E] endo_chain_closed simp: assms)
    by (metis assms(3) assms(4) equals0D hd_in_set in_mono set_empty)
  finally have "chain (edge_fg h) ns n (flow_fg h (hd ns)) \<noteq> 0" by simp
  then show False using contradict_eff_acyclic_flow assms by metis
qed

subsection \<open>Upper Bound of Path Length\<close>

text \<open>@{term eff_acyclic_chain_length_le_card}: in an effectively acyclic context paths with
flow have an upper bound of their length.\<close>

lemma eff_acyclic_chain_length_le_card:
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "eff_acyclic' h" "h \<noteq> bot" "chain (edge_fg h) xs y (inf_fg h (hd xs)) \<noteq> 0"
    "End_closed E" "\<forall>x y. edge_fg h x y \<in> E" "set xs \<subseteq> dom_fg h" "(\<lambda>_. 0) \<in> E" "id \<in> E"
  shows "length xs \<le> card (dom_fg h)"
proof (rule ccontr)
  assume "\<not> length xs \<le> card (dom_fg h)"
  then have *: "length xs \<ge> card (dom_fg h) + 1" by simp
  then obtain xs1 x xs2 xs3 where **: "xs = xs1 @ x # xs2 @ x # xs3"
    using pigeonhole_split_list[OF *] assms by auto
  then have "chain (edge_fg h) (xs1 @ x # xs2) x (inf_fg h (hd (xs1 @ x # xs2))) \<noteq> 0"
    using chain_append_not_zero(1)[of xs "xs1 @ x # xs2" "x # xs3" _ y _ E] assms
    by (metis (no_types, lifting) Nil_is_append_conv append_Cons
        append_eq_append_conv2 hd_append2 list.sel(1) list.simps(3))
  moreover have "set (xs1 @ x # xs2) \<subseteq> dom_fg h" "x \<in> dom_fg h"
    using assms ** by auto
  ultimately show False
    using contradict_eff_acyclic[of h "xs1 @ x # xs2" x E] assms by simp
qed

text \<open>@{term eff_acyclic_chain_length_le_card'}: Lift the previous result to alternating convoluted paths,
i.e. each path segment is at most as long as the upper bound of its subgraph admits.\<close>

lemma eff_acyclic_chain_length_le_card':
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes alt: "alternating (segment_fg h1) (segment_fg h2) xss"
    and def: "h1 + h2 \<noteq> bot"
    and edge: "End_closed E" "\<forall>x y. edge_fg h1 x y \<in> E" "\<forall>x y. edge_fg h2 x y \<in> E"
      "\<forall>x y. edge_fg (h1 + h2) x y \<in> E" "id \<in> E" "(\<lambda>_. 0) \<in> E"
    and ea: "eff_acyclic' h1" "eff_acyclic' h2"
    and null: "chains' (chain (edge_fg (h1 + h2))) xss n (inf_fg h1 (hd (hd xss))) \<noteq> 0"
  shows "alternating (len_segment_fg h1) (len_segment_fg h2) xss"
  using assms
proof (induction xss rule: alternating_induct'_symmetric[where a=h1 and b=h2])
  case empty
  then show ?case by simp
next
  case (base h1 h2 xs)
  have "0 < chain (edge_fg (h1 + h2)) xs n (inf_fg h1 (hd xs))"
    using base gr_zeroI by fastforce
  also have "... = chain (edge_fg h1) xs n (inf_fg h1 (hd xs))"
    apply (subst chain_cong'[OF edge_fg_plus_fg_on1[of h1 h2]])
    using base by simp_all
  finally have *: "chain (edge_fg h1) xs n (inf_fg h1 (hd xs)) \<noteq> 0"
    by simp
  have "length xs \<le> card (dom_fg h1)"    
    apply (rule eff_acyclic_chain_length_le_card[where y=n])
    using assms  base * plus_fg_ops_exist unfolding id_def by blast+
  with base show ?case
    by simp
next
  case (step h1 h2 xs ys zss)

  let ?e12 = "edge_fg (h1 + h2)"
  let ?i1 = "inf_fg h1"
  let ?e1 = "edge_fg h1"

  have "chain ?e12 xs (hd ys) (?i1 (hd xs)) \<noteq> 0"
    apply (rule endo_f_n0_n0_closed[OF endo_chains', where E=E])
    using step apply simp_all
    by (clarsimp, rule endo_chain_closed[where E=E], simp_all add: step)
  then have "0 < chain ?e12 xs (hd ys) (inf_fg h1 (hd xs))"
    using gr_zeroI by fastforce
  also have "... = chain ?e1 xs (hd ys) (?i1 (hd xs))"
    apply (subst chain_cong'[OF edge_fg_plus_fg_on1[of h1 h2]])
    using step by simp_all
  finally have *: "chain ?e1 xs (hd ys) (?i1 (hd xs)) \<noteq> 0"
    by simp
  have A: "length xs \<le> card (dom_fg h1)"
    apply (rule eff_acyclic_chain_length_le_card[where y="hd ys" and E=E])
    using assms step * plus_fg_ops_exist unfolding id_def by blast+
  have "0 < chains' (chain ?e12) (ys # zss) n (chain ?e12 xs (hd ys) (?i1 (hd xs)))"
    using step gr_zeroI by fastforce
  also have "... = chains' (chain ?e12) (ys # zss) n (chain ?e1 xs (hd ys) (?i1 (hd (xs @ [hd ys]))))"
    using step by (smt chain_cong' edge_fg_plus_fg_on1' hd_append2)
  also have "... \<le> chains' (chain ?e12) (ys # zss) n (inf_fg h2 (hd ys))"
    apply (rule pos_endo_mono'_closed[OF
            chain_inf_fg_le_inf_fg[where E=E and h="h1 + h2"], where E=E])
    using step apply blast+
    using hd_in_set step.hyps(3) step apply blast
         apply blast
    using step apply blast+
     apply (rule endo_chains'[OF \<open>End_closed E\<close>])
    apply (simp add: endo_chain_closed step)
    using step by blast+
  finally have B: "chains' (chain (edge_fg (h1 + h2))) (ys # zss) n (inf_fg h2 (hd ys)) \<noteq> 0"
    by simp
  from A B step show ?case
    by (simp add: algebra_simps)
qed



end
