\<^marker>\<open>create Bernhard Pöttinger\<close>

chapter \<open>Approximations\<close>
theory Effectively_Acyclic_Approximations
imports Effectively_Acyclic
begin

paragraph \<open>Summary\<close>
text \<open>This theory complements theory Approximations with some approximations/results on capacities
that depend on effective acyclicity and can not be put into Approximations due to this dependency.\<close>

text \<open>@{term cap_eff_acyclic}: the capacity from x to x equals the identity function as all paths of
length >= 1 that reach from x to x are cycles, i.e. have flow 0.\<close>

lemma cap_eff_acyclic:
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "eff_acyclic' h" "h \<noteq> bot" "x \<in> dom_fg h" "End_closed E" "\<forall>x y. edge_fg h x y \<in> E"
    "a \<le> flow_fg h x" "id \<in> E"
  shows "cap' k (dom_fg h) (edge_fg h) x x a = a"
  using assms
  apply (subst cap'_unrolled_closed[where E=E], simp_all)
  apply (subst plus_fun_apply_iterated[OF l_lists'_finite[OF dom_fg_finite]])
  apply (rule sum.neutral, safe)
  apply (subst chain2_chain)
  subgoal premises prems for xs
  proof -
    have K: "x # xs \<in> k_lists (dom_fg h) (length (x # xs))"
      using prems unfolding k_lists_def l_lists'_def by auto
    then have L: "chain (edge_fg h) (x # xs) x (flow_fg h (hd (x # xs))) = 0"
      using prems unfolding eff_acyclic'_def eff_acyclic_def by force

    have "chain (edge_fg h) (x # xs) x a \<le> chain (edge_fg h) (x # xs) x (flow_fg h x)"
      apply (rule pos_endo_mono'_closed[where f="chain (edge_fg h) (x # xs) x" and E=E])
      using prems apply simp_all
      by (rule endo_chain_closed, simp_all)
    with L show ?thesis by simp
  qed
  done

text \<open>@{term cap_cap_le_cap}: some kind of triangle inequality for capacities,
i.e. the capacity from x to z is >= than the capacity from x to y to z for y != z\<close>

lemma cap_cap_le_cap:
  fixes E :: "('a \<Rightarrow> 'a :: pos_cancel_comm_monoid_add) set"
  assumes "End_closed E" "\<forall>x y. edge_fg h x y \<in> E" "x \<in> dom_fg h" "y \<in> dom_fg h" "z \<in> dom_fg h"
    and "h \<noteq> bot" "id \<in> E" "0 \<in> E"
    and dist: "y \<noteq> z"
    and flow: "a \<le> inf_fg h x"
    and ea: "eff_acyclic' h"
  shows "cap' k (dom_fg h) (edge_fg h) y z (cap' l (dom_fg h) (edge_fg h) x y a)
       \<le> cap' (k + l) (dom_fg h) (edge_fg h) x z a"
  using assms
proof (induction k arbitrary: y z)
  case 0
  then show ?case by simp
next
  case (Suc k)

  let ?e = "edge_fg h" let ?N = "dom_fg h"

  have "(\<Sum>n''\<in>?N. ?e n'' z \<circ> cap' k ?N ?e y n'') (cap' l ?N ?e x y a) =
        (\<Sum>n''\<in>?N. (?e n'' z o cap' k ?N ?e y n'') (cap' l ?N ?e x y a))"
    by (rule plus_fun_apply_iterated[OF dom_fg_finite])
  also have "... \<le> (\<Sum>n''\<in>?N. ?e n'' z (cap' (k + l) ?N ?e x n'' a))"
    apply (simp, rule sum_mono)
    subgoal for n''
      apply (rule pos_endo_mono'_closed[where f="?e n'' z" and E=E])
      apply (cases "y \<noteq> n''")
        apply (rule Suc.IH[of y n''])
      using Suc apply simp_all
      apply (subst cap_eff_acyclic, simp_all)
        apply (rule order_trans[OF pos_endo_mono'_closed[OF flow, where E=E]])
          apply (rule endo_cap'[where E=E], simp_all add: zero_fun_def id_def)
       apply (cases l)
        apply (clarsimp simp: \<delta>_def)
      apply (rule inf_fg_le_flow_fg, simp, simp)
      apply (rule cap'_inf_fg_le_flow_fg, simp_all add: id_def)
      by (rule cap'_superset_iterations[OF dom_fg_finite], simp_all)
    done
  finally have A: "(\<Sum>n''\<in>?N. ?e n'' z \<circ> cap' k ?N ?e y n'') (cap' l ?N ?e x y a)
                 \<le> (\<Sum>n''\<in>?N. ?e n'' z (cap' (k + l) ?N ?e x n'' a))" .

  show ?case
    using Suc apply (auto simp: \<delta>_def)
    using A apply (subst (2) plus_fun_apply_iterated[OF dom_fg_finite],
                   simp add: comp_def add_increasing)
    using A by (subst (2) plus_fun_apply_iterated[OF dom_fg_finite], simp add: comp_def)
qed

text \<open>@{term unroll_flow_eq_eff_acyclic}: like @{thm unroll_flow_eq} but in an effectively acyclic context
we can eliminiate its second big-sum if we unroll the flow equation far enough to obtain cycles
in the second big-sum.\<close>

lemma unroll_flow_eq_eff_acyclic:
  fixes e :: "'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b :: pos_cancel_comm_monoid_add"
  assumes "eff_acyclic N e f" "flow_eq2' N e f i" "\<forall>x y. e x y \<in> E" "End_closed E" "finite N"
    "k \<ge> card N" "id \<in> E" "(\<lambda>_. 0) \<in> E"
  shows "\<forall>x \<in> N. f x = i x + (\<Sum>xs \<in> l_lists N k. chain e xs x (i (hd xs)))"
proof (cases "card N")
  case 0
  then have "N = {}" using assms card_0_eq by blast
  then show ?thesis by blast
next
  case (Suc nat)
  then have "k \<ge> 1" using assms by simp
  show ?thesis
  proof
    fix x
    assume A: "x \<in> N"
  
    have zt: "(\<Sum>ns\<in>k_lists N k. chain e ns x (f (hd ns))) = 0"
    proof (rule sum.neutral, safe)
      fix ns
      assume A: "ns \<in> k_lists N k"
      then obtain z xs ys zs where *: "ns @ [x] = xs @ z # ys @ z # zs"
        using pigeonhole_split_list[of N "ns @ [x]"] k_lists_finite[of N k] assms \<open>x \<in> N\<close>
        unfolding k_lists_def by auto
      then have **: "ns = butlast (xs @ z # ys @ z # zs)"
        by (metis butlast_snoc)
      have "set ns \<subseteq> N"
        using A unfolding k_lists_def by simp
      then have ***: "z \<in> N" "set (ns @ [x]) \<subseteq> N"
        using * A \<open>x \<in> N\<close> apply (simp_all add: "**" butlast_append)
        by (metis UnE list.set(1) list.set(2) set_append set_subset_Cons singletonD subset_code(1))
      have "set (ns @ [x]) \<subseteq> N"
        using A \<open>x \<in> N\<close> unfolding k_lists_def by simp
      then have "z # ys \<in> k_lists N (length ys + 1)"
        using A \<open>x \<in> N\<close> * unfolding k_lists_def by auto
      then have C: "chain e (z # ys) z (f z) = 0"
        using assms unfolding eff_acyclic_def by fastforce
      have B: "chain e xs z (f (hd (ns @ [x]))) \<le> f z"
      proof (cases xs)
        case Nil
        then show ?thesis using * by simp
      next
        case (Cons a xs')
        have "chain e xs z (f (hd (xs @ [x])))
           \<le> (\<Sum>ns\<in>k_lists N (length xs). chain e ns z (f (hd (ns @ [x]))))"
          apply (rule sum_insert_pos_monoid[where f="\<lambda>xs. chain e xs z (f (hd (xs @ [x])))"])
          using k_lists_finite[OF \<open>finite N\<close>] apply simp
          using Cons * *** unfolding k_lists_def by simp
        also have "... \<le> i z + (\<Sum>ns\<in>l_lists N (length xs). chain e ns z (i (hd ns))) +
                               (\<Sum>ns\<in>k_lists N (length xs). chain e ns z (f (hd (ns @ [x]))))"
          by (simp add: add_increasing)
        also have "... = i z + (\<Sum>ns\<in>l_lists N (length xs). chain e ns z (i (hd ns))) +
                              (\<Sum>ns\<in>k_lists N (length xs). chain e ns z (f (hd ns)))"
          apply (simp, rule sum.cong, simp)
          unfolding k_lists_def using Cons
          by (metis (mono_tags, lifting) append_Cons hd_append2
              length_0_conv list.sel(1) mem_Collect_eq)
        also have "... = f z"
          apply (rule unroll_flow_eq[of "length xs" N e f i E z, symmetric])
          using assms Cons *** by simp_all
        finally show ?thesis
          using * Cons by simp
      qed
      have "chain e (z # ys) z (chain e xs z (f (hd (ns @ [x])))) \<le> chain e (z # ys) z (f z)"
        apply (rule pos_endo_mono'_closed[OF B])
        using endo_chain_closed assms by simp_all
      also have "... = 0"
        using C by simp
      finally have "chain e (z # ys) z (chain e xs z (f (hd (ns @ [x])))) = 0"
        by simp
      then have Z: "chain e (xs @ z # ys) z (f (hd ns)) = 0"
        apply (subst chain_append, simp_all)
        using A \<open>1 \<le> k\<close> k_lists_nonempty(2) by fastforce
      have X: "(xs @ z # ys) @ butlast (z # zs) = ns"
        using **  by (simp add: butlast_append)
      have "chain e ((xs @ z # ys) @ butlast (z # zs)) (last (ns @ [x])) =
        chain e (butlast (z # zs)) (last (ns @ [x])) o chain e (xs @ z # ys) (hd (butlast (z # zs) @ [last (ns @ [x])]))"
        using chain_append_nonempty[of e "xs @ z # ys" "butlast (z # zs)" "last (ns @ [x])"]
        apply simp unfolding comp_def by (auto split: if_splits)
      then have "chain e ns (last (ns @ [x])) =
        chain e (butlast (z # zs)) (last (ns @ [x])) o chain e (xs @ z # ys) (hd (butlast (z # zs) @ [last (ns @ [x])]))"
        using X by auto
      then show "chain e ns x (f (hd ns)) = 0"
        using endo_f_0_0_closed[of "chain e (butlast (z # zs)) x" E] Z
          assms endo_chain_closed[of e E "butlast (z # zs)" x]
        by (metis (no_types, lifting) "*" append_butlast_last_id append_is_Nil_conv
            comp_apply last_ConsR last_appendR last_snoc list.discI list.sel(1))
    qed
  
    have "f x = i x + (\<Sum>ns\<in>l_lists N k. chain e ns x (i (hd ns))) +
                      (\<Sum>ns\<in>k_lists N k. chain e ns x (f (hd ns)))"
      apply (rule unroll_flow_eq[of k N e f i E x], simp_all add: assms A) using \<open>k \<ge> 1\<close> by simp
    then show "f x = i x + (\<Sum>xs\<in>l_lists N k. chain e xs x (i (hd xs)))"
      using zt by simp
  qed
qed

text \<open>@{term unroll_flow_eq_eff_acyclic'}: wrapper lemma for @{thm unroll_flow_eq_eff_acyclic} that integrates
"i x" in the big-sum by using @{term l_lists'} instead of @{term l_lists}.\<close>

lemma unroll_flow_eq_eff_acyclic':
  fixes e :: "'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b :: pos_cancel_comm_monoid_add"
  assumes "eff_acyclic N e f" "flow_eq2' N e f i" "\<forall>x y. e x y \<in> E" "End_closed E" "finite N"
    "k \<ge> card N" "k \<ge> 1" "id \<in> E" "(\<lambda>_. 0) \<in> E"
  shows "\<forall>x \<in> N. f x = (\<Sum>xs \<in> l_lists' N k. chain e xs x (i (hd (xs @ [x]))))"
proof -
  have S: "\<forall>x \<in> N. f x = i x + (\<Sum>xs \<in> l_lists N k. chain e xs x (i (hd xs)))"
    using assms unroll_flow_eq_eff_acyclic by blast
  have T: "\<forall>x \<in> N. i x = chain e [] x (i (hd ([] @ [x])))"
    by simp
  show ?thesis
  proof 
    fix x assume A: "x \<in> N"
    have "f x = i x + (\<Sum>xs \<in> l_lists N k. chain e xs x (i (hd xs)))" using S A by simp
    also have "... = i x + (\<Sum>xs \<in> l_lists N k. chain e xs x (i (hd (xs @ [x]))))"
      apply (simp, rule sum.cong, simp)
      unfolding l_lists_def using Suc_le_lessD by fastforce
    also have"... =
      chain e [] x (i (hd ([] @ [x]))) + (\<Sum>xs \<in> l_lists N k. chain e xs x (i (hd (xs @ [x]))))"
      using S by simp
    also have "... = (\<Sum>xs \<in>insert [] (l_lists N k). chain e xs x (i (hd (xs @ [x]))))"
      apply (rule sum.insert[symmetric, where g="\<lambda>xs. chain e xs x (i (hd (xs @ [x])))"])
       apply (rule l_lists_finite[OF \<open>finite N\<close>])
      unfolding l_lists_def by simp
    also have "... = (\<Sum>xs \<in>(l_lists' N k). chain e xs x (i (hd (xs @ [x]))))"
      apply (rule sum.cong)
      using l_lists_eq_l_lists'[of k N]  assms by auto
    finally show " f x = (\<Sum>xs\<in>l_lists' N k. chain e xs x (i (hd (xs @ [x]))))" .
  qed
qed


end
