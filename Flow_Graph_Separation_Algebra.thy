\<^marker>\<open>creator Bernhard Pöttinger\<close>

theory Flow_Graph_Separation_Algebra
imports Flow_Graph "Separation_Algebra.Separation_Algebra"
begin

paragraph \<open>Summary\<close>
text \<open>We show that our flow graph type is a separation algebra if we exclude the invalid
flow graph element. We are using a typedef to obtain a type for valid flow graphs and
instantiate type-class @{text sep_algebra} for this type.\<close>

paragraph \<open>Major Definitions\<close>
text \<open>\<^item> fg2: fg constrained to valid values\<close>

paragraph \<open>Major Theorems\<close>
text \<open>\<^item> Flow Graphs are Separation Algebra @{cite krishna20}\<close>

section \<open>Flow Interfaces as Separation Algebra\<close>

text \<open>We introduce a flow graph type that only contains the valid flow graphs in order
to show that this type is a separation algebra\<close>

typedef (overloaded) ('n,'m) fg2 = "{h :: ('n,'m :: cancel_comm_monoid_add) fg . h \<noteq> bot}"
  by (rule exI[where x=0], simp)

text \<open>Claim from @{cite krishna20}\<close>

instantiation fg2 :: (type, cancel_comm_monoid_add) sep_algebra
begin

definition sep_disj_fg2 :: "('a, 'b) fg2 \<Rightarrow> ('a, 'b) fg2 \<Rightarrow> bool" where
"sep_disj_fg2 \<equiv> \<lambda>h1 h2. Rep_fg2 h1 + Rep_fg2 h2 \<noteq> bot"

definition plus_fg2 :: "('a, 'b) fg2 \<Rightarrow> ('a, 'b) fg2 \<Rightarrow> ('a, 'b) fg2" where
"plus_fg2 \<equiv> \<lambda>h1 h2. Abs_fg2 (Rep_fg2 h1 + Rep_fg2 h2)"

definition zero_fg2 :: "('a, 'b) fg2" where
"zero_fg2 \<equiv> Abs_fg2 0"

instance
proof (standard, goal_cases)
case (1 x)
  then show ?case
    unfolding sep_disj_fg2_def
    by (metis (mono_tags, lifting) Abs_fg2_inverse Rep_fg2 add.right_neutral mem_Collect_eq
        zero_fg2_def zero_fg_nbot)
next
  case (2 x y)
  then show ?case
    unfolding sep_disj_fg2_def
    by (simp add: add.commute)
next
  case (3 x)
  then show ?case 
    unfolding sep_disj_fg2_def
    by (simp add: Abs_fg2_inverse Rep_fg2_inverse plus_fg2_def zero_fg2_def)
next
  case (4 x y)
  then show ?case 
    unfolding sep_disj_fg2_def
    by (simp add: add.commute plus_fg2_def)
next
  case (5 x y z)
  then show ?case 
    unfolding sep_disj_fg2_def plus_fg2_def
    by (simp add: Abs_fg2_inverse ab_semigroup_add_class.add_ac(1))
next
  case (6 x y z)
  then show ?case 
    unfolding sep_disj_fg2_def plus_fg2_def
    by (smt Abs_fg2_inverse add.left_commute mem_Collect_eq plus_fg_comm plus_fg_ops_exist)
next
  case (7 x y z)
  then show ?case 
    unfolding sep_disj_fg2_def plus_fg2_def
    by (smt Abs_fg2_inverse add.left_commute mem_Collect_eq plus_fg_bot_bot(2) plus_fg_comm)
qed

end

end
