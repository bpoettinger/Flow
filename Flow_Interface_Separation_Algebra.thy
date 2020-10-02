\<^marker>\<open>creator Bernhard Pöttinger\<close>

theory Flow_Interface_Separation_Algebra
imports Flow_Interface "Separation_Algebra.Separation_Algebra"
begin

paragraph \<open>Summary\<close>
text \<open>We show that our flow graph type is a separation algebra if we exclude the invalid
flow graph element. We are using a typedef to obtain a type for valid flow graphs and
instantiate type-class @{text sep_algebra} for this type.\<close>

paragraph \<open>Major Definitions\<close>
text \<open>\<^item> fi2: fi constrained to valid values\<close>

paragraph \<open>Major Theorems\<close>
text \<open>\<^item> Flow Interfaces are Separation Algebra @{cite \<open>th. 1\<close> krishna20}\<close>

section \<open>Flow Interfaces as Separation Algebra\<close>

text \<open>We introduce a flow interface type that only contains the valid flow interfaces in order
to show that this type is a separation algebra\<close>

typedef (overloaded) ('n,'m) fi2 = "{h :: ('n,'m :: cancel_comm_monoid_add) fi . h \<noteq> bot}"
  by (rule exI[where x=0], simp)

text \<open>@{cite \<open>th. 1\<close> krishna20}\<close>

instantiation fi2 :: (type, cancel_comm_monoid_add) sep_algebra
begin

definition sep_disj_fi2 :: "('a, 'b) fi2 \<Rightarrow> ('a, 'b) fi2 \<Rightarrow> bool" where
"sep_disj_fi2 \<equiv> \<lambda>h1 h2. Rep_fi2 h1 + Rep_fi2 h2 \<noteq> bot"

definition plus_fi2 :: "('a, 'b) fi2 \<Rightarrow> ('a, 'b) fi2 \<Rightarrow> ('a, 'b) fi2" where
"plus_fi2 \<equiv> \<lambda>h1 h2. Abs_fi2 (Rep_fi2 h1 + Rep_fi2 h2)"

definition zero_fi2 :: "('a, 'b) fi2" where
"zero_fi2 \<equiv> Abs_fi2 0"

instance
proof (standard, goal_cases)
case (1 x)
  then show ?case
    unfolding sep_disj_fi2_def
    by (metis (mono_tags, lifting) Abs_fi2_inverse Rep_fi2 add.right_neutral mem_Collect_eq
        zero_fi2_def zero_fi_ne_bot)
next
  case (2 x y)
  then show ?case
    unfolding sep_disj_fi2_def
    by (simp add: add.commute)
next
  case (3 x)
  then show ?case 
    unfolding sep_disj_fi2_def
    by (simp add: Abs_fi2_inverse Rep_fi2_inverse plus_fi2_def zero_fi2_def)
next
  case (4 x y)
  then show ?case 
    unfolding sep_disj_fi2_def
    by (simp add: add.commute plus_fi2_def)
next
  case (5 x y z)
  then show ?case 
    unfolding sep_disj_fi2_def plus_fi2_def
    by (simp add: Abs_fi2_inverse ab_semigroup_add_class.add_ac(1))
next
  case (6 x y z)
  then show ?case 
    unfolding sep_disj_fi2_def plus_fi2_def
    by (smt "6"(2) Abs_fi2_inverse add.commute add.left_commute mem_Collect_eq plus_fi_bot_bot(2))
next
  case (7 x y z)
  then show ?case 
    unfolding sep_disj_fi2_def plus_fi2_def
    by (smt Abs_fi2_inverse add.commute add.left_commute mem_Collect_eq plus_fi_bot_bot(2))
qed

end

end
