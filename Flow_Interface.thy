\<^marker>\<open>creator Bernhard Pöttinger\<close>

chapter \<open>Flow Interface\<close>
theory Flow_Interface
imports Main Auxiliary
begin

paragraph \<open>Summary\<close>
text \<open>This theory implements the basic data structures used by the Flow Framework
@{cite krishna20}: flow interfaces.\<close>

section \<open>Flow Interface\<close>

subsection \<open>Preliminary Flow Interfaces\<close>

text \<open>Flow Interfaces basically are equivalence classes of flow graphs with respect to
their ability to replace each other in sums.\<close>

text \<open>Analogously to flow graphs, we first introduce a preliminary type for flow interfaces due to
unique representation concerns. A flow interface (N,i,o) consists of a domain N,
an inflow i, and an outflow o.\<close>

type_synonym ('n,'m) fi' = "'n set \<times> ('n \<Rightarrow> 'm) \<times> ('n \<Rightarrow> 'm)"

text \<open>We need a notion of equality again due to being partially defined only on N.
Note that the outflow is defined on -N!\<close>

definition fi'_eq :: "('n,'m) fi' \<Rightarrow> ('n,'m) fi' \<Rightarrow> bool" where
"fi'_eq \<equiv> \<lambda>(N1,i1,o1) (N2,i2,o2). N1 = N2 \<and> (i1 = i2 on N1) \<and> (o1 = o2 on -N1)"

lemma fi'_eqI:
  assumes "N1 = N2" "i1 = i2 on N1" "o1 = o2 on -N1"
  shows "fi'_eq (N1,i1,o1) (N2,i2,o2)"
  using assms unfolding fi'_eq_def by (auto split: prod.splits)

text \<open>The only restriction for flow interfaces is that their domain has to be finite.\<close>

definition "def_fi' \<equiv> \<lambda>(N,_,_). finite N"

text \<open>We need a representation for invalid flow interfaces, i.e. lift to option type.\<close>

definition fi'_option_eq
  :: "('n,'m) fi' option \<Rightarrow> ('n,'m :: cancel_comm_monoid_add) fi' option \<Rightarrow> bool" where
"fi'_option_eq \<equiv> \<lambda>i1 i2.
    case (i1,i2) of
      (Some i1', Some i2') \<Rightarrow> (if def_fi' i1' \<and> def_fi' i2' then fi'_eq i1' i2' else
                              if \<not>def_fi' i1' \<and> \<not>def_fi' i2' then True else
                              False)
    | (None, None) \<Rightarrow> True
    | (Some i1, None) \<Rightarrow> \<not>def_fi' i1
    | (None, Some i2) \<Rightarrow> \<not>def_fi' i2"

subsection \<open>Flow Interfaces @{cite \<open>def. 5\<close> krishna20}\<close>

quotient_type (overloaded) ('n,'m) fi =
  "('n,'m :: cancel_comm_monoid_add) fi' option" / fi'_option_eq
  apply (rule equivpI)
  subgoal by (rule reflpI, simp add: fi'_option_eq_def fi'_eq_def split: option.splits)
  subgoal by (rule sympI, auto simp: fi'_option_eq_def fi'_eq_def split: option.splits if_splits)
  subgoal by (rule transpI, simp add: fi'_option_eq_def fi'_eq_def def_fi'_def
              split: option.splits if_splits prod.splits)
  done

text \<open>Accessor functions again... Default values for invalid flow interfaces, default values
for inflow and outflow outside their domain.\<close>

lift_definition dom_fi :: "('n,'m::cancel_comm_monoid_add) fi \<Rightarrow> 'n set"
  is "\<lambda>i. case i of Some (N,f,g) \<Rightarrow> if def_fi' (N,f,g) then N else {} | _ \<Rightarrow> {}"
  by (auto simp: fi'_option_eq_def def_fi'_def fi'_eq_def
      split: option.splits if_splits prod.splits)

lift_definition inf_fi :: "('n,'m::cancel_comm_monoid_add) fi \<Rightarrow> ('n \<Rightarrow> 'm)"
  is "\<lambda>i. case i of
    Some (N,f,g) \<Rightarrow> if def_fi' (N,f,g) then restrict N 0 f else (\<lambda>_. 0) |
    None \<Rightarrow> (\<lambda>_. 0)"
  by (auto simp: fi'_option_eq_def def_fi'_def fi'_eq_def
      split: option.splits if_splits prod.splits)

lift_definition outf_fi :: "('n,'m::cancel_comm_monoid_add) fi \<Rightarrow> ('n \<Rightarrow> 'm)" is
  "\<lambda>i. case i of
    Some (N,f,g) \<Rightarrow> if def_fi' (N,f,g) then restrict (-N) 0 g else (\<lambda>_. 0) |
    None \<Rightarrow> (\<lambda>_. 0)"
  by (auto simp: fi'_option_eq_def def_fi'_def fi'_eq_def
      split: option.splits if_splits prod.splits)

text \<open>Constructor function avoiding Some...\<close>

lift_definition fi :: "'n set \<Rightarrow> ('n \<Rightarrow> 'm) \<Rightarrow> ('n \<Rightarrow> 'm) \<Rightarrow> ('n,'m::cancel_comm_monoid_add) fi" is
  "\<lambda>N1 i1 o1. Some (N1, i1, o1)" .

text \<open>Notation for the invalid element. As discussed for flow graphs, None is the representation.\<close>

instantiation fi :: (type,type) bot
begin
lift_definition bot_fi :: "('n,'m :: cancel_comm_monoid_add) fi" is None .
instance ..
end

text \<open>Simplification rules for accessor functions\<close>

lemma dom_fi_bot[simp]: "dom_fi bot = {}"
  by (transfer, simp)

lemma outf_fi_bot[simp]: "outf_fi bot = (\<lambda>_. 0)"
  by (transfer, simp)

lemma inf_fi_bot[simp]: "inf_fi bot = (\<lambda>_. 0)"
  by (transfer, simp)

lemma dom_fi_fi[simp]:
  "fi N1 i1 o1 \<noteq> bot \<Longrightarrow> dom_fi (fi N1 i1 o1) = N1"
  by (transfer, auto simp: def_fi'_def fi'_option_eq_def)

lemma inf_fi_fi[simp]:
  "fi N1 i1 o1 \<noteq> bot \<Longrightarrow> inf_fi (fi N1 i1 o1) = restrict N1 0 i1"
  by (transfer, auto simp: def_fi'_def fi'_option_eq_def)

lemma outf_fi_fi[simp]:
  "fi N1 i1 o1 \<noteq> bot \<Longrightarrow> outf_fi (fi N1 i1 o1) = restrict (-N1) 0 o1"
  by (transfer, auto simp: def_fi'_def fi'_option_eq_def)

lemma dom_fi_finite[simp]: "finite (dom_fi i)"
  by (transfer, auto split: option.splits simp: def_fi'_def)

text \<open>Establish validity of flow interfaces.\<close>

lemma fiI[simp,intro]: "finite N1 \<Longrightarrow> fi N1 i1 o1 \<noteq> bot"
  by (transfer, auto simp: fi'_option_eq_def def_fi'_def)

text \<open>Establish equality of flow interfaces.\<close>

lemma fi_cong:
  assumes "N1 = N2" "\<forall>n \<in> N1. i1 n = i2 n" "\<forall>n \<in> -N1. o1 n = o2 n"
  shows "fi N1 i1 o1 = fi N2 i2 o2"
  using assms
  by (transfer, auto simp: fi'_option_eq_def fi'_eq_def def_fi'_def)

lemma fi_eqI2:
  fixes i1 i2 :: "('n,'m::cancel_comm_monoid_add) fi"
  assumes "i1 \<noteq> bot \<Longrightarrow> i1 = i2" "i2 \<noteq> bot \<Longrightarrow> i2 = i1"
  shows "i1 = i2"
  using assms
  by auto

(* We need the assumptions that both i1 and i2 do not equal bot as dom_fi, inf_fi and
    outf_fi depend on this information. *)
lemma fi_eqI:
  assumes "i1 \<noteq> bot" "i2 \<noteq> bot"
    and "dom_fi i1 = dom_fi i2"
    "inf_fi i1 = inf_fi i2 on (dom_fi i1)"
    "outf_fi i1 = outf_fi i2 on (-dom_fi i1)"
  shows "i1 = i2"
  using assms
  apply transfer
  by (auto split: option.splits simp: fi'_option_eq_def fi'_eq_def)

lemma fi_components[simp]:
  assumes "i \<noteq> bot"
  shows "fi (dom_fi i) (inf_fi i) (outf_fi i) = i"
  apply (rule fi_eqI)
  using assms by simp+

subsection \<open>Flow Interfaces are a commutative monoid @{cite \<open>def. 6, thm. 1\<close> krishna20}\<close>

instantiation fi :: (type,cancel_comm_monoid_add) comm_monoid_add
begin

text \<open>Empty flow interface is unit element:\<close>

definition zero_fi where
  "zero_fi \<equiv> fi {} (\<lambda>_.0) (\<lambda>_.0)"

lemma zero_fi_ne_bot[simp]:
  "0 \<noteq> (bot :: ('n,'m::cancel_comm_monoid_add) fi)"
  unfolding zero_fi_def bot_fi_def fi_def def_fi'_def
  apply simp
  using fi.abs_eq_iff unfolding fi'_option_eq_def def_fi'_def
  apply (auto split: option.splits if_splits) by force

text \<open>The implicit definition of flow interface sums according to @{cite \<open>def. 6\<close> krishna20}\<close>

definition is_sum_fi
  :: "('n,'m) fi \<Rightarrow> ('n,'m) fi \<Rightarrow> ('n,'m::cancel_comm_monoid_add) fi \<Rightarrow> bool" where
  "is_sum_fi i1 i2 i12 \<equiv>
    i1 \<noteq> bot \<and> i2 \<noteq> bot \<and> i12 \<noteq> bot \<and>
    dom_fi i1 \<inter> dom_fi i2 = {} \<and>
    dom_fi i1 \<union> dom_fi i2 = dom_fi i12 \<and>
    (\<forall>n \<in> dom_fi i1. inf_fi i1 n = inf_fi i12 n + outf_fi i2 n) \<and>
    (\<forall>n \<in> dom_fi i2. inf_fi i2 n = inf_fi i12 n + outf_fi i1 n) \<and>
    (\<forall>n \<in> -dom_fi i12. outf_fi i12 n = outf_fi i1 n + outf_fi i2 n)"

lemma is_sum_fi_unique:
  assumes "is_sum_fi i1 i2 i12"
  shows "\<And>i12'. is_sum_fi i1 i2 i12' \<Longrightarrow> i12 = i12'"
proof (rule fi_eqI)
  fix i12'
  assume *: "is_sum_fi i1 i2 i12'"

  show "i12 \<noteq> bot" "i12' \<noteq> bot" "dom_fi i12 = dom_fi i12'"
    using assms *
    unfolding is_sum_fi_def
    by simp_all

  show "inf_fi i12 = inf_fi i12' on dom_fi i12"
    using assms *
    unfolding is_sum_fi_def dom_fi_def inf_fi_def outf_fi_def
    by (auto split: option.splits)

  show "outf_fi i12 = outf_fi i12' on -dom_fi i12"
    using assms *
    unfolding is_sum_fi_def dom_fi_def inf_fi_def outf_fi_def
    by (auto split: option.splits)
qed

lemma is_sum_fi_sym:
  "is_sum_fi i1 i2 i12 \<longleftrightarrow> is_sum_fi i2 i1 i12"
  unfolding is_sum_fi_def
  by (auto simp: algebra_simps)

lemma is_sum_assoc_rl:
  assumes "is_sum_fi i2 i3 i23" "is_sum_fi i1 i23 i123"
  shows "\<exists>i12. is_sum_fi i1 i2 i12 \<and> is_sum_fi i12 i3 i123"
proof -
  let ?N1 = "dom_fi i1" let ?i1 = "inf_fi i1" let ?o1 = "outf_fi i1"
  let ?N2 = "dom_fi i2" let ?i2 = "inf_fi i2" let ?o2 = "outf_fi i2"
  let ?N3 = "dom_fi i3" let ?i3 = "inf_fi i3" let ?o3 = "outf_fi i3"
  let ?N23 = "dom_fi i23" let ?i23 = "inf_fi i23" let ?o23 = "outf_fi i23"
  let ?N123 = "dom_fi i123" let ?i123 = "inf_fi i123" let ?o123 = "outf_fi i123"
  let ?N12 = "dom_fi i1 \<union> dom_fi i2"
  let ?i12 = "\<lambda>n. if n \<in> ?N12 then inf_fi i123 n + outf_fi i3 n else 0"
  let ?o12 = "\<lambda>n. if n \<in> -?N12 then outf_fi i1 n + outf_fi i2 n else 0"

  have *: "is_sum_fi i1 i2 (fi ?N12 ?i12 ?o12)"
  proof -
    have "\<forall>n\<in>?N1. ?i1 n = ?i123 n + ?o3 n + ?o2 n"
    proof 
      fix n assume "n \<in> ?N1"
      hence "?o23 n = ?o2 n + ?o3 n" "?i1 n = ?i123 n + ?o23 n"
        using assms unfolding is_sum_fi_def by auto
      thus "?i1 n = ?i123 n + ?o3 n + ?o2 n" by (simp add: ac_simps)
    qed
    moreover have "\<forall>n\<in>?N2. ?i2 n = ?i123 n + ?o3 n + ?o1 n"
    proof
      fix n assume "n \<in> ?N2"
      hence "?i2 n = ?i23 n + ?o3 n" "?i23 n = ?i123 n + ?o1 n"
        using assms unfolding is_sum_fi_def by auto
      thus "?i2 n = ?i123 n + ?o3 n + ?o1 n" by (simp add: ac_simps)
    qed
    ultimately show ?thesis
      using assms
      unfolding is_sum_fi_def
      by auto
  qed

  have "\<forall>n\<in>?N3. ?i3 n = ?i123 n + ?o12 n"
  proof
    fix n assume A: "n \<in> ?N3"
    moreover have "?N3 \<subseteq> -?N12"
      using assms unfolding is_sum_fi_def by auto
    ultimately have A': "n \<in> -?N12" by blast
    hence "?i3 n = ?i23 n + ?o2 n"
      "?i23 n = ?i123 n + ?o1 n" "?o12 n = ?o1 n + ?o2 n"
      using assms A unfolding is_sum_fi_def by auto
    thus "?i3 n = ?i123 n + ?o12 n" using A' by (auto simp: ac_simps)
  qed
  moreover have "\<forall>n\<in>- ?N123. ?o123 n = ?o12 n + ?o3 n"
  proof
    fix n assume A: "n \<in> -?N123"
    hence "?o12 n = ?o1 n + ?o2 n" "?o23 n = ?o2 n + ?o3 n" "?o123 n = ?o1 n + ?o23 n"
      using assms unfolding is_sum_fi_def by auto
    moreover have "n \<notin> ?N12" using A assms unfolding is_sum_fi_def by auto
    ultimately show "?o123 n = ?o12 n + ?o3 n" by (simp add: ac_simps)
  qed
  moreover have "?N12 \<inter> ?N3 = {} \<and> ?N123 = ?N12 \<union> ?N3"
    using assms unfolding is_sum_fi_def by auto 
  ultimately have "is_sum_fi (fi ?N12 ?i12 ?o12) i3 i123"
    using assms
    unfolding is_sum_fi_def
    by simp
  thus ?thesis using * by blast
qed

lemma is_sum_assoc_lr:
  assumes "is_sum_fi h1 h2 h12" "is_sum_fi h12 h3 h123"
  shows "\<exists>h23. is_sum_fi h2 h3 h23 \<and> is_sum_fi h1 h23 h123"
proof -
  (* second direction of associativity based on first one and commutativity*)
  have "is_sum_fi h3 h12 h123"
    using is_sum_fi_sym assms by blast
  then obtain h13 where *: "is_sum_fi h3 h1 h13" "is_sum_fi h13 h2 h123"
    using is_sum_assoc_rl[of h1 h2 h12 h3 h123] assms by blast
  hence "is_sum_fi h2 h13 h123"
    using is_sum_fi_sym by blast
  then obtain h23' where "is_sum_fi h2 h3 h23'" "is_sum_fi h23' h1 h123"
    using is_sum_assoc_rl * by blast
  thus ?thesis
    using is_sum_fi_sym assms
    by blast
qed

lemma is_sum_fi_unit:
  "i1 \<noteq> bot \<Longrightarrow> is_sum_fi 0 i1 i1"
  unfolding is_sum_fi_def zero_fi_def
  by (auto)

text \<open>Here, we define the actual addition of flow interfaces by obtaining an implicitly
provided sum if available.\<close>

definition plus_fi
  :: "('n,'m) fi \<Rightarrow> ('n,'m) fi \<Rightarrow> ('n,'m::cancel_comm_monoid_add) fi" where
  "plus_fi i1 i2 \<equiv>
    if (\<exists>i12. is_sum_fi i1 i2 i12)
      then (THE i12. is_sum_fi i1 i2 i12)
      else bot"

lemma plus_fi_ops_exist:
  assumes "i1 + i2 \<noteq> (bot :: ('n,'m::cancel_comm_monoid_add) fi)"
  shows "i1 \<noteq> bot" "i2 \<noteq> bot"
  using assms unfolding plus_fi_def is_sum_fi_def
  by auto

lemma plus_fi_bot_bot[simp]: "bot + h = bot" "h + bot = (bot :: ('n,'m::cancel_comm_monoid_add) fi)"
  unfolding bot_fi_def plus_fi_def is_sum_fi_def by auto

text \<open>Converting between the explicit and implicit representations of sums:\<close>

lemma plus_fi_to_is_sum_fi:
  assumes "i1 + i2 = i12" "i12 \<noteq> bot"
  shows "is_sum_fi i1 i2 i12"
proof -
  obtain i12' where *: "is_sum_fi i1 i2 i12'"
    using assms unfolding plus_fi_def by (auto split: if_splits)
  moreover have **: "(THE i12. is_sum_fi  i1 i2 i12) = i12"
    using assms unfolding plus_fi_def by auto
  ultimately have "is_sum_fi i1 i2 (THE i12. is_sum_fi i1 i2 i12)"
    using is_sum_fi_unique theI by metis
  thus ?thesis
    using ** is_sum_fi_unique by simp
qed

lemma is_sum_fi_to_plus_fi:
  assumes "is_sum_fi i1 i2 i12"
  shows "i1 + i2 = i12"
proof -
  have *: "i1 + i2 = (THE i12. is_sum_fi i1 i2 i12)"
    using assms unfolding plus_fi_def is_sum_fi_def by auto
  hence "is_sum_fi i1 i2 (THE i12. is_sum_fi i1 i2 i12)"
    using is_sum_fi_unique assms theI by metis
  hence "i12 = (THE i12. is_sum_fi i1 i2 i12)"
    using assms is_sum_fi_unique by auto
  thus ?thesis
    using * by simp
qed

lemma unfold_inf_fi:
  assumes "i1 + i2 \<noteq> bot" "x \<in> dom_fi i1"
  shows "inf_fi i1 x = inf_fi (i1 + i2) x + outf_fi i2 x"
  using assms is_sum_fi_def plus_fi_to_is_sum_fi by fastforce

text \<open>Simplification of domain calculations of flow interfaces\<close>

lemma dom_fi_plus_fi[simp]:
  "i1 + i2 \<noteq> bot \<Longrightarrow> dom_fi (i1 + i2) = dom_fi i1 \<union> dom_fi i2"
  "i1 + i2 \<noteq> bot \<Longrightarrow> dom_fi i1 \<inter> dom_fi i2 = {}"
  unfolding plus_fi_def
   apply (auto split: if_splits simp: is_sum_fi_unique the_equality)
     apply (metis UnE is_sum_fi_def)
  apply (metis UnI1 is_sum_fi_def)
   apply (metis UnI2 is_sum_fi_def)
  by (metis insert_Diff insert_disjoint(1) is_sum_fi_def)

text \<open>Proof of flow interfaces being a commutative monoid @{cite \<open>thm. 1\<close> krishna20}\<close>

instance
proof (standard,goal_cases)
  case (1 a b c)
  then show ?case
  proof (rule fi_eqI2, goal_cases)
    case 1
    then have A: "is_sum_fi (a + b) c (a + b + c)"
      by (simp add: plus_fi_to_is_sum_fi)
    then have "a + b \<noteq> bot"
      unfolding is_sum_fi_def by simp
    then have "is_sum_fi a b (a + b)"
      by (simp add: plus_fi_to_is_sum_fi)
    then obtain bc where "is_sum_fi b c bc" "is_sum_fi a bc (a + b + c)"
      using is_sum_assoc_lr[of a b "a + b" c "a + b + c"] A by auto
    then have "a + bc = a + b + c" "b + c = bc"
      by (simp_all add: is_sum_fi_to_plus_fi)
    then show ?case
      by simp
  next
    case 2
    then have A: "is_sum_fi a (b + c) (a + (b + c))"
      by (simp add: plus_fi_to_is_sum_fi)
    then have "b + c \<noteq> bot"
      unfolding is_sum_fi_def by simp
    then have "is_sum_fi b c (b + c)"
      by (simp add: plus_fi_to_is_sum_fi)
    then obtain ab where "is_sum_fi ab c (a + (b + c))" "is_sum_fi a b ab"
      using is_sum_assoc_rl[of b c "b + c" a "a + (b + c)"] A by auto
    then have "ab + c = a + (b + c)" "a + b = ab"
      by (simp_all add: is_sum_fi_to_plus_fi)
    then show ?case
      by simp
  qed
next
  case (2 a b)
  then show ?case
    unfolding plus_fi_def using is_sum_fi_sym by auto
next
  case (3 a)
  then show ?case
    unfolding plus_fi_def
    using is_sum_fi_unit
    apply (cases "a = bot", auto simp: is_sum_fi_unique the_equality)
    unfolding is_sum_fi_def by auto
qed

end

text \<open>Again, flow interfaces are not generally cancellative but only for valid sums:\<close>

lemma is_sum_fi_unique2:
  assumes "is_sum_fi i1 i2 i12" "is_sum_fi i1 i2' i12"
  shows "i2 = i2'"
proof (rule fi_eqI)
  show "i2 \<noteq> bot" "i2' \<noteq> bot"
    using assms unfolding is_sum_fi_def by auto
  show *: "dom_fi i2 = dom_fi i2'"
    using assms unfolding is_sum_fi_def by auto
  show "inf_fi i2 = inf_fi i2' on dom_fi i2"
    using assms unfolding is_sum_fi_def by auto
  have "\<forall>n \<in> -dom_fi i12. outf_fi i1 n + outf_fi i2 n = outf_fi i1 n + outf_fi i2' n"
    using assms unfolding is_sum_fi_def by auto
  moreover have "\<forall>n \<in> dom_fi i1. inf_fi i12 n + outf_fi i2 n = inf_fi i12 n + outf_fi i2' n"
    using assms unfolding is_sum_fi_def by auto
  ultimately show "outf_fi i2 = outf_fi i2' on -dom_fi i2"
    using assms unfolding is_sum_fi_def by auto
qed

lemma plus_fi_cancel_right:
  fixes a b c :: "('a,'b::cancel_comm_monoid_add) fi"
  assumes "a + b \<noteq> bot" "a + b = a + c"
  shows "b = c"
proof -
  have "a \<noteq> bot" "b \<noteq> bot" "c \<noteq> bot"
    using assms plus_fi_ops_exist by auto
  hence "is_sum_fi a b (a + c)" "is_sum_fi a c (a + c)"
    using plus_fi_to_is_sum_fi assms by auto
  thus "b = c"
    using is_sum_fi_unique2 by blast
qed

lemma plus_fi_cancel_left:
  assumes "a + c \<noteq> (bot :: ('a,'b::cancel_comm_monoid_add) fi)" "a + c = b + c"
  shows "a = b"
  using plus_fi_cancel_right[of c a b] assms by (simp add: algebra_simps)

section \<open>Computations on Flow Interfaces\<close>

text \<open>Here we try to simplify validity proofs for flow interfaces\<close>

lemma fi_plus_fi_nbot:
  assumes "X1 \<inter> X2 = {}" "\<forall>x \<in> X1. i1 x = i x + o2 x" "\<forall>x \<in> X2. i2 x = i x + o1 x"
    "finite X1" "finite X2"
  shows "fi X1 i1 o1 + fi X2 i2 o2 \<noteq> bot"
proof -
  let ?i1 = "fi X1 i1 o1" let ?i2 = "fi X2 i2 o2" let ?i12' = "?i1 + ?i2"
  let ?i12 = "fi (X1 \<union> X2) i (\<lambda>x. o1 x + o2 x)"

  have nbot: "?i1 \<noteq> bot" "?i2 \<noteq> bot" "?i12 \<noteq> bot"
    using assms fiI by auto
  then have "is_sum_fi ?i1 ?i2 ?i12"
    using assms unfolding is_sum_fi_def by auto
  then have "?i1 + ?i2 = ?i12"
    using is_sum_fi_to_plus_fi by blast
  then show ?thesis
    using nbot is_sum_fi_to_plus_fi by simp
qed

text \<open>For some flow domains the following rule might be simpler to apply:\<close>
text \<open>Exploiting a stronger flow domain enables us to check equalities more efficiently!\<close>

lemma fi_plus_fi_nbot':
  fixes i1 i2 o1 o2 :: "'a \<Rightarrow> 'b :: ordered_cancel_comm_monoid_diff"
  assumes "X1 \<inter> X2 = {}" "\<forall>x \<in> X1. i1 x \<ge> o2 x" "\<forall>x \<in> X2. i2 x \<ge> o1 x" "finite X1" "finite X2"
  shows "fi X1 i1 o1 + fi X2 i2 o2 \<noteq> bot"
  apply (rule fi_plus_fi_nbot[of _ _ _ "\<lambda>x. if x \<in> X1 then i1 x - o2 x else i2 x - o1 x"])
  using assms by (auto simp: ordered_cancel_comm_monoid_diff_class.diff_add)

lemma fi_plus_fg_calc:
  fixes i1 i2 o1 o2 :: "'a \<Rightarrow> 'b :: ordered_cancel_comm_monoid_diff"
  assumes "X1 \<inter> X2 = {}" "\<forall>x \<in> X1. i1 x \<ge> o2 x" "\<forall>x \<in> X2. i2 x \<ge> o1 x" "finite X1" "finite X2"
  shows "fi X1 i1 o1 + fi X2 i2 o2 =
    fi (X1 \<union> X2) (\<lambda>x. if x \<in> X1 then i1 x - o2 x else i2 x - o1 x) (\<lambda>x. o1 x + o2 x)"
proof -
  let ?i1 = "fi X1 i1 o1" let ?i2 = "fi X2 i2 o2"
  let ?i12 = "fi (X1 \<union> X2) (\<lambda>x. if x \<in> X1 then i1 x - o2 x else i2 x - o1 x) (\<lambda>x. o1 x + o2 x)"

  have *: "is_sum_fi ?i1 ?i2 ?i12"
    unfolding is_sum_fi_def
    using assms
    by (auto simp: algebra_simps ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
  show ?thesis
    by (fact is_sum_fi_to_plus_fi[OF *])
qed

end
