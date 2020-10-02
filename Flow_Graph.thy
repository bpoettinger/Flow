\<^marker>\<open>creator Bernhard Pöttinger\<close>

chapter \<open>Flow Graph\<close>
theory Flow_Graph
  imports Main Auxiliary
begin

paragraph \<open>Summary\<close>
text \<open>This theory implements the basic data structure used by the Flow Framework
@{cite krishna20}: flow graphs.\<close>

section \<open>Flow Graph\<close>

subsection \<open>Preliminary Flow Graphs\<close>

text \<open>We start with the definition of a preliminary type for flow graphs.
Preliminary flow graphs (N,e,f) consist of a set of nodes N, a function e representing directed
edges (e.g. e x y represents the edge from x to y), and a function f labeling all nodes with
their so-called flow.
As e and f both are only defined on N this representation is not unique.
We will lift this type to a quotient type to obtain a unique representation.\<close>

type_synonym ('n,'m) fg' = "'n set \<times> ('n \<Rightarrow> 'n \<Rightarrow> 'm \<Rightarrow> 'm) \<times> ('n \<Rightarrow> 'm)"

text \<open>We define the notion of equality for preliminary flow graphs.\<close>

definition fg'_eq :: "('n,'m) fg' \<Rightarrow> ('n,'m) fg' \<Rightarrow> bool" where
  "fg'_eq \<equiv> \<lambda>(N1,e1,f1) (N2,e2,f2). N1 = N2 \<and> (e1 = e2 on N1) \<and> (f1 = f2 on N1)"

lemma fg'_eqI:
  assumes "N1 = N2" "e1 = e2 on N1" "f1 = f2 on N1"
  shows "fg'_eq (N1,e1,f1) (N2,e2,f2)"
  using assms unfolding fg'_eq_def by simp

text \<open>The central ingredient to define valid flow graphs: the flow equation
(@{cite \<open>p. 313\<close> krishna20}).
The flow equation describes if a label function f is a solution to an equation system
induced by a graph (N,e). If there exists an i such that f is a solution to the flow equation
then (N,e,f) is a valid flow graph. Function i is called inflow.\<close>

definition
  flow_eq' :: "('n,'m) fg' \<Rightarrow> ('n \<Rightarrow> 'm::cancel_comm_monoid_add) \<Rightarrow> bool"
where
  "flow_eq' \<equiv> \<lambda>(N,e,f) i. \<forall>n \<in> N. f n = i n + (\<Sum>n' \<in> N. e n' n (f n'))"

lemma flow_eq'_eq: "fg'_eq h1 h2 \<Longrightarrow> flow_eq' h1 i \<longleftrightarrow> flow_eq' h2 i"
  unfolding fg'_eq_def flow_eq'_def
  by auto

text \<open>For historical reasons we also keep this notation for flow equations:\<close>

definition
  flow_eq2'
  :: "'n set \<Rightarrow> ('n \<Rightarrow> 'n \<Rightarrow> 'm \<Rightarrow> 'm) \<Rightarrow> ('n \<Rightarrow> 'm) \<Rightarrow> ('n \<Rightarrow> 'm::cancel_comm_monoid_add) \<Rightarrow> bool"
where
  "flow_eq2' N e f i = flow_eq' (N,e,f) i"

text \<open>A flow graph is valid iff. there is an inflow i such that f solves the flow equation.
Furthermore, the domain of the flow graph must be finite. (@{cite \<open>def. 3\<close> krishna20})\<close>

definition def_fg' :: "('n,'m::cancel_comm_monoid_add) fg' \<Rightarrow> bool" where
  "def_fg' \<equiv> \<lambda>(N,e,f). (\<exists>i. flow_eq' (N,e,f) i) \<and> finite N"

text \<open>Before we can define the final flow graph type using a quotient type,
we have to lift preliminary flow graphs to the option type in order to obtain a representation
for invalid flow graphs in the quotient type.\<close>

text \<open>The notion of equality for is lifted canonically:\<close>

definition fg'_option_eq
  :: "('n,'m) fg' option \<Rightarrow> ('n,'m::cancel_comm_monoid_add) fg' option \<Rightarrow> bool"
where
  "fg'_option_eq \<equiv> \<lambda>h1 h2. 
    case (h1,h2) of
       (Some h1', Some h2') \<Rightarrow> if \<not>def_fg' h1' \<and> \<not>def_fg' h2' then True else
                               if def_fg' h1' \<and> def_fg' h2' then fg'_eq h1' h2' else
                               False
     | (None, None) \<Rightarrow> True
     | (Some h1', None) \<Rightarrow> \<not>def_fg' h1'
     | (None, Some h2') \<Rightarrow> \<not>def_fg' h2'"

subsection \<open>Flow Graph\<close>

text \<open>Defining the actual type for flow graphs using our notion of equality.
(@{cite \<open>def. 3\<close> krishna20})\<close>

quotient_type (overloaded) ('n,'m) fg =
  "('n,'m::cancel_comm_monoid_add) fg' option" / fg'_option_eq
    apply (rule equivpI)
  subgoal by (auto intro: reflpI simp: fg'_option_eq_def fg'_eq_def split: option.splits)
  subgoal by (auto intro: sympI simp: fg'_option_eq_def fg'_eq_def split: option.splits)
  subgoal by (rule transpI, auto simp: fg'_option_eq_def fg'_eq_def split: option.splits if_splits)
  done

text \<open>A constructor function that allows us to define flow graphs without mentioning Some.\<close>

lift_definition fg
  :: "'n set \<Rightarrow> ('n \<Rightarrow> 'n \<Rightarrow> 'm \<Rightarrow> 'm) \<Rightarrow> ('n \<Rightarrow> 'm) \<Rightarrow>
      ('n,'m::cancel_comm_monoid_add) fg"
  is "\<lambda>N e f. Some (N,e,f)" .

text \<open>Accessor functions that provide us with the components of flow graphs.
For invalid flow graphs we obtain default values. edge function and flow function are set to
default values outside the domain of their flow graph.\<close>

lift_definition dom_fg :: "('n,'m::cancel_comm_monoid_add) fg \<Rightarrow> 'n set"
  is "\<lambda>h. case h of Some (N,e,f) \<Rightarrow> if def_fg' (N,e,f) then N else {} | _ \<Rightarrow> {}"
  unfolding fg'_option_eq_def def_fg'_def fg'_eq_def
  by (auto split: option.splits if_splits)

lift_definition flow_fg :: "('n,'m::cancel_comm_monoid_add) fg \<Rightarrow> ('n \<Rightarrow> 'm)"
  is "\<lambda>h. case h of
    Some (N,e,f) \<Rightarrow> if def_fg' (N,e,f) then restrict N 0 f else (\<lambda>_. 0) |
    None \<Rightarrow> (\<lambda>_. 0)"
  unfolding fg'_option_eq_def fg'_eq_def
  by (auto split: option.splits)

lift_definition edge_fg :: "('n,'m::cancel_comm_monoid_add) fg \<Rightarrow> ('n \<Rightarrow> 'n \<Rightarrow> 'm \<Rightarrow> 'm)"
  is "\<lambda>h. case h of
    Some (N,e,f) \<Rightarrow> if def_fg' (N,e,f) then restrict N (\<lambda>_ _. 0) e else (\<lambda>_ _ _. 0) |
    None \<Rightarrow> (\<lambda>_ _ _. 0)"
  unfolding fg'_option_eq_def fg'_eq_def
  by (auto split: option.splits)

lemma dom_fg_finite[simp]: "finite (dom_fg h)"
  apply (transfer)
  unfolding def_fg'_def
  by (auto split: option.splits)

text \<open>Lift the flow equation to the actual flow graph type. (@{cite \<open>p. 313\<close> krishna20})\<close>

lift_definition flow_eq :: "('n,'m) fg \<Rightarrow> ('n \<Rightarrow> 'm :: cancel_comm_monoid_add) \<Rightarrow> bool" is
  "\<lambda>h i. case h of Some h' \<Rightarrow> if def_fg' h' then flow_eq' h' i else False | _ \<Rightarrow> False"
  unfolding fg'_option_eq_def fg'_eq_def
  apply (auto split: option.splits if_splits)
  subgoal for e1 f1 N1 e2 f2
    using flow_eq'_eq[OF fg'_eqI[of N1 N1 e1 e2 f1 f2]] by auto
  done

lemma flow_eq_outside_irrelevant:
  assumes "flow_eq h i"
  shows "flow_eq h (restrict (dom_fg h) 0 i)"
  using assms
  apply transfer
  by (auto split: option.splits if_splits simp: def_fg'_def flow_eq'_def)

text \<open>Notation for the invalid flow graph:\<close>

instantiation fg :: (type,type) bot
begin
lift_definition bot_fg :: "('n,'m::cancel_comm_monoid_add) fg" is None .
instance ..
end

lemma dom_fg_bot[simp]: "dom_fg bot = {}"
  apply transfer unfolding bot_fg_def dom_fg_def by simp

text \<open>Some simplification rules for accessor functions and constructor.\<close>

lemma dom_fg_fg[simp]:
  "fg N e f \<noteq> bot \<Longrightarrow> dom_fg (fg N e f) = N"
  apply transfer by (auto split: option.splits simp: fg'_option_eq_def)

lemma edge_fg_fg[simp]:
  "fg N e f \<noteq> bot \<Longrightarrow> edge_fg (fg N e f) = restrict N (\<lambda>_ _. 0) e"
  apply transfer by (auto split: option.splits simp: fg'_option_eq_def)

lemma flow_fg_fg[simp]:
  "fg N e f \<noteq> bot \<Longrightarrow> flow_fg (fg N e f) = restrict N 0 f"
  apply transfer by (auto split: option.splits simp: fg'_option_eq_def)

lemma fg_restrict_components[simp]:
  assumes "a \<noteq> bot"
  shows "fg (dom_fg a) (restrict (dom_fg a) x0 (edge_fg a)) (restrict (dom_fg a) x1 (flow_fg a)) = a"
  using assms
  apply transfer
  by (auto split: option.splits if_splits
      simp: fg'_option_eq_def def_fg'_def fg'_eq_def flow_eq'_def)

lemma fg_components[simp]:
  "a \<noteq> bot \<Longrightarrow> fg (dom_fg a) (edge_fg a) (flow_fg a) = a"
  apply transfer
  by (auto split: option.splits if_splits
      simp: fg'_option_eq_def def_fg'_def fg'_eq_def flow_eq'_def)

text \<open>Part 1 from @{cite \<open>lemma 1\<close> krishna20}: There exists an inflow for valid flow graphs.
As we extended the notion of flow graphs with validity of flow graphs we add the additional
assumption that h is valid.\<close>

lemma flow_eq_exists:
  assumes "h \<noteq> bot"
  shows "\<exists>i. flow_eq h i"
  using assms
  apply transfer by (auto simp: fg'_option_eq_def def_fg'_def split: option.splits if_splits)

text \<open>Part 2 from @{cite \<open>lemma 1\<close> krishna20}: The inflow of flow graphs is unique\<close>

lemma flow_eq_unique:
  assumes "flow_eq h i1" "flow_eq h i2"
  shows "i1 = i2 on (dom_fg h)"
  using assms
  apply transfer by (auto split: option.splits simp: flow_eq'_def)

lemma pos_flow_nbot:
  assumes "flow_fg h x \<noteq> 0"
  shows "h \<noteq> bot"
  using assms unfolding flow_fg_def bot_fg_def apply (auto split: option.splits if_splits)
  by (metis (no_types, lifting) assms flow_fg.abs_eq option.simps(4))

lemma pos_flow_dom:
  assumes "flow_fg h x \<noteq> 0"
  shows "x \<in> dom_fg h"
  using assms unfolding flow_fg_def bot_fg_def apply (auto split: option.splits if_splits)
  by (metis pos_flow_nbot assms fg_components flow_fg_fg)

text \<open>Determining the validity of constructed flow graphs:\<close>

lemma fgI:
  assumes "f = (\<lambda>n. i n + (\<Sum>n' \<in> N. e n' n (f n'))) on N" "finite N"
  shows "fg N e f \<noteq> bot"
  using assms
  apply transfer
  by (auto simp: fg'_option_eq_def def_fg'_def flow_eq'_def)

lemma fgI2:
  assumes "flow_eq (fg N e f) i" "finite N"
  shows "fg N e f \<noteq> bot"
  using assms
  apply transfer
  by (auto simp: fg'_option_eq_def def_fg'_def flow_eq'_def split: if_splits)

lemma flow_eqI:
  assumes "f = (\<lambda>n. i n + (\<Sum>n' \<in> N. e n' n (f n'))) on N" "finite N"
  shows "flow_eq (fg N e f) i"
  using assms
  apply transfer
  by (auto simp add: flow_eq'_def def_fg'_def)

text \<open>Gain access to flow equation for valid flow graphs:\<close>

lemma fgE:
  assumes "h \<noteq> bot"
  shows "(\<exists>i. finite (dom_fg h) \<and> flow_fg h =
    (\<lambda>n. i n + (\<Sum>n' \<in> dom_fg h. edge_fg h n' n (flow_fg h n'))) on dom_fg h)"
  using assms
  by (transfer, auto simp: fg'_option_eq_def def_fg'_def flow_eq'_def
      split: option.splits if_splits)

lemma fgE': 
  "flow_eq h i \<Longrightarrow> \<forall>n \<in> dom_fg h.
    flow_fg h n = i n + (\<Sum>n' \<in> dom_fg h. edge_fg h n' n (flow_fg h n'))"
  by (transfer, auto simp: fg'_option_eq_def def_fg'_def flow_eq'_def
      split: option.splits if_splits)

lemma fgE'': 
  "flow_eq (fg N e f) i \<Longrightarrow> N \<noteq> {} \<Longrightarrow> \<forall>n \<in> N. f n = i n + (\<Sum>n' \<in> N. e n' n (f n'))"
  by (transfer, auto split: option.splits if_splits simp: flow_eq'_def)

text \<open>Determine equality of flow graphs:\<close>

lemma fg_eqI:
  assumes "h1 \<noteq> bot" "h2 \<noteq> bot" "dom_fg h1 = dom_fg h2"
    "edge_fg h1 = edge_fg h2 on dom_fg h1" "flow_fg h1 = flow_fg h2 on dom_fg h2"
  shows "h1 = h2"
  using assms
  apply transfer
  by (auto split: option.splits simp: fg'_option_eq_def fg'_eq_def)

lemma fg_eqI2:
  assumes "h1 \<noteq> bot \<Longrightarrow> h1 = h2" "h2 \<noteq> bot \<Longrightarrow> h1 = h2"
  shows "h1 = h2"
  using assms by auto

lemma fg_cong:
  assumes "N1 = N2" "e1 = e2 on N1" "f1 = f2 on N1"
  shows "fg N1 e1 f1 = fg N2 e2 f2"
  using assms
  apply transfer
  by (auto simp: fg'_option_eq_def fg'_eq_def def_fg'_def flow_eq'_def)

lemma fg_eqD:
  assumes "h1 = h2"
  shows "dom_fg h1 = dom_fg h2 \<and> edge_fg h1 = edge_fg h2 on dom_fg h1 \<and>
    flow_fg h1 = flow_fg h2 on dom_fg h2"
  using assms
  unfolding edge_fg_def dom_fg_def flow_fg_def
  by auto

subsection \<open>Flow Graphs are Cancellative Monoids\<close>

instantiation fg :: (type,cancel_comm_monoid_add) comm_monoid_add
begin

text \<open>The unit flow graph is the flow graph consisting of no nodes. @{cite krishna20}\<close>

definition zero_fg where
  "zero_fg \<equiv> fg {} (\<lambda>_ _ _. 0) (\<lambda>_. 0)"

lemma zero_fg_nbot [simp]: "0 \<noteq> (bot :: ('n,'m :: cancel_comm_monoid_add) fg)"
  unfolding zero_fg_def bot_fg_def fg_def   apply (auto)
  by (auto simp: fg.abs_eq_iff fg'_option_eq_def def_fg'_def flow_eq'_def)

lemma dom_fg_zero_fg [simp]: "dom_fg 0 = {}"
  unfolding zero_fg_def using dom_fg_fg by force

text \<open>Addition for flow graphs @{cite \<open>def. 4\<close> krishna20} requires the summands to be disjoint.
The edge and flow functions are merely the combination of the two summand's functions.
We have to additionally take validity into account in our definition.\<close>

definition
  plus_fg :: "('n,'m) fg \<Rightarrow> ('n,'m) fg \<Rightarrow> ('n,'m :: cancel_comm_monoid_add) fg"
where
  "plus_fg h1 h2 \<equiv>
    let N = dom_fg h1 \<union> dom_fg h2;
        e = combine (dom_fg h1) (dom_fg h2) (\<lambda>_ _. 0) (edge_fg h1) (edge_fg h2);
        f = combine (dom_fg h1) (dom_fg h2)        0  (flow_fg h1) (flow_fg h2) in
    if h1 \<noteq> bot \<and> h2 \<noteq> bot \<and> dom_fg h1 \<inter> dom_fg h2 = {}
      then fg N e f
      else bot"

lemma plus_fg_fg:
  assumes "fg N1 e1 f1 \<noteq> bot" "fg N2 e2 f2 \<noteq> bot" "N1 \<inter> N2 = {}"
  shows "fg N1 e1 f1 + fg N2 e2 f2 =
    fg (N1 \<union> N2) (combined N1 N2 (\<lambda>_ _. 0) e1 e2) (combined N1 N2 0 f1 f2)"
proof -
  have *:
    "fg (N1 \<union> N2)
      (combined N1 (dom_fg (fg N2 e2 f2)) (\<lambda>_ _. 0) (edge_fg (fg N1 e1 f1)) (edge_fg (fg N2 e2 f2)))
      (combined N1 (dom_fg (fg N2 e2 f2)) 0 (flow_fg (fg N1 e1 f1)) (flow_fg (fg N2 e2 f2))) =
     fg (N1 \<union> N2) (combined N1 N2 (\<lambda>_ _. 0) e1 e2) (combined N1 N2 0 f1 f2)"
    unfolding combined_def
    by (rule fg_cong, auto simp: assms)
  show ?thesis
    using assms *
    unfolding plus_fg_def combined_def
    by (auto simp: Let_def)
qed

lemma plus_fg_fg':
  assumes "fg N1 e1 f1 \<noteq> bot" "fg N2 e2 f2 \<noteq> bot" "N1 \<inter> N2 = {}" "N1 \<union> N2 = N"
      "e = e1 on N1" "e = e2 on N2" "f = f1 on N1" "f = f2 on N2"
    shows "fg N1 e1 f1 + fg N2 e2 f2 = fg N e f"
proof -
  have "fg N1 e1 f1 + fg N2 e2 f2 =
    fg (N1 \<union> N2) (combined N1 N2 (\<lambda>_ _. 0) e1 e2) (combined N1 N2 0 f1 f2)"
    using plus_fg_fg assms by simp
  also have "... = fg N e f"
    apply (rule fg_cong) unfolding combined_def using assms by auto
  finally show ?thesis .
qed

lemma plus_fg_bot_bot[simp]: "bot + h = bot" "h + bot = (bot :: ('n,'m::cancel_comm_monoid_add) fg)"
  unfolding bot_fg_def plus_fg_def by (auto split: option.splits)

lemma def_fg_zero_fg[simp]:
  "0 \<noteq> (bot :: ('a,'b) fg)"
  by auto

lemma plus_fg_ops_exist:
  "h1 + h2 \<noteq> bot \<Longrightarrow> h1 \<noteq> bot \<and> h2 \<noteq> (bot :: ('n,'m :: cancel_comm_monoid_add) fg)"
  unfolding plus_fg_def
  by auto

lemma plus_fg_dom_un[simp]:
  "h1 + h2 \<noteq> bot \<Longrightarrow> dom_fg (h1 + h2) = dom_fg h1 \<union> dom_fg h2"
  unfolding plus_fg_def
  by (auto simp: Let_def split: if_splits)

lemma plus_fg_dom_disj[simp]:
  "h1 + h2 \<noteq> bot \<Longrightarrow> dom_fg h1 \<inter> dom_fg h2 = {}"
  unfolding plus_fg_def
  by (auto simp: Let_def split: if_splits)

lemma flow_fg_plus_fg_on1:
  "h1 + h2 \<noteq> bot \<Longrightarrow> flow_fg (h1 + h2) = flow_fg h1 on (dom_fg h1)"
  unfolding plus_fg_def
  by (auto simp: Let_def split: if_splits)

lemma flow_fg_plus_fg_on2:
  "h1 + h2 \<noteq> bot \<Longrightarrow> flow_fg (h1 + h2) = flow_fg h2 on (dom_fg h2)"
  unfolding plus_fg_def
  by (auto simp: Let_def split: if_splits)

lemma flow_fg_plus_fg_on1':
  "h1 + h2 \<noteq> bot \<Longrightarrow> x \<in> dom_fg h1 \<Longrightarrow> flow_fg (h1 + h2) x = flow_fg h1 x"
  unfolding plus_fg_def
  by (auto simp: Let_def split: if_splits)

lemma flow_fg_plus_fg_on2':
  "h1 + h2 \<noteq> bot \<Longrightarrow> x \<in> dom_fg h2 \<Longrightarrow> flow_fg (h1 + h2) x = flow_fg h2 x"
  unfolding plus_fg_def
  by (auto simp: Let_def split: if_splits)

lemma edge_fg_plus_fg_on1:
  "h1 + h2 \<noteq> bot \<Longrightarrow> edge_fg (h1 + h2) = edge_fg h1 on (dom_fg h1)"
  unfolding plus_fg_def
  by (auto simp: Let_def split: if_splits)

lemma edge_fg_plus_fg_on2:
  "h1 + h2 \<noteq> bot \<Longrightarrow> edge_fg (h1 + h2) = edge_fg h2 on (dom_fg h2)"
  unfolding plus_fg_def
  by (auto simp: Let_def split: if_splits)

lemma edge_fg_plus_fg_on1':
  "h1 + h2 \<noteq> bot \<Longrightarrow> x \<in> dom_fg h1 \<Longrightarrow> edge_fg (h1 + h2) x = edge_fg h1 x"
  unfolding plus_fg_def
  by (auto simp: Let_def split: if_splits)

lemma edge_fg_plus_fg_on2':
  "h1 + h2 \<noteq> bot \<Longrightarrow> x \<in> dom_fg h2 \<Longrightarrow> edge_fg (h1 + h2) x = edge_fg h2 x"
  unfolding plus_fg_def
  by (auto simp: Let_def split: if_splits)

lemma flow_fg_zero_outside_dom:
  "flow_fg h = (\<lambda>_. 0) on (-dom_fg h)"
  unfolding plus_fg_def flow_fg_def dom_fg_def
  by (auto simp: Let_def split: option.splits)

lemma edge_fg_0_outside_dom:
  "x \<in> -dom_fg h \<Longrightarrow> h \<noteq> bot \<Longrightarrow> edge_fg h x = (\<lambda> _ _. 0)"
  by (transfer, auto split: option.splits)

lemma flow_fg_0_outside_dom:
  "x \<in> -dom_fg h \<Longrightarrow> h \<noteq> bot \<Longrightarrow> flow_fg h x = 0"
  by (transfer, auto split: option.splits)

text \<open>@{text split_fg} enables us to decompose a valid flow graph into a sum of valid flow graphs.
This lemma significantly simplifies the proof of @{text plus_fg_assoc} as we have to decompose
(a + b) + c there, this lemma and its existential quantification saves us from stating the
quite verbose decomposition terms manually.\<close>

lemma split_fg:
  assumes "h \<noteq> bot" "dom_fg h = N1 \<union> N2" "N1 \<inter> N2 = {}"
  shows "\<exists>h1 h2. h = h1 + h2 \<and> h1 \<noteq> bot \<and> h2 \<noteq> bot \<and>
    dom_fg h1 = N1 \<and> dom_fg h2 = N2 \<and>
    edge_fg h = edge_fg h1 on N1 \<and> edge_fg h = edge_fg h2 on N2 \<and>
    flow_fg h = flow_fg h1 on N1 \<and> flow_fg h = flow_fg h2 on N2"
proof -
  obtain i where *: "flow_eq h i" using assms(1) flow_eq_exists by auto
  have "finite (dom_fg h)" using assms(1) by simp
  hence **: "finite N1" "finite N2" using assms(2) by auto

  let ?i1 = "\<lambda>n. if n \<in> N1 then i n + (\<Sum>n'\<in>N2. edge_fg h n' n (flow_fg h n')) else 0"
  let ?i2 = "\<lambda>n. if n \<in> N2 then i n + (\<Sum>n'\<in>N1. edge_fg h n' n (flow_fg h n')) else 0"
  let ?f = "flow_fg h" let ?e = "edge_fg h"

  have X1: "fg N1 ?e ?f \<noteq> bot"
  proof (rule fgI)
    show "?f = \<lambda>x. ?i1 x + (\<Sum>n'\<in>N1. ?e n' x (?f n')) on N1"
    proof
      fix n assume "n\<in>N1"
      then have "?f n = i n + (\<Sum>n'\<in>dom_fg h. ?e n' n (?f n'))"
        using assms `n\<in>N1` * fgE'[of h i] by simp
      thus "?f n = ?i1 n + (\<Sum>n'\<in>N1. ?e n' n (?f n'))"
        using assms sum.union_disjoint  * ** \<open>n \<in> N1\<close>
        by (auto simp: Un_commute algebra_simps)
    qed
    show "finite N1" using ** by simp
  qed

  have X2: "fg N2 ?e ?f \<noteq> bot"
  proof (rule fgI)
    show "?f = \<lambda>x. ?i2 x + (\<Sum>n'\<in>N2. ?e n' x (?f n')) on N2"
    proof
      fix n assume "n\<in>N2"
      show "?f n = ?i2 n + (\<Sum>n'\<in>N2. ?e n' n (?f n'))"
      proof -
        have "?f n = i n + (\<Sum>n'\<in>dom_fg h. ?e n' n (?f n'))"
          using assms `n\<in>N2` * fgE'[of h i] by simp
        thus ?thesis
          using assms sum.union_disjoint[of N2 N1 "\<lambda>n'. ?e n' n (?f n')"] * ** \<open>n \<in> N2\<close>
          by (auto simp: Un_commute algebra_simps)
      qed
    qed

    show "finite N2"
      using ** by simp
  qed

  have *: "fg N1 ?e ?f + fg N2 ?e ?f = h"
    using plus_fg_fg' X1 X2 fg_components[of h] assms by metis

  show ?thesis
    apply (rule exI[where x="fg N1 ?e ?f"])
    apply (rule exI[where x="fg N2 ?e ?f"])
    using X1 X2 * assms by simp
qed

lemma plus_fg_assoc:
  fixes a b c :: "('a,'b :: cancel_comm_monoid_add) fg"
  assumes "a + b + c \<noteq> bot"
  shows "a + b + c = a + (b + c)"
proof -
  let ?h = "a + b + c"
  let ?Na = "dom_fg a"
  let ?Nb = "dom_fg b"
  let ?Nc = "dom_fg c"

  (* Exploit split_fg to obtain exactly the parts required by the proof and then
    show the equality between those parts and the actual parts. *)

  have nbot: "a + b + c \<noteq> bot" "a + b \<noteq> bot" "a \<noteq> bot" "b \<noteq> bot" "c \<noteq> bot"
    using assms by auto

  have dom: "dom_fg (a + b) \<inter> ?Nc = {}" "?Na \<inter> ?Nc = {}" "?Na \<inter> ?Nb = {}" "?Nb \<inter> ?Nc = {}"
    "dom_fg (a + b + c) = dom_fg (a + b) \<union> ?Nc" "dom_fg (a + b) = ?Na \<union> ?Nb"
    using nbot plus_fg_dom_disj[of "a + b" c] by auto

  then have "dom_fg (a + b + c) = ?Na \<union> (?Nb \<union> ?Nc)" "?Na \<inter> (?Nb \<union> ?Nc) = {}"
    using dom by blast+

  then obtain h1 h2 where *: "a + b + c = h1 + h2" "dom_fg h1 = ?Na" "dom_fg h2 = ?Nb \<union> ?Nc"
     "edge_fg ?h = edge_fg h1 on ?Na" "edge_fg ?h = edge_fg h2 on ?Nb \<union> ?Nc"
     "flow_fg ?h = flow_fg h1 on ?Na" "flow_fg ?h = flow_fg h2 on ?Nb \<union> ?Nc"
     "h1 \<noteq> bot" "h2 \<noteq> bot"
    using split_fg[of ?h ?Na "?Nb \<union> ?Nc"] assms by blast

  then obtain h21 h22 where **: "h2 = h21 + h22" "dom_fg h21 = ?Nb" "dom_fg h22 = ?Nc"
    "edge_fg h2 = edge_fg h21 on ?Nb" "edge_fg h2 = edge_fg h22 on ?Nc"
    "flow_fg h2 = flow_fg h21 on ?Nb" "flow_fg h2 = flow_fg h22 on ?Nc"
    "h21 \<noteq> bot" "h22 \<noteq> bot"
    using split_fg[of h2 ?Nb ?Nc] dom * by blast

  have ***: "edge_fg ?h = edge_fg a on ?Na" "flow_fg ?h = flow_fg a on ?Na"
      "edge_fg ?h = edge_fg b on ?Nb" "flow_fg ?h = flow_fg b on ?Nb"
      "edge_fg ?h = edge_fg c on ?Nc" "flow_fg ?h = flow_fg c on ?Nc"
    using edge_fg_plus_fg_on1 edge_fg_plus_fg_on2
          flow_fg_plus_fg_on1 flow_fg_plus_fg_on2 nbot by simp_all

  have "h1 = a"
    apply (rule fg_eqI) using nbot * ** *** by simp_all
  moreover have "h21 = b"
    apply (rule fg_eqI) using nbot * ** *** by simp_all
  moreover have "h22 = c"
    apply (rule fg_eqI) using nbot * ** *** by simp_all
  ultimately show ?thesis
    using * ** by simp
qed

lemma plus_fg_comm:
  fixes a b :: "('a,'b :: cancel_comm_monoid_add) fg"
  shows "a + b = b + a"
  unfolding plus_fg_def
  by (auto simp: Let_def Un_commute split: if_splits)

instance
proof (standard, goal_cases)
  case (1 a b c)
  then show ?case
  proof (rule fg_eqI2, goal_cases)
    case 1
    then show ?case
      using plus_fg_assoc by simp
  next
    case 2
    \<comment> \<open>derive second direction from first direction of associativity and commutativity\<close>
    then have "a + (b + c) = (b + c) + a" using plus_fg_comm by simp
    then have "a + (b + c) = b + (c + a)" using 2 plus_fg_assoc by simp
    then have "a + (b + c) = (c + a) + b" using plus_fg_comm by simp
    then have "a + (b + c) = c + (a + b)" using 2 plus_fg_assoc by simp
    then show ?case using plus_fg_comm by simp
  qed
next
  case (2 a b)
  then show ?case
    using plus_fg_comm by simp
next
  case (3 a)
  then show ?case
    unfolding plus_fg_def
    by (cases "a = bot", auto simp: Let_def split: if_splits)
qed

end

lemma split_sum:
  fixes f :: "'n \<Rightarrow> ('n,'m::cancel_comm_monoid_add) fg"
  assumes "sum f (xs \<union> ys) \<noteq> bot" "xs \<inter> ys = {}" "finite xs" "finite ys"
  shows "sum f (xs \<union> ys) = sum f xs + sum f ys \<and> sum f xs \<noteq> bot \<and> sum f ys \<noteq> bot"
proof -
  have "sum f (xs \<union> ys) = sum f xs + sum f ys"
    using assms by (smt disjoint_iff_not_equal sum.cong sum.union_disjoint)
  thus ?thesis
    using assms by auto
qed

text \<open>Cancellativity only holds for valid flow graphs,
therefore we can not instantiate @{text cancel_comm_monoid_add}.\<close>

lemma plus_fg_cancel_left:
  fixes h1 h2 h3 :: "('n,'m :: cancel_comm_monoid_add) fg"
  assumes "h1 + h2 \<noteq> bot"
    and "h1 + h2 = h1 + h3"
  shows "h2 = h3"
proof (rule fg_eqI)
  have "h1 \<noteq> bot" "h2 \<noteq> bot" "h3 \<noteq> bot"
    using assms plus_fg_ops_exist by auto

  thus "h2 \<noteq> bot" "h3 \<noteq> bot"
    by simp_all

  have "dom_fg h1 \<inter> dom_fg h2 = {}"
    "dom_fg h1 \<inter> dom_fg h3 = {}"
    "dom_fg (h1 + h2) = dom_fg h1 \<union> dom_fg h2"
    "dom_fg (h1 + h3) = dom_fg h1 \<union> dom_fg h3"
    using assms plus_fg_dom_un[of h1 h2] by auto
  thus *: "dom_fg h2 = dom_fg h3"
    using assms(2) by auto

  have "edge_fg (h1 + h2) = edge_fg h2 on (dom_fg h2)"
    "edge_fg (h1 + h3) = edge_fg h3 on (dom_fg h3)"
    using edge_fg_plus_fg_on2[of h1 h2] edge_fg_plus_fg_on2[of h1 h3] assms by simp_all
  thus "edge_fg h2 = edge_fg h3 on dom_fg h2"
    using assms(2) * by simp

  have "flow_fg (h1 + h2) = flow_fg h2 on (dom_fg h2)"
    "flow_fg (h1 + h3) = flow_fg h3 on (dom_fg h3)"
    using flow_fg_plus_fg_on2[of h1 h2] flow_fg_plus_fg_on2[of h1 h3] assms by simp_all
  thus "flow_fg h2 = flow_fg h3 on dom_fg h3"
    using assms(2) * by simp
qed

lemma plus_fg_cancel_right:
  assumes "a + c \<noteq> (bot :: (('n,'m :: cancel_comm_monoid_add) fg))" "a + c = b + c"
  shows "a = b"
  using assms plus_fg_cancel_left[of c a b] by (simp add: algebra_simps)

text \<open>Some results about validity of special cases of flow graphs\<close>

lemma def_fg_singleton[simp]:
  (* weird/seemingly circular, but can be used to show that fg {x} e f \<noteq> bot *)
  "dom_fg h = {n} \<Longrightarrow> edge_fg h n n = (\<lambda>_. 0) \<Longrightarrow> h \<noteq> bot"
  by (transfer, auto split: option.splits if_splits simp: fg'_option_eq_def)

lemma def_fg_singleton_id:
  (* also weird *)
  "dom_fg h = {n} \<Longrightarrow> edge_fg h n n = id \<Longrightarrow> h \<noteq> bot"
  by (transfer,
      auto split: option.splits if_splits simp: fg'_option_eq_def def_fg'_def flow_eq'_def)

lemma def_fg_singleton':
  "e x x = (\<lambda>_. 0) \<Longrightarrow> fg {x} e f \<noteq> bot"
  by (transfer,
      auto split: option.splits if_splits simp: fg'_option_eq_def def_fg'_def flow_eq'_def)

end
