\<^marker>\<open>creator Bernhard Pöttinger\<close>

chapter \<open>Alternating List Predicates\<close>
theory Alternating
  imports Main
begin

paragraph \<open>Summary\<close>
text \<open>This theory introduces alternating list predicates @{term "alternating P Q xs"}:
for a list @{term xs} all elements with an odd index satisfy P and all elements with an
even index satisfy Q.

We introduce alternating variables @{term "alt x y zs"} that enable us to state variables
that depend on the positions within lists.

Furthermore, we introduce lemmas that split lists into lists of lists where each
for each sublist all element either belong to P or to Q.\<close>

paragraph \<open>Major Definitions\<close>
text \<open>\<^item> alternating: alternating list predicate\<close>
text \<open>\<^item> alternating': alternating list predicate with explicitly stated last element\<close>
text \<open>\<^item> alt: alternating list predicate with explicitly stated last element\<close>

paragraph \<open>Major Lemmas\<close>
text \<open>
\<^item> @{term alternating_induct}
\<^item> @{term alternating_induct'}
\<^item> @{term alternating_induct'_symmetric}
\<^item> @{term alternating_induct'_symmetric'}
\<^item> @{term alternating'_induct}
\<^item> @{term alternating'_induct'}
\<^item> @{term alternating'_induct'_symmetric}
\<^item> @{term alternating'_induct'_symmetric'}
\<^item> @{term split_segments}
\<close>

fun alternating :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "alternating _ _ [] = True" |
  "alternating P Q (x # xs) = (P x \<and> alternating Q P xs)"

fun alternating' where
  "alternating' P Q [] y = P y" |
  "alternating' P Q (x # xs) y = (P x \<and> alternating' Q P xs y)"

lemma alternating_to_alternating':
  assumes "alternating P Q xs" "xs \<noteq> []"
  shows "alternating' P Q (butlast xs) (last xs)"
  using assms
  by (induction xs arbitrary: P Q, auto)

lemma alternating'_to_alternating: "alternating' P Q xs y \<Longrightarrow> alternating P Q xs"
  by (induction xs rule: induct_list012, auto)

section \<open>Induction rules for alternating lists\<close>

lemma alternating_induct'[consumes 1, case_names emptyP emptyQ baseP baseQ stepP stepQ]:
  assumes "alternating P Q xs" "R a aa b bb []" "R b bb a aa []"
    "\<And>x. alternating P Q [x] \<Longrightarrow> P x \<Longrightarrow> R a aa b bb [x]" "\<And>x. alternating Q P [x] \<Longrightarrow>  Q x
          \<Longrightarrow> R b bb a aa [x]"
    "\<And>x y zs. alternating P Q (x # y #zs) \<Longrightarrow> P x \<Longrightarrow> Q y \<Longrightarrow> R b bb a aa (y # zs)
          \<Longrightarrow> R a aa b bb (x # y # zs)"
    "\<And>x y zs. alternating Q P (x # y #zs) \<Longrightarrow> Q x \<Longrightarrow> P y \<Longrightarrow> R a aa b bb (y # zs)
          \<Longrightarrow> R b bb a aa (x # y # zs)"
  shows "R a aa b bb xs"
  using assms
proof (induction xs arbitrary: a aa b bb P Q rule: induct_list012)
  case 1                                     
  then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 x y zs)
  then have "P x" "Q y" by auto
  moreover have "R b bb a aa (y # zs)"
    apply (rule "3.IH"[of Q P])
    using 3 by simp_all
  ultimately show ?case
    using 3 by blast
qed

lemma alternating_induct[consumes 1, case_names empty baseP baseQ stepP stepQ]:
  assumes "alternating P Q xs" "R []"
    "\<And>x. alternating P Q [x] \<Longrightarrow> P x \<Longrightarrow> R [x]" "\<And>x. alternating Q P [x] \<Longrightarrow>  Q x \<Longrightarrow> R [x]"
    "\<And>x y zs. alternating P Q (x # y #zs) \<Longrightarrow> P x \<Longrightarrow> Q y \<Longrightarrow> R (y # zs) \<Longrightarrow> R (x # y # zs)"
    "\<And>x y zs. alternating Q P (x # y #zs) \<Longrightarrow> Q x \<Longrightarrow> P y \<Longrightarrow> R (y # zs) \<Longrightarrow> R (x # y # zs)"
  shows "R xs"
  apply (rule alternating_induct'[where a=P and aa=P and b=Q and bb=Q])
  using assms by blast+

lemma alternating_induct'_symmetric[consumes 1, case_names empty base step]:
  assumes "alternating (P a b) (P b a) xs" "\<And>a b. R a b []"
    "\<And>a b x. alternating (P a b) (P b a) [x] \<Longrightarrow> (P a b) x \<Longrightarrow> R a b [x]"
    "\<And>a b x y zs. alternating (P a b) (P b a) (x # y # zs) \<Longrightarrow> (P a b) x \<Longrightarrow> (P b a) y
          \<Longrightarrow> R b a (y # zs) \<Longrightarrow> R a b (x # y # zs)"
  shows "R a b xs"
  using assms
  by (induction xs rule: alternating_induct'[where a=a and b=b and aa=a and bb=b], blast+)

lemma alternating_induct'_symmetric'[consumes 1, case_names empty base step]:
  assumes "alternating (P a b aa bb) (P b a bb aa) xs" "\<And>a b aa bb. R a b aa bb []"
    "\<And>a b aa bb x. (P a b aa bb) x \<Longrightarrow> R a b aa bb [x]"
    "\<And>a b aa bb x y zs. (P a b aa bb) x \<Longrightarrow> (P b a bb aa) y \<Longrightarrow> R b a bb aa (y # zs)
          \<Longrightarrow> R a b aa bb (x # y # zs)"
  shows "R a b aa bb xs"
  using assms
  by (induction xs rule: alternating_induct'[where a=a and b=b and aa=aa and bb=bb], blast+)

lemma alternating'_induct'[consumes 1, case_names emptyP emptyQ baseP baseQ stepP stepQ]:
  assumes "alternating' P Q xs y" "P y \<Longrightarrow> R a aa b bb []" "Q y \<Longrightarrow> R b bb a aa []"
    "\<And>x. P x \<Longrightarrow> Q y \<Longrightarrow> R a aa b bb [x]" "\<And>x. Q x \<Longrightarrow> P y \<Longrightarrow> R b bb a aa [x]"
    "\<And>x y' zs. alternating' P Q (x # y' # zs) y \<Longrightarrow> P x \<Longrightarrow> Q y' \<Longrightarrow> R b bb a aa (y' # zs)
          \<Longrightarrow> R a aa b bb (x # y' # zs)"
    "\<And>x y' zs. alternating' Q P (x # y' # zs) y \<Longrightarrow> Q x \<Longrightarrow> P y' \<Longrightarrow> R a aa b bb (y' # zs)
          \<Longrightarrow> R b bb a aa (x # y' # zs)"
  shows "R a aa b bb xs"
  using assms
proof (induction xs arbitrary: a b aa bb P Q rule: induct_list012)
  case 1                                     
  then show ?case by simp
next
  case (2 x)
  then show ?case by auto
next
  case (3 x y zs)
  then have "P x" "Q y" by auto
  moreover have "R b bb a aa (y # zs)"
    apply (rule "3.IH"[of Q P])
    using 3 by simp_all
  ultimately show ?case
    using 3 by auto
qed

lemma alternating'_induct[consumes 1, case_names emptyP emptyQ baseP baseQ stepP stepQ]:
  assumes "alternating' P Q xs y" "P y \<Longrightarrow> R []" "Q y \<Longrightarrow> R []"
    "\<And>x. P x \<Longrightarrow> Q y \<Longrightarrow> R [x]" "\<And>x. Q x \<Longrightarrow> P y \<Longrightarrow> R [x]"
    "\<And>x y zs. P x \<Longrightarrow> Q y \<Longrightarrow> R (y # zs) \<Longrightarrow> R (x # y # zs)"
    "\<And>x y zs. Q x \<Longrightarrow> P y \<Longrightarrow> R (y # zs) \<Longrightarrow> R (x # y # zs)"
  shows "R xs"
  using assms
  by (rule alternating'_induct'[where a=P and b=Q and aa=P and bb=Q], blast)

lemma alternating'_induct'_symmetric[consumes 1, case_names empty base step]:
  assumes "alternating' (P a b) (P b a) xs y" "\<And>a b. R a b []"
    "\<And>a b x. (P a b) x \<Longrightarrow> (P b a) y \<Longrightarrow> R a b [x]"
    "\<And>a b x y zs. (P a b) x \<Longrightarrow> (P b a) y \<Longrightarrow> R b a (y # zs) \<Longrightarrow> R a b (x # y # zs)"
  shows "R a b xs"
  using assms
  by (induction xs rule: alternating'_induct'[where a=a and b=b and aa=a and bb=b], blast+)

lemma alternating'_induct'_symmetric'[consumes 1, case_names empty base step]:
  assumes "alternating' (P a b aa bb) (P b a bb aa) xs y" "\<And>a b aa bb. R a b aa bb []"
    "\<And>a b aa bb x. (P a b aa bb) x \<Longrightarrow> (P b a bb aa) y \<Longrightarrow> R a b aa bb [x]"
    "\<And>a b aa bb x y' zs. alternating' (P a b aa bb) (P b a bb aa) (x # y' # zs) y
          \<Longrightarrow> (P a b aa bb) x \<Longrightarrow> (P b a bb aa) y' \<Longrightarrow> R b a bb aa (y' # zs)
          \<Longrightarrow> R a b aa bb (x # y' # zs)"
  shows "R a b aa bb xs"
  using assms
  by (induction xs rule: alternating'_induct'[where a=a and b=b and aa=aa and bb=bb], blast+)

section \<open>Lemmas on alternating list predicates\<close>

lemma alternating_append1:
  assumes "alternating P Q (xs @ ys)"
  shows "alternating P Q xs"
  using assms
  by (induction xs arbitrary: P Q, auto)

lemma alternating_props:
  "alternating P Q xs \<Longrightarrow> \<forall>x \<in> set xs. P x \<or> Q x"
  by (induction xs arbitrary: P Q, auto)

lemma alternatingD:
  assumes "alternating P Q xs" "\<And>x. P x \<Longrightarrow> R x" "\<And>x. Q x \<Longrightarrow> R x"
  shows "\<forall>x \<in> set xs. R x"
  using assms by (induction xs arbitrary: P Q, auto)

fun alternating_map where
  "alternating_map f g [] = []" |
  "alternating_map f g (x # xs) = f x # (alternating_map g f xs)"

lemma alternating_map_id: "alternating_map id id xs = xs"
  by (induction xs, auto)

lemma alternating_map_props:
  assumes "alternating P Q xs" "\<forall>x \<in> set xs. P x \<longrightarrow> P' (f x)" "\<forall>x \<in> set xs. Q x \<longrightarrow> Q' (g x)"
  shows "alternating P' Q' (alternating_map f g xs)"
  using assms by (induction xs arbitrary: P Q P' Q' f g, auto)

lemma alternating_map_fwd:
  assumes "alternating P Q xs" "\<And>x. x \<in> set xs \<Longrightarrow> P x \<Longrightarrow> P' x" "\<And>x. x \<in> set xs \<Longrightarrow> Q x \<Longrightarrow> Q' x"
  shows "alternating P' Q' xs"
proof -
  have "alternating P' Q' (alternating_map id id xs)"
    using alternating_map_props[of P Q xs P' id Q' id] assms by simp
  then show ?thesis
    by (subst (asm) alternating_map_id, simp)
qed

lemma alternating'_props:
  assumes "alternating' P Q xs y"
  shows "(\<forall>x \<in> set xs. P x \<or> Q x) \<and> (P y \<or> Q y)"
  using assms
  by (induction xs arbitrary: P Q, auto)

lemma alternating_consequence:
  assumes "alternating P Q xs" "\<forall>x \<in> set xs. P x \<longrightarrow> P' x" "\<forall>x \<in> set xs. Q x \<longrightarrow> Q' x"
  shows "alternating P' Q' xs"
  using assms
  by (induction xs arbitrary: P Q P' Q', auto)

section \<open>Alternating Variables\<close>

text \<open>alt enables us to state the value of alternating variables that correspond to
a certain element in an alternating list.\<close>

fun alt :: "'a \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a" where
  "alt _ y [] = y" |
  "alt x y (_ # xs) = alt y x xs"

lemma alt_in: "zs \<noteq> [] \<Longrightarrow> alt x y zs \<in> {x,y}"
  by (induction zs arbitrary: x y rule: induct_list012, auto)

lemma alt_butlast:
  assumes "xss \<noteq> []"
  shows "alt x y xss = alt y x (butlast xss)"
  using assms
  by (induction xss arbitrary: x y rule: induct_list012, auto)

lemma alt_cases:
  assumes "alt x y zs = x \<Longrightarrow> P x" "alt x y zs = y \<Longrightarrow> P y"
  shows "P (alt x y zs)"
  using assms by (induction zs arbitrary: x y rule: induct_list012, auto)

lemma alt_odd: "alternating P Q xss \<Longrightarrow> xss \<noteq> [] \<Longrightarrow> \<not> Q (last xss) \<Longrightarrow> alt x y xss = x"
  and alt_even: "alternating P Q xss \<Longrightarrow> xss \<noteq> [] \<Longrightarrow> \<not> P (last xss) \<Longrightarrow> alt x y xss = y"
  by (induction xss arbitrary: P Q x y rule: induct_list012, auto)

lemma alt_comm:
  "alt x y xss = x \<Longrightarrow> alt y x xss = y" "alt x y xss = y \<Longrightarrow> alt y x xss = x"
  apply (induction xss arbitrary: x y rule: induct_list012)
  apply (simp, simp, simp, simp)
  by (metis alt.simps(2))+

lemma alt_sum:
  fixes h1 h2 :: "'a :: comm_monoid_add"
  shows "h1 + h2 = alt h1 h2 xs + alt h2 h1 xs"
  by (induction xs, auto simp: algebra_simps)

lemma alt_alt_to_alt: "alt (alt P Q xs) (alt Q P xs) ys = alt Q P (xs @ ys)"
  by (induction xs arbitrary: P Q, auto)

lemma alt_P_P_hom: "alt (P a) (P b) xs = P (alt a b xs)"
  by (induction xs arbitrary: a b, auto)

lemma alternating_append_inner: "alternating P Q (xs @ ys) \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> (alt Q P xs) (hd ys)"
proof -
  assume "alternating P Q (xs @ ys)"
  then have "alternating P Q xs" using alternating_append1 by auto
  then show "alternating P Q (xs @ ys) \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> (alt Q P xs) (hd ys)"
  proof (induction xs rule: alternating_induct'[where a=P and b=Q and aa=P and bb=Q])
    case emptyP
    then show ?case by (simp, cases ys, simp, simp)
  next
    case emptyQ
    then show ?case by (simp, cases ys, simp, simp)
  next
    case (baseP xs)
    then show ?case by (simp, cases ys, simp, simp)
  next
    case (baseQ xs)
    then show ?case by (simp, cases ys, simp, simp)
  next
    case (stepP xs ys zss)
    then show ?case by simp
  next
    case (stepQ xs ys zss)
    then show ?case by simp
  qed
qed

lemma alt_cases':
  assumes "P x" "P y"
  shows "P (alt x y zs)"
  using assms by (induction zs arbitrary: x y rule: induct_list012, auto)

lemma alternating_append2:
  assumes "alternating P Q (xs @ ys)"
  shows "alternating (alt Q P xs) (alt P Q xs) ys"
  using assms
  by (induction xs arbitrary: P Q, auto)

lemma alternating_to_alternating2':
  assumes "alternating P Q xs" "(alt Q P xs) y"
  shows "alternating' P Q xs y"
  using assms
  by (induction xs arbitrary: P Q, auto)

section \<open>Obtain and Extend Convoluted Alternating Lists\<close>

text \<open>segment enables us to lift the single-element-only alternating list predicate
to alternating list predicates that group multiple consecutive elements of lists into
sublists where all elements in a sublist satisfy the same one of the two predicates.\<close>

abbreviation "segment N \<equiv> \<lambda>xs. set xs \<subseteq> N \<and> xs \<noteq> []"

text \<open>@{term split_segments'} is the most general variant of the split lemmas\<close>

lemma split_segments':
  assumes "set xs \<subseteq> A \<union> B" "hd xs \<in> A"
  shows "\<exists>xss. concat xss = xs \<and> (\<forall>xs \<in> set xss. xs \<noteq> []) \<and>
    alternating (segment A) (segment B) xss"
  using assms
proof (induction xs arbitrary: A B rule: induct_list012)
  case 1
  then show ?case
    using concat.simps(1) by fastforce
next
  case (2 x)
  show ?case
    apply (rule exI[where x="[[x]]"])
    using 2 by auto
next
  case (3 x y xs')
  let ?xs = "y # xs'"  
  show ?case
  proof (cases "y \<in> A")
    case True
    moreover have "set ?xs \<subseteq> A \<union> B"
      using 3 by auto
    moreover have "hd ?xs \<in> A"
      using True by simp
    ultimately obtain xss where **:
      "concat xss = ?xs \<and> alternating (segment A) (segment B) xss \<and> (\<forall>xs\<in>set xss. xs \<noteq> [])"
      using "3.IH"[of A B] by auto
    then have C: "hd xss \<noteq> [] \<and> set (hd xss) \<subseteq> A \<and> alternating (segment B) (segment A) (tl xss)"
      by (cases xss, auto)
    then have A: "x # hd xss \<noteq> []" "set (x # hd xss) \<subseteq> A"
      using 3 by auto
    have B: "concat ((x # hd xss) # tl xss) = x # ?xs"
      using ** 3
      by (metis append_eq_Cons_conv concat.simps(1) concat.simps(2) hd_Cons_tl list.simps(3))
    show ?thesis
      apply (rule exI[where x="(x # hd xss) # tl xss"])
      using A B C **
      by (metis (mono_tags, lifting) alternating.simps(2) concat.simps(1)
          list.set_sel(2) list.simps(3) set_ConsD)
  next
    case False
    moreover have "set ?xs \<subseteq> A \<union> B"
      using 3 by auto
    moreover have "hd ?xs \<in> B"
      using False 3 by simp
    ultimately obtain xss where **:
      "concat xss =?xs \<and> alternating (segment B) (segment A) xss \<and> (\<forall>xs\<in>set xss. xs \<noteq> [])"
      using "3.IH"[of B A] by auto
    then have C: "hd xss \<noteq> [] \<and> set (hd xss) \<subseteq> B \<and> alternating (segment A) (segment B) (tl xss)"
      by (cases xss, auto)
    show ?thesis
      apply (rule exI[where x="[x] # xss"])
      using 3 False ** by simp
  qed
qed

lemma split_segments:
  assumes "xs \<noteq> []" "set xs \<subseteq> A \<union> B" "hd xs \<in> A"
  shows "\<exists>xss. concat xss = xs \<and> xss \<noteq> [] \<and> (\<forall>xs \<in> set xss. xs \<noteq> []) \<and>
    alternating (segment A) (segment B) xss"
  using assms split_segments'[of xs A B] by auto

lemma split_segments_extend:
  assumes some: "alternating (segment h1) (segment h2) xss" "xss \<noteq> []"
    "ys = concat xss @ zs" "zs \<noteq> []" "h1 \<inter> h2 = {}" "set zs \<subseteq> h1 \<union> h2"
    "segment h1 zs \<longleftrightarrow> \<not> segment h2 zs" "segment h1 zs2 \<longleftrightarrow> \<not> segment h2 zs2"
    "segment h1 zs \<longleftrightarrow> segment h2 zs2"
  shows "\<exists>ys' yss.
    alternating' (segment h1) (segment h2) (butlast xss @ [last xss @ ys'] @ yss) zs2 \<and>
    ys = concat (butlast xss @ [last xss @ ys'] @ yss) \<and> (\<forall>xs \<in> set xss. xs \<noteq> []) \<and>
    last xss @ ys' \<noteq> [] \<and> (\<forall>xs \<in> set yss. xs \<noteq> []) \<and> (ys' @ concat yss = zs) \<and>
    (ys' = [] \<or> yss = [])"
  using some
proof (induction xss arbitrary: ys rule: alternating_induct'_symmetric[where a=h1 and b=h2])
  case empty
  then show ?case by simp
next
  case (base h1 h2 xs)

  show ?case
  proof (cases "hd zs \<in> h1")
    case True
    then have X: "segment h1 zs" using base by (meson disjoint_iff_not_equal hd_in_set subset_eq)
    then have XX: "segment h2 zs2" using base by simp
    show ?thesis
      apply (rule exI[where x="zs"])
      apply (rule exI[where x="[]"])
      using X base by simp
  next
    case False
    then have X: "segment h2 zs" using base by (meson disjoint_iff_not_equal hd_in_set subset_eq)
    then have XX: "segment h1 zs2" using base by simp
    show ?thesis
      apply (rule exI[where x="[]"])
      apply (rule exI[where x="[zs]"])
      using X base by simp
  qed
next
  case (step h1 h2 xs ys' zss)
  obtain ys yss where *:
    "alternating' (segment h2) (segment h1) (butlast (ys' # zss) @ [last (ys' # zss) @ ys] @ yss) zs2 \<and>
    concat (ys' # zss) @ zs = concat (butlast (ys' # zss) @ [last (ys' # zss) @ ys] @ yss) \<and>
    (\<forall>xs\<in>set (ys' # zss). xs \<noteq> []) \<and> last (ys' # zss) @ ys \<noteq> [] \<and>
    (\<forall>xs\<in>set yss. xs \<noteq> []) \<and> ys @ concat yss = zs \<and> (ys = [] \<or> yss = [])"
    using step(4)[of "concat (ys' # zss) @ zs"] step by auto
  show ?case apply (rule exI[where x=ys], rule exI[where x=yss]) using step * by simp
qed

section \<open>Auxiliary Result\<close>

lemma length_ge_2_alternating:
  assumes "N1 \<inter> N2 = {}" "n1 \<in> N1" "n2 \<in> N2" "n1 \<in> set (concat nss)" "n2 \<in> set (concat nss)"
    "alternating (segment N1) (segment N2) nss"
  shows "length nss \<ge> 2"
proof (rule ccontr)
  assume "\<not> 2 \<le> length nss"
  then have "length nss = 0 \<or> length nss = 1" by linarith
  then consider (a) "length nss = 0" | (b) "length nss = 1" by blast
  then show False
  proof cases
    case a
    then show ?thesis using assms by simp
  next
    case b
    then obtain ns where *: "nss = [ns]" by (metis One_nat_def Suc_length_conv length_0_conv)
    then have **: "n1 \<in> set ns" "n2 \<in> set ns" using assms by auto

    have "set ns \<subseteq> N1 \<or> set ns \<subseteq> N2" using assms * by simp
    then consider (a) "set ns \<subseteq> N1" | (b) "set ns \<subseteq> N2" by blast
    then show False
    proof cases
      case a
      then show ?thesis using assms ** by blast
    next
      case b
      then show ?thesis using assms ** by blast
    qed
  qed
qed

end
