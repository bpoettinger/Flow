\<^marker>\<open>creator Bernhard Pöttinger\<close>

chapter \<open>Pigeonhole\<close>
theory Pigeonhole
  imports Main
begin

paragraph \<open>Summary\<close>
text \<open>We introduce the generalized pigeonhole principle (which is/was not available in
Isabelle when formalizing it here).

Additionally, we introduce an auxiliary lemma that uses the simple pigeonhole principle
to find a reoccurring element in a list and to decompose the list into three lists with
the reoccurring element as a split element.\<close>

lemma generalized_pigeonhole:
  assumes "dom f \<noteq> {}" "finite (dom f)" "card (dom f) \<ge> card (ran f) * k + 1"
  shows "\<exists>y \<in> ran f. card (f -` {Some y}) \<ge> k + 1"
proof (rule ccontr)
  assume "\<not> (\<exists>y\<in>ran f. k + 1 \<le> card (f -` {Some y}))"
  then have A: "\<And>y. y \<in> ran f \<Longrightarrow> card (f -` {Some y}) \<le> k"
    by auto

  have "finite (ran f)"
    using assms finite_ran by simp
  moreover have "dom f = (\<Union>y \<in> ran f. f -` {Some y})"
    unfolding dom_def ran_def by auto
  ultimately have "card (dom f) = (\<Sum>y \<in> ran f. card (f -` {Some y}))"
    using assms by (auto intro: card_UN_disjoint)
  also have "... \<le> (\<Sum>y \<in> ran f. k)"
    using sum_mono[OF A] by simp
  also have "... < card (ran f) * k + 1"
    by simp
  also have "... \<le> card (dom f)"
    using assms by simp
  finally show False ..
qed

lemma pigeonhole_ex:
  assumes "length fs \<ge> card N + 1" "set fs \<subseteq> N" "finite N"
  shows "\<exists>i j. i < j \<and> j < length fs \<and> fs!i = fs!j"
proof -
  let ?f = "\<lambda>n. if n < length fs then fs!n else undefined"
  let ?d = "{0..<length fs}"
  have "?f ` ?d \<subseteq> set fs"
    by auto
  then have "?f ` ?d \<subseteq> N"
    using assms by blast
  then have "card (?f ` ?d) + 1 \<le> length fs"
    using card_mono[of "N" "?f ` ?d"] assms by simp
  moreover have "card (set fs) \<le> card ?d"
    by (simp add: card_length)
  ultimately have "\<not> inj_on ?f ?d"
    using pigeonhole[of ?f ?d] by simp
  then obtain x y where *: "x \<in> ?d" "y \<in> ?d" "x \<noteq> y" "?f x = ?f y"
    unfolding inj_on_def by blast
  then have "fs!x = fs !y"
    by auto
  then show "\<exists>i j. i < j \<and> j < length fs \<and> fs ! i = fs ! j"
    using *
    apply (cases "x < y")
     apply auto[1]
    by (rule exI[where x="y"], rule exI[where x="x"], simp)
qed

lemma pigeonhole_split_list:
  assumes "length fs \<ge> card N + 1" "set fs \<subseteq> N" "finite N"
  shows "\<exists>x xs ys zs. fs = xs @ x # ys @ x # zs"
proof -
  obtain i j where "i < j" "j < length fs" "fs!i = fs!j"
    using pigeonhole_ex assms by blast
  then have "\<not> distinct fs"
    using distinct_conv_nth[of fs] by auto
  then obtain xs ys zs y where **: "fs = xs @ [y] @ ys @ [y] @ zs"
    using not_distinct_decomp[of fs] by blast
  then show ?thesis
    by auto
qed

end
