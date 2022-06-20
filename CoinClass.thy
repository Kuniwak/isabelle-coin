theory CoinClass imports "~~/src/HOL/Library/Multiset" begin

type_alias val = nat


class coins =
  fixes val_unit :: "'a \<Rightarrow> val"
  fixes coin1 :: 'a
  assumes val_unit_coin1: "val_unit coin1 = 1"
  assumes inj_val_unit: "inj val_unit"
  assumes val_unit_gt_0: "\<forall>v \<in> range val_unit. v > 0"
  assumes dvd_val_units: "\<forall>v1 \<in> range val_unit. \<forall>v2 \<in> range val_unit. v1 < v2 \<longrightarrow> v1 dvd v2"
begin

lemma val_unit_neq_0: "val_unit c \<noteq> 0"
  by (simp add: val_unit_gt_0)

lemma val_unit_eq_1_is_coin1:
  assumes "val_unit c = 1"
  shows "c = coin1"
using assms inj_val_unit val_unit_coin1 by (metis inj_eq)

lemma neq_coin1_implies_val_unit_gt_1:
  assumes "c \<noteq> coin1"
  shows "val_unit c > 1"
proof -
  have "\<nexists>c. val_unit c = 0" using val_unit_gt_0 by simp
  thus "val_unit c > 1" using assms val_unit_eq_1_is_coin1 by (meson less_one linorder_cases)
qed

definition next_coin :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "next_coin c1 c3 \<equiv> val_unit c1 < val_unit c3 \<and> (\<nexists>c2. val_unit c1 < val_unit c2 \<and> val_unit c2 < val_unit c3)"

theorem not_next_coin_ne: "\<not>next_coin c c"
  unfolding next_coin_def by blast


inductive trans_next_coin :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "next_coin c1 c2 \<Longrightarrow> trans_next_coin c1 c2" |
  "\<lbrakk> next_coin c1 c2; trans_next_coin c2 cN \<rbrakk> \<Longrightarrow> trans_next_coin c1 cN"


theorem trans_nect_coin_implies_val_unit_lt:
  assumes "trans_next_coin c1 c2"
  shows "val_unit c1 < val_unit c2"
using assms proof (induct rule: trans_next_coin.induct)
  case (1 c1 c2)
  then show ?case unfolding next_coin_def by simp
next
  case (2 c1 c2 cN)
  have "val_unit c1 < val_unit c2" using 2 unfolding next_coin_def by simp
  thus ?case using 2(3) unfolding next_coin_def by simp
qed


theorem trans_next_coin_implies_dvd:
  assumes "trans_next_coin c1 c2"
  shows "val_unit c1 dvd val_unit c2"
proof -
  have "val_unit c1 < val_unit c2" using assms trans_nect_coin_implies_val_unit_lt by blast
  thus "val_unit c1 dvd val_unit c2" using dvd_val_units by blast
qed


definition val :: "'a multiset \<Rightarrow> val" where
  "val C \<equiv> sum_mset (image_mset val_unit C)"


lemma val_mempty: "val {#} = 0"
  by (simp add: val_def)

lemma val_add_mset:
  "val (add_mset c C) = val_unit c + val C"
  by (simp add: val_def)

lemma val_singleton: "val {#c#} = val_unit c"
  unfolding val_add_mset val_mempty by simp

lemma val_eq_0D:
  assumes "val C = 0"
  shows "C = {#}"
using assms proof (rule contrapos_pp)
  assume "C \<noteq> {#}"
  then obtain c C' where 1: "c \<in># C" and 2: "C = add_mset c C'" by (meson mset_add multiset_nonemptyE)
  have 3: "val C = val_unit c + val C'" using val_add_mset 2 by simp
  have 4: "val_unit c > 0" using val_unit_gt_0 by simp
  have 5: "val C > 0" using 3 4 by presburger
  thus "val C \<noteq> 0" by simp
qed
  

lemma val_gt_0_eq_not_empty: "val C > 0 \<longleftrightarrow> C \<noteq> {#}"
  using val_mempty val_eq_0D by auto

definition normal_form :: "'a multiset \<Rightarrow> bool"
  where "normal_form C \<equiv> \<forall>C'. val C = val C' \<longrightarrow> size C \<le> size C'"

lemma val_only_coin1: "val {#coin1#} = 1"
  by (simp add: val_unit_coin1 val_def)

lemma val_eq_1_is_only_one_coin1:
  assumes "val C = 1"
  shows "C = {# coin1 #}"
proof -
  have "C \<noteq> {#}" using assms val_mempty by auto
  then obtain c C' where C_eq: "C = add_mset c C'" by (meson multiset_cases)
  have "val C = val_unit c + val C'" using val_add_mset C_eq by simp
  hence "1 = val_unit c + val C'" using assms by simp
  hence "val_unit c = 0 \<and> val C' = 1 \<or> val_unit c = 1 \<and> val C' = 0" by auto
  hence 1: "val_unit c = 1" and 2: "val C' = 0" by (auto simp add: val_unit_neq_0)
  have 3:"c = coin1" using 1 val_unit_eq_1_is_coin1 by simp
  have 4: "C' = {#}" using 2 val_eq_0D by simp
  show "C = {#coin1#}" using 3 4 C_eq by simp
qed

theorem normal_form_singleton: "normal_form {#c#}"
unfolding normal_form_def val_singleton proof auto
  fix C'
  assume "val_unit c = val C'"
  hence "C' \<noteq> {#}" using val_unit_gt_0 val_gt_0_eq_not_empty val_mempty val_unit_neq_0 by force
  thus "Suc 0 \<le> size C'" using Suc_le_eq by blast
qed

theorem val_eqE:
  fixes v :: val
  obtains C where "val C = v"
proof -
  assume 1: "\<And>C. val C = v \<Longrightarrow> thesis"
  have "val (replicate_mset v coin1) = v"
  proof (induct v)
    case 0
    thus "val (replicate_mset 0 coin1) = 0" using val_mempty by simp
  next
    case (Suc v)
    note step = Suc
    thus "val (replicate_mset (Suc v) coin1) = Suc v" unfolding replicate_mset_Suc val_add_mset val_unit_coin1 step by simp
  qed
  thus thesis using 1 by simp
qed


lemma ex_normal_form:
  obtains C where "v = val C" and "normal_form C"
proof -
  assume 1: "\<And>C. \<lbrakk>v = val C; normal_form C\<rbrakk> \<Longrightarrow> thesis"
  
  show thesis oops

lemma
  assumes "normal_form C"
    and "val C = val C'"
    and "C \<noteq> C'"
  shows "size C < size C'"
  by (meson assms size_inject less_le normal_form_def)

theorem ex1_normal_form: "\<exists>!C. v = val C \<and> normal_form C"
  oops

lemma "\<lbrakk> v1 dvd v2; v1 * c1 + v2 * c2 = v1 * (c1 + c1') + v2 * (c2 - c2'); c2 \<ge> c2' \<rbrakk> \<Longrightarrow> c1 + c2 < c1 + c1' + c2 - c2'" for c1 :: nat
  apply(subst diff_add_assoc)
  apply(assumption)
  apply(subst add.assoc)
  apply(subst nat_add_left_cancel_less)
  apply(subst diff_add_assoc[symmetric])
  apply(assumption)
  apply(subst add.commute)
  apply(subst add_0_right[symmetric])

  apply(assumption)
  apply(subst nat_add_left_cancel_less)




lemma "\<lbrakk> v1 * c1 + v2 * c2 = v1 * c1' + v2 * c2' \<rbrakk> \<Longrightarrow> c1 + c2 < c1' + c2'"


lemma "\<lbrakk> v1 dvd v2; c2 \<ge> c2' \<rbrakk> \<Longrightarrow> \<nexists>c1' c2'. v1 * c1 + v2 * c2 = v1 * (c1 + c1') + v2 * (c2 - c2')"
end


end