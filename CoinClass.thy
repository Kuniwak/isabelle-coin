theory CoinClass imports "~~/src/HOL/Library/Multiset" begin

type_alias val = nat

locale coin =
  fixes val_unit :: "'a \<Rightarrow> val"
    and coin1 :: 'a
    and less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and less :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes less_eq_def: "less_eq x y \<longleftrightarrow> val_unit x \<le> val_unit y"
    and less_def: "less x y \<longleftrightarrow> val_unit x < val_unit y"
    and finite_coins: "finite (UNIV :: 'a set)"
    and val_unit_coin1: "val_unit coin1 = 1"
    and inj_val_unit: "inj val_unit"
    and val_unit_gt_0: "\<And>v. v \<in> range val_unit \<Longrightarrow> v > 0"
    and dvd_val_units: "\<And>v1 v2. \<lbrakk> v1 \<in> range val_unit; v2 \<in> range val_unit; v1 < v2 \<rbrakk> \<Longrightarrow> v1 dvd v2"
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


definition normal_form :: "'a multiset \<Rightarrow> bool"
  where "normal_form C \<equiv> \<forall>C'. val C = val C' \<longrightarrow> size C \<le> size C'"

theorem normal_form_empty: "normal_form {#}"
  unfolding normal_form_def val_def by simp

theorem normal_form_singleton: "normal_form {#c#}"
unfolding normal_form_def val_singleton proof auto
  fix C'
  assume "val_unit c = val C'"
  hence "C' \<noteq> {#}" using val_unit_gt_0 val_gt_0_eq_not_empty val_mempty val_unit_neq_0 by force
  thus "Suc 0 \<le> size C'" using Suc_le_eq by blast
qed

lemma ex_normal_form:
  obtains C where "v = val C" and "normal_form C"
proof -
  assume 1: "\<And>C. \<lbrakk>v = val C; normal_form C\<rbrakk> \<Longrightarrow> thesis"
  show thesis oops


theorem ex1_normal_form: "\<exists>!C. v = val C \<and> normal_form C"
  oops

lemma "\<lbrakk> v1 dvd v2; v1 * c1 + v2 * c2 = v1 * (c1 + c1') + v2 * (c2 - c2'); c2 \<ge> c2' \<rbrakk> \<Longrightarrow> c1 + c2 < c1 + c1' + c2 - c2'" for c1 :: nat
  oops

lemma "\<lbrakk> v1 * c1 + v2 * c2 = v1 * c1' + v2 * c2' \<rbrakk> \<Longrightarrow> c1 + c2 < c1' + c2'"
  oops

lemma "\<lbrakk> v1 dvd v2; c2 \<ge> c2' \<rbrakk> \<Longrightarrow> \<nexists>c1' c2'. v1 * c1 + v2 * c2 = v1 * (c1 + c1') + v2 * (c2 - c2')"
  oops

sublocale linorder less_eq less
unfolding less_eq_def less_def proof
  fix x y
  have 1: "x \<noteq> y \<longleftrightarrow> val_unit x \<noteq> val_unit y" using inj_val_unit by (simp add: inj_eq)
  thus "(val_unit x < val_unit y) = (val_unit x \<le> val_unit y \<and> \<not> val_unit y \<le> val_unit x)" unfolding 1 by auto
next
  fix a
  show "val_unit a \<le> val_unit a" by simp
next
  fix a b
  assume 1: "val_unit a \<le> val_unit b"
    and 2: "val_unit b \<le> val_unit a"
  have 3: "a = b \<longleftrightarrow> val_unit a = val_unit b" using inj_val_unit by (simp add: inj_eq)
  show "a = b" unfolding 3 using 1 2 by simp
next
  fix a b c
  assume 1: "val_unit a \<le> val_unit b"
    and 2: "val_unit b \<le> val_unit c"
  thus "val_unit a \<le> val_unit c" by simp
next
  fix x y
  show "val_unit x \<le> val_unit y \<or> val_unit y \<le> val_unit x" by fastforce
qed
end

end