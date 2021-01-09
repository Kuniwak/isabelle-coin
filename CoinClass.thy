theory CoinClass imports "~~/src/HOL/Library/Multiset" begin


type_alias val = nat


class coins =
  fixes val_unit :: "'a \<Rightarrow> val"
  assumes inj_val_unit: "inj val_unit"
  assumes val_unit_gt_0: "\<forall>v \<in> range val_unit. v > 0"
  assumes dvd_val_units: "\<forall>v1 \<in> range val_unit. \<forall>v2 \<in> range val_unit. v1 < v2 \<longrightarrow> v1 dvd v2"
begin


definition next_coin :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "next_coin c1 c3 \<equiv> \<nexists>c2. val_unit c1 < val_unit c2 \<and> val_unit c2 < val_unit c3"


inductive trans_next_coin :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "next_coin c1 c2 \<Longrightarrow> trans_next_coin c1 c2" |
  "\<lbrakk> next_coin c1 c2; trans_next_coin c2 cN \<rbrakk> \<Longrightarrow> trans_next_coin c1 cN"


theorem "trans_next_coin c1 c2 \<Longrightarrow> val_unit c1 dvd val_unit c2"
  apply(erule trans_next_coin.induct)
  oops


definition val :: "'a multiset \<Rightarrow> val" where
  "val C \<equiv> sum_mset (image_mset val_unit C)"


lemma val_empty: "val {#} = 0"
  by (simp add: val_def)


lemma val_gt_0_eq_not_empty: "val C > 0 \<longleftrightarrow> C \<noteq> {#}"
  by (auto simp add: val_def val_unit_gt_0 dest!: multi_nonempty_split)


lemma "\<lbrakk> v1 dvd v2; v = v1 * c1 + v2 * c2; c2 \<ge> c2' \<rbrakk> \<Longrightarrow> \<exists>c1'. v = v1 * (c1 + c1') + v2 * (c2 - c2')" for v :: val
  apply(rule_tac x="(v2 div v1) * c2'" in exI)
  apply(auto simp add: add_mult_distrib2 diff_mult_distrib2)
  done

lemma mult_left_add_diff_imp: "v1 > 0 \<Longrightarrow> v1 * k * c2 = v1 * c1' + v1 * k * c2 - v1 * k * c2' \<longleftrightarrow> k * c2 = c1' + k * c2 - k * c2'" for v1 :: nat
proof -
assume a1: "0 < v1"
{ assume "c1' + k * c2 - k * c2' \<noteq> k * c2"
  { assume "\<not> k * c2 < c1' + k * c2 - k * c2' \<and> c1' + k * c2 - k * c2' \<noteq> k * c2"
    then have "\<exists>n>c1' + k * c2 - k * c2'. c1' + k * c2 - k * c2' \<noteq> k * c2 \<and> \<not> 0 < v1 * (n - k * c2)"
      by (metis diff_mult_distrib2 diff_self_eq_0 linorder_neqE_nat not_less0)
    then have "v1 * (c1' + k * c2 - k * c2') \<noteq> v1 * (k * c2) \<and> c1' + k * c2 - k * c2' \<noteq> k * c2"
      using a1 by (metis diff_mult_distrib2 nat_mult_less_cancel1 zero_less_diff) }
  then have ?thesis
    using a1 by (metis (no_types) add_mult_distrib2 diff_mult_distrib2 diff_self_eq_0 mult.assoc nat_mult_less_cancel1 not_less0 zero_less_diff) }
  then show ?thesis
    by (metis (no_types) add_mult_distrib2 diff_mult_distrib2 mult.assoc)
qed


lemma "\<lbrakk>v1 > 0; v1 dvd v2; v1 * c1 + v2 * c2 = v1 * (c1 + c1') + v2 * (c2 - c2'); c2' \<le> c2 \<rbrakk> \<Longrightarrow> c1' \<ge> c2'" for c1 :: nat
  apply(subst (asm) add_mult_distrib2)
  apply(subst (asm) diff_mult_distrib2)
  apply(subst (asm) add.assoc)
  apply(drule add_left_imp_eq)
  apply(subst (asm) diff_add_assoc[symmetric])
  apply(erule mult_le_mono2)
  apply(subst (asm) dvd_def)
  apply(elim exE)
  apply(clarify)
  apply(subst (asm) mult_left_add_diff_imp)
  apply(assumption)
try



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