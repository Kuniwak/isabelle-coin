theory CoinClass imports "RmMultiset" begin


type_alias val = nat


class coins = linorder +
  fixes val_unit :: "'a \<Rightarrow> val"
  assumes inj_val_unit: "inj val_unit"
  assumes mono_val_unit: "mono val_unit"
  assumes val_unit_gt_0: "\<forall>v \<in> range val_unit. v > 0"
  assumes val_unit_1: "1 \<in> range val_unit"
  assumes dvd_val_units[rule_format]: "\<forall>v1 \<in> range val_unit. \<forall>v2 \<in> range val_unit. v1 < v2 \<longrightarrow> v1 dvd v2"
begin


theorem val_unit_1_ex: "\<exists>c. val_unit c = 1"
  apply(insert val_unit_1)
  apply(subst (asm) range_ex1_eq)
  apply(rule inj_val_unit)
  apply(clarify)
  apply(erule ssubst)
  apply(rule_tac x=x in exI)
  apply(rule refl)
  done


theorem all_coin_val_gt_0: "\<forall>c. val_unit c > 0"
  apply(insert val_unit_gt_0)
  apply(rule allI)
  apply(erule_tac x="val_unit c" in bspec)
  apply(rule rangeI)
  done


definition val :: "'a multiset \<Rightarrow> val" where
  "val C \<equiv> sum_mset (image_mset val_unit C)"


lemma val_empty: "val {#} = 0"
  by (simp add: val_def)


lemma val_gt_0_eq_not_empty: "val C > 0 \<longleftrightarrow> C \<noteq> {#}"
  by (auto simp add: val_def val_unit_gt_0 dest!: multi_nonempty_split)


lemma val_add_mset: "val (add_mset c C) = val_unit c + val C"
  by (auto simp add: val_def)


lemma surj_val': "\<exists>C. v = val C"
  apply(induct v)
  apply(insert val_unit_1_ex)
  apply(auto intro: val_empty)
  apply(rule_tac x="add_mset c C" in exI)
  apply(auto simp add: val_add_mset)
  done


theorem surj_val: "surj val"
  by (auto simp add: surj_def intro: surj_val')


end
end