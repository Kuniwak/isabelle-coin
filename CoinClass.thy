theory CoinClass imports "RmMultiset" begin


type_alias val = nat


class coins = linorder + complete_lattice +
  fixes val_unit :: "'a \<Rightarrow> val"
  assumes strict_mono_val_unit: "strict_mono val_unit"
  assumes val_unit_bot_1: "val_unit bot = 1"
  assumes dvd_val_units[rule_format]: "\<forall>v1 \<in> range val_unit. \<forall>v2 \<in> range val_unit. v1 < v2 \<longrightarrow> v1 dvd v2"
begin


theorem val_unit_gt_0: "val_unit c > 0"
  apply(insert strict_mono_val_unit)
  apply(drule strict_mono_mono)
  apply(unfold mono_def)
  apply(drule_tac x=bot in spec)
  apply(drule_tac x=c in spec)
  apply(drule mp)
  apply(rule bot_least)
  apply(subst (asm) val_unit_bot_1)
  apply(simp)
  done


theorem inj_val_unit: "inj val_unit"
  apply(unfold inj_def)
  apply(intro allI)
  apply(insert strict_mono_eq)
  apply(drule_tac x=val_unit in meta_spec)
  apply(drule_tac x=x in meta_spec)
  apply(drule_tac x=y in meta_spec)
  apply(drule meta_mp)
  apply(rule strict_mono_val_unit)
  apply(erule ssubst)
  apply(rule imp_refl)
  done


definition val :: "'a multiset \<Rightarrow> val" where
  "val C \<equiv> sum_mset (image_mset val_unit C)"


lemma val_empty: "val {#} = 0"
  by (simp add: val_def)


lemma val_gt_0_eq_not_empty: "val C > 0 \<longleftrightarrow> C \<noteq> {#}"
  by (auto simp add: val_def val_unit_gt_0 dest!: multi_nonempty_split)


lemma val_add_mset: "val (add_mset c C) = val_unit c + val C"
  by (simp add: val_def)


lemma surj_val': "\<exists>C. v = val C"
  apply(induct v)
  apply(insert val_unit_bot_1)
  apply(auto intro: val_empty)
  apply(rule_tac x="add_mset bot C" in exI)
  apply(simp add: val_add_mset)
  done


theorem surj_val: "surj val"
  by (auto simp add: surj_def intro: surj_val')




end
end