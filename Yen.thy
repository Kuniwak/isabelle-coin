theory Yen imports CoinClass begin


datatype Yen = Y1 | Y5 | Y10 | Y50 | Y100 | Y500
fun Yen_val_unit :: "Yen \<Rightarrow> val" where
  "Yen_val_unit Y1 = 1" |
  "Yen_val_unit Y5 = 5" |
  "Yen_val_unit Y10 = 10" |
  "Yen_val_unit Y50 = 50" |                  
  "Yen_val_unit Y100 = 100" |
  "Yen_val_unit Y500 = 500"


lemma Yen_double_exhaust: "\<lbrakk>
    P Y1 Y1; P Y1 Y5; P Y1 Y10; P Y1 Y50; P Y1 Y100; P Y1 Y500;
    P Y5 Y1; P Y5 Y5; P Y5 Y10; P Y5 Y50; P Y5 Y100; P Y5 Y500;
    P Y10 Y1; P Y10 Y5; P Y10 Y10; P Y10 Y50; P Y10 Y100; P Y10 Y500;
    P Y50 Y1; P Y50 Y5; P Y50 Y10; P Y50 Y50; P Y50 Y100; P Y50 Y500;
    P Y100 Y1; P Y100 Y5; P Y100 Y10; P Y100 Y50; P Y100 Y100; P Y100 Y500;
    P Y500 Y1; P Y500 Y5; P Y500 Y10; P Y500 Y50; P Y500 Y100; P Y500 Y500
\<rbrakk> \<Longrightarrow> P c1 c2"
  apply(rule_tac y=c1 in Yen.exhaust)
  apply(rule_tac y=c2 in Yen.exhaust; erule ssubst; erule ssubst; assumption)
  apply(rule_tac y=c2 in Yen.exhaust; erule ssubst; erule ssubst; assumption)
  apply(rule_tac y=c2 in Yen.exhaust; erule ssubst; erule ssubst; assumption)
  apply(rule_tac y=c2 in Yen.exhaust; erule ssubst; erule ssubst; assumption)
  apply(rule_tac y=c2 in Yen.exhaust; erule ssubst; erule ssubst; assumption)
  apply(rule_tac y=c2 in Yen.exhaust; erule ssubst; erule ssubst; assumption)
  done


lemma inj_Yen_val_unit: "inj Yen_val_unit"
  apply(unfold inj_def)
  apply(intro allI)
  apply(rule Yen_double_exhaust)
  apply(auto)
  done


lemma dvd_Yen_val_unit[rule_format]: "Yen_val_unit c1 < Yen_val_unit c2 \<longrightarrow> Yen_val_unit c1 dvd Yen_val_unit c2"
  apply(rule Yen_double_exhaust)
  apply(auto)
  done


lemma Yen_val_unit_gt_0: "Yen_val_unit c > 0"
  apply(case_tac c; auto)
  done


lemma Yen_val_unit_range: "range Yen_val_unit = {1, 5, 10, 50, 100, 500}"
  apply(auto)
  apply(case_tac "xa"; auto)
  apply(subst One_nat_def[symmetric])
  apply(fold Yen_val_unit.simps)
  apply(rule range_eqI; rule refl)
  apply(rule range_eqI; rule refl)
  apply(rule range_eqI; rule refl)
  apply(rule range_eqI; rule refl)
  apply(rule range_eqI; rule refl)
  apply(rule range_eqI; rule refl)
  done


instantiation Yen :: linorder begin
definition "less_Yen (a::Yen) (b::Yen) \<equiv> Yen_val_unit a < Yen_val_unit b"
definition "less_eq_Yen (a::Yen) (b::Yen) \<equiv> Yen_val_unit a \<le> Yen_val_unit b"  

instance
  apply(standard)
  apply(auto simp add: less_Yen_def less_eq_Yen_def inj_def)
  apply(insert inj_Yen_val_unit)
  apply(auto simp add: inj_def)
  done
end


lemma mono_Yen_val_unit: "mono Yen_val_unit"
  apply(simp add: mono_def less_eq_Yen_def)
  done


instantiation Yen :: coins begin
definition "val_unit_Yen \<equiv> Yen_val_unit"

instance
  apply(standard)
  apply(auto simp add: val_unit_Yen_def Yen_val_unit_range intro: inj_Yen_val_unit mono_Yen_val_unit Yen_val_unit_gt_0)
  done
end
end