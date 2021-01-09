theory Yen imports CoinClass begin



datatype Yen = One | Five | Ten | Fifty | Hundred | FiveHundreds


instantiation Yen :: coins begin
fun Yen_unit :: "Yen \<Rightarrow> val" where
  "Yen_unit One = 1" |
  "Yen_unit Five = 5" |
  "Yen_unit Ten = 10" |
  "Yen_unit Fifty = 50" |
  "Yen_unit Hundred = 100" |
  "Yen_unit FiveHundreds = 500"


definition val_unit_Yen: "val_unit_Yen \<equiv> Yen_unit"


lemma inj_val_unit_Yen: "inj Yen_unit"
  apply(unfold inj_def)
  apply(intro allI)
  apply(rule_tac y=x in Yen.exhaust; auto)
  apply(rule_tac y=y in Yen.exhaust; auto)
  apply(rule_tac y=y in Yen.exhaust; auto)
  apply(rule_tac y=y in Yen.exhaust; auto)
  apply(rule_tac y=y in Yen.exhaust; auto)
  apply(rule_tac y=y in Yen.exhaust; auto)
  apply(rule_tac y=y in Yen.exhaust; auto)
  done


lemma dvd_val_units_Yen: "\<forall>c1 c2. Yen_unit c1 < Yen_unit c2 \<longrightarrow> Yen_unit c1 dvd Yen_unit c2"
  apply(intro allI)
  apply(rule_tac y=c1 in Yen.exhaust; auto)
  apply(rule_tac y=c2 in Yen.exhaust; auto)
  apply(rule_tac y=c2 in Yen.exhaust; auto)
  apply(rule_tac y=c2 in Yen.exhaust; auto)
  apply(rule_tac y=c2 in Yen.exhaust; auto)
  apply(rule_tac y=c2 in Yen.exhaust; auto)
  done


instance
  by standard (auto simp add: val_unit_Yen inj_val_unit_Yen dvd_val_units_Yen)
end
end