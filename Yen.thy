theory Yen imports CoinClass begin


datatype Yen = Y1 | Y5 | Y10 | Y50 | Y100 | Y500


lemma UNIV_Yen: "(UNIV::Yen set) = {Y1, Y5, Y10, Y50, Y100, Y500}"
  apply(rule equalityI)
  apply(rule subsetI)
  apply(case_tac x; force)
  apply(rule subset_UNIV)
  done


theorem finite_UNIV_Yen: "finite (UNIV::Yen set)"
  apply(subst UNIV_Yen)
  apply(subst finite.intros)+
  apply(rule TrueI)
  done


theorem finite_Yen: "finite C" for C :: "Yen set"
  apply(rule rev_finite_subset)
  apply(rule finite_UNIV_Yen)
  apply(rule subset_UNIV)
  done


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


instantiation Yen :: linorder begin
fun Yen_val_unit :: "Yen \<Rightarrow> val" where
  "Yen_val_unit Y1 = 1" |
  "Yen_val_unit Y5 = 5" |
  "Yen_val_unit Y10 = 10" |
  "Yen_val_unit Y50 = 50" |                  
  "Yen_val_unit Y100 = 100" |
  "Yen_val_unit Y500 = 500"

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

definition "less_Yen (a::Yen) (b::Yen) \<equiv> Yen_val_unit a < Yen_val_unit b"
definition "less_eq_Yen (a::Yen) (b::Yen) \<equiv> Yen_val_unit a \<le> Yen_val_unit b"  

instance
  apply(standard)
  apply(auto simp add: less_Yen_def less_eq_Yen_def inj_def)
  apply(insert inj_Yen_val_unit)
  apply(auto simp add: inj_def)
  done
end


lemma strict_mono_Yen_val_unit: "strict_mono Yen_val_unit"
  apply(simp add: strict_mono_def less_Yen_def)
  done


instantiation Yen :: order_bot begin
definition "bot_Yen \<equiv> Y1"
instance
  apply(standard)
  apply(unfold bot_Yen_def less_eq_Yen_def)
  apply(case_tac "a"; auto)
  done
end


instantiation Yen :: order_top begin
definition "top_Yen \<equiv> Y500"
instance
  apply(standard)
  apply(unfold top_Yen_def less_eq_Yen_def)
  apply(case_tac "a"; auto)
  done
end


instantiation Yen :: Inf begin
definition "Inf_Yen C \<equiv>
  if Y1 \<in> C then Y1
    else if Y5 \<in> C then Y5
      else if Y10 \<in> C then Y10
        else if Y50 \<in> C then Y50
          else if Y100 \<in> C then Y100
            else Y500"


lemma Inf_empty_is_top_Yen: "Inf {} = (top::Yen)"
  apply(unfold top_Yen_def Inf_Yen_def)
  apply(auto)
  done


lemma Yen_val_unit_Inf_le: "x \<in> A \<Longrightarrow> Yen_val_unit (Inf A) \<le> Yen_val_unit x"
  apply(unfold Inf_Yen_def)
  apply(case_tac x; auto)
  done


lemma Yen_val_unit_le_Inf: "(\<forall>x \<in> A. Yen_val_unit z \<le> Yen_val_unit x)
    \<Longrightarrow> Yen_val_unit z \<le> Yen_val_unit (Inf A)"
  apply(unfold Inf_Yen_def)
  apply(case_tac z; auto)
  done


instance by standard
end


instantiation Yen :: Sup begin
definition "Sup_Yen C \<equiv>
  if Y500 \<in> C then Y500
    else if Y100 \<in> C then Y100
      else if Y50 \<in> C then Y50
        else if Y10 \<in> C then Y10
          else if Y5 \<in> C then Y5
            else Y1"

lemma Sup_empty_is_bot_Yen: "Sup {} = (bot::Yen)"
  apply(unfold bot_Yen_def Sup_Yen_def)
  apply(auto)
  done

lemma Yen_val_unit_le_Sup: "x \<in> A \<Longrightarrow> Yen_val_unit x \<le> Yen_val_unit (Sup A)"
  apply(unfold Sup_Yen_def)
  apply(case_tac x; auto)
  done

lemma Yen_val_unit_Sup_le: "(\<forall>x \<in> A. Yen_val_unit x \<le> Yen_val_unit z)
    \<Longrightarrow> Yen_val_unit (Sup A) \<le> Yen_val_unit z"
  apply(unfold Sup_Yen_def)
  apply(case_tac z; auto)
  done

instance by standard
end


instantiation Yen :: complete_lattice begin
definition "inf_Yen (a::Yen) (b::Yen) \<equiv> if a \<le> b then a else b"
definition "sup_Yen (a::Yen) (b::Yen) \<equiv> if a \<le> b then b else a"
instance
  apply(standard)
  apply(auto simp add: less_eq_Yen_def inf_Yen_def sup_Yen_def top_Yen_def bot_Yen_def)
  apply(auto intro: Yen_val_unit_Inf_le Yen_val_unit_le_Inf Yen_val_unit_le_Sup Yen_val_unit_Sup_le)
  apply(fold top_Yen_def bot_Yen_def)
  apply(auto intro: Inf_empty_is_top_Yen Sup_empty_is_bot_Yen)
  done
end


instantiation Yen :: coins begin
definition "val_unit_Yen \<equiv> Yen_val_unit"
instance
  apply(standard)
  apply(auto simp add: val_unit_Yen_def bot_Yen_def intro: strict_mono_Yen_val_unit dvd_Yen_val_unit)
  done
end
end