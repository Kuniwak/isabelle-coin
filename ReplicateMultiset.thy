theory ReplicateMultiset imports "~~/src/HOL/Library/Multiset" begin

lemma finite_ex_insert[rule_format]:"finite A \<longrightarrow> x \<in> A \<longrightarrow> (\<exists>A'. x \<notin> A' \<and> A = {x} \<union> A')"
  apply(rule impI)
  apply(erule_tac F=A in finite_induct)
  apply(rule impI)
  apply(erule emptyE)
  apply(intro impI)
  apply(subst (asm) insert_iff)
  apply(elim disjE)
  apply(clarify)
  apply(rule_tac x=F in exI)
  apply(erule conjI)
  apply(subst insert_is_Un[symmetric])
  apply(rule refl)
  apply(drule mp)
  apply(assumption)
  apply(elim exE)
  apply(elim conjE)
  apply(rule_tac x="insert xa A'" in exI)
  apply(auto)
  done

lemma sum_split: "\<lbrakk> x \<in> A; finite A \<rbrakk> \<Longrightarrow> sum f A = f x + sum f (A - {x})" 
  apply(frule finite_ex_insert)
  apply(auto)
  done

lemma sum_if_not_P[rule_format]: "finite A \<longrightarrow> (\<forall>x \<in> A. \<not>P x) \<longrightarrow> sum (\<lambda>y. if P y then f y else g y) A = sum g A"
  apply(rule impI)
  apply(erule_tac F=A in finite_induct)
  apply(auto)
  done

lemma count_sum: "finite A \<Longrightarrow> count (sum f A) x = sum (\<lambda>y. count (f y) x) A"
  apply(erule finite_induct)
  apply(subst (1 2) sum.empty)
  apply(subst count_empty)
  apply(rule refl)

  apply(subst (1 2) sum.insert)
  apply(assumption)
  apply(assumption)
  apply(subst count_union)
  apply(subst nat_add_left_cancel)
  apply(assumption)
  done

theorem sum_replicate_mset: "M = sum (\<lambda>m. replicate_mset (count M m) m) (set_mset M)"
  apply(rule multiset_eqI)
  apply(subst count_sum)
  apply(rule finite_set_mset)
  apply(subst count_replicate_mset)
  apply(case_tac "x \<in># M")
  apply(subst sum_split)
  apply(assumption)
  apply(rule finite_set_mset)
  apply(subst if_P)
  apply(rule refl)
  apply(subst sum_if_not_P)
  apply(subst finite_Diff)
  apply(rule finite_set_mset)
  apply(rule TrueI)
  apply(rule notI)
  apply(simp)
  apply(subst sum.neutral_const)
  apply(rule add_0_right[symmetric])
  apply(subst sum_if_not_P)
  apply(rule finite_set_mset)
  apply(erule contrapos_nn)
  apply(erule ssubst)
  apply(assumption)
  apply(subst sum.neutral_const)
  apply(subst (asm) not_in_iff)
  apply(assumption)
  done
end