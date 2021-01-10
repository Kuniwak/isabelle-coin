theory ReplicateMultiset imports "~~/src/HOL/Library/Multiset" begin

lemma set_mset_add_mset: "set_mset (add_mset x M) = (if x \<in># M then set_mset M else insert x (set_mset M))"
  apply(auto)
  done

lemma sum_eq_weak: "\<forall>x \<in> A. f x = g x \<Longrightarrow> sum f A = sum g A"
  apply(auto)
  done

lemma sum_replicate_mset_if[rule_format]: "\<forall>x. x \<notin># M \<longrightarrow> (\<Sum>m\<in>set_mset M. replicate_mset (count (add_mset x M) m) m) = (\<Sum>m\<in>set_mset M. replicate_mset (count M m) m)"
  apply(rule_tac M=M in multiset_induct)
  apply(auto intro: sum_eq_weak)
  done

lemma replicate_mset_count_add_mset: "replicate_mset (count (add_mset x M) m) m = (if x = m then replicate_mset (Suc (count M m)) m else replicate_mset (count M m) m)"
  apply(auto)
  done

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

lemma singleton_diff_id: "x \<notin> A \<Longrightarrow> {x} - A = {x}"
  apply(auto)
  done

lemma diff_singleton_id: "x \<notin> A \<Longrightarrow> A - {x} = A"
  apply(auto)
  done

lemma singleton_Int_id: "x \<notin> A \<Longrightarrow> {x} \<inter> A = {}"
  apply(auto)
  done

lemma sum_split: "\<lbrakk> x \<in> A; finite A \<rbrakk> \<Longrightarrow> sum f A = f x + sum f (A - {x})" 
  apply(frule finite_ex_insert)
  apply(auto)
  done

lemma sum_ifI[rule_format]: "finite A \<longrightarrow> (\<forall>x \<in> A. \<not>P x) \<longrightarrow> sum (\<lambda>y. if P y then f y else g y) A = sum g A"
  apply(rule impI)
  apply(erule_tac F=A in finite_induct)
  apply(auto)
  done

lemma sum_diff_replicate_mset_count: "\<forall>x. (\<Sum>m\<in>set_mset M - {x}. replicate_mset (count M m) m) = (\<Sum>m\<in>set_mset M. replicate_mset (count M m) m) - replicate_mset (count M x) x"
  apply(induct M)
  apply(subst (1 2) set_mset_empty)
  apply(subst empty_Diff)
  apply(subst (1 2) sum.empty)
  apply(subst diff_empty)
  apply(rule allI)
  apply(rule refl)
  apply(rule allI)
  by (metis (no_types, lifting) add_diff_cancel_left' count_inI diff_empty diff_singleton_id finite_set_mset replicate_mset_eq_empty_iff sum_split)

theorem sum_replicate_mset: "M = sum (\<lambda>m. replicate_mset (count M m) m) (set_mset M)"
  apply(rule_tac M=M in multiset_induct)
  apply(subst set_mset_empty)
  apply(subst sum.empty)
  apply(rule refl)

  apply(subst set_mset_add_mset)
  apply(case_tac "x \<in># M")

  apply(subst if_P)
  apply(assumption)
  apply(subst replicate_mset_count_add_mset)
  apply(subst sum_split)
  apply(assumption)
  apply(rule finite_set_mset)
  apply(subst if_P)
  apply(rule refl)
  apply(subst sum_ifI)
  apply(force)
  apply(force)
  apply(subst sum_diff_replicate_mset_count)
  apply(subst replicate_mset_Suc)
  apply(subst union_mset_add_mset_left)
  apply(subst add_mset_add_mset_same_iff)
  apply(erule subst)
  apply(metis count_le_replicate_mset_subset_eq order_refl subset_mset.add_diff_inverse)

  apply(subst if_not_P)
  apply(assumption)
  apply(subst sum.insert)
  apply(rule finite_set_mset)
  apply(assumption)
  apply(subst count_add_mset)
  apply(subst if_P)
  apply(rule refl)
  apply(subst replicate_mset_Suc)
  apply(subst union_mset_add_mset_left)
  apply(subst add_mset_add_mset_same_iff)
  apply(subst sum_replicate_mset_if)
  apply(assumption)
  apply(subst (asm) not_in_iff)
  apply(erule_tac s=0 in ssubst)
  apply(subst replicate_mset_0)
  apply(subst empty_neutral)
  apply(assumption)
  done
end