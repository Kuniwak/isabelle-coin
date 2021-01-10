theory RmMultiset imports "~~/src/HOL/Library/Multiset" begin


definition rm_mset :: "'a \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset" where
  "rm_mset x M \<equiv> M - replicate_mset (count M x) x"


lemma diff_id[rule_format]: "A - B = A \<longrightarrow> (\<forall>a \<in># A. a \<notin># B)"
  apply(rule_tac M=B in multiset_induct)
  apply(simp)
  by (metis diff_empty disjunct_not_in multiset_inter_def)


lemma rm_mset_idD[rule_format]: "\<forall>x. rm_mset x M = M \<longrightarrow> x \<notin># M"
  apply(unfold rm_mset_def)
  apply(rule multiset_induct)
  apply(simp)
  apply(clarify)
  apply(drule diff_id)
  apply(assumption)
  apply(erule notE)
  apply(case_tac "x = xa")
  apply(auto)
  done


lemma rm_mset_idI: "x \<notin># M \<Longrightarrow> rm_mset x M = M"
  apply(unfold rm_mset_def)
  apply(subst (asm) count_eq_zero_iff[symmetric])
  apply(erule ssubst)
  apply(subst replicate_mset_0)
  apply(subst diff_empty)
  apply(rule refl)
  done


theorem rm_mset_id_iff: "x \<notin># M \<longleftrightarrow> rm_mset x M = M"
  apply(rule iffI)
  apply(erule rm_mset_idI)
  apply(erule rm_mset_idD)
  done


theorem rm_mset_plus_replicate_mset_count_cancel: "(rm_mset x M) + replicate_mset (count M x) x = M"
  apply(unfold rm_mset_def)
  by (meson count_le_replicate_mset_subset_eq less_imp_le not_le subset_mset.diff_add)


theorem nmem_rm_mset: "x \<notin># rm_mset x M"
  by (simp add: rm_mset_def in_diff_count)


theorem count_rm_set: "count (rm_mset x M) x = (if x \<in># M then 0 else count M x)"
  apply(case_tac "x \<in># M")
  apply(subst if_P)
  apply(assumption)
  apply(subst rm_mset_def)
  apply(subst count_diff)
  apply(subst count_replicate_mset)
  apply(subst if_P)
  apply(rule refl)
  apply(rule diff_self_eq_0)
  apply(subst if_not_P)
  apply(assumption)
  apply(subst (asm) rm_mset_id_iff)
  apply(erule ssubst)
  apply(rule refl)
  done
end