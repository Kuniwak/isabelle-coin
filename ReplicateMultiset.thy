theory ReplicateMultiset imports "~~/src/HOL/Library/Multiset" begin

lemma finite_ex_insert[rule_format]:"finite A \<longrightarrow> x \<in> A \<longrightarrow> (\<exists>A'. x \<notin> A' \<and> A = {x} \<union> A')"
  apply(rule impI)
  apply(erule_tac F=A in finite_induct)
  apply(simp)
  by (metis insert_is_Un mk_disjoint_insert)

lemma sum_split: "\<lbrakk> x \<in> A; finite A \<rbrakk> \<Longrightarrow> sum f A = f x + sum f (A - {x})" 
  apply(frule finite_ex_insert)
  by auto

lemma sum_if_not_P[rule_format]: "finite A \<longrightarrow> (\<forall>x \<in> A. \<not>P x) \<longrightarrow> sum (\<lambda>y. if P y then f y else g y) A = sum g A"
  apply(rule impI)
  apply(erule_tac F=A in finite_induct)
  by auto

lemma count_sum: "finite A \<Longrightarrow> count (sum f A) x = sum (\<lambda>y. count (f y) x) A"
  apply(erule finite_induct)
  by auto

theorem sum_replicate_mset: "M = sum (\<lambda>m. replicate_mset (count M m) m) (set_mset M)"
  apply(rule multiset_eqI)
  by (auto simp add: count_sum not_in_iff)
end