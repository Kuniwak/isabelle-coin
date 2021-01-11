theory ReplicateMultiset imports "~~/src/HOL/Library/Multiset" begin

lemma count_sum: "finite A \<Longrightarrow> count (sum f A) x = sum (\<lambda>y. count (f y) x) A"
  apply(erule finite_induct)
  by auto

theorem sum_replicate_mset: "M = sum (\<lambda>m. replicate_mset (count M m) m) (set_mset M)"
  apply(rule multiset_eqI)
  by (auto simp add: count_sum not_in_iff)

end