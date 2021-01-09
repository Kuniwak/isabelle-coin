theory Coin imports "~~/src/HOL/Library/Multiset" begin


section "Fundamental Lemmas"
subsection "nat"


theorem "\<lbrakk> v1 dvd v2; v = v1 * c1 + v2 * c2; c2 \<ge> c2' \<rbrakk> \<Longrightarrow> \<exists>c1'. v = v1 * (c1 + c1') + v2 * (c2 - c2')" for v :: nat
  apply(rule_tac x="(v2 div v1) * c2'" in exI)
  apply(auto simp add: add_mult_distrib2 diff_mult_distrib2)
  done


lemma le_div_plus_mod[rule_format]: "\<forall>x. x \<ge> y \<longrightarrow> y > 1 \<longrightarrow> x > x div y + x mod y" for x :: nat and y :: nat
  apply(induct y)
  apply(force)
  apply(auto)
  by (metis Suc_mono div_greater_zero_iff less_diff_conv minus_mod_eq_div_mult n_less_n_mult_m zero_less_Suc)


lemma plus_minus_assoc: "b \<ge> c \<Longrightarrow> a + b - c = a + (b - c)" for a :: nat
  by auto


lemma a_minus_b_plus_c_plus_d_le_a: "a \<ge> b \<Longrightarrow> a - b + c + d < a \<longleftrightarrow> b > c + d" for a :: nat
  by auto


lemma a_eq_a_minus_b_plus_c_plus_d_is_b_eq_c_plus_d: "a \<ge> b \<Longrightarrow> a = a - b + c + d \<longleftrightarrow> b = c + d"  for a :: nat
  by auto


lemma a_eq_b_plus_a_minus_b: "a \<ge> b \<Longrightarrow> a = b + (a - b)" for a :: nat
  by auto


lemma a_plus_b_eq_b_plus_c_minus_d: "c \<ge> d \<Longrightarrow> a + b = b + c - d \<longleftrightarrow> a = c - d" for a :: nat
  by auto


lemma a_plus_b_minus_c_le_a: "c \<ge> b \<Longrightarrow> a + b - c \<le> a" for a :: nat
  apply(simp)
  done


lemma le_1_is_lt_2: "x \<le> Suc 0 \<Longrightarrow> x < 2" for x :: nat
  by auto


lemma le_4_is_lt_5: "x \<le> 4 \<Longrightarrow> x < 5" for x :: nat
  by auto


lemma le_Suc_flip_le: "\<lbrakk> x \<le> Suc y; y < x \<rbrakk> \<Longrightarrow> Suc y = x"
  apply(simp)
  done


lemma neq_le_SucD: "\<lbrakk> x \<noteq> z; x < y; y = z + 1 \<rbrakk> \<Longrightarrow> x < z" for x :: nat
  apply(auto)
  done


lemma n_eq_div_plus_mod: "v2 = m * v1 \<Longrightarrow> n * v1 = n div m * v2 + n mod m * v1" for n :: nat
  by (metis distrib_right div_mult_mod_eq mult.assoc)


lemma le_minus[rule_format]: "x \<le> x - y \<longrightarrow> x \<le> y \<or> y = 0"  for x :: nat
  apply(induct x arbitrary: y)
  apply(auto)
  done


subsection "multiset"
lemma (in comm_monoid_diff) fold_mset_empty: "fold_mset (+) x {#} = x"
  by auto


lemma (in comm_monoid_diff) abc_bac: "a + (b + c) = b + (a + c)"
  by (rule local.add.left_commute)


lemma (in comm_monoid_diff) comm_monoid_add_comp_fun_commute: "comp_fun_commute (+)"
  by (auto simp add: comp_fun_commute_def abc_bac intro: local.add.left_commute)


lemma (in comm_monoid_diff) fold_mset_add: "fold_mset (+) y (add_mset x M) = x + (fold_mset (+) y M)"
  by (auto simp add: comp_fun_commute.fold_mset_add_mset comm_monoid_add_comp_fun_commute)


lemma (in comm_monoid_diff) fold_mset_plus: "fold_mset (+) (x + y) M = y + fold_mset (+) x M"
  apply(induct M)
  apply(subst (1 2) fold_mset_empty)
  apply(rule add_commute)
  apply(subst (1 2) fold_mset_add)
  apply(erule ssubst)
  apply(subst (1 2) add_assoc[symmetric])
  apply(subst add_commute)
  apply(rule refl)
  done


lemma replicate_mset_subseteq: "replicate_mset (count C c) c \<subseteq># C"
  using count_le_replicate_mset_subset_eq by fastforce


lemma count_le_size: "count C x \<le> size C"
  using replicate_mset_subseteq size_mset_mono by fastforce


lemma count_add_mset_eq_count: "\<lbrakk> xa \<noteq> x \<rbrakk> \<Longrightarrow> count (add_mset xa M) x = count M x"
  by auto


lemma count_eq_replicate_mset_subset_eq: "count M x = n \<Longrightarrow> replicate_mset n x \<subseteq># M"
  using count_le_replicate_mset_subset_eq by fastforce


lemma subset_add_weak: "A \<subseteq># B \<Longrightarrow> A \<subseteq># add_mset x B"
  using subset_mset.order.trans by fastforce


lemma subset_plus_weak: "A \<subseteq># B \<Longrightarrow> A \<subseteq># B + C"
  by (simp add: subset_mset.add_increasing2)


lemma count_size_FalseE: "\<lbrakk>count M x = n; size M < n\<rbrakk> \<Longrightarrow> False"
  by (meson count_le_size not_le)


lemma image_mset_diff_nat: "B \<subseteq># A \<Longrightarrow> image_mset f (A - B) = image_mset f A - image_mset f B"  for f :: "'a \<Rightarrow> nat"
  apply(unfold image_mset_def)
  by (metis image_mset_Diff image_mset_def)


section "Coins"
subsection "Coin Definitions"
datatype Coin = One | Five | Ten | Fifty | Hundred | FiveHundred


subsection "Value of Coins"
type_alias val_unit = nat


fun val_yen_unit :: "Coin \<Rightarrow> val_unit" where
  "val_yen_unit One = 1" |
  "val_yen_unit Five = 5" |
  "val_yen_unit Ten = 10" |
  "val_yen_unit Fifty = 50" |
  "val_yen_unit Hundred = 100" |
  "val_yen_unit FiveHundred = 500"


theorem inj_val_yen_unit: "inj val_yen_unit"
  apply(unfold inj_def)
  apply(intro allI)
  apply(case_tac x)
  apply(case_tac y)
  apply(auto)
  apply(case_tac y)
  apply(auto)
  apply(case_tac y)
  apply(auto)
  apply(case_tac y)
  apply(auto)
  apply(case_tac y)
  apply(auto)
  apply(case_tac y)
  apply(auto)
  done


theorem range_val_yen_unit: "range val_yen_unit = {1, 5, 10, 50, 100, 500}"
  apply(subst full_SetCompr_eq[symmetric])
  apply(auto)
  apply(case_tac xa)
  apply(auto)
  apply(rule_tac x=One in exI)
  apply(force)
  apply(rule_tac x=Five in exI)
  apply(force)
  apply(rule_tac x=Ten in exI)
  apply(force)
  apply(rule_tac x=Fifty in exI)
  apply(force)
  apply(rule_tac x=Hundred in exI)
  apply(force)
  apply(rule_tac x=FiveHundred in exI)
  apply(force)
  done


lemma val_yen_unit_gt_0: "val_yen_unit x > 0"
  apply(case_tac x)
  apply(auto)
  done


lemma val_yen_unit_eq_0E: "val_yen_unit x = 0 \<Longrightarrow> P"
  apply(insert val_yen_unit_gt_0)
  apply(subst (asm) zero_less_iff_neq_zero)
  apply(drule_tac x=x in meta_spec)
  apply(erule notE)
  apply(assumption)
  done


definition val :: "Coin multiset \<Rightarrow> nat" where
  "val M = sum_mset (image_mset val_yen_unit M)"


lemma val_empty: "val {#} = 0"
  apply(auto simp add: val_def)
  done


lemma val_singleton: "val {#c#} = val_yen_unit c"
  apply(unfold val_def)
  apply(auto)
  done


lemma val_add: "val (add_mset x M) = val_yen_unit x + val M"
  apply(induct M)
  apply(auto simp add: val_def)
  done


lemma val_plus: "val (A + B) = val A + val B"
  apply(auto simp add: val_def)
  done


lemma val_diff: "B \<subseteq># A \<Longrightarrow> val (A - B) = val A - val B"
  apply(auto simp add: val_def)
  apply(subst image_mset_diff_nat)
  apply(assumption)
  apply(rule ordered_cancel_comm_monoid_diff_class.sum_mset_diff)
  apply(erule image_mset_subseteq_mono)
  done


theorem val_aribitrary: "\<exists>C1 C2. C1 \<noteq> C2 \<and> val C1 = val C2"
  apply(rule_tac x="{# Five #}" in exI)
  apply(rule_tac x="{# One, One, One, One, One #}" in exI)
  apply(auto simp add: val_add)
  done


lemma val_0: "val C = 0 \<longleftrightarrow> C = {#}"
  apply(case_tac C)
  apply(auto simp add: val_empty val_add val_yen_unit_gt_0)
  done


lemma val_add_gt_0: "val (add_mset c C) > 0"
  apply(subst val_add)
  apply(rule trans_less_add1)
  apply(rule val_yen_unit_gt_0)
  done


lemma val_gt_0_eq_not_empty: "val C > 0 \<longleftrightarrow> C \<noteq> {#}"
  apply(rule iffI)
  apply(case_tac C)
  apply(clarify)
  apply(subst (asm) val_empty)
  apply(subst (asm) less_nat_zero_code)
  apply(erule FalseE)
  apply(erule ssubst)
  apply(subst neq_commute)
  apply(rule empty_not_add_mset)
  apply(drule multi_nonempty_split)
  apply(elim exE)
  apply(erule ssubst)
  apply(rule val_add_gt_0)
  done


lemma val_replicate_mset_count: "val (replicate_mset n x) = n * val_yen_unit x"
  apply(induct n)
  apply(auto simp add: val_empty val_add)
  done


lemma count_le_val: "count C x * val_yen_unit x \<le> val C"
  apply(induct C)
  apply(auto simp add: val_add)
  done


lemma same_val_singleton_size_le[rule_format]: "val {#c#} = val C \<longrightarrow> size {#c#} \<le> size C"
  apply(case_tac C)
  apply(erule ssubst)
  apply(rule impI)
  apply(subst (asm) val_add)
  apply(subst (asm) (1 2) val_empty)
  apply(subst (asm) add_0_right)
  apply(erule val_yen_unit_eq_0E)
  apply(case_tac x)
  apply(auto)
  done


definition dvd_coins :: "val_unit set \<Rightarrow> bool" where
  "dvd_coins V \<equiv> \<forall>v1 \<in> V. \<forall>v2 \<in> V. v1 < v2 \<longrightarrow> v1 dvd v2"


theorem dvd_coins_yen: "dvd_coins (range val_yen_unit)"
  apply(unfold dvd_coins_def range_val_yen_unit)
  apply(auto)
  done



definition next_Coin :: "Coin \<Rightarrow> Coin \<Rightarrow> bool" where
  "next_Coin c1 c3 \<equiv> \<nexists>c2. val_unit c1 < val_unit c2 \<and> val_unit c2 < val_unit c3"


fun next_Coin :: "Coin \<Rightarrow> Coin option"where
  "next_Coin One = Some Five" |
  "next_Coin Five = Some Ten" |
  "next_Coin Ten = Some Fifty" |
  "next_Coin Fifty = Some Hundred" |
  "next_Coin Hundred = Some FiveHundred" |
  "next_Coin FiveHundred = None"


fun redundant_since :: "Coin \<Rightarrow> nat option"where
  "redundant_since One = Some 5" |
  "redundant_since Five = Some 2" |
  "redundant_since Ten = Some 5" |
  "redundant_since Fifty = Some 2" |
  "redundant_since Hundred = Some 5" |
  "redundant_since FiveHundred = None"


lemma redundant_sinceD: "redundant_since c = Some m \<Longrightarrow> \<exists>c'. next_Coin c = Some c'"
  apply(case_tac c)
  apply(auto)
  done


lemma redundant_since_gtD: "redundant_since x = Some m \<Longrightarrow> m > 1"
  apply(case_tac x)
  apply(auto)
  done


lemma all_redundant_since_imp: "(\<forall>c m. redundant_since c = Some m \<longrightarrow> P c m) \<longleftrightarrow>
    (P One 5 \<and> P Five 2 \<and> P Ten 5 \<and> P Fifty 2 \<and> P Hundred 5)"
  apply(auto)
  apply(case_tac c)
  apply(auto)
  done


lemma val_yen_unit_next_Coin: "\<lbrakk> redundant_since c = Some m; next_Coin c = Some c'\<rbrakk> \<Longrightarrow> val_yen_unit c' = m * val_yen_unit c"
  apply(case_tac c)
  apply(auto)
  done


subsection "Normal form"
definition normal :: "Coin multiset \<Rightarrow> bool" where
  "normal C \<equiv> \<forall>C'. val C = val C' \<longrightarrow> size C \<le> size C'"  


lemma normal_empty: "normal {#}"
  apply(unfold normal_def)
  apply(auto)
  done


lemma normal_singleton: "normal {# c #}"
  apply(unfold normal_def)
  apply(clarify)
  apply(erule same_val_singleton_size_le)
  done


lemma not_normal_singletonE: "\<not>normal {# c #} \<Longrightarrow> P"
  apply(erule notE)
  apply(rule normal_singleton)
  done


lemma normal_add_imp_normal: "normal (add_mset c C) \<Longrightarrow> normal C"
  apply(unfold normal_def)
  apply(auto)
  apply(drule_tac x="add_mset c C'" in spec)
  apply(drule mp)
  apply(subst (1 2) val_add)
  apply(auto)
  done


lemma normal_add_add_imp_normal: "normal (add_mset c1 (add_mset c2 C)) \<Longrightarrow> normal C \<and> normal (add_mset c1 C) \<and> normal (add_mset c2 C)"
  apply(intro conjI)
  apply(drule normal_add_imp_normal)
  apply(erule normal_add_imp_normal)
  apply(subst (asm) add_mset_commute)
  apply(erule normal_add_imp_normal)
  apply(erule normal_add_imp_normal)
  done


theorem not_normal_if_redundant: "\<lbrakk> redundant_since c = Some m; count C c = m \<rbrakk> \<Longrightarrow> \<not> normal C"
  apply(unfold normal_def)
  apply(subst not_all)
  apply(frule redundant_sinceD)
  apply(clarify)
  apply(rule_tac x="C + {# c' #} - replicate_mset m c" in exI)
  apply(clarify)
  apply(subst (asm) size_Diff_submset)
  apply(rule subset_plus_weak)
  apply(force intro: count_eq_replicate_mset_subset_eq)
  apply(clarsimp)
  apply(drule mp)
  apply(subst val_diff)
  apply(rule subset_add_weak)
  apply(force intro: count_eq_replicate_mset_subset_eq)
  apply(subst val_replicate_mset_count)
  apply(subst val_add)
  apply(case_tac c)
  apply(auto)
  apply(case_tac c)
  apply(auto dest!: le_minus le_1_is_lt_2 le_4_is_lt_5 elim: count_size_FalseE)
  done


definition no_redundant :: "Coin multiset \<Rightarrow> bool" where
  "no_redundant C \<equiv> \<forall>c n. redundant_since c = Some n \<longrightarrow> count C c < n"


lemma no_redundant_empty: "no_redundant {#}"
  apply(unfold no_redundant_def)
  apply(auto)
  apply(case_tac c)
  apply(auto)
  done


lemma no_redundant_singleton: "no_redundant {#c#}"
  apply(unfold no_redundant_def)
  apply(rule allI)
  apply(case_tac ca)
  apply(auto)
  done


lemma no_redundant_add_imp_no_redundant[rule_format]: "no_redundant (add_mset c C) \<longrightarrow> no_redundant C"
  apply(auto simp add: no_redundant_def)
  done


lemma no_redundant_not_no_redundant_addD: "\<lbrakk> no_redundant C; \<not> no_redundant (add_mset c C) \<rbrakk> \<Longrightarrow> redundant_since c = Some (Suc (count C c))"
  apply(unfold no_redundant_def not_all not_imp not_less)
  apply(elim exE conjE)
  apply(drule_tac x=x in spec)
  apply(drule_tac x=xa in spec)
  apply(drule mp)
  apply(assumption)
  apply(subst (asm) count_add_mset)
  apply(case_tac "c=x")
  apply(subst (asm) if_P)
  apply(assumption)
  apply(drule le_Suc_flip_le)
  apply(assumption)
  apply(clarify)
  apply(subst (asm) if_not_P)
  apply(assumption)
  apply(subst (asm) not_less[symmetric])
  apply(erule notE)
  apply(assumption)
  done


lemma redundant_since_eq_Some_SucD: "\<lbrakk> redundant_since c = Some (Suc (count C c)); next_Coin c = Some c' \<rbrakk> \<Longrightarrow> val (replicate_mset (count C c) c) \<le> val {#c'#}"
  apply(subst val_replicate_mset_count)
  apply(subst val_singleton)
  apply(case_tac c)
  apply(auto)
  done


lemma not_no_redundant_imp_not_normal[rule_format]: "\<not>no_redundant C \<longrightarrow> \<not>normal C"
  apply(induct C)
  apply(rule impI)
  apply(erule notE)
  apply(rule no_redundant_empty)

  apply(rule impI)
  apply(case_tac "\<not>no_redundant C")
  apply(drule mp)
  apply(assumption)
  apply(erule_tac Q="normal C" in contrapos_nn)
  apply(erule normal_add_imp_normal)

  apply(subst (asm) not_not)
  apply(drule no_redundant_not_no_redundant_addD)
  apply(assumption)
  apply(subst normal_def)
  apply(unfold not_all not_imp size_add_mset not_le less_Suc_eq_le)
  apply(frule redundant_sinceD)
  apply(elim exE)
  apply(rule_tac x="C + {#c'#} - replicate_mset (count C x) x" in exI)
  apply(rule conjI)
  apply(subst val_add)
  apply(subst val_diff)
  apply(rule subset_plus_weak)
  apply(rule replicate_mset_subseteq)
  apply(subst val_plus)
  apply(subst a_plus_b_eq_b_plus_c_minus_d)
  apply(erule redundant_since_eq_Some_SucD)
  apply(assumption)
  apply(subst val_replicate_mset_count)
  apply(drule_tac val_yen_unit_next_Coin)
  apply(assumption)
  apply(subst val_singleton)
  apply(erule_tac t="val_yen_unit c'" in ssubst)
  apply(subst mult_Suc)
  apply(subst diff_add_inverse2)
  apply(rule refl)

  apply(subst size_Diff_submset)
  apply(rule subset_plus_weak)
  apply(rule replicate_mset_subseteq)
  apply(subst size_union)
  apply(subst size_single)
  apply(subst size_replicate_mset)
  apply(drule redundant_since_gtD)
  apply(subst (asm) less_Suc_eq_le)
  apply(rule a_plus_b_minus_c_le_a)
  apply(assumption)
  done


theorem normal_imp_no_redundant: "normal C \<Longrightarrow> no_redundant C"
  apply(erule contrapos_pp)
  apply(erule not_no_redundant_imp_not_normal)
  done


lemma x[rule_format]: "no_redundant C \<longrightarrow> val C = val C' \<longrightarrow> size C \<le> size C' \<longrightarrow>
       no_redundant (add_mset x C) \<longrightarrow> val (add_mset x C) = val C' \<longrightarrow> size (add_mset x C) \<le> size C'"
  apply(induct C')
  apply(force simp add: val_empty val_0)

  apply(clarsimp simp add: val_add)
  apply(case_tac x)
  apply(auto)
  done


lemma "no_redundant C \<longrightarrow> val C = val C' \<longrightarrow> size C \<le> size C'"
  apply(induct C)
  apply(intro impI)
  apply(subst size_empty)
  apply(rule le0)
  apply(clarify)
  oops


theorem no_redundant_imp_normal[rule_format]: "no_redundant C \<longrightarrow> normal C"
  apply(unfold no_redundant_def normal_def)
  oops


theorem normal_uniq: "\<lbrakk> normal C1; normal C2; val C1 = val C2 \<rbrakk> \<Longrightarrow> C1 = C2"
  apply(auto simp add: normal_def)
  oops


theorem normal_total: "\<forall>v. \<exists>C. v = val C \<and> normal C"
  apply(unfold normal_def)
  oops


theorem "\<lbrakk> normal C0; normal C2 \<rbrakk> \<Longrightarrow> \<exists>C1. C1 \<subseteq># C0 \<and> normal (C0 - C1 + C2)"
  oops


subsection "Normalize"
definition normalize1 :: "Coin \<Rightarrow> Coin multiset \<Rightarrow> Coin multiset" where
  "normalize1 c C \<equiv> case (next_Coin c, redundant_since c) of
    (Some c', Some n) \<Rightarrow>
      C - (replicate_mset (count C c) c)
      + (replicate_mset ((count C c) div n) c')
      + (replicate_mset ((count C c) mod n) c) |
    _ \<Rightarrow> C"


lemma redundant_since_normnalize1_D: "\<lbrakk> redundant_since c = Some n; C' = normalize1 c C; next_Coin c = Some c' \<rbrakk> \<Longrightarrow>
    C' = C - (replicate_mset (count C c) c)
       + (replicate_mset ((count C c) div n) c')
       + (replicate_mset ((count C c) mod n) c)"
  apply(unfold normalize1_def)
  apply(auto)
  done


theorem same_val_size_leI: "\<lbrakk> redundant_since c = Some m; count C c \<ge> m; C' = normalize1 c C \<rbrakk> \<Longrightarrow> val C = val C' \<and> size C' < size C"
  apply(frule redundant_sinceD)
  apply(elim exE)
  apply(frule redundant_since_normnalize1_D)
  apply(assumption)
  apply(assumption)
  apply(erule_tac s=" C - replicate_mset (count C c) c + replicate_mset (count C c div m) c' + replicate_mset (count C c mod m) c" in ssubst)
  apply(auto simp add: val_plus val_replicate_mset_count)
  apply(subst val_diff)
  apply(rule replicate_mset_subseteq)
  apply(subst val_replicate_mset_count)
  apply(subst a_eq_a_minus_b_plus_c_plus_d_is_b_eq_c_plus_d)
  apply(rule count_le_val)
  apply(rule n_eq_div_plus_mod)
  apply(force intro: val_yen_unit_next_Coin)
  apply(subst size_Diff_submset)
  apply(rule replicate_mset_subseteq)
  apply(subst size_replicate_mset)
  apply(subst a_minus_b_plus_c_plus_d_le_a)
  apply(rule count_le_size)
  apply(rule le_div_plus_mod)
  apply(assumption)
  apply(case_tac c)
  apply(auto)
  done


end
