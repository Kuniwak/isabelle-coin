theory CoinClass imports "~~/src/HOL/Library/Multiset" begin
type_alias val = nat

lemma finite_induct1[induct set: finite]:
  assumes finite: "finite X"
    and mem: "x \<in> X"
    and base: "P {x}"
    and step: "\<And>X x'. \<lbrakk> finite X; P X; x' \<notin> X; x \<in> X \<rbrakk> \<Longrightarrow> P (insert x' X)"
  shows "P X"
proof -
  obtain X' where 1: "X = insert x X'" and 2: "x \<notin> X'" by (meson Set.set_insert mem)
  have 3: "finite X'" using finite 1 by simp
  show ?thesis
  using 3 mem step[where ?X=X] unfolding 1 proof (induct rule: finite_induct)
    case empty
    show ?case using base .
  next
    case (insert x' F)
    thus ?case
    proof -
      have "\<lbrakk> finite (insert x F); P (insert x F); x' \<notin> insert x F; x \<in> insert x F \<rbrakk> \<Longrightarrow> P (insert x' (insert x F))"
        using step by blast
      hence "P (insert x' (insert x F))" proof (cases "x = x'")
        case True
        thus ?thesis using insert.hyps(3) insert.prems(2) local.step by fastforce
      next
        case False
        then show ?thesis using insert.hyps(1) insert.hyps(2) insert.hyps(3) insert.prems(2) local.step by force
      qed
      thus "P (insert x (insert x' F))" using insert_commute by metis
    qed
  qed
qed

context linorder
begin
lemma infinite_growing2:
  assumes "X \<noteq> {}"
  assumes *: "\<And>x. x \<in> X \<Longrightarrow> \<exists>y\<in>X. y < x"
  shows "\<not> finite X"
proof
  assume "finite X"
  with \<open>X \<noteq> {}\<close> have "Min X \<in> X" "\<forall>x\<in>X. Min X \<le> x"
    by auto
  with *[of "Min X"] show False
    by auto
qed
end

locale dual_wellorder_finite = wellorder + finite +
  assumes greater_induct[case_names greater]: "\<And>z. (\<And>x. (\<And>y. less x y \<Longrightarrow> P y) \<Longrightarrow> P x) \<Longrightarrow> P z"
begin

definition is_bot :: "'a \<Rightarrow> bool"
  where "is_bot a \<equiv> \<forall>b. less_eq a b"

lemma bot_uniq:
  assumes "is_bot a"
    and "is_bot b"
  shows "a = b"
unfolding is_bot_def using antisym assms is_bot_def by force

lemma ex_bot:
  obtains bot where "is_bot bot"
  unfolding is_bot_def by (metis dual_order.order_iff_strict dual_order.trans le_less_linear less_induct)

lemma ex1_bot:
  shows "\<exists>!x. is_bot x"
  using ex_bot bot_uniq by metis

definition bot :: 'a
  where "bot \<equiv> (The is_bot)"

sublocale order_bot bot less_eq less
unfolding bot_def proof standard
  fix a
  show "less_eq (The is_bot) a" by (metis ex1_bot is_bot_def the_equality)
qed

definition is_top :: "'a \<Rightarrow> bool"
  where "is_top a \<equiv> \<forall>b. less_eq b a"

lemma top_uniq:
  assumes "is_top a"
    and "is_top b"
  shows "a = b"
using assms unfolding is_top_def using local.antisym by force

lemma ex_top:
  obtains top where "is_top top"
  unfolding is_top_def using greater_induct by (metis not_le_imp_less that)

lemma ex1_top:
  shows "\<exists>!x. is_top x" using top_uniq ex_top by metis

definition top :: 'a
  where "top \<equiv> (The is_top)"

sublocale order_top less_eq less top
unfolding top_def proof standard
  fix a
  show "less_eq a (The is_top)" by (metis ex1_top is_top_def the_equality)
qed

definition suc :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "suc a b \<equiv> less a b \<and> (\<nexists>c. less a c \<and> less c b)"

lemma suc_uniq1:
  assumes "suc a b"
    and "suc c b"
  shows "a = c"
using assms unfolding suc_def by (meson antisym_conv3)

lemma suc_uniq2:
  assumes "suc a b"
    and "suc a c"
  shows "b = c"
using assms unfolding suc_def by (meson antisym_conv3)

lemma neq_topE:
  assumes "a \<noteq> top"
  obtains b where "less a b" and "\<nexists>x. less a x \<and> less x b"
proof (induct rule: greater_induct)
  case (greater x)
  thus ?case by (metis assms empty_iff less_top finite infinite_growing2 greaterThan_iff that)
qed

lemma ex1_prev:
  assumes "a \<noteq> top"
  obtains b where "suc a b" and "\<And>c. suc a c \<Longrightarrow> c = b"
using assms proof (rule neq_topE)
  fix c
  assume 1: "\<And>b. \<lbrakk> suc a b; \<And>c. suc a c \<Longrightarrow> c = b \<rbrakk> \<Longrightarrow> thesis"
    and 2: "less a c" "\<nexists>x. less a x \<and> less x c"
  have 3: "suc a c" using 2 unfolding suc_def by simp
  have 4: "\<And>b. suc a b \<Longrightarrow> b = c" using 3 suc_uniq2 by blast
  show thesis using 1 3 4 .
qed

lemma neq_botE:
  assumes "a \<noteq> bot"
  obtains b where "less b a" and "\<nexists>x. less b x \<and> less x a"
proof (induct rule: less_induct)
  case (less x)
  thus ?case by (metis assms empty_iff bot_less finite infinite_growing lessThan_iff that)
qed

lemma ex1_suc:
  assumes "a \<noteq> bot"
  obtains b where "suc b a" and "\<And>c. suc c a \<Longrightarrow> c = b"
using assms proof (rule neq_botE)
  fix b
  assume 1: "\<And>b. \<lbrakk>suc b a; \<And>c. suc c a \<Longrightarrow> c = b\<rbrakk> \<Longrightarrow> thesis"
    and 2: "less b a" "\<nexists>x. less b x \<and> less x a"
  have 3: "suc b a" unfolding suc_def using 2 by blast
  have 4: "\<And>c. suc c a \<Longrightarrow> c = b" using 3 suc_uniq1 by blast
  show ?thesis using 1 3 4 .
qed                                                    

theorem transfinite_induct:
  assumes base: "P bot"
    and step: "\<And>x y. \<lbrakk> P x; suc x y \<rbrakk> \<Longrightarrow> P y"
  shows "P x"
proof (induct x rule: less_induct)
  case (less x)
  assume less_step: "\<And>y. less y x \<Longrightarrow> P y"
  show ?case proof (cases "x = bot")
    case True
    show ?thesis unfolding True by (rule base)
  next
    case False
    then obtain y where less: "less y x" and nex: "\<nexists>z. less y z \<and> less z x" using neq_botE by blast
    have P: "P y" using less by (rule less_step)
    have suc: "suc y x" unfolding suc_def using less nex by simp
    show ?thesis using step P suc .
  qed
qed

theorem transfinite_induct_reverse:
  assumes base: "P top"
    and step: "\<And>x y. \<lbrakk> P x; suc y x \<rbrakk> \<Longrightarrow> P y"
  shows "P x"
proof (induct x rule: greater_induct)
  case (greater x)
  assume less_step: "\<And>y. less x y \<Longrightarrow> P y"
  show ?case proof (cases "x = top")
    case True
    show ?thesis unfolding True by (rule base)
  next
    case False
    then obtain y where less: "less x y" and nex: "\<nexists>z. less x z \<and> less z y" using neq_topE by blast
    have P: "P y" using less by (rule less_step)
    have suc: "suc x y" unfolding suc_def using less nex by simp
    show ?thesis using step P suc .
  qed
qed
end

locale coin = finite +
  fixes val_unit :: "'a \<Rightarrow> val"
    and coin1 :: 'a
  assumes val_unit_coin1[simp]: "val_unit coin1 = 1"
    and inj_val_unit: "inj val_unit"
    and val_unit_gt_0: "\<And>v. v \<in> range val_unit \<Longrightarrow> v > 0"
    and dvd_val_units: "\<And>v1 v2. \<lbrakk> v1 \<in> range val_unit; v2 \<in> range val_unit; v1 < v2 \<rbrakk> \<Longrightarrow> v1 dvd v2"
    and greater_induct: "(\<And>x. (\<And>y. val_unit x < val_unit y \<Longrightarrow> P y) \<Longrightarrow> P x) \<Longrightarrow> P x" (* \<leftarrow> FIXME *)
begin

definition less_eq_coin :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "less_eq_coin x y \<longleftrightarrow> val_unit x \<le> val_unit y"

definition less_coin :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "less_coin x y \<longleftrightarrow> val_unit x < val_unit y"

sublocale dual_wellorder_finite less_eq_coin less_coin
unfolding less_eq_coin_def less_coin_def proof
  fix x y
  have 1: "x \<noteq> y \<longleftrightarrow> val_unit x \<noteq> val_unit y" using inj_val_unit by (simp add: inj_eq)
  thus "(val_unit x < val_unit y) = (val_unit x \<le> val_unit y \<and> \<not> val_unit y \<le> val_unit x)" unfolding 1 by auto
next
  fix a
  show "val_unit a \<le> val_unit a" by simp
next
  fix a b
  assume 1: "val_unit a \<le> val_unit b"
    and 2: "val_unit b \<le> val_unit a"
  have 3: "a = b \<longleftrightarrow> val_unit a = val_unit b" using inj_val_unit by (simp add: inj_eq)
  show "a = b" unfolding 3 using 1 2 by simp
next
  fix a b c
  assume 1: "val_unit a \<le> val_unit b"
    and 2: "val_unit b \<le> val_unit c"
  thus "val_unit a \<le> val_unit c" by simp
next
  fix x y
  show "val_unit x \<le> val_unit y \<or> val_unit y \<le> val_unit x" by fastforce
  fix P a
  assume step: "(\<And>x. (\<And>y. val_unit y < val_unit x \<Longrightarrow> P y) \<Longrightarrow> P x)"
  thus "P a" by (rule measure_induct_rule[where ?f=val_unit]; metis)
next
  fix P z
  assume step: "(\<And>x. (\<And>y. val_unit x < val_unit y \<Longrightarrow> P y) \<Longrightarrow> P x)"
  show "P z" using greater_induct step .
qed

lemma val_unit_neq_0: "val_unit c \<noteq> 0"
  by (simp add: val_unit_gt_0)

lemma val_unit_eq_1_is_bot:
  assumes "val_unit c = 1"
  shows "c = coin1"
using assms inj_val_unit val_unit_coin1 by (metis inj_eq)

lemma bot_eq[simp]: "coin1 = bot"
  by (metis less_eq_coin_def less_one linorder_class.not_less bot_least order_class.le_imp_less_or_eq rangeI val_unit_coin1 val_unit_eq_1_is_bot val_unit_gt_0)

lemma val_unit_bot[simp]: "val_unit bot = 1"
  unfolding bot_eq[symmetric] val_unit_coin1 by (rule refl) 

lemma neq_bot_implies_val_unit_gt_1:
  assumes "c \<noteq> coin1"
  shows "val_unit c > 1"
proof -
  have "\<nexists>c. val_unit c = 0" using val_unit_gt_0 by simp
  thus "val_unit c > 1" using assms val_unit_eq_1_is_bot by (meson less_one nat_neq_iff)
qed

definition val :: "'a multiset \<Rightarrow> val" where
  "val C \<equiv> sum_mset (image_mset val_unit C)"

lemma val_mempty: "val {#} = 0"
  by (simp add: val_def)

lemma val_add_mset:
  "val (add_mset c C) = val_unit c + val C"
  by (simp add: val_def)

lemma val_plus:
  "val (C1 + C2) = val C1 + val C2"
  by (simp add: val_def)

lemma val_sum:
  assumes "finite m"
  shows "val (sum f m) = sum (val \<circ> f) m"
using assms proof (induct rule: finite_induct)
  case empty
  thus ?case by (simp add: val_mempty)
next
  case (insert x F)
  then show ?case by (simp add: val_plus)
qed

lemma val_singleton: "val {#c#} = val_unit c"
  unfolding val_add_mset val_mempty by simp

lemma val_eq_0D:
  assumes "val C = 0"
  shows "C = {#}"
using assms proof (rule contrapos_pp)
  assume "C \<noteq> {#}"
  then obtain c C' where 1: "c \<in># C" and 2: "C = add_mset c C'" by (meson mset_add multiset_nonemptyE)
  have 3: "val C = val_unit c + val C'" using val_add_mset 2 by simp
  have 4: "val_unit c > 0" using val_unit_gt_0 by simp
  have 5: "val C > 0" using 3 4 by presburger
  thus "val C \<noteq> 0" by simp
qed
  
lemma val_gt_0_eq_not_empty: "val C > 0 \<longleftrightarrow> C \<noteq> {#}"
  using val_mempty val_eq_0D by auto

lemma val_only_bot: "val {#bot#} = 1"
  by (simp add: val_def )

lemma val_eq_1_is_only_one_bot:
  assumes "val C = 1"
  shows "C = {# bot #}"
proof -
  have "C \<noteq> {#}" using assms val_mempty by auto
  then obtain c C' where C_eq: "C = add_mset c C'" by (meson multiset_cases)
  have "val C = val_unit c + val C'" using val_add_mset C_eq by simp
  hence "1 = val_unit c + val C'" using assms by simp
  hence "val_unit c = 0 \<and> val C' = 1 \<or> val_unit c = 1 \<and> val C' = 0" by auto
  hence 1: "val_unit c = 1" and 2: "val C' = 0" by (auto simp add: val_unit_neq_0)
  have 3:"c = bot" using 1 val_unit_eq_1_is_bot by simp
  have 4: "C' = {#}" using 2 val_eq_0D by simp
  show "C = {#bot#}" using 3 4 C_eq by simp
qed

theorem val_eqE:
  fixes v :: val
  obtains C where "val C = v"
proof -
  assume 1: "\<And>C. val C = v \<Longrightarrow> thesis"
  have "val (replicate_mset v bot) = v"
  proof (induct v)
    case 0
    thus "val (replicate_mset 0 bot) = 0" using val_mempty by simp
  next
    case (Suc v)
    note step = Suc
    thus "val (replicate_mset (Suc v) bot) = Suc v" unfolding replicate_mset_Suc val_add_mset val_unit_bot step by simp
  qed
  thus thesis using 1 by simp
qed


definition normal_form :: "'a multiset \<Rightarrow> bool"
  where "normal_form C \<equiv> \<forall>C'. val C = val C' \<longrightarrow> size C \<le> size C'"

theorem normal_form_empty: "normal_form {#}"
  unfolding normal_form_def val_def by simp

theorem normal_form_singleton: "normal_form {#c#}"
unfolding normal_form_def val_singleton proof auto
  fix C'
  assume "val_unit c = val C'"
  hence "C' \<noteq> {#}" using val_unit_gt_0 val_gt_0_eq_not_empty val_mempty val_unit_neq_0 by force
  thus "Suc 0 \<le> size C'" using Suc_le_eq by blast
qed

lemma ex_normal_form:
  obtains C where "v = val C" and "normal_form C"
proof -
  assume 1: "\<And>C. \<lbrakk>v = val C; normal_form C\<rbrakk> \<Longrightarrow> thesis"
  show thesis oops

definition normalize_on :: "'a set \<Rightarrow> val \<Rightarrow> 'a multiset"
  where "normalize_on C v \<equiv> sum
  (\<lambda>c. replicate_mset (
    if c = Max C
    then v div (val_unit c)
    else (v mod (val_unit (The (suc c)))) div (val_unit c)
  ) c) C"

abbreviation normalize :: "val \<Rightarrow> 'a multiset"
  where "normalize \<equiv> normalize_on UNIV"

lemma normalize_0: "normalize 0 = {#}"
unfolding normalize_on_def proof -
  have 1: "\<And>c. 0 div val_unit c = 0" by simp
  have 2: "\<And>c c'. 0 mod val_unit c' div val_unit c = 0" by simp
  have 3: "\<And>c. (if c = top then 0 div val_unit c else 0 mod val_unit (The (suc c)) div val_unit c) = 0" by (simp add: option.case_eq_if)
  show "sum (\<lambda>c. replicate_mset (if c = local.Max UNIV then 0 div val_unit c else 0 mod val_unit (The (suc c)) div val_unit c) c) UNIV = {#}"
  unfolding 1 2 3 by simp
qed

lemma normalize_val_unit: "normalize (val_unit c) = {# c #}"
unfolding normalize_on_def proof -
  have 1: "val_unit c div val_unit (Max UNIV) = (if c = Max UNIV then 1 else 0)"
  proof auto
    assume "c = Max UNIV"
    have "val_unit (Max UNIV) \<noteq> 0" using val_unit_gt_0 by auto
    thus "val_unit (Max UNIV) div val_unit (Max UNIV) = Suc 0" by simp
  next
    assume "c \<noteq> Max UNIV"
    hence "less_coin c (Max UNIV)" using top.not_eq_extremum by (meson UNIV_I local.Max.coboundedI local.antisym_conv2 local.finite)
    thus "val_unit c div val_unit (Max UNIV) = 0" unfolding less_coin_def by simp
  qed
  have 2: "\<And>c' c''. suc c' c'' \<Longrightarrow> val_unit c mod val_unit c'' div val_unit c' = (if c = c' then 1 else 0)"
  proof auto
    fix c2
    assume "suc c c2"
    hence "less_coin c c2" unfolding suc_def by blast
    hence "val_unit c mod val_unit c2 = val_unit c" unfolding less_coin_def by simp
    thus "val_unit c mod val_unit c2 div val_unit c = Suc 0" using val_unit_neq_0[where ?c=c] by simp
  next
    fix c1 c2
    assume suc_1_2: "suc c1 c2"
      and neq: "c \<noteq> c1"
    show "val_unit c mod val_unit c2 div val_unit c1 = 0"
    proof (cases "less_coin c2 c")
      case True
      hence "val_unit c2 dvd val_unit c" using dvd_val_units[where ?v1.0="val_unit c2" and ?v2.0="val_unit c"] suc_def by (simp add: less_coin_def)
      hence "val_unit c mod val_unit c2 = 0" by simp
      thus ?thesis by simp
    next
      case False
      hence "val_unit c2 = val_unit c \<or> less_coin c c2" using antisym_conv3 by force
      thus ?thesis unfolding less_coin_def proof (auto; cases "less_coin c c1")
        case True
        thus "val_unit c div val_unit c1 = 0" by (simp add: less_coin_def)
      next
        case False
        hence less: "less_coin c1 c" using neq by (meson less_coin_def local.not_less_iff_gr_or_eq)
        assume val_unit_gt: "val_unit c < val_unit c2"
        have "\<nexists>c3. less_coin c1 c3 \<and> less_coin c3 c2" using suc_1_2 unfolding suc_def by blast
        hence "False" using less val_unit_gt by (simp add: less_coin_def)
        thus "val_unit c div val_unit c1 = 0" by simp
      qed
    qed
  qed
  have *: "\<And>ca. (if ca = Max UNIV then val_unit c div val_unit ca else val_unit c mod val_unit (The (suc ca)) div val_unit ca) = (if c = ca then 1 else 0)"
  proof -
    fix ca :: 'a
    show " (if ca = Max UNIV then val_unit c div val_unit ca else val_unit c mod val_unit (The (suc ca)) div val_unit ca) = (if c = ca then 1 else 0)"
    proof (cases "ca = Max UNIV")
      case True
      thus ?thesis using 1 by simp
    next
      case False
      have "Max UNIV = top" using ex1_top is_top_def by force
      then obtain cb where suc_a_b: "suc ca cb" using False by (metis exists_least_iff top.not_eq_extremum suc_def)
      have 3: "val_unit c mod val_unit cb div val_unit ca = (if c = ca then 1 else 0)" using 2 suc_a_b .
      have 4: "The (suc ca) = cb" using suc_a_b the_equality by (metis (full_types) neqE suc_def)
      show ?thesis unfolding 4 3 using False by simp
    qed
  qed
  have 2: "UNIV = insert c (UNIV - {c})" by blast
  show "(\<Sum>ca\<in>UNIV. replicate_mset (if ca = local.Max UNIV then val_unit c div val_unit ca else val_unit c mod val_unit (The (suc ca)) div val_unit ca) ca) = {#c#}"
    unfolding * proof (subst 2)
    show "(\<Sum>ca\<in> insert c (UNIV - {c}). replicate_mset (if c = ca then 1 else 0) ca) = {#c#}" 
    proof (subst sum.insert)
      show "finite (UNIV - {c})" by simp
    next
      show "c \<notin> UNIV - {c}" by simp
    next
      show "replicate_mset (if c = c then 1 else 0) c + (\<Sum>ca\<in>UNIV - {c}. replicate_mset (if c = ca then 1 else 0) ca) = {#c#}" by simp
    qed
  qed
qed

lemma val_replicate_mset: "val (replicate_mset n c) = n * val_unit c"
proof (induct n)
  case 0
  thus ?case by (simp add: val_mempty)
next
  case (Suc n)
  thus ?case by (simp add: val_add_mset)
qed

lemma size_sum:
  fixes f :: "'b \<Rightarrow> 'a multiset"
  assumes "finite m"
  shows "size (sum f m) = sum (size \<circ> f) m"
using assms proof (induct rule: finite_induct)
  case empty
  thus ?case by simp
next
  case (insert x F)
  thus ?case by simp
qed

lemma
  assumes "suc (Max A) y"
  shows "normalize_on (insert y A) v = (normalize_on A v) - (replicate_mset (v div val_uni) (Max A)) + (replicate_mset TODO y)"

lemma val_normalize_on: "val (normalize_on {c1. less_eq_coin c1 ct} v) = v"
proof (induct ct arbitrary: v rule: transfinite_induct)
  case 1
  have 2: "{c1. less_eq_coin c1 bot} = {bot}"
  proof auto
    fix x
    assume "less_eq_coin x bot"
    thus "x = bot" using bot_unique by force
  qed
  thus ?case unfolding 2 by (auto simp add: val_def normalize_on_def)
next
  case (2 x y)
  assume 1: "\<And>v. val (normalize_on {c1. less_eq_coin c1 x} v) = v"
    and 2: "suc x y"
  have less: "less_coin x y" and nex: "\<nexists>z. less_coin x z \<and> less_coin z y" using 2 unfolding suc_def by blast
  have 3: "{c1. less_eq_coin c1 y} = insert y {c1. less_eq_coin c1 x}" using nex sorry
  have "y \<notin> {c1. less_eq_coin c1 x}" using less by auto
  thus ?case unfolding 3 proof auto
qed

lemma val_normalize: "val (normalize v) = v"
unfolding normalize_def proof (simp add: val_sum val_replicate_mset)
  show "(\<Sum>x\<in>UNIV. (if x = top then v div val_unit x else v mod val_unit (The (suc x)) div val_unit x) * val_unit x) = v"
proof -
  have UNIV_eq: "UNIV = {c. less_eq_coin c top}" by simp
  show "(\<Sum>x\<in>UNIV. (if x = top then v div val_unit x else v mod val_unit (The (suc x)) div val_unit x) * val_unit x) = v"
  unfolding UNIV_eq proof (induct top rule: transfinite_induct)
    case 1
    have 2: "{c. less_eq_coin c local.top} = {local.bot}"  by (metis (mono_tags) "1.hyps" Collect_cong UNIV_I all_not_in_conv bot_def ex1_bot is_bot_def local.finite_code local.finite_has_maximal local.top_greatest singleton_conv2 the_equality)
    show ?case unfolding 2 using 1[symmetric] by auto
  next
    case (2 x)
    then show ?case sorry
  qed


theorem normal_form_normalize: "normal_form (normalize v)"
unfolding normal_form_def normalize_def proof auto
  fix C'
  assume "val (sum (\<lambda>c. replicate_mset (case next_coin c of None \<Rightarrow> v div val_unit c | Some c' \<Rightarrow> v mod val_unit c' div val_unit c) c) UNIV) = val C'"
  hence "sum (\<lambda>c. (case next_coin c of None \<Rightarrow> v div val_unit c | Some c' \<Rightarrow> v mod val_unit c' div val_unit c) * val_unit c) UNIV = val C'"
    by (metis (mono_tags, lifting) coin.val_sum coin_axioms comp_apply finite sum.cong val_replicate_mset)
  thus "size (sum (\<lambda>c. replicate_mset (case next_coin c of None \<Rightarrow> v div val_unit c | Some c' \<Rightarrow> v mod val_unit c' div val_unit c) c) UNIV) \<le> size C'"
  using finite proof (simp add: size_sum)    
    assume "sum (\<lambda>c. (case next_coin c of None \<Rightarrow> v div val_unit c | Some c' \<Rightarrow> v mod val_unit c' div val_unit c) * val_unit c) UNIV = val C'"
    show "sum (\<lambda>c. (case next_coin c of None \<Rightarrow> v div val_unit c | Some c' \<Rightarrow> v mod val_unit c' div val_unit c)) UNIV \<le> size C'"
  oops

theorem ex_normal_form:
  fixes v :: val
  assumes "normal_form Otsuri"
    and "val Watasu \<ge> v"
    and "Watasu \<subseteq># Saifu"
  obtains Watasu where "normal_form (Saifu - Watasu + normalize (val Watasu - v))"
  by (metis add.left_neutral cancel_comm_monoid_add_class.diff_cancel normal_form_normalize)

end
end