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

locale wellorder_finite = finite + wellorder + order_bot
begin

definition suc :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "suc a b \<equiv> less a b \<and> (\<nexists>c. less a c \<and> less c b)"

lemma neq_botE:
  assumes "a \<noteq> bot"
  obtains b where "less b a" and "\<nexists>x. less b x \<and> less x a"
proof (induct rule: less_induct)
  case (less x)
  then show ?case by (metis assms empty_iff bot_less finite infinite_growing lessThan_iff that)
qed

lemma
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
end

locale ordering_bot = ordering +
  fixes bot :: 'a ("\<bottom>")
  assumes extremum[simp]: "\<And>x. less_eq bot x"

locale semilattice_bot = semilattice_order_set + ordering_bot
begin

lemma finite_induct1_max:
  fixes P :: "'a set \<Rightarrow> bool"
  assumes finite: "finite X"
    and bot_mem: "x \<in> X"
    and base: "P {x}"
    and extra: "Q X"
    and extra_step: "\<And>X x'. Q (insert x' X) \<Longrightarrow> Q X"
    and step: "\<And>X x'. \<lbrakk> finite X; P X; x' \<notin> X; x \<in> X; Q X\<rbrakk> \<Longrightarrow> P (insert x' X)"
  shows "P X"
using finite bot_mem extra proof (induct rule: finite_induct1)
  show "x \<in> X" using bot_mem .
next
  show "P {x}" using base .
next
  fix X' :: "'a set" and x'
  assume finite': "finite X'"
    and imp_P_x: "\<lbrakk> x \<in> X'; Q X'\<rbrakk> \<Longrightarrow> P X'"
    and nmem': "x' \<notin> X'"
    and bot_mem_insert: "x \<in> insert x' X'"
    and Q_insert: "Q (insert x' X')"
  have Q_x': "Q X'" using extra_step Q_insert .
  have "x = x' \<or> x \<in> X'" using bot_mem_insert by simp
  thus "P (insert x' X')" proof
    assume 1: "x \<in> X'"
    have P_x': "P X'" using imp_P_x 1 Q_x' .
    show "P (insert x' X')" using step finite' P_x' nmem' 1 Q_x' .
  next
    assume x_eq: "x = x'"
    show "P (insert x' X')"
    using finite' Q_x' Q_insert proof (induct rule: finite_induct)
      case empty
      show ?case using base unfolding x_eq .
    next
      case (insert x'' X'')
      assume finite'': "finite X''"
        and nmem'': "x'' \<notin> X''"
        and imp_P_insert'_'': "\<lbrakk> Q X''; Q (insert x' X'') \<rbrakk> \<Longrightarrow> P (insert x' X'')"
        and Q_insert''_'': "Q (insert x'' X'')"
      have Q_x'': "Q X''" using extra_step Q_insert''_'' .
      show ?case
      using step[where ?X="insert x' X''" and ?x'=x''] proof (subst insert_commute)
        assume 2: "\<lbrakk>finite (insert x' X''); P (insert x' X''); x'' \<notin> insert x' X''; x \<in> insert x' X''; Q (insert x' X'')\<rbrakk>
     \<Longrightarrow> P (insert x'' (insert x' X''))"
        show "P (insert x'' (insert x' X''))" proof (cases "x'' = x")
          case True
          have P_insert'_'': "P (insert x' X'')" using imp_P_insert'_'' Q_x'' Q_insert''_'' unfolding x_eq True .
          show ?thesis using P_insert'_'' unfolding x_eq True by simp
        next
          case False
          show ?thesis
          proof (rule 2)
            show "finite (insert x' X'')" using finite'' by simp
          next
            show "P (insert x' X'')" by (metis extra_step imp_P_insert'_'' insert.prems(2) insert_commute)
          next
            show "x'' \<notin> insert x' X''" using nmem'' False unfolding x_eq by simp
          next
            show "x \<in> insert x' X''" unfolding x_eq by simp
          next
            show "Q (insert x' X'')" by (metis extra_step insert.prems(2) insert_commute)
          qed
        qed
      qed
    qed
  qed
qed
end

locale coin = wellorder_finite +
  fixes val_unit :: "'a \<Rightarrow> val"
  assumes val_unit_coin1[simp]: "val_unit bot = 1"
    and inj_val_unit: "inj val_unit"
    and val_unit_gt_0: "\<And>v. v \<in> range val_unit \<Longrightarrow> v > 0"
    and dvd_val_units: "\<And>v1 v2. \<lbrakk> v1 \<in> range val_unit; v2 \<in> range val_unit; v1 < v2 \<rbrakk> \<Longrightarrow> v1 dvd v2"
begin

definition less_eq_coin :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "less_eq_coin x y \<longleftrightarrow> val_unit x \<le> val_unit y"

definition less_coin :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "less_coin x y \<longleftrightarrow> val_unit x < val_unit y"

sublocale wellorder less_eq_coin less_coin
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
qed

definition next_coin_on :: "'a set \<Rightarrow> 'a rel"
  where "next_coin_on C \<equiv> { (c, c') | c c'. c \<in> C \<and> c' \<in> C \<and> less_coin c c' \<and> (\<nexists>c''. c'' \<in> C \<and> less_coin c c'' \<and> less_coin c'' c')}"

theorem next_coin_on_emptyE:
  assumes "p \<in> next_coin_on {}"
  shows "P"
using assms unfolding next_coin_on_def by simp

theorem next_coin_on_singletonE:
  assumes "p \<in> next_coin_on {c0}"
  shows "P"
using assms unfolding next_coin_on_def by clarsimp

theorem id_nmem_next_coin_on: "(c, c) \<notin> next_coin_on C"
  unfolding next_coin_on_def by simp

theorem coin1_nmem_next_coin_on: "(c, bot) \<notin> next_coin_on C"
unfolding next_coin_on_def proof auto
  assume less: "less_coin c bot"
  have not_less: "\<not>less_coin c bot" using val_unit_gt_0 unfolding less_coin_def val_unit_coin1 by auto
  show "\<exists>c''. less_coin c c'' \<and> c'' \<in> C \<and> less_coin c'' bot " using less not_less by simp
qed

theorem wf_next_coin_on:
  shows "wf (next_coin_on X)"
unfolding wf_def proof 


theorem next_coin_on_uniq:
  assumes "(c1, c2) \<in> next_coin_on C"
    and "(c1, c3) \<in> next_coin_on C"
  shows "c2 = c3"
using assms unfolding next_coin_on_def by fastforce


abbreviation next_coin :: "'a rel"
  where "next_coin \<equiv> next_coin_on UNIV"

theorem
  fixes c :: 'a
  assumes mem: "c \<in> X"
    and Min: "c = Min X"
  shows "(\<nexists>c'. (c, c') \<in> next_coin_on X) \<longleftrightarrow> c = Max X"
using finite[where ?A=X] mem proof (induct rule: finite_induct1_max[where ?x=c])
  case mem
  show "c \<in> X" using assms(1) .
next
  case Min
  show "c = Min X" using assms(2) .
next
  case singleton
  show ?case proof
next
  case (insert X x')
  have "\<And>c' X c. \<lbrakk> \<nexists>a. next_coin_on (insert c' X) c a; c' \<notin> X \<rbrakk> \<Longrightarrow> (\<nexists>a. next_coin_on X c a)"
    unfolding next_coin_on_def by (metis (full_types) insert_iff local.dual_order.strict_trans local.less_irrefl)
  hence 1: "\<nexists>c'. next_coin_on X c c'" using insert.prems(2) insert.hyps(3) .
  have "c = local.Max X" using insert.hyps(2) using insert.hyps(4) 1 .
  thus "c = local.Max (insert x' X)" 
qed


theorem Min_UNIV: "local.Min UNIV = coin1"
  by (metis UNIV_I finite image_eqI less_eq_coin_def less_one linorder_class.not_le local.Min.coboundedI local.antisym val_unit_coin1 val_unit_gt_0)


theorem next_coin_on_eq_None: 
  assumes "c \<in> X"
  shows "next_coin_on X c = None \<longleftrightarrow> c = local.Max X"
proof
  assume "next_coin_on X c = None"
  hence 1: "\<And>c'. c' \<in> X \<Longrightarrow> less_eq_coin c' c" using less_eq_coin_def next_coin_on2 by presburger
  show "c = Max X" using finite[where ?A=X] 1 proof (induct rule: finite_induct1[where ?x=c])
    case mem
    thus "c \<in> X" using assms by simp
  next
    case singleton
    thus ?case by simp
  next
    case (insert X x')
    then show ?case by (metis empty_not_insert insertCI local.Max.coboundedI local.Max_in local.antisym local.finite)
  qed
next
  assume "c = Max X"
  thus "next_coin_on X c = None"
    by (metis less_eq_coin_def linorder_class.not_le local.Max.coboundedI local.finite next_coin_on1 not_None_eq)
qed

theorem next_coin_eq_None: "next_coin c = None \<longleftrightarrow> c = local.Max UNIV"
proof
  assume "next_coin c = None"
  hence "\<And>c'. less_eq_coin c' c" by (simp add: next_coin2)
  thus "c = local.Max UNIV" by (simp add: local.antisym)
next
  assume 1: "c = local.Max UNIV"
  show "next_coin c = None"
  proof (cases "next_coin c")
    case None
    then show ?thesis by simp
  next
    case (Some a)
    hence "less_coin c a" using next_coin1 by (simp add: less_coin_def)
    then show ?thesis using 1 using finite by auto
  qed
qed


lemma next_coin_neq_Some_coin1: "next_coin c \<noteq> Some coin1"
  by (metis less_one linorder_class.not_less next_coin_def next_coin_on1 preorder_class.order_refl rangeI val_unit_coin1 val_unit_gt_0)

lemma disj_next_coin_on:
  assumes "x \<in> X"
  shows "(\<exists>x'. x' \<in> X \<and> next_coin_on X x = Some x') \<or> next_coin_on X x = None"
  using next_coin_on1 by blast

lemma val_unit_neq_0: "val_unit c \<noteq> 0"
  by (simp add: val_unit_gt_0)

lemma val_unit_eq_1_is_coin1:
  assumes "val_unit c = 1"
  shows "c = coin1"
using assms inj_val_unit val_unit_coin1 by (metis inj_eq)

lemma neq_coin1_implies_val_unit_gt_1:
  assumes "c \<noteq> coin1"
  shows "val_unit c > 1"
proof -
  have "\<nexists>c. val_unit c = 0" using val_unit_gt_0 by simp
  thus "val_unit c > 1" using assms val_unit_eq_1_is_coin1 by (meson less_one nat_neq_iff)
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

lemma val_only_coin1: "val {#coin1#} = 1"
  by (simp add: val_def)

lemma val_eq_1_is_only_one_coin1:
  assumes "val C = 1"
  shows "C = {# coin1 #}"
proof -
  have "C \<noteq> {#}" using assms val_mempty by auto
  then obtain c C' where C_eq: "C = add_mset c C'" by (meson multiset_cases)
  have "val C = val_unit c + val C'" using val_add_mset C_eq by simp
  hence "1 = val_unit c + val C'" using assms by simp
  hence "val_unit c = 0 \<and> val C' = 1 \<or> val_unit c = 1 \<and> val C' = 0" by auto
  hence 1: "val_unit c = 1" and 2: "val C' = 0" by (auto simp add: val_unit_neq_0)
  have 3:"c = coin1" using 1 val_unit_eq_1_is_coin1 by simp
  have 4: "C' = {#}" using 2 val_eq_0D by simp
  show "C = {#coin1#}" using 3 4 C_eq by simp
qed

theorem val_eqE:
  fixes v :: val
  obtains C where "val C = v"
proof -
  assume 1: "\<And>C. val C = v \<Longrightarrow> thesis"
  have "val (replicate_mset v coin1) = v"
  proof (induct v)
    case 0
    thus "val (replicate_mset 0 coin1) = 0" using val_mempty by simp
  next
    case (Suc v)
    note step = Suc
    thus "val (replicate_mset (Suc v) coin1) = Suc v" unfolding replicate_mset_Suc val_add_mset val_unit_coin1 step by simp
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

definition normalize :: "val \<Rightarrow> 'a multiset"
  where "normalize v \<equiv> sum
  (\<lambda>c. replicate_mset (
    case next_coin c of
      None \<Rightarrow> v div (val_unit c) |
      Some c' \<Rightarrow> (v mod (val_unit c')) div (val_unit c)
  ) c) (UNIV :: 'a set)"

lemma normalize_0: "normalize 0 = {#}"
unfolding normalize_def proof -
  have 1: "\<And>c. 0 div val_unit c = 0" by simp
  have 2: "\<And>c c'. 0 mod val_unit c' div val_unit c = 0" by simp
  have 3: "\<And>c. (case next_coin c of None \<Rightarrow> 0 | _ \<Rightarrow> 0) = 0" by (simp add: option.case_eq_if)
  show "sum (\<lambda>c. replicate_mset (case next_coin c of None \<Rightarrow> 0 div val_unit c | Some c' \<Rightarrow> 0 mod val_unit c' div val_unit c) c) UNIV = {#}"
  unfolding 1 2 3 by simp
qed

lemma normalize_val_unit: "normalize (val_unit c) = {# c #}"
unfolding normalize_def proof -
  have 1: "\<And>c'. next_coin c' = None \<Longrightarrow> val_unit c div val_unit c' = (if c = c' then 1 else 0)"
  proof auto
    assume "next_coin c = None"
    hence "c = local.Max UNIV" using next_coin_eq_None by blast
    have "val_unit c \<noteq> 0" using val_unit_gt_0 by auto
    thus "val_unit c div val_unit c = Suc 0" by simp
  next
    fix c'
    assume "next_coin c' = None" and neq: "c \<noteq> c'"
    hence c'_eq: "c' = local.Max UNIV" using next_coin_eq_None by blast
    hence "less_coin c (local.Max UNIV)"
      by (metis UNIV_I finite local.Max.coboundedI local.antisym local.not_le neq)
    thus "val_unit c div val_unit c' = 0" unfolding c'_eq less_coin_def by simp
  qed
  have 2: "\<And>c' c''. next_coin c' = Some c'' \<Longrightarrow> val_unit c mod val_unit c'' div val_unit c' = (if c = c' then 1 else 0)"
  proof auto
    fix c2
    assume "next_coin c = Some c2"
    hence "less_coin c c2" using next_coin1 by blast
    hence "val_unit c mod val_unit c2 = val_unit c" unfolding less_coin_def by simp
    thus "val_unit c mod val_unit c2 div val_unit c = Suc 0" using val_unit_neq_0[where ?c=c] by simp
  next
    fix c1 c2
    assume 1: "next_coin c1 = Some c2"
      and neq: "c \<noteq> c1"
    show "val_unit c mod val_unit c2 div val_unit c1 = 0"
    proof (cases "less_coin c2 c")
      case True
      hence "val_unit c2 dvd val_unit c" using dvd_val_units[where ?v1.0="val_unit c2" and ?v2.0="val_unit c"] next_coin1 by (simp add: less_coin_def)
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
        hence 2: "less_coin c1 c" using neq by (meson less_coin_def local.not_less_iff_gr_or_eq)
        assume 3: "val_unit c < val_unit c2"
        have "\<nexists>c3. less_coin c1 c3 \<and> less_coin c3 c2" using 1 next_coin1 by blast
        hence "False" using 2 3 by (simp add: less_coin_def)
        thus "val_unit c div val_unit c1 = 0" by simp
      qed
    qed
  qed
  have 1: "\<And>ca. (case next_coin ca of None \<Rightarrow> val_unit c div val_unit ca | Some c' \<Rightarrow> val_unit c mod val_unit c' div val_unit ca) = (if c = ca then 1 else 0)"
  proof -
    fix ca :: 'a
    show "(case next_coin ca of None \<Rightarrow> val_unit c div val_unit ca | Some c' \<Rightarrow> val_unit c mod val_unit c' div val_unit ca) = (if c = ca then 1 else 0)"
    proof (cases "next_coin ca")
      case None
      thus ?thesis using 1 by simp
    next
      case (Some a)
      thus ?thesis using 2 by simp
    qed
  qed
  have 2: "UNIV = (UNIV - {c}) \<union> {c}" by blast
  show "sum (\<lambda>ca. replicate_mset (case next_coin ca of None \<Rightarrow> val_unit c div val_unit ca | Some c' \<Rightarrow> val_unit c mod val_unit c' div val_unit ca) ca) UNIV = {#c#}"
  unfolding 1 proof (subst 2)
    have 3: "sum (\<lambda>ca. replicate_mset (if c = ca then 1 else 0) ca) (UNIV - {c} \<union> {c}) = sum (\<lambda>ca. replicate_mset (if c = ca then 1 else 0) ca) (UNIV - {c}) + sum (\<lambda>ca. replicate_mset (if c = ca then 1 else 0) ca) {c}"
      by (metis (no_types, lifting) "2" Diff_UNIV Diff_eq_empty_iff finite sum.subset_diff)
    show "sum (\<lambda>ca. replicate_mset (if c = ca then 1 else 0) ca) (UNIV - {c} \<union> {c}) = {#c#}"
    unfolding 3 by simp
  qed
qed

lemma sum_Un:
  fixes f :: "'b \<Rightarrow> 'a multiset"
  assumes "finite X" "finite Y"
    and "disjnt X Y"
  shows "sum f (X \<union> Y) = sum f X + sum f Y"
  by (meson assms(1) assms(2) assms(3) disjnt_def sum.union_disjoint)

lemma sum_subst:
  fixes f :: "'b \<Rightarrow> 'a multiset"
  assumes "\<And>y. \<lbrakk> y \<in> X; x \<noteq> y \<rbrakk> \<Longrightarrow> f y = g y"
  shows "sum f (X - {x}) = sum g (X - {x})"
  by (metis DiffD1 DiffD2 assms(1) singletonI sum.cong)

lemma
  assumes "Some c2 = next_coin coin1"
    and "1 < v" "v < val_unit c2"
  shows "normalize v = replicate_mset v coin1"
unfolding normalize_def proof -
  have 1: "UNIV = UNIV - {coin1} \<union> {coin1}" by blast
  show "sum (\<lambda>c. replicate_mset (case next_coin c of None \<Rightarrow> v div val_unit c | Some c' \<Rightarrow> v mod val_unit c' div val_unit c) c) UNIV = replicate_mset v coin1"
  proof (subst 1)
    have 2: "sum (\<lambda>c. replicate_mset (case next_coin c of None \<Rightarrow> v div val_unit c | Some c' \<Rightarrow> v mod val_unit c' div val_unit c) c) (UNIV - {coin1} \<union> {coin1}) = sum (\<lambda>c. replicate_mset (case next_coin c of None \<Rightarrow> v div val_unit c | Some c' \<Rightarrow> v mod val_unit c' div val_unit c) c) (UNIV - {coin1}) + sum (\<lambda>c. replicate_mset (case next_coin c of None \<Rightarrow> v div val_unit c | Some c' \<Rightarrow> v mod val_unit c' div val_unit c) c) {coin1}"
      by (rule sum_Un; simp)
    show "sum (\<lambda>c. replicate_mset (case next_coin c of None \<Rightarrow> v div val_unit c | Some c' \<Rightarrow> v mod val_unit c' div val_unit c) c) (UNIV - {coin1} \<union> {coin1}) = replicate_mset v coin1"
    unfolding 2 proof -
      have 3: "\<And>c. c \<noteq> coin1 \<Longrightarrow> v < val_unit c"
      proof -
        fix c
        assume neq1: "c \<noteq> coin1"
        show "v < val_unit c"
        proof (cases "c = c2")
          case True
          thus ?thesis using assms(3) by simp
        next
          case False
          note neq2 = False
          hence "\<nexists>c3. val_unit coin1 < val_unit c3 \<and> val_unit c3 < val_unit c2" using assms(1) next_coin1 less_coin_def by metis
          thus ?thesis using neq1 neq2 using assms(3) neq_coin1_implies_val_unit_gt_1 val_unit_coin1 by fastforce
        qed
      qed
      have 4: "\<And>c. c \<noteq> coin1 \<Longrightarrow> v div val_unit c = 0" using 3 by simp
      have 5: "\<And>c c'. \<lbrakk> c \<noteq> coin1; Some c' = next_coin c \<rbrakk> \<Longrightarrow> v mod val_unit c' div val_unit c = 0"
      proof -
        fix c c'
        assume neq: "c \<noteq> coin1" and x: "Some c' = next_coin c"
        have neq': "c' \<noteq> coin1" using next_coin_neq_Some_coin1[where ?c=c] x by auto
        have "v < val_unit c'" using 3 neq' by simp
        hence 6: "v mod val_unit c' = v" by simp
        have 7: "v < val_unit c" using 3 neq by simp
        thus " v mod val_unit c' div val_unit c = 0" unfolding 6 using 7 by simp
      qed
      have "\<And>c. c \<noteq> coin1 \<Longrightarrow> (case next_coin c of None \<Rightarrow> v div val_unit c | Some c' \<Rightarrow> v mod val_unit c' div val_unit c) = 0" using 4 5 by (simp add: option.case_eq_if)
      hence 8: "sum (\<lambda>c. replicate_mset (case next_coin c of None \<Rightarrow> v div val_unit c | Some c' \<Rightarrow> v mod val_unit c' div val_unit c) c) (UNIV - {coin1}) = {#}"
        by simp
      have "\<And>c. c = coin1 \<Longrightarrow> (case next_coin c of None \<Rightarrow> v div val_unit c | Some c' \<Rightarrow> v mod val_unit c' div val_unit c) = v"
        by (simp add: assms(1)[symmetric] assms(3))
      hence 9: "sum (\<lambda>c. replicate_mset (case next_coin c of None \<Rightarrow> v div val_unit c | Some c' \<Rightarrow> v mod val_unit c' div val_unit c) c) {coin1} = replicate_mset v coin1"
       by simp
      show "sum (\<lambda>c. replicate_mset (case next_coin c of None \<Rightarrow> v div val_unit c | Some c' \<Rightarrow> v mod val_unit c' div val_unit c) c) (UNIV - {coin1}) + sum (\<lambda>c. replicate_mset (case next_coin c of None \<Rightarrow> v div val_unit c | Some c' \<Rightarrow> v mod val_unit c' div val_unit c) c) {coin1} = replicate_mset v coin1"
      unfolding 8 9 by simp
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


lemma size_replicate_mset: "size (replicate_mset n c) = n"
 by simp

lemma card_UNIV_eq_1D:
  assumes UNIV: "card (UNIV :: 'a set) = 1"
  shows "next_coin coin1 = None"
proof -
  have 1: "\<And>X x. \<lbrakk> x \<in> X; card X = 1 \<rbrakk> \<Longrightarrow> X = {x}" using card_1_singletonE by blast
  hence 2: "(UNIV::'a set) = {coin1}"
  proof (rule_tac 1[where ?X1="UNIV :: 'a set" and ?x1=coin1])
    show "coin1 \<in> UNIV" by simp
  next
    show "card (UNIV :: 'a set) = 1" using UNIV .
  qed
  show "next_coin coin1 = None" by (simp add: 2 next_coin_eq_None)
qed

lemma finite_induct1_max:
  fixes X :: "'a set"
  assumes finite: "finite X"
    and mem: "x \<in> X"
    and x_eq_Min: "x = Min X"
    and base: "P {x}"
    and step: "\<And>X x'. \<lbrakk> finite X; P X; x' \<notin> X; x \<in> X; x = Min X; \<And>x''. x'' \<in> X \<Longrightarrow> less_coin x'' x' \<rbrakk> \<Longrightarrow> P (insert x' X)"
  shows "P X"
proof -
  obtain X' where X_eq: "X = insert x X'" and nmem: "x \<notin> X'" using Set.set_insert[OF mem] .
  have finite': "finite X'" using X_eq finite by simp
  show ?thesis
  using finite' mem x_eq_Min nmem unfolding X_eq proof (induct rule: finite_linorder_max_induct[where ?A=X'])
    case empty
    show ?case using base .
  next
    case (insert x' X)
    assume finite': "finite X"
      and step': "\<lbrakk>x \<in> insert x X; x = Min (insert x X); x \<notin> X\<rbrakk> \<Longrightarrow> P (insert x X)"
      and nmem: "x \<notin> insert x' X"
      and less_all: "\<forall>x'' \<in> X. less_coin x'' x'"
      and Min: "x = Min (insert x (insert x' X))"
    have x_eq: "x = Min (insert x X)"
    proof -
      have 1: "finite (insert x (insert x' X))" using finite' by simp
      have 2: "x \<noteq> x'" using nmem by blast
      have 3: "x = Min (insert x (insert x' X) - {x'})"
      proof -
        have Min_subI: "\<And>X x y. \<lbrakk> finite X; x = Min X; x \<noteq> y \<rbrakk> \<Longrightarrow> x = Min (X - {y})"
        proof -
          fix X :: "'a set" and x y :: 'a
          assume finite: "finite X"
            and x_eq: "x = Min X"
            and x_neq: "x \<noteq> y"
          show "x = Min (X - {y})"
          proof (cases "y \<in> X")
            case True
            then show ?thesis using local.Min.remove local.finite_code local.min_def x_eq x_neq by presburger
          next
            case False
            then show ?thesis by (simp add: x_eq)
          qed
        qed
        show "x = Min (insert x (insert x' X) - {x'})" using Min_subI[where ?X1="insert x (insert x' X)" and ?x1=x and ?y1=x'] 1 Min 2 .
      qed
      have 4: "insert x (insert x' X) - {x'} = insert x X" using less_all nmem by fastforce
      show "x = Min (insert x X)" using 3 unfolding 4 .
    qed
    show ?case
    using step proof (subst insert_commute; rule meta_mp[where P="True"])
      show "finite (insert x X)" using finite' by blast
    next
      show "P (insert x X)"
      using step' proof (rule meta_mp; simp)
      next
        show "x = Min (insert x X)" using x_eq .
      next
        show "x \<notin> X" using nmem by blast
      qed
    next
      show "x' \<notin> insert x X" using nmem less_all by fastforce
    next
      show "x \<in> insert x X" by simp
    next
      show "x = Min (insert x X)" using x_eq .
    next
      fix x''
      assume "x'' \<in> insert x X"
      thus "less_coin x'' x'" by (metis Min Min_le finite' finite_insert insert_iff less_all less_le nmem)
    next
      show True by simp
    qed
  qed
qed


lemma val_normalize: "val (normalize v) = v"
unfolding normalize_def proof (simp add: val_sum val_replicate_mset)
  show "(\<Sum>x\<in>UNIV. (case next_coin x of None \<Rightarrow> v div val_unit x | Some c' \<Rightarrow> v mod val_unit c' div val_unit x) * val_unit x) = v"
  unfolding next_coin_def
  using finite proof (induct arbitrary: v rule: finite_induct1_max[where ?x=coin1])
    show "finite (UNIV::'a set)" using finite .
  next
    show "coin1 \<in> UNIV" by simp
  next
    show "coin1 = Min UNIV" using Min_UNIV by force
  next
    fix v
    have 1: "next_coin_on {coin1} coin1 = None" using next_coin_on_eq_None by fastforce
    show "(\<Sum>x\<in>{coin1}. (case next_coin_on {coin1} x of None \<Rightarrow> v div val_unit x | Some c' \<Rightarrow> v mod val_unit c' div val_unit x) * val_unit x) = v"
      by (simp add: 1)
  next
    fix X x' v
    assume "\<And>v. (\<And>x :: 'a set. finite x) \<Longrightarrow> (\<Sum>x\<in>X. (case next_coin_on X x of None \<Rightarrow> v div val_unit x | Some c' \<Rightarrow> v mod val_unit c' div val_unit x) * val_unit x) = v"
    hence step: "\<And>v. (\<Sum>x\<in>X. (case next_coin_on X x of None \<Rightarrow> v div val_unit x | Some c' \<Rightarrow> v mod val_unit c' div val_unit x) * val_unit x) = v"
    proof
      fix v and x :: "'a set"
      show "finite x" using finite .
    next
      fix v :: val
      show "v = v" by (rule refl)
    qed
    assume nmem: "x' \<notin> X"
      and mem: "coin1 \<in> X"
      and coin1_eq: "coin1 = Min X"
      and upper_bound: "\<And>x''. x'' \<in> X \<Longrightarrow> less_coin x'' x'"
    have 1: "finite (insert x' X)" using finite .
    have "x' = Max (insert x' X)" using upper_bound by (simp add: local.Max_insert2 local.dual_order.order_iff_strict)
    hence 2: "next_coin_on (insert x' X) x' = None" using next_coin_on_eq_None by force
    show "(\<Sum>x\<in>insert x' X. (case next_coin_on (insert x' X) x of None \<Rightarrow> v div val_unit x | Some c' \<Rightarrow> v mod val_unit c' div val_unit x) * val_unit x) = v"
    using finite[where ?A=X] nmem proof (simp add: 2)
      obtain y where y_eq: "y = Max X" and "y \<in> X" using mem by (metis empty_iff local.Max_in local.finite)
      have "\<And>z. z \<noteq> y \<Longrightarrow> next_coin_on (insert x' X) z = next_coin_on X z" 
      show "v div val_unit x' * val_unit x' +
      (\<Sum>x\<in>X. (case next_coin_on (insert x' X) x of None \<Rightarrow> v div val_unit x | Some c' \<Rightarrow> v mod val_unit c' div val_unit x) * val_unit x) = v"
    oops

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