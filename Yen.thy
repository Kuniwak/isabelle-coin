theory Yen imports CoinClass begin



datatype Yen = One | Five | Ten | Fifty | Hundred | FiveHundreds

fun Yen_unit :: "Yen \<Rightarrow> val"
  where "Yen_unit One = 1"
      | "Yen_unit Five = 5"
      | "Yen_unit Ten = 10"
      | "Yen_unit Fifty = 50"
      | "Yen_unit Hundred = 100"
      | "Yen_unit FiveHundreds = 500"

fun Yen_next :: "Yen \<Rightarrow> Yen option"
  where "Yen_next One = Some Five"
      | "Yen_next Five = Some Ten"
      | "Yen_next Ten = Some Fifty"
      | "Yen_next Fifty = Some Hundred"
      | "Yen_next Hundred = Some FiveHundreds"
      | "Yen_next FiveHundreds = None"

theorem Yen_UNIV_eq: "UNIV = {One, Five, Ten, Fifty, Hundred, FiveHundreds}"
proof (rule equalityI; rule subsetI)
  fix x :: Yen
  show "x \<in> {One, Five, Ten, Fifty, Hundred, FiveHundreds}" by (rule Yen.exhaust[where ?y=x]; simp)
next
  fix x :: Yen
  show "x \<in> UNIV" by simp
qed

interpretation Yen: coin Yen_unit One Yen_next
proof
  show "finite (UNIV::Yen set)"
  unfolding Yen_UNIV_eq by simp
next
  show "Yen_unit One = 1" by simp
next
  show "inj Yen_unit"
  unfolding inj_def proof auto
    fix x y :: Yen
    assume "Yen_unit x = Yen_unit y"
    thus "x = y" proof (cases x)
      assume "Yen_unit x = Yen_unit y" "x = One"
      thus "x = y" by (cases y; simp)
    next
      assume "Yen_unit x = Yen_unit y" "x = Five"
      thus "x = y" by (cases y; simp)
    next
      assume "Yen_unit x = Yen_unit y" "x = Ten"
      thus "x = y" by (cases y; simp)
    next
      assume "Yen_unit x = Yen_unit y" "x = Fifty"
      thus "x = y" by (cases y; simp)
    next
      assume "Yen_unit x = Yen_unit y" "x = Hundred"
      thus "x = y" by (cases y; simp)
    next
      assume "Yen_unit x = Yen_unit y" "x = FiveHundreds"
      thus "x = y" by (cases y; simp)
    qed
  qed
next
  fix v
  assume "v \<in> range Yen_unit"
  thus "0 < v" unfolding Yen_UNIV_eq by fastforce
next
  fix v1 v2
  assume "v1 \<in> range Yen_unit" "v2 \<in> range Yen_unit" "v1 < v2"
  thus "v1 dvd v2" unfolding Yen_UNIV_eq by fastforce
next
  fix c1 c2
  assume 1: "Yen_next c1 = Some c2"
  thus "Yen_unit c1 < Yen_unit c2 \<and> (\<nexists>c3. Yen_unit c3 < Yen_unit c2 \<and> Yen_unit c1 < Yen_unit c3)" 
  proof (rule_tac Yen.exhaust[where ?y=c1]; auto)
    fix c3
    assume "Yen_unit c3 < 5" "Suc 0 < Yen_unit c3"
    thus False by (rule_tac Yen.exhaust[where ?y=c3]; simp)
  next
    fix c3
    assume "Yen_unit c3 < 10" "5 < Yen_unit c3"
    thus False by (rule_tac Yen.exhaust[where ?y=c3]; simp)
  next
    fix c3
    assume "Yen_unit c3 < 50" "10 < Yen_unit c3"
    thus False by (rule_tac Yen.exhaust[where ?y=c3]; simp)
  next
    fix c3
    assume "Yen_unit c3 < 100" "50 < Yen_unit c3"
    thus False by (rule_tac Yen.exhaust[where ?y=c3]; simp)
  next
    fix c3
    assume "Yen_unit c3 < 500" "100 < Yen_unit c3"
    thus False by (rule_tac Yen.exhaust[where ?y=c3]; simp)
  qed
next
  fix c1 c2
  assume "Yen_next c1 = None"
  thus "Yen_unit c2 \<le> Yen_unit c1" by (rule_tac Yen.exhaust[where ?y=c1]; simp; rule_tac Yen.exhaust[where ?y=c2]; simp)
qed

lemma max_FiveHundreds: "Yen.max c FiveHundreds = FiveHundreds"
  by (rule Yen.exhaust[where ?y=c]; simp add: Yen.max_def Yen.less_eq_coin_def)

theorem "Yen.Min UNIV = One"
  by (rule Yen.Min_UNIV)

theorem "Yen.Max UNIV = FiveHundreds"
proof -
  have "Yen.Max UNIV = Yen.Max {One, Five, Ten, Fifty, Hundred, FiveHundreds}" unfolding Yen_UNIV_eq by (rule refl)
  also have "... = Yen.max One (Yen.Max {Five, Ten, Fifty, Hundred, FiveHundreds})" by simp
  also have "... = Yen.max One (Yen.max Five (Yen.Max {Ten, Fifty, Hundred, FiveHundreds}))" by simp
  also have "... = Yen.max One (Yen.max Five (Yen.max Ten (Yen.Max {Fifty, Hundred, FiveHundreds})))" by simp
  also have "... = Yen.max One (Yen.max Five (Yen.max Ten (Yen.max Fifty (Yen.Max {Hundred, FiveHundreds}))))" by simp
  also have "... = Yen.max One (Yen.max Five (Yen.max Ten (Yen.max Fifty (Yen.max Hundred FiveHundreds))))" by simp
  also have "... = FiveHundreds" by (simp add: max_FiveHundreds)
  ultimately show "Yen.Max UNIV = ..." by simp
qed


end