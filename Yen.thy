theory Yen imports CoinClass begin



datatype Yen = One | Five | Ten | Fifty | Hundred | FiveHundreds

fun Yen_unit :: "Yen \<Rightarrow> val" where
  "Yen_unit One = 1" |
  "Yen_unit Five = 5" |
  "Yen_unit Ten = 10" |
  "Yen_unit Fifty = 50" |
  "Yen_unit Hundred = 100" |
  "Yen_unit FiveHundreds = 500"

theorem Yen_UNIV_eq: "UNIV = {One, Five, Ten, Fifty, Hundred, FiveHundreds}"
proof (rule equalityI; rule subsetI)
  fix x :: Yen
  show "x \<in> {One, Five, Ten, Fifty, Hundred, FiveHundreds}" by (rule Yen.exhaust[where ?y=x]; simp)
next
  fix x :: Yen
  show "x \<in> UNIV" by simp
qed

definition less_eq_Yen :: "Yen \<Rightarrow> Yen \<Rightarrow> bool"
  where "less_eq_Yen y1 y2 \<equiv> Yen_unit y1 \<le> Yen_unit y2"

definition less_Yen :: "Yen \<Rightarrow> Yen \<Rightarrow> bool"
  where "less_Yen y1 y2 \<equiv> Yen_unit y1 < Yen_unit y2"

interpretation Yen: coin_linorder Yen_unit One less_eq_Yen less_Yen
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
  fix x y
  show "less_eq_Yen x y = (Yen_unit x \<le> Yen_unit y)" unfolding less_eq_Yen_def by simp
next
  fix x y
  show "less_Yen x y = (Yen_unit x < Yen_unit y)" unfolding less_Yen_def by simp
qed
end