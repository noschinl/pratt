theory Lehmer
imports
  Main
  "~~/src/HOL/Number_Theory/Number_Theory"
begin

(* XXX: Add to Isabelle *)

text {* Proofs of Lehmer's theorem and the extended Lehmer's theorem *}

(* XXX add to Isabelle! *)
lemma prime_phi:
  assumes  "2 \<le> p" "phi p = (nat p) - 1" shows "prime p"
proof -
  have "{x. 0 < x \<and> x < p \<and> coprime x p} = {1..p - 1}"
    using assms unfolding phi_def by (intro card_seteq) fastforce+
  then have cop: "\<And>x. x \<in> {1..p - 1} \<Longrightarrow> coprime x p" by blast

  { fix x assume *: "1 < x" "x < p" and "x dvd p"
    from * have "coprime x p" by (auto intro: cop)
    with `x dvd p` `1 < x` have "False" by auto }
  then show ?thesis unfolding prime_int_code
    using `2 \<le> p` by fastforce
qed

lemma coprime_power_nat:
  fixes a b :: nat assumes "0 < n" shows "coprime a (b ^ n) \<longleftrightarrow> coprime a b"
  using assms
proof (induct n)
  case (plus1 n) then show ?case
    by (cases n) (simp_all add: coprime_mul_eq_nat del: One_nat_def)
qed simp

lemma mod_1_coprime_nat:
  fixes a b :: nat assumes "0 < n" "[a ^ n = 1] (mod b)" shows "coprime a b"
proof -
  from assms have "coprime (a ^ n) b" by (simp cong: cong_gcd_eq_nat)
  with `0 < n` show ?thesis
    by (simp add: coprime_power_nat gcd_commute_nat del: One_nat_def)
qed

lemma phi_leq: "phi x \<le> nat x - 1"
proof -
  have "phi x \<le> card {1..x - 1}"
    unfolding phi_def by (rule card_mono) auto
  then show ?thesis by simp
qed

lemma phi_nonzero:
  assumes "2 \<le> x" shows "phi x \<noteq> 0"
proof -
  have "coprime ((x - 1) + 1) (x - 1)"
    by (simp only: coprime_plus_one_int)
  with assms have "card {x - 1} \<le> phi x"
    unfolding phi_def by (intro card_mono bounded_set1_int) (simp add: gcd_commute_int)
    (* XXX: We need bounded_set1_int here because of the finite_Collect simproc) *)
  then show ?thesis by auto
qed

lemma lehmers_theorem:
  assumes "2 \<le> p"
  assumes min_cong1: "\<And>x. 0 < x \<Longrightarrow> x < p - 1 \<Longrightarrow> [a ^ x \<noteq> 1] (mod p)"
  assumes cong1: "[a ^ (p - 1) = 1] (mod p)"
  shows "prime p"
proof -
  from `2 \<le> p` cong1 have "coprime a p"
    by (intro mod_1_coprime_nat[of "p - 1"]) auto
  then have "[a ^ phi (int p) = 1] (mod p)"
    by (intro euler_theorem[transferred]) auto
  then have "phi (int p) \<ge> p - 1 \<or> phi (int p) = 0"
    using min_cong1[of "phi (int p)"] by fastforce
  then have "prime (int p)" using phi_leq[transferred, of p] phi_nonzero `2 \<le> p`
    by (auto intro: prime_phi)
  then show ?thesis by (simp add: prime_int_def)
qed

lemma prime_factors_elem:
  fixes n :: nat assumes "1 < n" shows "\<exists>p. p \<in> prime_factors n"
  using assms by (cases "prime n") (auto simp: prime_factors_altdef2_nat prime_factor_nat)

lemma prime_factors_dvd_nat:
  fixes p :: nat assumes "x \<in> prime_factors p" shows "x dvd p"
  using assms by (cases "0 < p") (auto simp: prime_factors_altdef2_nat)

lemma cong_pow_1_nat:
  fixes a b :: nat assumes "[a = 1] (mod b)" shows "[a ^ x = 1] (mod b)"
by (metis assms cong_exp_nat power_one)

lemma cong_gcd_eq_1_nat:
  fixes a b :: nat
  assumes "0 < m" and cong_props: "[a ^ m = 1] (mod b)" "[a ^ n = 1] (mod b)"
  shows "[a ^ gcd m n = 1] (mod b)"
proof -
  obtain c d where gcd: "m * c = n * d + gcd m n" using bezout_nat[of m n] `0 < m`
    by auto
  have cong_m: "[a ^ (m * c) = 1] (mod b)" and cong_n: "[a ^ (n * d) = 1] (mod b)"
    using cong_props by (simp_all only: cong_pow_1_nat power_mult)
  have "[1 * a ^ gcd m n = a ^ (n * d) * a ^ gcd m n] (mod b)" 
    using cong_n[simplified cong_sym_eq_nat] by (simp only: power_one cong_scalar_nat)
  also have "[a ^ (n * d) * a ^ gcd m n = a ^ (m * c)] (mod b)"
    using gcd by (simp add: power_add)
  also have "[a ^ (m * c) = 1] (mod b)" using cong_m by simp
  finally show "[a ^ gcd m n = 1] (mod b)" by simp
qed

lemma One_leq_div:
  fixes a b :: nat assumes "a dvd b" "a < b" shows "1 < b div a"
by (metis assms dvd_mult_div_cancel gr_implies_not0 less_Suc0 linorder_not_le mult_1_right
  mult_zero_right nat_1 order_le_neq_trans order_refl transfer_nat_int_numerals(2))

lemma lehmer_extended:
  assumes "2 \<le> p"
  assumes pf_notcong1: "\<And>x. x \<in> prime_factors (p - 1) \<Longrightarrow> [a ^ ((p - 1) div x) \<noteq> 1] (mod p)"
  assumes cong1: "[a ^ (p - 1) = 1] (mod p)"
  shows "prime p"
proof cases
  assume "[a = 1] (mod p)" with `2 \<le>p` pf_notcong1 show ?thesis
    by (metis cong_pow_1_nat less_diff_conv linorder_neqE_nat linorder_not_less
      one_add_one prime_factors_elem two_is_prime_nat)
next
  assume A_notcong_1: "[a \<noteq> 1] (mod p)"
  { fix x assume "0 < x" "x < p - 1"
    have "[a ^ x \<noteq> 1] (mod p)"
    proof
      assume "[a ^ x = 1] (mod p)"
      then have gcd_cong_1: "[a ^ gcd x (p - 1) = 1] (mod p)"
        by (rule cong_gcd_eq_1_nat[OF `0 < x` _ cong1])

      have "gcd x (p - 1) = p - 1"
      proof (rule ccontr)
        assume "\<not>?thesis"
        then have gcd_p1: "gcd x (p - 1) dvd (p - 1)" "gcd x (p - 1) < p - 1"
          using gcd_le2_nat[of "p - 1" x] `2 \<le> p` by (simp, linarith)

        def c \<equiv> "(p - 1) div (gcd x (p - 1))"
        then have p_1_eq: "p - 1 = gcd x (p - 1) * c" unfolding c_def using gcd_p1
          by (metis dvd_mult_div_cancel)

        from gcd_p1 have "1 < c" unfolding c_def by (rule One_leq_div)
        then obtain q where q_pf: "q \<in> prime_factors c"
          using prime_factors_elem by auto
        then have "q dvd c" by (auto simp: prime_factors_dvd_nat)

        have "q \<in> prime_factors (p - 1)" using q_pf `1 < c` `2 \<le> p`
          by (subst p_1_eq) (simp add: prime_factors_product_nat)
        moreover
        have "[a ^ ((p - 1) div q) = 1] (mod p)"
          by (subst p_1_eq,subst dvd_div_mult_self[OF `q dvd c`,symmetric])
             (simp del: One_nat_def add: power_mult gcd_cong_1 cong_pow_1_nat)
        ultimately
        show False using pf_notcong1 by metis
      qed
      then show False using `x < p - 1`
        by (metis `0 < x` gcd_le1_nat gr_implies_not0 linorder_not_less)
    qed
  }
  with lehmers_theorem[OF `2 \<le> p` _ cong1] show ?thesis by metis
qed



section {* Unused *}

lemma cong_pow_1_int:
  fixes a b :: int assumes "[a ^ x = 1] (mod b)" shows "[a ^ (x * y) = 1] (mod b)"
by (metis assms cong_exp_int power_mult power_one)

lemma cong_pow_comb_int:
  fixes a b :: int
  assumes "[a ^ m = 1] (mod b)" "[a ^ n = 1] (mod b)"
  shows "[a ^ (m * c - n * d) = 1] (mod b)"
proof -
  from assms have cong_m: "[a ^ (m * c) = 1] (mod b)" and cong_n: "[a ^ (n * d) = 1] (mod b)"
    by (simp_all add: cong_pow_1_int del: One_nat_def)
  show ?thesis
  proof (cases "m * c > n * d")
    case True
    have "[1 * a ^ (m * c - n * d) = a ^ (n * d) * a ^ (m * c - n * d)] (mod b)" using cong_n
      by (intro cong_scalar_int) (simp add: cong_sym_eq_int)
    also have "[a ^ (n * d) * a ^ (m * c - n * d) = 1] (mod b)"
      using True cong_m by (simp add: power_add[symmetric])
    finally show "[a ^ (m * c - n * d) = 1] (mod b)" by simp
  qed simp
qed

lemma coprime_power_int:
  fixes a b :: int assumes "0 < n" shows "coprime a (b ^ n) \<longleftrightarrow> coprime a b"
  using assms
proof (induct n)
  case (plus1 n) then show ?case
    by (cases n) (simp_all add: coprime_mul_eq_int del: One_nat_def)
qed simp

lemma mod_1_coprime_int:
  fixes a b :: int assumes "0 < n" "[a ^ n = 1] (mod b)" shows "coprime a b"
proof -
  from assms have "coprime (a ^ n) b" by (simp cong: cong_gcd_eq_int)
  with `0 < n` show ?thesis
    by (simp add: coprime_power_int gcd_commute_int)
qed




end
