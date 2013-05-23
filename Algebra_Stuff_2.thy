theory Algebra_Stuff_2 imports
  Algebra_Stuff
  "~~/src/HOL/Number_Theory/Number_Theory"
begin

lemma mod_nat_int_pow_eq:
  fixes n :: nat and p a :: int
  assumes "a \<ge> 0" "p \<ge> 0"
  shows "(nat a ^ n) mod (nat p) = nat ((a ^ n) mod p)"
  using assms 
  by (simp add: int_one_le_iff_zero_less nat_mod_distrib order_less_imp_le nat_power_eq[symmetric])

theorem residue_prime_mult_group_has_gen :
 fixes p :: nat
 assumes prime_p : "prime p"
 shows "\<exists> a \<in> {1 .. p - 1} . {1 .. p - 1} = {a^i mod p|i . i \<in> UNIV}"
proof -
  have "p\<ge>2" using prime_gt_1_nat[OF prime_p] by simp
  interpret R:residues_prime "int p" "residue_ring (int p)" unfolding residues_prime_def
    by (simp add: transfer_int_nat_prime prime_p)
  have car: "carrier (residue_ring (int p)) - {\<zero>\<^bsub>residue_ring (int p)\<^esub>} =  {1 .. int p - 1}"
    by (auto simp add: R.zero_cong R.res_carrier_eq)
  obtain a where a:"a \<in> {1 .. int p - 1}"
         and a_gen:"{1 .. int p - 1} = {a(^)\<^bsub>residue_ring (int p)\<^esub>i|i::nat . i \<in> UNIV}"
    apply atomize_elim using field.finite_field_mult_group_has_gen[OF R.is_field]
    by (auto simp add: car[symmetric] carrier_mult_of)
  { fix x fix i :: nat assume x: "x \<in> {1 .. int p - 1}"
    hence "x (^)\<^bsub>residue_ring (int p)\<^esub> i = x ^ i mod (int p)" using R.pow_cong[of x i] by auto}
  note * = this
  have **:"nat ` {1 .. int p - 1} = {1 .. p - 1}" (is "?L = ?R")
  proof
    { fix n assume n: "n \<in> ?L"
      then have "n \<in> ?R" using `p\<ge>2` by force
    } thus "?L \<subseteq> ?R" by blast
    { fix n assume n: "n \<in> ?R"
      then have "n \<in> ?L" using `p\<ge>2` Set_Interval.transfer_nat_int_set_functions(2) by fastforce
    } thus "?R \<subseteq> ?L" by blast
  qed
  have "nat ` {a^i mod (int p)|i::nat . i \<in> UNIV} = {nat a^i mod p|i . i \<in> UNIV}" (is "?L = ?R")
  proof
    { fix x assume x: "x \<in> ?L"
      then obtain i where i:"x = nat (a^i mod (int p))" by blast
      hence "x = nat a ^ i mod p" using mod_nat_int_pow_eq[of a "int p" i] a `p\<ge>2` by auto
      hence "x \<in> ?R" using i by blast 
    } thus "?L \<subseteq> ?R" by blast
    { fix x assume x: "x \<in> ?R"
      then obtain i where i:"x = nat a^i mod p" by blast
      hence "x \<in> ?L" using mod_nat_int_pow_eq[of a "int p" i] a `p\<ge>2` by auto
    } thus "?R \<subseteq> ?L" by blast
  qed
  hence ***:"{1 .. p - 1} = {nat a^i mod p|i . i \<in> UNIV}" using * a a_gen ** by presburger
  have "nat a \<in> {1 .. p - 1}" using a by force
  thus ?thesis using *** by blast
qed


end
