theory pratt
imports Main "~~/src/HOL/Number_Theory/Number_Theory" "Lehmer" "~~/src/HOL/Algebra/Coset" "~~/src/HOL/Library/Multiset"  "~~/src/HOL/Algebra/Group"
begin

datatype pratt =
 Prime nat
 |Triple nat nat nat

find_theorems "field"

type_synonym cert = "pratt list"

lemma dvd_prime_eq_prime :
 fixes p::nat
 assumes "prime p"
 assumes "q \<noteq> 1"
 assumes "q dvd p"
 shows "q = p"
 using assms by (metis prime_nat_def)

theorem lagrange_ex :
 assumes "group G"
 assumes "finite(carrier G)" 
 assumes "subgroup H G"
 shows "(card H) dvd (order G)"
 using assms by (metis dvd.eq_iff dvd_mult_left group.lagrange nat_mult_commute)

lemma (in group) nat_inv_pow_mult :
 fixes m :: nat
 fixes n :: nat
 assumes "x \<in> carrier G"
 shows "inv (x (^) m)  \<otimes> inv (x (^) n) = inv (x (^) (m + n))"
 by (metis assms inv_mult_group nat_add_commute nat_pow_closed nat_pow_mult)

lemma (in group) int_pow_mult :
 fixes m :: int
 fixes n :: int
 assumes "x \<in> carrier G"
 shows "x (^) m  \<otimes> x (^) n = x (^) (m + n)"
 proof -
  {
   assume 1:"m\<ge>0 \<and> n \<ge> 0"
   hence "nat m + nat n = nat (m+n)" by auto
   hence ?thesis using int_pow_def2 nat_pow_mult[of x "nat m" "nat n"] assms 1 by auto
  }
  moreover
  {
   assume 1:"m < 0 \<and> n < 0"
   hence "nat (-m) + nat (-n) = nat (-m -n)" by auto
   hence ?thesis using int_pow_def2 assms 1 nat_inv_pow_mult[of x "nat (- m)" "nat (- n)"]  by auto
  }
  moreover
  {
   assume 1:"m < 0 \<and> n \<ge> 0"
   hence 3:"x (^) m  \<otimes> x (^) n = inv (x (^) nat (- m)) \<otimes> x (^) nat n" using int_pow_def2 by auto
   {
    assume 2:"-m < n"
    hence "nat n = nat (-m) + nat (m + n)" using 1 by auto
    hence "x (^) m  \<otimes> x (^) n = inv (x (^) nat (- m)) \<otimes> x (^) nat (-m) \<otimes> x (^) nat (m + n)" using 1 nat_pow_mult[of x "nat (-m)" "nat (m+n)"]  m_assoc assms inv_closed nat_pow_closed 3 by presburger
    hence ?thesis using 1 2 int_pow_def2  assms l_inv nat_pow_closed one_closed r_cancel_one by auto
   }
   moreover
   {
    assume 2:"-m \<ge> n"
    hence "nat (-m) = nat (-(m + n)) + nat (n)" using 1 by auto
    hence "x (^) m  \<otimes> x (^) n = inv (x (^) nat (-(m+n))) \<otimes> (inv (x (^) nat (n)) \<otimes> x (^) nat n)" using 1 nat_inv_pow_mult[of x "nat (-(m+n))" "nat n"]  m_assoc assms inv_closed nat_pow_closed 3 by metis
    hence ?thesis using 1 2 int_pow_def2  assms l_inv nat_pow_closed one_closed r_cancel_one by auto
   }
   ultimately have ?thesis by linarith
  }
  moreover
  {
   assume 1:"n < 0 \<and> m \<ge> 0"
   hence 3:"x (^) m  \<otimes> x (^) n = x (^) nat m \<otimes> inv (x (^) nat (-n))" using int_pow_def2 by auto
   {
    assume 2:"-n < m"
    hence "nat m = nat (m + n) + nat (-n)" using 1 by auto
    hence "x (^) m  \<otimes> x (^) n = x (^) nat (m+n) \<otimes> (x (^) nat (-n)  \<otimes> inv (x (^) nat (- n)))" using 1 nat_pow_mult[of x "nat (m+n)" "nat (-n)"]  m_assoc assms inv_closed nat_pow_closed 3 by metis
    hence ?thesis using 1 2 int_pow_def2  assms l_inv nat_pow_closed one_closed r_cancel_one by auto
   }
   moreover
   {
    assume 2:"-n \<ge> m"
    hence "nat (-n) =  nat (m) + nat (-(m + n))" using 1 by auto
    hence "x (^) m  \<otimes> x (^) n =  x (^) nat m \<otimes> inv (x (^) nat (m)) \<otimes> inv (x (^) nat (-(m+n)))" using 1 nat_inv_pow_mult[of x "nat m" "nat (-(m+n))"]  m_assoc assms inv_closed nat_pow_closed 3 by metis
    hence ?thesis using 1 2 int_pow_def2  assms l_inv nat_pow_closed one_closed r_cancel_one by auto
   }
   ultimately have ?thesis by linarith
  }
  ultimately show ?thesis by linarith
 qed

(*
lemma (in group) int_pow_pow :
 fixes m :: int
 fixes n :: int
 shows "(x (^) m) (^) n = x (^) (m * n) " sorry
*)

lemma (in group) pow_eq_div2 :
 fixes m :: int 
 fixes n :: int
 assumes "x \<in> carrier G"
 assumes "x (^) m = x (^) n"
 shows "x (^) (m - n) = \<one>"
 proof -
  have 1:"x (^) (m - n) = x (^) m \<otimes> x (^) (- n)" using int_pow_mult[of x m "-n"] assms by auto
  {
   assume "n > 0"
   hence "- n < 0" by auto
   hence 2:"x (^) (m - n) = x (^) m \<otimes> inv (x (^) m)" using 1 int_pow_def2 assms by auto
   have "(x (^) m) \<in> carrier G"
    proof cases
     assume "m \<ge> 0"
     thus ?thesis using int_pow_def2 nat_pow_closed assms by auto
     next
     assume "\<not> m \<ge> 0"
     hence "m < 0" by auto
     thus ?thesis using int_pow_def2 nat_pow_closed assms by (metis inv_closed)
    qed
   hence ?thesis using r_inv[of "x (^) m"] 2 by auto
  }
  moreover
  {
   assume "n \<le> 0"
   hence "-n \<ge> 0" by auto
   hence 2:"x (^) (m - n) = inv (x (^) (nat (-n))) \<otimes> x (^) (nat (-n))" using int_pow_def2 1 assms  by auto
   have "x (^) (nat (-n)) \<in> carrier G"
    proof cases
     assume "m \<ge> 0"
     thus ?thesis using int_pow_def2 nat_pow_closed assms by auto
     next
     assume "\<not> m \<ge> 0"
     hence "m < 0" by auto
     thus ?thesis using int_pow_def2 nat_pow_closed assms by (metis inv_closed)
    qed
   hence ?thesis using r_inv[of "x (^) (nat (-n))"] 2 by auto
  }
  ultimately show ?thesis by linarith
  (* thus "x (^) (m - n) = \<one>" by (metis assms int_pow_0 int_pow_mult right_minus)  *)
 qed

(*
lemma (in group) pow_eq_div :
 fixes m :: nat
 fixes n :: nat
 assumes "x \<in> carrier G"
 assumes "x (^) m = x (^) n"
 assumes "m \<ge> n"
 shows "x (^) (m - n) = \<one>"
 sorry
*)

lemma (in group) finite_group_elem_finite_ord :
 assumes finite_G:"finite (carrier G)"
 assumes x:"x \<in> carrier G"
 shows "\<exists> d::nat . d \<ge> 1 \<and> x (^) d = \<one>"
 proof -
  let ?H = "{x (^) i |i. i \<in> (UNIV :: nat set)}"
  obtain f::"nat \<Rightarrow> 'a"  where f:"f = (\<lambda> i . x (^) i)" by auto
  hence f_pic:"?H = f ` (UNIV :: nat set)" by auto
 have subset:"?H \<subseteq> carrier G" using x nat_pow_closed by auto
 have "finite ?H" using subset finite_subset finite_G by blast
 hence "finite (f ` (UNIV :: nat set))" using f_pic by metis then obtain n1::nat where "\<not> finite {a \<in> (UNIV :: nat set). f a = f n1}" using Finite_Set.pigeonhole_infinite[of "(UNIV :: nat set)" f] by auto
 then obtain n2 where n1n2_neq:"n2 \<noteq> n1" and n1n2:"f n1 = f n2" by (metis (lifting, full_types) CollectD finite_nat_set_iff_bounded_le linorder_linear)
 then obtain d::nat where d:"d = nat (abs (int n1 - int n2))" by auto
 hence x_d:"x (^) d = \<one>"
 proof cases
   assume "n1 < n2"
   hence "d = nat (int n2 - int n1)" using d  by auto
   hence "x (^) nat (int n2 - int n1) = \<one>"  using int_pow_def2 n1n2 pow_eq_div2[of x "int n2" "int n1"] f `n1 < n2` x by auto
   thus ?thesis using `d = nat (int n2 - int n1)` by auto
  next
   assume "\<not> n1 < n2"
   hence "n2 \<le> n1" by auto
   hence "d = nat (int n1 - int n2)" using d  by auto
   hence "x (^) nat (int n1 - int n2) = \<one>"  using n1n2 pow_eq_div2[of x "int n1" "int n2"] f int_pow_def2 `n2 \<le> n1` x by auto
   thus ?thesis using `d = nat (int n1 - int n2)` by auto
  qed
  have "d \<ge> 1" using n1n2_neq d by auto
  thus ?thesis using x_d by auto
 qed

(*
theorem residue_prime_has_gen:
 assumes p:"residues p"
 assumes prime_p: "prime p"
 shows "carrier (residue_ring p) = {2^i mod p|i . i \<in> (UNIV :: nat set)}"
 proof -
  {
  fix i::nat
  have "2^i mod p \<in> carrier (residue_ring p)" using Residues.residues.mod_in_carrier[of p "2^i"] p by auto
 }
 hence subs:"{2 ^ i mod p |i. i \<in> (UNIV :: nat set)} \<subseteq> carrier (residue_ring p)" by auto
 find_theorems "residues_prime"
 (*
 have "ring (residue_ring p)" find_theorems intro  using  p by auto
 have "abelian_group (residue_ring p)" using Residues.residues.abelian_group p by auto
 *) 
 hence group_p:"group (residue_ring p)" sorry
 have sub_p:"subgroup {2^i mod p|i . i \<in> (UNIV :: nat set)} (residue_ring p)" find_theorems intro
  proof
    show "{2 ^ i mod p |i. i \<in> (UNIV :: nat set)} \<subseteq> carrier (residue_ring p)" using subs by auto
   next
    fix x
    fix y
    assume x:"x \<in> {2 ^ i mod p |i. i \<in> (UNIV :: nat set)}"
    assume y:"y \<in> {2 ^ i mod p |i. i \<in> (UNIV :: nat set)}"
    obtain i::nat where i:"x = 2 ^ i mod p" and i2:"i \<in> (UNIV :: nat set)"using x by auto
    obtain j::nat where j:"y = 2 ^ j mod p" and j2:"j\<in>(UNIV :: nat set)"using y by auto
    hence "x \<otimes>\<^bsub>residue_ring p\<^esub> y = (2^i mod p) \<otimes>\<^bsub>residue_ring p\<^esub> (2 ^ j mod p)" using i by auto
    hence "x \<otimes>\<^bsub>residue_ring p\<^esub> y = (2^i  * 2^j) mod p" using Residues.residues.mult_cong p by auto
    hence xy:"x \<otimes>\<^bsub>residue_ring p\<^esub> y = (2^(i+j)) mod p" by (metis power_add)
    have "i+j \<in> (UNIV :: nat set)" using i2 j2 by auto
    hence "(2^(i+j)) mod p \<in> {2 ^ i mod p |i. i \<in> (UNIV :: nat set)}" by auto
    thus "x \<otimes>\<^bsub>residue_ring p\<^esub> y \<in> {2 ^ i mod p |i. i \<in> (UNIV :: nat set)}" using xy by auto
  next
    have 1:"\<one>\<^bsub>residue_ring p\<^esub> = 1 mod p" using Residues.residues.one_cong p by auto
    have "1 mod p= 2^0 mod p" by (metis power_0)
    hence "1 mod p \<in> {2 ^ i mod p |i. i \<in> (UNIV :: nat set)}" by fastforce
    thus "\<one>\<^bsub>residue_ring p\<^esub> \<in> {2 ^ i mod p |i. i \<in> (UNIV :: nat set)}" using 1 by auto
  next
     fix x
     assume x:"x \<in> {2 ^ i mod p |i. i \<in> (UNIV :: nat set)}"
     hence x_in_carrier:"x \<in> carrier (residue_ring p)" using subs by auto
     have "finite (carrier (residue_ring p))" by (metis p residues.finite)
     then obtain d::nat where "x (^)\<^bsub>residue_ring p\<^esub> d = \<one>\<^bsub>residue_ring p\<^esub>" and "d\<ge>1"  using group.finite_group_elem_finite_ord[of "residue_ring p" x] x_in_carrier group_p by auto
     hence x_d:"x ^ d mod p = 1" using p Residues.residues.one_cong Residues.residues.pow_cong by (metis (hide_lams, no_types) group.finite_group_elem_finite_ord group_p mod_0 not_one_le_zero power_eq_0_iff residues.finite residues.mod_in_carrier residues.res_one_eq zero_le_one)
     hence inv_1:"x^d mod p = (x^(d - 1) * x) mod p" using `d\<ge>1` by (metis comm_semiring_1_class.normalizing_semiring_rules(7) le_0_eq power_eq_0_iff power_eq_if)
     hence inv_2:"x^d mod p = (x * x^(d - 1)) mod p" by (metis comm_semiring_1_class.normalizing_semiring_rules(7))  
     have inv_11:"1=(x^(d - 1) * x) mod p" using x_d using inv_1 by auto
     hence inv_111:"\<one>\<^bsub>residue_ring p\<^esub>=(x^(d - 1) mod p) \<otimes>\<^bsub>residue_ring p\<^esub> (x mod p)" using Residues.residues.mult_cong[of p] p Residues.residues.one_cong[of p] by (metis residues.res_one_eq)
     have inv_22:"1=(x * x^(d - 1)) mod p" using x_d using inv_2 by auto
     hence inv_222:"\<one>\<^bsub>residue_ring p\<^esub>=(x mod p) \<otimes>\<^bsub>residue_ring p\<^esub> (x^(d - 1) mod p)" using Residues.residues.mult_cong[of p] p Residues.residues.one_cong[of p] by (metis residues.res_one_eq)
     have elem:"x ^ (d - 1) mod p \<in> {2 ^ i mod p |i. i \<in> (UNIV :: nat set)}"
      proof -
       obtain i::nat where i:"x = 2^i mod p \<and> i \<in> (UNIV :: nat set)" using x by auto
       hence "x ^ (d - 1) mod p = ((2 ^ i) mod p) ^ (d - 1) mod p" by auto
       hence "x ^ (d - 1) mod p = (2 ^ i)  ^ (d - 1) mod p" by (metis power_mod)
       hence 1:"x ^ (d - 1) mod p = 2 ^ (i * (d - 1)) mod p" by (metis power_mult)
       hence "d - 1 \<in> (UNIV :: nat set)" using `d \<ge> 1` by auto
       hence "i * (d - 1) \<in> (UNIV :: nat set)" using i by auto
       thus ?thesis using 1 by auto
      qed
      hence "x ^ (d - 1) mod p \<in> carrier (residue_ring p)" by (metis p residues.mod_in_carrier)
      hence inv:"inv\<^bsub>residue_ring p\<^esub> (x mod p) = x^(d - 1) mod p" using inv_111 inv_222 m_inv_def[of "residue_ring p" "x mod p"] p by (metis comm_monoid.comm_inv_char residues.comm_monoid residues.mod_in_carrier)
      have "x mod p = x"
      proof -
        obtain i where i:"2 ^ i mod p = x" using x by auto
        hence "x mod p = 2 ^ i mod p mod p " by auto
        hence "x mod p = 2 ^ i mod p" using mod_mod_trivial by auto
        thus "x mod p = x" using i by auto
      qed
      thus "inv\<^bsub>residue_ring p\<^esub> x \<in> {2 ^ i mod p |i. i \<in> (UNIV :: nat set)}" using elem inv by auto
   qed
   have "finite (carrier (residue_ring p))" using p by (metis residues.finite)
   hence dvds_p:"card {2 ^ i mod p |i. i \<in> (UNIV :: nat set)} dvd order (residue_ring p)" using lagrange_ex sub_p group_p by auto
   have "p\<ge>2" using prime_p by (metis prime_ge_2_int)
   hence ord_p:"order (residue_ring p) = nat p" using prime_p Residues.residues.res_carrier_eq[of p] p by (metis card_atLeastAtMost_int diff_add_cancel minus_int_code(1) order_def)
   have card_ge_2:"card {2 ^ i mod p |i. i \<in> (UNIV :: nat set)} \<ge> 2" using `p\<ge>2`
     proof -
      have "\<one>\<^bsub>residue_ring p\<^esub> \<in> {2 ^ i mod p |i. i \<in> (UNIV :: nat set)}" using sub_p Group.subgroup.one_closed by auto
      hence 1 : "1 \<in> {2 ^ i mod p | i . i \<in> (UNIV :: nat set)}" using p residues.res_one_eq by auto
      {
        assume "2 = p"
        hence "2 ^ 1 mod p = 0" by auto
        hence "0 \<in> {2 ^ i mod p | i . i \<in> (UNIV :: nat set)}" by (metis (lifting, full_types) UNIV_I mem_Collect_eq)
      }
      moreover
      {
        assume "p>2"
        hence "2 ^ 1 mod p = 2" by auto
        hence "2 \<in> {2 ^ i mod p | i . i \<in> (UNIV :: nat set)}" by (metis (lifting, full_types) UNIV_I mem_Collect_eq)
      }
      ultimately obtain a where a:"a\<in> {2 ^ i mod p |i. i \<in> (UNIV :: nat set)} \<and> (a = 0 | a = 2)" using `p \<ge> 2` by fastforce
      hence "a \<noteq> 1" by auto
      hence subs:"{a,1} \<subseteq> {2 ^ i mod p |i. i \<in> (UNIV :: nat set)}" using a 1 by auto
      have "card {a,1} = 2" using `a \<noteq> 1` by auto
      have "{2 ^ i mod p | i . i \<in> (UNIV :: nat set)} \<subseteq> {0 .. p - 1}" using `p\<ge>2` by auto
      hence "finite {2 ^ i mod p | i . i \<in> (UNIV :: nat set)}" using finite_subset  by auto
      thus ?thesis using subs `card {a,1} = 2` Finite_Set.card_mono[of "{2 ^ i mod p | i . i \<in> (UNIV :: nat set)}" "{a,1}"] by auto
     qed
   have "prime (nat p)" using prime_p by (metis prime_int_def)
   hence "card {2 ^ i mod p |i. i \<in> (UNIV :: nat set)} = nat p" using dvds_p dvd_prime_eq_prime ord_p card_ge_2 by auto
   hence "card {2 ^ i mod p |i. i \<in> (UNIV :: nat set)} \<ge> card (carrier (residue_ring p))" using ord_p order_def[of "residue_ring p"] by auto
   thus ?thesis using  subs card_seteq[of "carrier (residue_ring p)" "{2 ^ i mod p |i. i \<in> (UNIV :: nat set)}"] `finite (carrier (residue_ring p))` by auto
 qed
*)

lemma dvd_nat_bounds :
 fixes n :: nat
 fixes p :: nat
 assumes "p > 0"
 assumes "n dvd p"
 shows "n > 0 \<and> n \<le> p"
 proof
  show "n > 0" using assms by (metis dvd_pos_nat)
  show "n \<le> p" using assms by (metis dvd_imp_le)
 qed

(*
theorem (in field) field_mult_group_has_gen :
 shows "\<exists> a. a \<in> carrier R - {\<zero>} \<and> carrier R - {\<zero>} = {a (^) i | i . i \<in> (UNIV :: nat set)}" sorry
*)

definition ord where "ord a p = Min {d . d\<in> {1 .. p} \<and> (a ^ d) mod p = 1}"

lemma (in monoid) Units_pow_closed :
  fixes d :: nat
  assumes "x \<in> Units G"
  shows "x (^) d \<in> Units G"
  proof (induction d)
  case zero
    thus ?case by auto
  case (plus1 d)
    show ?case by (metis assms group.is_monoid monoid.nat_pow_closed units_group units_of_carrier units_of_pow)
  qed

lemma (in comm_monoid) is_monoid:
  shows "monoid G" by unfold_locales

declare comm_monoid.is_monoid[intro?]

lemma atLeastAtMost_nat:
  fixes m n :: nat
  shows "nat ` {1 .. int n} = {1 .. n}" (is "?L = ?R")
proof
  { fix x :: nat
    assume "x\<in>{1 .. n}"
    hence "int x \<in> {1 .. int n}" by auto
    hence "nat (int x) \<in> nat ` {1 .. int n}" by blast
    hence "x \<in> nat ` {1 .. int n}" by simp
  } thus "?R \<subseteq> ?L" ..
next
  { fix x :: nat
    assume x : "x \<in> nat ` {1 .. int n}"
    hence "x \<in> {1 .. n}" by auto
  } thus "?L \<subseteq> ?R" ..
qed

lemma p_prime_impl_mult_group_closed :
  fixes p :: nat
  fixes a :: nat
  fixes d :: nat
  assumes a:"a \<in> {1 .. p - 1}"
  assumes prime_p:"prime p"
  shows "a^d mod p \<in> {1 .. p - 1}"
  proof -
    have "prime (int p)" using prime_p by (metis transfer_int_nat_prime)
    hence res_p:"residues_prime (int p)" using residues_prime_def by auto
    hence "int a \<in> {1 .. int p - 1}" using a by force
    hence "int a \<in> Units (residue_ring (int p))" using residues_prime.res_prime_units_eq res_p residues.pow_cong by auto
    have "int p \<ge> 2" using `prime (int p)` by (metis prime_ge_2_int)
    hence "residues (int p)" using residues_def by auto
    hence "Group.comm_monoid (residue_ring (int p))" using residues.comm_monoid by auto
    hence "Group.monoid (residue_ring (int p))" using comm_monoid.is_monoid by auto
    hence pow:"int a (^)\<^bsub>residue_ring (int p)\<^esub> d \<in> Units (residue_ring (int p))" using monoid.Units_pow_closed[of "residue_ring (int p)"] `int a \<in> Units (residue_ring (int p))` by auto
    have "int a = (int a) mod (int p)" using a by auto
    hence subs:"int a ^ d mod (int p) \<in> {1 .. int p - 1}" using residues_prime.res_prime_units_eq res_p `residues (int p)` pow residues.pow_cong by metis
    have nat_trans:"a ^ d mod p = nat (int a ^ d mod (int p))" by (metis int_power nat_int zmod_int)
    thus ?thesis using subs by auto
    qed

lemma (in field) field_mult_group :
  shows "group \<lparr> carrier = carrier R - {\<zero>}, mult = mult R, one = \<one>\<rparr>"
  apply (rule groupI)
  apply (auto simp add: field_Units)
  apply (metis integral)
  apply (metis m_assoc)
  by (metis Diff_iff Units_inv_Units Units_l_inv field_Units singletonE)
  
lemma prime_has_ord :
  fixes p::nat
  fixes a::nat
  assumes prime_p:"prime p"
  assumes "1 \<le>a \<and> a < p"
  shows "\<exists> d \<in> {1 .. p} . a ^ d mod p = 1"
  proof -
    have "prime (int p)" using prime_p by (metis transfer_int_nat_prime)
    hence res_p:"residues_prime (int p)" using residues_prime_def by auto
    have "int p \<ge> 2" using `prime (int p)` by (metis prime_ge_2_int)
    hence res:"residues (int p)" using residues_def by auto
    have card:"card (Units (residue_ring (int p))) = p - 1" using residues_prime.res_prime_units_eq res_p by auto
    have "int a \<in> Units (residue_ring (int p))" using residues_prime.res_prime_units_eq assms res_p by auto
    hence pow_eq:"int a (^)\<^bsub>residue_ring (int p)\<^esub> (p - 1)  = \<one>\<^bsub>residue_ring (int p)\<^esub>" using res residues.cring residues.finite_Units cring.units_power_order_eq_one card by metis
    hence "int a = int a mod (int p)" using assms by auto
    hence "int a ^ (p - 1) mod (int p) = 1 mod (int p)" using res residues.one_cong residues.pow_cong pow_eq by metis
    hence "int a ^ (p - 1) mod (int p) = 1" using `int p\<ge>2` by auto
    hence 1:"a ^ (p - 1) mod p = 1" by (metis Divides.transfer_int_nat_functions(2) int_1 of_nat_eq_iff of_nat_power)
    have "p - 1 \<in> {1 .. p}" using `int p\<ge>2` by auto
    thus ?thesis using 1 by auto
  qed

lemma pow_ord_eq_1 :
  fixes p::nat
  fixes a::nat
  assumes prime_p:"prime p"
  assumes "1 \<le>a \<and> a < p"
  shows "a ^ (ord a p) mod p = 1"
  proof -
    obtain d where d:"d\<ge>1 \<and> (a ^ d) mod p = 1 \<and> d \<le> p" using prime_has_ord assms by fastforce
    hence "d \<in> {1 .. p}" by auto
    have "{d . d\<in> {1 .. p} \<and> (a ^ d) mod p = 1} \<noteq> {}" using d by auto
    hence "ord a p \<in> {d . d\<in> {1 .. p} \<and> (a ^ d) mod p = 1}" using Min_in[of "{d . d\<in> {1 .. p} \<and> (a ^ d) mod p = 1}"] ord_def[of a p] `d \<in> {1 .. p}` by force
    thus ?thesis by auto
  qed

lemma ord_ge_1 :
  fixes p::nat
  fixes a::nat
  assumes prime_p:"prime p"
  assumes "1 \<le>a \<and> a < p"
  shows "ord a p \<ge> 1"
  proof -
    obtain d where d:"d\<ge>1 \<and> (a ^ d) mod p = 1 \<and> d \<le> p" using prime_has_ord assms by fastforce
    hence "d \<in> {1 .. p}" by auto
    have "{d . d\<in> {1 .. p} \<and> (a ^ d) mod p = 1} \<noteq> {}" using d by auto
    hence "ord a p \<in> {d . d\<in> {1 .. p} \<and> (a ^ d) mod p = 1}" using Min_in[of "{d . d\<in> {1 .. p} \<and> (a ^ d) mod p = 1}"] ord_def[of a p] `d \<in> {1 .. p}` by force
    thus ?thesis by auto
  qed

lemma ord_elems :
  fixes p::nat
  fixes a::nat
  assumes prime_p:"prime p"
  assumes "1\<le>a \<and> a < p"
  shows "{a^x mod p | x . x\<in>(UNIV::nat set)} = {a^x mod p | x . x \<in> {0 .. ord a p - 1}}"
  proof
    show "{a ^ x mod p |x. x \<in> {0..ord a p - 1}} \<subseteq> {a ^ x mod p |x. x \<in> UNIV}" by fast
    {
    fix y
    assume "y \<in> {a ^ x mod p |x. x\<in>(UNIV::nat set)}"
    then obtain x where x:"y = a^x mod p" by auto
    def r \<equiv> "x mod ord a p"
    then obtain q where q:"x = q * ord a p + r" by (metis comm_semiring_1_class.normalizing_semiring_rules(24) mod_eqD)
    hence "y = (a^(q * ord a p) mod p * (a^r mod p)) mod p" by (metis comm_semiring_1_class.normalizing_semiring_rules(26) mod_mult_eq x)  
    hence y:"y = (((a^ord a p mod p)^q) mod p * (a^r mod p)) mod p" by (metis comm_semiring_1_class.normalizing_semiring_rules(7) power_mod power_mult)
    have "a^ord a p mod p = 1" using pow_ord_eq_1 assms by auto
    hence "y = a^r mod p" using y by (metis mod_mod_trivial nat_mult_1 power_one)
    have "r < ord a p" using ord_ge_1[OF assms] by (simp add: r_def)
    hence "r \<in> {0 .. ord a p - 1}" by (force simp: r_def)
    hence "y \<in> {a^x mod p | x . x \<in> {0 .. ord a p - 1}}" using `y=a^r mod p` by blast
    }
    thus "{a ^ x mod p |x. x \<in> UNIV} \<subseteq> {a ^ x mod p |x. x \<in> {0..ord a p - 1}}" by auto
    qed

lemma mod_nat_int_pow_eq :
  fixes n :: nat
  fixes p :: int
  fixes a :: int
  assumes "a > 1"
  assumes "p > 1"
  shows "(nat a ^ n) mod (nat p) = nat ((a ^ n) mod p)" by (metis assms(1) assms(2) int_one_le_iff_zero_less nat_mod_distrib nat_power_eq order_less_imp_le zero_le_power)

lemma mod_nat_int_pow_eq2 :
  fixes n :: nat
  fixes p :: int
  fixes a :: int
  assumes "a > 1"
  assumes "p > 1"
  assumes "nat a ^ n mod (nat p) = 1"
  shows "a^n mod p = 1" using assms by (metis (full_types) less_not_refl3 linorder_neqE_linordered_idom mod_nat_int_pow_eq transfer_nat_int_numerals(2) zero_less_one zless_nat_conj)
  
lemma ord_elems_int :
  fixes p::int
  fixes a::int
  assumes prime_p:"prime p"
  assumes "1\<le>a \<and> a < p"
  shows "{a^x mod p | x . x\<in>(UNIV::nat set)} = {a^x mod p | x . x \<in> {0 .. ord (nat a) (nat p) - 1}}"
  proof
    show "{a ^ x mod p |x. x \<in> {0..ord (nat a) (nat p) - 1}} \<subseteq> {a ^ x mod p |x. x \<in> UNIV}" by blast
    have "p\<ge>2" using prime_p by (metis prime_ge_2_int)
    {
    fix y
    assume "y \<in> {a ^ x mod p |x. x\<in>(UNIV::nat set)}"
    then obtain x where x:"y = a^x mod p" by auto
    then obtain r where r:"r = x mod ord (nat a) (nat p)" by auto
    then obtain q where q:"x = q * ord (nat a) (nat p) + r" by (metis comm_semiring_1_class.normalizing_semiring_rules(24) mod_eqD)
    hence "y = (a^(q * ord (nat a) (nat p)) mod p * (a^r mod p)) mod p" by (metis comm_semiring_1_class.normalizing_semiring_rules(26) mod_mult_eq x)  
    hence y:"y = (((a^ord (nat a) (nat p) mod p)^q) mod p * (a^r mod p)) mod p" by (metis comm_semiring_1_class.normalizing_semiring_rules(7) power_mod power_mult)
    have "nat a^ord (nat a) (nat p) mod (nat p) = 1" using pow_ord_eq_1 assms by (metis (full_types) add1_zle_eq comm_monoid_add_class.add.right_neutral comm_semiring_1_class.normalizing_semiring_rules(24) less_imp_not_eq2 mod_by_1 mod_less not_leE prime_gt_0_int prime_int_def zero_less_nat_eq zless_nat_conj)
    hence "a ^ ord (nat a) (nat p) mod p = 1" using mod_nat_int_pow_eq2[of a p "ord (nat a) (nat p)"] assms `p\<ge>2` by fastforce
    hence "y = a^r mod p" using y by (metis comm_semiring_1_class.normalizing_semiring_rules(11) mod_mod_trivial power_one)
    have "ord (nat a) (nat p) \<ge> 1" using ord_ge_1 assms by (metis add1_zle_eq comm_monoid_add_class.add.right_neutral comm_semiring_1_class.normalizing_semiring_rules(24) mod_by_1 mod_less neq_iff not_leE prime_gt_0_int prime_int_def zero_less_nat_eq zless_nat_conj)
    hence "r \<le> ord (nat a) (nat p) - 1" using r by (metis Suc_eq_plus1 add_leE antisym gr_implies_not0 le_diff_conv2 mod_le_divisor mod_mod_trivial mod_self not_le not_less_eq_eq)
    hence "r \<in> {0 .. ord (nat a) (nat p) - 1}" using r by force
    hence "y \<in> {a^x mod p | x . x \<in> {0 .. ord (nat a) (nat p) - 1}}" using `y=a^r mod p` by blast
    }
    thus "{a^x mod p | x . x\<in>(UNIV::nat set)} \<subseteq> {a^x mod p | x . x \<in> {0 .. ord (nat a) (nat p) - 1}}" by auto
    qed
    
lemma ord_inj :
  fixes p::nat
  fixes a::nat
  assumes prime_p:"prime p"
  assumes "1\<le>a \<and> a < p"
  shows "inj_on (\<lambda> x . a^x mod p) {0 .. ord a p - 1}" sorry
  
lemma ord_inj_int :
  fixes p::nat
  fixes a::nat
  assumes prime_p:"prime p"
  assumes "1\<le>a \<and> a < p"
  shows "inj_on (\<lambda> x . int a^x mod int p) {0 .. ord a p - 1}"
  proof -
    let ?G = "\<lparr> carrier = carrier (residue_ring (int p)) - {\<zero>\<^bsub>residue_ring (int p)\<^esub>}, mult = op \<otimes>\<^bsub>residue_ring (int p)\<^esub>, one = \<one>\<^bsub>residue_ring (int p)\<^esub>\<rparr>"
    have "prime (int p)" using assms transfer_int_nat_prime by auto
    hence "residues_prime (int p)" using residues_prime_def by auto
    hence "field (residue_ring (int p))" using residues_prime.is_field by auto
    hence "group ?G" using field.field_mult_group by auto
    have "int p \<ge> 2" using `prime (int p)` by fast
    hence res : "residues (int p)" using residues_def by auto
    hence "int a \<in> carrier ?G" using assms(2) residues.zero_cong residues.res_carrier_eq by fastforce
    {
    fix x
    fix y
    assume x:"x \<in> {0 .. ord a p - 1}"
    assume y:"y \<in> {0 .. ord a p - 1}"
    assume xy : "int a^x mod int p = int a^y mod int p"
    hence "int a (^)\<^bsub>?G\<^esub> x = int a (^)\<^bsub>?G\<^esub> y" using `int a \<in> carrier ?G` res residues.pow_cong sorry
    }
    thus ?thesis sorry
    qed

lemma ord_pow_dvd_ord_elem :
  fixes p :: nat
  fixes a :: nat
  fixes n :: nat
  assumes a:"a \<in> {1 .. p - 1}"
  assumes prime_p:"prime p"
  shows "ord ((a^n) mod p) p = ord a p div gcd n (ord a p)" sorry

lemma ord_dvd_group_order :
  fixes p :: nat
  fixes a :: nat
  assumes a:"a \<in> {1 .. p - 1}"
  assumes prime_p:"prime p"
  shows "ord a p dvd p - 1"
  proof -
    let ?G = "\<lparr> carrier = carrier (residue_ring (int p)) - {\<zero>\<^bsub>residue_ring (int p)\<^esub>}, mult = op \<otimes>\<^bsub>residue_ring (int p)\<^esub>, one = \<one>\<^bsub>residue_ring (int p)\<^esub>\<rparr>"
    have "prime (int p)" using assms transfer_int_nat_prime by auto
    hence "residues_prime (int p)" using residues_prime_def by auto
    hence "field (residue_ring (int p))" using residues_prime.is_field by auto
    hence "group ?G" using field.field_mult_group by auto
    have "int p \<ge> 2" using `prime (int p)` by fast
    hence res : "residues (int p)" using residues_def by auto
    {
      fix x :: int
      fix y :: nat
      have "x (^) \<^bsub>residue_ring (int p)\<^esub> y = x (^) \<^bsub>?G\<^esub> y"
      proof (induction y)
      case zero
        thus ?case by (metis monoid.simps(2) nat_pow_def nat_rec_0)
      case plus1
        thus ?case by (metis monoid.simps(1) monoid.simps(2) nat_pow_def)
      qed
    }
    hence ops_eq:"\<forall> (x :: int) (y :: nat) . x (^) \<^bsub>residue_ring (int p)\<^esub> y = x (^) \<^bsub>?G\<^esub> y" by auto
    have "1 \<le> int a \<and> int a < int p" using assms by auto
    have "p \<ge> 2" using assms by auto
    {
       fix x
       assume x : "x \<in> {(int a) ^ i mod (int p) | i . i \<in> {0 .. ord a p - 1}}"
       then obtain i where i:"i \<in> {0 .. ord a p - 1} \<and> x = int a ^ i mod (int p)" by auto
       hence "a ^ i mod p \<in> {1 .. p - 1}" using assms p_prime_impl_mult_group_closed by auto
       have nat_trans : "a ^ i mod p = nat (int a ^ i mod (int p))" by (metis nat_int zmod_int zpower_int)
       hence "int a ^ i mod (int p) \<in> {1 .. int p - 1}" using nat_trans `a ^ i mod p \<in> {1 .. p - 1}` by force
       hence "x \<in> carrier ?G" using res residues.zero_cong residues.res_carrier_eq i by auto
    } hence subs : "{int a ^ i mod (int p) | i . i \<in> {0 .. ord a p - 1}} \<subseteq> carrier ?G" by auto
    have sub_p:"subgroup {(int a) ^ i mod (int p) | i . i \<in> {0 .. ord a p - 1}} ?G"
    proof
     show "{(int a) ^ i mod (int p) | i . i \<in> {0 .. ord a p - 1}} \<subseteq> carrier ?G" using subs by auto
     next
      fix x
      fix y
      assume x:"x \<in> {(int a) ^ i mod (int p) | i . i \<in> {0 .. ord a p - 1}}"
      assume y:"y \<in> {(int a) ^ i mod (int p) | i . i \<in> {0 .. ord a p - 1}}"
      obtain i::nat where i:"x = (int a) ^ i mod (int p)" and i2:"i \<in> (UNIV :: nat set)"using x by auto
      obtain j::nat where j:"y = (int a) ^ j mod (int p)" and j2:"j\<in>(UNIV :: nat set)"using y by auto
      hence "x \<otimes>\<^bsub>?G\<^esub> y = ((int a) ^ i mod (int p)) \<otimes>\<^bsub>?G\<^esub> ((int a) ^ j mod (int p))" using i by auto
      hence "x \<otimes>\<^bsub>?G\<^esub> y = (int a ^ i  * int a^j) mod (int p)" using Residues.residues.mult_cong res by auto
      hence xy:"x \<otimes>\<^bsub>?G\<^esub> y = (int a^(i+j)) mod (int p)" by (metis power_add)
      have "i+j \<in> (UNIV :: nat set)" using i2 j2 by auto
      hence "(int a^(i+j)) mod (int p) \<in> {(int a) ^ i mod (int p) | i . i \<in> (UNIV :: nat set)}" by blast
      hence "(int a^(i+j)) mod (int p) \<in> {int a ^ x mod int p |x. x \<in> {0..ord a p - 1}}" using ord_elems_int[of "int p" "int a"] `prime (int p)` `1 \<le> int a \<and> int a < int p` by auto
      thus "x \<otimes>\<^bsub>?G\<^esub> y \<in> {(int a) ^ i mod (int p) | i . i \<in> {0 .. ord a p - 1}}" using xy ord_elems assms by auto
     next
      have "1 mod (int p)= int a ^ 0 mod int p" by (metis power_0)
      hence "1 mod (int p) \<in> {int a ^ i mod int p |i. i \<in> {0..ord a p - 1}}" by fastforce
      thus "\<one>\<^bsub>?G\<^esub> \<in> {int a ^ i mod int p |i. i \<in> {0..ord a p - 1}}" using Residues.residues.one_cong res by auto
    next
     fix x
     assume x:"x \<in> {int a ^ i mod int p |i. i \<in> {0..ord a p - 1}}"
     hence x_in_carrier:"x \<in> carrier ?G" using subs by auto
     have "finite (carrier ?G)" using res residues.finite by simp
     then obtain d::nat where d:"x (^)\<^bsub>?G\<^esub> d = \<one>\<^bsub>?G\<^esub>" and "d\<ge>1"  using group.finite_group_elem_finite_ord[of ?G x] x_in_carrier `group ?G` by auto
     have "x = x mod int p" using x by auto
     have "x (^)\<^bsub>?G\<^esub> d = 1 mod int p" using res Residues.residues.one_cong d by auto
     hence "(x mod int p) (^)\<^bsub>?G\<^esub> d = 1 mod int p" using `x = x mod int p` by auto
     hence "(x mod int p) (^)\<^bsub>residue_ring (int p)\<^esub> d = 1 mod int p" using ops_eq by metis
     hence x_d: "x ^ d mod int p = 1" using res Residues.residues.pow_cong[of "int p" x] by (metis residues.one_cong residues.res_one_eq)
     hence inv_1:"x^d mod int p = (x^(d - 1) * x) mod int p" using `d\<ge>1` by (metis comm_semiring_1_class.normalizing_semiring_rules(7) le_0_eq power_eq_0_iff power_eq_if)
     hence inv_2:"x^d mod int p = (x * x^(d - 1)) mod int p" by (metis comm_semiring_1_class.normalizing_semiring_rules(7))  
     have inv_11:"1=(x^(d - 1) * x) mod int p" using x_d using inv_1 by auto
     hence inv_111:"\<one>\<^bsub>?G\<^esub>=(x^(d - 1) mod int p) \<otimes>\<^bsub>?G\<^esub> (x mod int p)" using Residues.residues.mult_cong[of "int p"] res Residues.residues.one_cong[of "int p"] residues.res_one_eq by auto
     have inv_22:"1=(x * x^(d - 1)) mod int p" using x_d using inv_2 by auto
     hence inv_222:"\<one>\<^bsub>?G\<^esub>=(x mod int p) \<otimes>\<^bsub>?G\<^esub> (x^(d - 1) mod int p)" using Residues.residues.mult_cong[of "int p"] res Residues.residues.one_cong[of "int p"] residues.res_one_eq by auto
     have elem:"x ^ (d - 1) mod int p \<in> {int a ^ i mod int p |i. i \<in> {0..ord a p - 1}}"
      proof -
       obtain i::nat where i:"x = int a ^ i mod int p" using x by auto
       hence "x ^ (d - 1) mod int p = (int a ^ i mod int p) ^ (d - 1) mod int p" by auto
       hence "x ^ (d - 1) mod int p = int a ^ (i * (d - 1)) mod int p" by (metis comm_semiring_1_class.normalizing_semiring_rules(31) power_mod)
       hence "x ^ (d - 1) mod int p \<in> {int a ^ i mod int p |i. i \<in> (UNIV :: nat set)}" by auto
       thus ?thesis using ord_elems_int[of "int p" "int a"] `prime (int p)` `1 \<le> int a \<and> int a < int p` by auto
      qed
      hence "x ^ (d - 1) mod int p \<in> carrier ?G"  using `\<And>x. x \<in> {int a ^ i mod int p |i. i \<in> {0..ord a p - 1}} \<Longrightarrow> x \<in> carrier ?G` by auto
      hence inv:"inv\<^bsub>?G\<^esub> x = x^(d - 1) mod int p" using inv_111 inv_222 m_inv_def[of ?G "x mod int p"] res `group ?G` `x = x mod int p` group.inv_equality x_in_carrier by fastforce
      thus "inv\<^bsub>?G\<^esub> x \<in> {int a ^ i mod int p |i. i \<in> {0..ord a p - 1}}" using elem inv by auto
   qed
   hence card_dvd:"card {int a ^ i mod int p |i. i \<in> {0..ord a p - 1}} dvd order ?G" using lagrange_ex[of ?G "{int a ^ i mod int p |i. i \<in> {0..ord a p - 1}}"] `group ?G` res residues.finite[of "int p"] by auto
   have "carrier ?G = {1 .. int p - 1}"  using res residues.zero_cong residues.res_carrier_eq by auto
   hence "order ?G = p - 1" using order_def[of ?G] by auto
   have "inj_on (\<lambda> i . int a ^ i mod int p) {0..ord a p - 1}" using ord_inj_int assms by auto
   hence cards_eq:"card ((\<lambda> i . int a ^ i mod int p) ` {0..ord a p - 1}) = card {0..ord a p - 1}" using card_image[of "(\<lambda> i . int a ^ i mod int p)" "{0..ord a p - 1}"] by auto
   have "(\<lambda> i . int a ^ i mod int p) ` {0..ord a p - 1} = {int a ^ i mod int p |i. i \<in> {0..ord a p - 1}}" by auto
   hence "card {int a ^ i mod int p |i. i \<in> {0..ord a p - 1}} = card {0..ord a p - 1}" using cards_eq by auto
   hence "card {int a ^ i mod int p |i. i \<in> {0..ord a p - 1}} = ord a p" using ord_ge_1 assms by fastforce
   thus ?thesis using card_dvd `order ?G = p - 1` by auto
  qed

lemma card_gt_0_ex :
  assumes "card {a | a . P a} > 0"
  shows "\<exists> a . P a" by (metis (lifting) assms card.neutral card_infinite less_not_refl3 mem_Collect_eq)

lemma dvd_div_ge1 :
 fixes m :: nat
 fixes n :: nat
 assumes "m > 0"
 assumes "n dvd m"
 shows "m div n \<ge> 1" using assms by (metis One_leq_div div_le_dividend div_self nat_dvd_not_less nat_neq_iff not_one_less_zero zero_neq_one)

definition phi' :: "nat => nat"
  where "phi' m = card({ x. 0 < x & x \<le> m & gcd x m = 1})"

lemma phi'_altdef :
 shows "phi' m = card { x :: nat. 1\<le> x & x \<le> m & gcd x m = 1}"
 proof -
 have "finite {x:: nat . 1 \<le> x & x\<le> m}" by fast
 have "{ x :: nat. 1\<le> x & x \<le> m & gcd x m = 1} \<subseteq> {x:: nat . 1 \<le> x & x\<le> m}" by blast
 hence "finite { x :: nat. 1\<le> x & x \<le> m & gcd x m = 1}" using `finite {x:: nat . 1 \<le> x & x\<le> m}` by auto
 have "{ x :: nat. 1\<le> x & x \<le> m & gcd x m = 1} = { x. 0 < x & x \<le> m & gcd x m = 1}" by force
 thus ?thesis using `finite { x :: nat. 1\<le> x & x \<le> m & gcd x m = 1}` phi'_def by presburger
 qed

lemma phi'_nonzero :
  assumes "m > 0"
  shows "phi' m > 0"
  proof -
  have "finite {x:: nat . 1 \<le> x & x\<le> m}" by fast
  have "{ x :: nat. 1\<le> x & x \<le> m & gcd x m = 1} \<subseteq> {x:: nat . 1 \<le> x & x\<le> m}" by blast
  hence "finite { x :: nat. 1\<le> x & x \<le> m & gcd x m = 1}" using `finite {x:: nat . 1 \<le> x & x\<le> m}` by auto
  have "1 \<in> { x :: nat. 1\<le> x & x \<le> m & gcd x m = 1}" using assms by simp
  hence "card { x :: nat. 1\<le> x & x \<le> m & gcd x m = 1} > 0" using `finite { x :: nat. 1\<le> x & x \<le> m & gcd x m = 1}` card_gt_0_iff by blast
  thus ?thesis using phi'_altdef by auto
  qed

lemma sum_phi_factors :
 fixes n :: nat
 assumes "n > 0"
 shows "(\<Sum>d \<in> {d . d dvd n} . phi' d) = n"
 proof -
   let ?f = "\<lambda> d . {m . m \<in> {1 .. n} \<and> n div gcd m n = d}"
   {
   fix d :: nat
     {
       fix m::nat
       assume m:"m \<in> {1 .. n} \<and> n div gcd m n = d"
       hence "gcd (m div gcd m n) d = 1" using assms div_gcd_coprime_nat by blast
       have "gcd m n dvd m" using m by fast
       hence "1 \<le> m div gcd m n" using m dvd_div_ge1 by auto
       have "m div gcd m n \<le> d" using m assms div_le_mono by force
       have "m div gcd m n * n div d = m" by (metis assms div_mult2_eq div_mult_self1_is_id div_mult_swap dvd_mult_div_cancel gcd_dvd2_nat gcd_semilattice_nat.inf_commute gr_implies_not0 m nat_mult_commute)
       hence "m \<in>{a * n div d | a . 1 \<le> a \<and> a \<le> d \<and> gcd a d = 1}" using `m div gcd m n \<le> d` `gcd (m div gcd m n) d = 1` `1 \<le> m div gcd m n` by force
     }
     hence "{m . m \<in> {1 .. n} \<and> n div gcd m n = d} \<subseteq> {a * n div d | a . 1 \<le> a \<and> a \<le> d \<and> gcd a d = 1}" by auto
   } note subs1 = this
   {
     fix d :: nat
     assume d:"d dvd n"
     {
       fix a :: nat
       assume a:"1 \<le> a \<and> a \<le> d \<and> gcd a d = 1"
       have "n div d \<ge> 1" using a d by (metis assms dvd_div_ge1)
       hence "a * n div d \<ge> 1" using a d by (metis dvd_div_eq_mult dvd_div_ge1 dvd_mult gcd_0_left_nat nat_0_less_mult_iff neq0_conv one_neq_zero)
       hence "a * n div d \<le> n" using a d by (metis dvd_div_mult dvd_mult_div_cancel mult_le_mono1 nat_mult_commute)
       have "gcd (a * n div d) n = n div d"
        proof -
          have "gcd a n \<le> n div d" using a d by (metis assms div_le_mono div_mult_self2_is_id divides_mult_nat dvd_nat_bounds gcd_commute_nat gcd_dvd1_nat gcd_lcm_complete_lattice_nat.inf_bot_right gcd_left_commute_nat gr_implies_not0 nat_mult_commute)
          hence "gcd (a * n div d) n \<le> n div d" by (metis a assms d div_le_mono div_mult_self2_is_id dvd_mult2 dvd_mult_div_cancel dvd_nat_bounds gcd_mult_distrib_nat gr_implies_not0 nat_mult_1_right nat_mult_commute order_refl)
          have "gcd (n div d) n = n div d" using d by (metis dvd_mult_div_cancel dvd_triv_right gcd_commute_nat gcd_proj2_if_dvd_nat)
          hence "gcd (a * n div d) n \<ge> n div d" by (metis `1 \<le> a * n div d` d dvd_div_mult dvd_triv_right gcd_dvd1_nat gcd_le2_nat gcd_proj1_if_dvd_nat gcd_semilattice_nat.le_inf_iff gcd_zero_nat nat_mult_commute not_one_le_zero)
          thus ?thesis using `gcd (a * n div d) n \<le> n div d` by auto
        qed
       hence "n div gcd (a * n div d) n = d" using d `1 \<le> a * n div d` div_mult_self2_is_id dvd_mult_div_cancel mult_is_0 not_one_le_zero by metis
       hence "a * n div d \<in> {m . m \<in> {1 .. n} \<and> n div gcd m n = d}" using `a*n div d \<le> n` `a*n div d \<ge> 1` by fastforce
     }
     hence "{a * n div d | a . 1 \<le> a \<and> a \<le> d \<and> gcd a d = 1} \<subseteq> {m . m \<in> {1 .. n} \<and> n div gcd m n = d}" by blast
   }
   hence "\<And> d . d dvd n \<Longrightarrow> {a * n div d | a . 1 \<le> a \<and> a \<le> d \<and> gcd a d = 1} = {m . m \<in> {1 .. n} \<and> n div gcd m n = d}" using subs1 by blast
   hence d_seteq:"\<And> d . d dvd n \<Longrightarrow> card {a * n div d | a . 1 \<le> a \<and> a \<le> d \<and> gcd a d = 1} = card {m . m \<in> {1 .. n} \<and> n div gcd m n = d}" using subs1 by presburger
   {
     fix d
     assume d:"d dvd n"
     have "card {a * n div d | a . 1 \<le> a \<and> a \<le> d \<and> gcd a d = 1} = card {a . 1 \<le> a \<and> a \<le> d \<and> gcd a d = 1}" using inj_on_def
     proof -
       {
         fix x
         fix y
         assume "x * n div d =  y * n div d"
         hence "x* (n div d) = y * (n div d)" using div_mult_swap d by metis
         have "0 < d \<and> d \<le> n" using d dvd_nat_bounds `n>0` by blast
         hence "n div d > 0" using `n>0` by (metis d dvd_div_ge1 neq0_conv not_one_le_zero)
         hence "x = y" using d `x * (n div d) = y * (n div d)` by (metis nat_mult_commute nat_mult_eq_cancel1)
       }
       hence inj:"inj_on (\<lambda> a . a * n div d) {a . 1 \<le> a \<and> a \<le> d \<and> gcd a d = 1}" using inj_on_def  by blast
       {
         fix y
         assume "y \<in> {a * n div d | a . 1 \<le> a \<and> a \<le> d \<and> gcd a d = 1}"
         then obtain a where a:"y = a * n div d \<and> 1 \<le> a \<and> a \<le> d \<and> gcd a d = 1" by auto
         hence "a \<in> {a . 1 \<le> a \<and> a \<le> d \<and> gcd a d = 1}" by auto
         hence "\<exists> x \<in> {a . 1 \<le> a \<and> a \<le> d \<and> gcd a d = 1} . y = x * n div d" using a by auto
       }
       hence "(\<lambda> a . a * n div d) ` {a . 1 \<le> a \<and> a \<le> d \<and> gcd a d = 1} = {a * n div d | a . 1 \<le> a \<and> a \<le> d \<and> gcd a d = 1}" by auto
       hence "bij_betw (\<lambda> a . a * n div d) {a . 1 \<le> a \<and> a \<le> d \<and> gcd a d = 1} {a * n div d | a . 1 \<le> a \<and> a \<le> d \<and> gcd a d = 1}" using inj bij_betw_def by fast
       thus ?thesis using bij_betw_same_card by force
     qed
   }
   hence "\<And> d . d dvd n \<Longrightarrow> card {a . 1 \<le> a \<and> a \<le> d \<and> gcd a d = 1} = card {m . m \<in> {1 .. n} \<and> n div gcd m n = d}" using d_seteq by auto
   hence "\<And> d . d dvd n \<Longrightarrow> phi' d = card {m . m \<in> {1 .. n} \<and> n div gcd m n = d}" using phi'_altdef by auto
   hence sum_eq1:"(\<Sum>d \<in> {d . d \<in> (UNIV :: nat set) \<and> d dvd n} . phi' d) = (\<Sum>d \<in> {d . d \<in> (UNIV :: nat set) \<and> d dvd n} . card {m . m \<in> {1 .. n} \<and> n div gcd m n = d})" by auto
   {
     fix i::nat
     fix j::nat
     assume ij:"i \<noteq> j"
     have "{m . m \<in> {1 .. n} \<and> n div gcd m n = i} \<inter> {m . m \<in> {1 .. n} \<and> n div gcd m n = j} = {}"
     proof (rule ccontr)
      assume "{m . m \<in> {1 .. n} \<and> n div gcd m n = i} \<inter> {m . m \<in> {1 .. n} \<and> n div gcd m n = j} \<noteq> {}"
      then obtain a where "a \<in> {m . m \<in> {1 .. n} \<and> n div gcd m n = i} \<inter> {m . m \<in> {1 .. n} \<and> n div gcd m n = j}" by auto
      hence a:"a \<in> {1 .. n} \<and> n div gcd a n = i \<and> n div gcd a n = j" by auto
      hence "i = j" by force
      thus False using ij by auto
     qed
   } note sets_disjoint = this
   {
     fix d :: nat
     have "finite {m . m \<in> {1 .. n} \<and> n div gcd m n = d}" by force
   } note sets_finite = this
   have "finite {d . d \<in> (UNIV :: nat set) \<and> d dvd n}" using dvd_nat_bounds `n>0` by force
   hence sum_card:"(\<Sum>d \<in> {d . d \<in> (UNIV :: nat set) \<and> d dvd n} . phi' d) = card (UNION {d . d \<in> (UNIV :: nat set) \<and> d dvd n} (\<lambda> d . {m . m \<in> {1 .. n} \<and> n div gcd m n = d}))" using Big_Operators.card_UN_disjoint[of "{d . d \<in> (UNIV :: nat set) \<and> d dvd n}" "(\<lambda> d . {m . m \<in> {1 .. n} \<and> n div gcd m n = d})"] sets_finite sets_disjoint sum_eq1 by fastforce
   have "UNION {d . d \<in> (UNIV :: nat set) \<and> d dvd n} (\<lambda> d . {m . m \<in> {1 .. n} \<and> n div gcd m n = d}) = {1 .. n}"
    proof
      show "(\<Union>d\<in>{d \<in> UNIV. d dvd n}. {m \<in> {1..n}. n div gcd m n = d}) \<subseteq> {1..n}" by fast
      {
        fix m
        assume m : "m \<in> {1 .. n}"
        hence "(n div gcd m n) dvd n" by (metis dvd_mult_div_cancel dvd_triv_right gcd_dvd1_nat gcd_semilattice_nat.inf_commute)
        hence "m \<in> (\<Union>d\<in>{d \<in> UNIV. d dvd n}. {m \<in> {1..n}. n div gcd m n = d})" using m by blast
      }
      thus "{1..n} \<subseteq> (\<Union>d\<in>{d \<in> UNIV. d dvd n}. {m \<in> {1..n}. n div gcd m n = d})" by auto
    qed
   thus ?thesis using sum_card by force
 qed

theorem residue_prime_mult_group_has_gen :
 fixes p :: nat
 assumes prime_p : "prime p"
 shows "\<exists> a \<in> {1 .. p - 1} . {1 .. p - 1} = {a^i mod p|i . i \<in> (UNIV :: nat set)}"
 proof -
  have "p\<ge>2" using prime_p by (metis prime_ge_2_nat)
  let ?N = "\<lambda> x . card {a | a . a \<in> {1 .. p - 1} \<and> ord a p = x}"
  have "finite {d | d . d \<in> (UNIV :: nat set) \<and> d dvd p - 1 }" using dvd_nat_bounds `p\<ge>2` by auto 
  {
    fix i::nat
    fix j::nat
    assume "i \<noteq> j"
    have "(\<lambda> x . {a | a . a \<in> {1 .. p - 1} \<and> ord a p = x}) i \<inter> (\<lambda> x . {a | a . a \<in> {1 .. p - 1} \<and> ord a p = x}) j = {}"
    proof (rule ccontr)
      assume "(\<lambda> x . {a | a . a \<in> {1 .. p - 1} \<and> ord a p = x}) i \<inter> (\<lambda> x . {a | a . a \<in> {1 .. p - 1} \<and> ord a p = x}) j \<noteq> {}"
      then obtain x where "x \<in> (\<lambda> x . {a | a . a \<in> {1 .. p - 1} \<and> ord a p = x}) i \<inter> (\<lambda> x . {a | a . a \<in> {1 .. p - 1} \<and> ord a p = x}) j" by auto
      hence x : "x \<in> {1 .. p - 1} \<and> ord x p = i \<and> ord x p = j" by auto
      hence "i = j" by auto
      thus False using `i \<noteq> j ` by auto
    qed
  } note sets_disjoint = this
  {
    fix i::nat
    have "finite ((\<lambda> x . {a | a . a \<in> {1 .. p - 1} \<and> ord a p = x}) i)" by auto
  }
  hence sum_disjoint_card:"(\<Sum> d \<in> {d | d . d \<in> (UNIV :: nat set) \<and> d dvd p - 1 } . ?N d) = card (UNION {d | d . d \<in> (UNIV :: nat set) \<and> d dvd p - 1 } (\<lambda> x . {a | a . a \<in> {1 .. p - 1} \<and> ord a p = x}))" using sets_disjoint Big_Operators.card_UN_disjoint[of "{d |d. d \<in> UNIV \<and> d dvd p - 1}" "\<lambda> x . {a | a . a \<in> {1 .. p - 1} \<and> ord a p = x}"] `finite {d | d . d \<in> (UNIV :: nat set) \<and> d dvd p - 1 }` by simp
  have "UNION {d | d . d \<in> (UNIV :: nat set) \<and> d dvd p - 1 } (\<lambda> x . {a | a . a \<in> {1 .. p - 1} \<and> ord a p = x}) = {1 .. p - 1}"
    proof
    show "UNION {d | d . d \<in> (UNIV :: nat set) \<and> d dvd p - 1 } (\<lambda> x . {a | a . a \<in> {1 .. p - 1} \<and> ord a p = x}) \<subseteq> {1 .. p - 1}" by auto
    {
      fix x::nat
      assume "x\<in>{1 .. p - 1}"
      hence "ord x p dvd p - 1" using ord_dvd_group_order using prime_p by auto
      hence "0 < ord x p \<and> ord x p \<le> p - 1" using `p\<ge>2` dvd_nat_bounds[of "p - 1" "ord x p"] by force
      hence "ord x p \<in>{1 .. p - 1}" by auto
      hence "x \<in> UNION {d | d . d \<in> (UNIV :: nat set) \<and> d dvd p - 1 } (\<lambda> x . {a | a . a \<in> {1 .. p - 1} \<and> ord a p = x})" using `ord x p dvd p - 1` by (metis (lifting, full_types) UNIV_I UN_iff `x \<in> {1..p - 1}` mem_Collect_eq)
    } thus "{1 .. p - 1} \<subseteq> UNION {d | d . d \<in> (UNIV :: nat set) \<and> d dvd p - 1 } (\<lambda> x . {a | a . a \<in> {1 .. p - 1} \<and> ord a p = x})" by auto
    qed
  hence sum_Ns_eq:"(\<Sum> d \<in> {d | d . d \<in> (UNIV :: nat set) \<and> d dvd p - 1 } . ?N d) = p - 1" using sum_disjoint_card by auto
  {
    fix d :: nat
    assume "d dvd p - 1"
    assume "?N d > 0"
    then obtain a where a:"a\<in>{1 .. p - 1} \<and> ord a p = d" using card_gt_0_ex by auto
    have card_le_d:"finite {x. x \<in> (UNIV :: nat set) \<and> x ^ d mod p = 1} \<and> card {x. x \<in> (UNIV :: nat set) \<and> x ^ d mod p = 1} \<le> d" sorry
    have subs:"{a^n mod p| n . n \<in> {0 .. d - 1}} \<subseteq> {x. x \<in> (UNIV :: nat set) \<and> x ^ d mod p = 1}"
      proof
        fix x
        assume "x \<in> {a ^ n mod p|n. n \<in> {0..d - 1}}"
        then obtain n where n:"x = a^n mod p\<and> n \<in> {0.. d - 1}" by auto
        have "a^d mod p = 1" using a pow_ord_eq_1 prime_p by auto
        hence "x^d mod p = 1" using n by (metis mod_mod_trivial nat_mult_commute power_mod power_mult power_one)
        thus "x \<in> {x \<in> UNIV. x ^ d mod p = 1}" by auto
      qed
    have "inj_on (\<lambda> n. a^n mod p) {0 .. d - 1}" using ord_inj prime_p a by auto
    hence cards_eq1:"card ((\<lambda> n. a^n mod p) ` {0 .. d - 1}) = card {0 .. d - 1}" using card_image[of "\<lambda> n. a^n mod p" "{0 .. d - 1}"] by fast
    have "{a^n mod p| n . n \<in> {0 .. d - 1}} = ((\<lambda> n. a^n mod p) ` {0 .. d - 1})" by auto
    hence cards_eq2:"card {a^n mod p| n . n \<in> {0 .. d - 1}} = card {0 .. d - 1}" using cards_eq1 by auto
    have "d > 0" using dvd_nat_bounds[of "p - 1" d] `p\<ge>2` `d dvd p - 1` by linarith
    hence "card {0 .. d - 1} = d" by fastforce
    hence "card {a^n mod p| n . n \<in> {0 .. d - 1}} = d" using cards_eq2 by auto
    hence set_eq1:"{a^n mod p| n . n \<in> {0 .. d - 1}} = {x. x \<in> (UNIV :: nat set) \<and> x ^ d mod p = 1}" using card_seteq[of "{x. x \<in> (UNIV :: nat set) \<and> x ^ d mod p = 1}" "{a^n mod p| n . n \<in> {0 .. d - 1}}"] subs card_le_d by presburger
    have set_eq2:"{a \<in> {1 .. p - 1} . ord a p = d} = {a^n mod p| n . n \<in> {1 .. d} \<and> ord (a^n mod p) p = d}"
    proof
      {
        fix x :: nat
        assume x:"x \<in> {1 .. p - 1} \<and> ord x p = d"
        hence "(x ^ ord x p) mod p = 1" using pow_ord_eq_1 prime_p by auto
        hence "x \<in> {x. x \<in> (UNIV :: nat set) \<and> x ^ d mod p = 1}" using x by auto
        then obtain n where n:"x = a^n mod p \<and> n \<in> {0 .. d - 1}" using set_eq1 by blast
        have "a^0 mod p = 1" by (metis assms mod_less power_0 prime_gt_1_nat)
        have "a^d mod p = 1" using a pow_ord_eq_1 prime_p by auto
        hence "a^d mod p = a ^ 0 mod p" using `a^0 mod p = 1` by auto
        obtain n' where n':"n' = (if n = 0 then d else n)" using n by auto
        have "d \<ge> 1" using `d dvd p - 1` dvd_nat_bounds[of "p - 1" d] `p\<ge>2` by linarith
        hence n'1:"n' \<in> {1 .. d}" using n' n by force
        hence n'2:"x = a^n' mod p" using `a^d mod p = a^0 mod p` n' n by auto
        hence "x\<in>{a^n mod p| n . n \<in> {1 .. d} \<and> ord (a^n mod p) p = d}" using x n'1 by fast
      } thus "{a \<in> {1 .. p - 1} . ord a p = d} \<subseteq> {a^n mod p| n . n \<in> {1 .. d} \<and> ord (a^n mod p) p = d}" by auto
      {
        fix x :: nat
        assume x:"x \<in> {a^n mod p| n . n \<in> {1 .. d} \<and> ord (a^n mod p) p = d}"
        then obtain n where n:"x = a^n mod p \<and> n \<in> {1 .. d} \<and> ord (a^n mod p) p = d" by auto
        have "a^n mod p \<in> {1 .. p - 1}" using p_prime_impl_mult_group_closed using a prime_p by auto
        hence "x \<in> {a \<in> {1 .. p - 1} . ord a p = d}" using n by auto
      } thus "{a^n mod p| n . n \<in> {1 .. d} \<and> ord (a^n mod p) p = d} \<subseteq> {a \<in> {1 .. p - 1} . ord a p = d}" by blast
    qed

    have inj1:"inj_on (\<lambda> n . a^n mod p) {0 .. d - 1}" using prime_p ord_inj a by auto
    {
      fix i :: nat
      fix j :: nat
      assume i : "i \<in> {1 .. d}"
      assume j : "j \<in> {1 .. d}"
      assume ij : "a^i mod p = a^j mod p"
      {
        assume "i = d"
        assume "j = d"
        hence "i = j" using `i=d` by auto
      }
      moreover
      {
        assume "i = d"
        assume "j \<noteq> d"
        hence "j \<in> {0 .. d - 1}" using j by auto
        have "a^0 mod p = 1" by (metis assms mod_less power_0 prime_gt_1_nat)
        have "a^d mod p = 1" using a pow_ord_eq_1 prime_p by auto
        hence "a^j mod p = a ^ 0 mod p" using `a^0 mod p = 1` `i=d` ij by auto
        have "0 \<in> {0 .. d - 1}" by auto
        hence "j = 0" using inj1 `j \<in> {0 .. d - 1}` inj_on_def using `a^j mod p = a^0 mod p` by metis
        hence "i = j" using j by auto
      }
      moreover
      {
        assume "j = d"
        assume "i \<noteq> d"
        hence "i \<in> {0 .. d - 1}" using i by auto
        have "a^0 mod p = 1" by (metis assms mod_less power_0 prime_gt_1_nat)
        have "a^d mod p = 1" using a pow_ord_eq_1 prime_p by auto
        hence "a^i mod p = a ^ 0 mod p" using `a^0 mod p = 1` `j=d` ij by auto
        have "0 \<in> {0 .. d - 1}" by auto
        hence "i = 0" using inj1 `i \<in> {0 .. d - 1}` inj_on_def using `a^i mod p = a^0 mod p` by metis
        hence "i = j" using i by auto
      }
      moreover
      {
        assume "j \<noteq> d"
        assume "i \<noteq> d"
        hence "i \<in> {0 .. d - 1}" using i by auto
        have "j \<in> {0 .. d - 1}" using j `j\<noteq>d` by auto
        hence "i = j" using ij `i\<in> {0 .. d - 1}` inj1 inj_on_def by metis
      }
      ultimately have "i = j" by fastforce
    }  hence inj2:"inj_on (\<lambda> n . a^n mod p) {1 .. d}" using inj_on_def by blast
    {
      fix i :: nat
      fix j :: nat
      assume i : "i \<in> {n . n \<in> {1 .. d} \<and> ord (a^n mod p) p = d}"
      assume j : "j \<in> {n . n \<in> {1 .. d} \<and> ord (a^n mod p) p = d}"
      assume ij : "a^i mod p = a^j mod p"
      have "i \<in> {1 .. d}" using i by fast
      have "j \<in> {1 .. d}" using j by fast
      hence "i=j" using ij inj2 `i \<in> {1 .. d}` `j \<in> {1 .. d}`  inj_on_def by metis
    } hence "inj_on (\<lambda> n . a^n mod p) {n . n \<in> {1 .. d} \<and> ord (a^n mod p) p = d}" using inj_on_def by blast
    hence card_proj_eq:"card ((\<lambda> n . a^n mod p) ` {n . n \<in> {1 .. d} \<and> ord (a^n mod p) p = d}) = card {k . k \<in> {1 .. d} \<and> ord (a^k mod p) p = d}" using card_image[of "\<lambda> n . a^n mod p" "{n . n \<in> {1 .. d} \<and> ord (a^n mod p) p = d}"] by blast
    have "{a^n mod p| n . n \<in> {1 .. d} \<and> ord (a^n mod p) p = d} = (\<lambda> n . a^n mod p) ` {n . n \<in> {1 .. d} \<and> ord (a^n mod p) p = d}" by blast
    hence card_proj_eq2:"card {a^n mod p| n . n \<in> {1 .. d} \<and> ord (a^n mod p) p = d} = card {k . k \<in> {1 .. d} \<and> ord (a^k mod p) p = d}" using card_proj_eq by auto
    {
      fix k 
      assume k:"k \<in> {1 .. d} \<and> ord (a^k mod p) p = d"
      have "ord (a^k mod p) p = d div (gcd k d)" using ord_pow_dvd_ord_elem prime_p a by presburger
      hence "ord (a^k mod p) p = d" using k by auto
      hence "gcd k d = 1" using `ord (a^k mod p) p = d div (gcd k d)` by (metis `d dvd p - 1` assms coprime_minus_one_nat dvd_mult_div_cancel gcd_nat.simps gcd_proj2_if_dvd_nat gcd_semilattice_nat.inf_commute gcd_semilattice_nat.inf_le1 mult_eq_self_implies_10 nat_mult_commute one_not_prime_nat zero_not_prime_nat)
    } note ord_eq_d_impl_coprime_k_d = this
    {
      fix k 
      assume k:"k \<in> {1 .. d} \<and> gcd k d = 1"
      have "ord (a^k mod p) p = d div (gcd k d)"  using ord_pow_dvd_ord_elem prime_p a by presburger
      hence "ord (a^k mod p) p = d" using k by auto
    }
    hence "{k \<in> {1 .. d} . gcd k d = 1} = {k . k \<in> {1 .. d} \<and> ord (a^k mod p) p = d}" using ord_eq_d_impl_coprime_k_d by fast
    hence cards_eq:"card {a \<in> {1 .. p - 1} . ord a p = d} = card {k \<in> {1 .. d} . gcd k d = 1}" using set_eq2 card_proj_eq2 by presburger
    have "{k \<in> {1 .. d} . gcd k d = 1} = {x. 1 \<le> x \<and> x \<le> d \<and> coprime x d}" by simp
    hence "?N d = phi' d" using phi'_altdef[of d] cards_eq by presburger
  } note bla = this
  {
    fix d
    assume d:"d dvd (p - 1)"
    have "phi' d \<ge> 0" by auto
    have "card {a |a. a \<in> {1..p - 1} \<and> ord a p = d} \<le> phi' d"
    proof cases
      assume "card {a |a. a \<in> {1..p - 1} \<and> ord a p = d} = 0"
      thus ?thesis by presburger
      next
      assume "card {a |a. a \<in> {1..p - 1} \<and> ord a p = d} \<noteq> 0"
      hence "card {a |a. a \<in> {1..p - 1} \<and> ord a p = d} > 0" by fast
      thus ?thesis using bla d by auto
    qed
  }
  hence all_le:"\<And>i. i \<in> {d | d . d \<in> (UNIV :: nat set) \<and> d dvd p - 1 } \<Longrightarrow> (\<lambda> i . card {a |a. a \<in> {1..p - 1} \<and> ord a p = i}) i \<le> (\<lambda> i . phi' i) i" by fast
  hence le:"(\<Sum>i\<in>{d |d. d \<in> UNIV \<and> d dvd p - 1}. ?N i) \<le> (\<Sum>i\<in>{d |d. d \<in> UNIV \<and> d dvd p - 1}. phi' i)" using setsum_mono[of "{d | d . d \<in> (UNIV :: nat set) \<and> d dvd p - 1}" "\<lambda> i . card {a |a. a \<in> {1..p - 1} \<and> ord a p = i}" "\<lambda> i . phi' i"] by fast
  have "p - 1 = (\<Sum> d \<in> {d | d . d \<in> (UNIV :: nat set) \<and> d dvd p - 1 } . phi' d)" using sum_phi_factors `p\<ge>2` by simp
  hence eq:"(\<Sum>i\<in>{d |d. d \<in> UNIV \<and> d dvd p - 1}. ?N i) = (\<Sum>i\<in>{d |d. d \<in> UNIV \<and> d dvd p - 1}. phi' i)" using le sum_Ns_eq by presburger
  have "\<And>i. i \<in> {d | d . d \<in> (UNIV :: nat set) \<and> d dvd p - 1 } \<Longrightarrow> (\<lambda> i . card {a |a. a \<in> {1..p - 1} \<and> ord a p = i}) i = (\<lambda> i . phi' i) i"
    proof (rule ccontr)
    fix i
    assume i1:"i \<in> {d |d. d \<in> UNIV \<and> d dvd p - 1}"
    assume i2:"card {a |a. a \<in> {1..p - 1} \<and> ord a p = i} \<noteq> phi' i"
    hence N_eq_0:"card {a |a. a \<in> {1..p - 1} \<and> ord a p = i} = 0" using bla i1 by blast
    have "0 < i" using `p\<ge>2` i1 dvd_nat_bounds[of "p - 1" i] by auto
    hence "?N i < phi' i" using phi'_nonzero N_eq_0 by presburger
    hence "(\<Sum>i\<in>{d |d. d \<in> UNIV \<and> d dvd p - 1}. ?N i) < (\<Sum>i\<in>{d |d. d \<in> UNIV \<and> d dvd p - 1}. phi' i)" using `finite {d |d. d \<in> UNIV \<and> d dvd p - 1}` i1 all_le setsum_strict_mono_ex1[of "{d | d . d \<in> (UNIV :: nat set) \<and> d dvd p - 1}" "\<lambda> i . card {a |a. a \<in> {1..p - 1} \<and> ord a p = i}" "\<lambda> i . phi' i"] by blast
    thus False using eq by linarith
    qed
  hence "?N (p - 1) = phi' (p - 1)" by fast
  hence "phi' (p - 1) > 0" using phi'_nonzero `p\<ge>2` by auto
  hence "card {a . a \<in> {1..p - 1} \<and> ord a p = p - 1} > 0" using `?N (p - 1) = phi' (p - 1)` by auto
  then obtain a where a:"a \<in> {1..p - 1} \<and> ord a p = p - 1" using card_gt_0_ex by auto
  hence set_eq:"{a^i mod p|i . i \<in> (UNIV :: nat set)} = (\<lambda> x . a^x mod p) ` {0 .. p - 2}" using ord_elems prime_p a by fastforce
  have card_eq:"card ((\<lambda> x . a^x mod p) ` {0 .. ord a p - 1}) = card {0 .. ord a p - 1}" using card_image[of "(\<lambda>x. a ^ x mod p)" "{0..ord a p - 1}"] ord_inj[of p a] a prime_p by auto
  have "ord a p - 1 = p - 2" using a `p\<ge>2` by auto
  hence "card ((\<lambda> x . a^x mod p) ` {0 .. p - 2}) = card {0 ..p - 2}" using card_eq by force
  hence card_p_minus_1:"card {a^i mod p|i . i \<in> (UNIV :: nat set)} =  p - 1" using set_eq `p\<ge>2` by auto
  have "{a^i mod p|i . i \<in> (UNIV :: nat set)} \<subseteq> {1 .. p - 1}" using p_prime_impl_mult_group_closed prime_p a by fast
  hence "{1 .. p - 1} = {a^i mod p|i . i \<in> (UNIV :: nat set)}" using card_seteq[of "{1 .. p - 1}" "{a^i mod p|i . i \<in> (UNIV :: nat set)}"] card_p_minus_1 `p\<ge>2` by simp
  thus ?thesis using a by blast
 qed

lemma blablub :
 fixes p :: nat
 fixes a :: nat
 assumes "p \<ge> 2"
 assumes "x \<le> p - 2"
 shows "x \<noteq> p - 1"
 proof
  assume x:"x = p - 1"
  hence "x > p - 2" using `p \<ge> 2` by auto
  thus False using `x \<le> p - 2` by auto
 qed

theorem lehmer_backwards:
 assumes 1:"prime p"
 shows "\<exists> a. [a^(p - 1) = 1] (mod p) \<and> (\<forall> x . 0 < x \<longrightarrow> x \<le> p - 2 \<longrightarrow> [a^x \<noteq> 1] (mod p))"
 proof -
   have "p \<ge> 2" using prime_ge_2_nat 1 by auto
   obtain a where a:"a \<in> {1 .. p - 1} \<and> {1 .. p - 1} = {a^i mod p|i . i \<in> (UNIV :: nat set)}" using residue_prime_mult_group_has_gen[of p] 1 by blast
  {
   {
    fix x::nat
    assume x:"0 < x \<and> x \<le> p - 2 \<and>[a^x = 1] (mod p)"
    have "{a^i mod p|i . i \<in> (UNIV :: nat set)} = {a^i mod p | i::nat . 0 < i \<and> i \<le> x}"
    proof
      {
        fix y
        assume y:"y \<in> {a^i mod p | i::nat . 0 \<le> i \<and> i \<le> x}"
        then obtain i :: nat where i:"(0 \<le> i) \<and> (i \<le> x) \<and> (y = a^i mod p)" using y by auto
        have "i \<in> (UNIV :: nat set)" by auto
        hence "y \<in> {a^i mod p|i . i \<in> (UNIV :: nat set)}" using i by auto
      }
      thus "{a ^ i mod p |i. 0 < i \<and> i \<le> x} \<subseteq> {a ^ i mod p |i. i \<in> (UNIV :: nat set)}" by auto
      {
        fix y
        assume y:"y \<in> {a^i mod p|i . i \<in> (UNIV :: nat set)}"
        then obtain i::nat where i:"y = a^i mod p" by auto
        obtain q where q:"q = i div x" by auto
        obtain r where r:"r = i mod x" by auto
        have "i = q*x + r" using q r by auto
        hence "y = (a ^ (q*x +r)) mod p" using i by auto
        hence y_q_r:"y = (((a ^ (q*x)) mod p) * ((a ^ r) mod p)) mod p" by (metis comm_semiring_1_class.normalizing_semiring_rules(26) comm_semiring_1_class.normalizing_semiring_rules(7) zmod_simps(3))
        have Bier:"2 ^ x mod (int p) = int (2 ^ x mod p)" by (metis int_numeral of_nat_power zmod_int)
        have "a ^ x mod p = 1" using mod_less prime_gt_1_nat 1 x cong_nat_def by auto
        hence Gnedl:"a ^ x mod p = 1" using Bier by auto
        have "a ^ (q*x) mod p = (a ^ x mod p) ^ q mod p" by (metis power_mod nat_mult_commute power_mult)
        hence "a ^ (q*x) mod p = 1" by (metis Gnedl mod_mod_trivial power_one)
        hence y_r:"y = a ^ r mod p" using y_q_r mod_mod_trivial by auto
        have r_x:"0 \<le> r \<and> r < x" using r x by auto
        hence "y \<in> {a ^ i mod p |i. 0 < i \<and> i \<le> x}"
        proof (cases)
          assume "r = 0"
            hence "y = 1" using y_r by (metis `a ^ (q * x) mod p = 1` `i = q * x + r` add.comm_neutral i)
            hence "y = a^x mod p" using x by (metis Gnedl)
            thus ?thesis by (metis (lifting, full_types) CollectI `0 \<le> r \<and> r < x` `r = 0` le_refl)
          next
          assume "r \<noteq> 0"
            hence "0 < r \<and> r < x" using r_x by auto
            thus ?thesis using y_r by auto
        qed
      }
      thus " {a ^ i mod p|i. i \<in> (UNIV :: nat set)} \<subseteq> {a ^ i mod p |i. 0 < i \<and> i \<le> x}" by auto
    qed
    hence gen_eq:"{1 .. p - 1} = {a^i mod p | i::nat . 1\<le> i \<and> i \<le> x}" using a by auto
    have "card {1 .. p - 1} = p - 1" by auto
    have "{a^i mod p | i::nat . i \<in> {1..x}} = (\<lambda> i. a^i mod p) ` ({1..x}::nat set)" by auto
    hence "card {a^i mod p | i::nat . 1 \<le> i \<and> i \<le> x} = card ((\<lambda> i. a^i mod p) ` ({1..x}::nat set))" by auto
    hence "card {a^i mod p | i::nat . 1 \<le> i \<and> i \<le> x} \<le> p - 2" using Finite_Set.card_image_le[of "{1..x}" "\<lambda> i. a^i mod p"] x by auto
    hence "card {1 .. p - 1} \<noteq> card {a^i mod p | i::nat . 1 \<le> i \<and> i \<le> x}" using `card {1.. p - 1} = p - 1` blablub[of p "card {a^i mod p | i::nat . 1 \<le> i \<and> i \<le> x}"] `p\<ge>2` by auto
    hence False using gen_eq by metis
   }
   hence "\<forall> x . 0 < x \<longrightarrow> x \<le> p - 2 \<longrightarrow> [a^x \<noteq> 1] (mod p)" by auto
  } note a_is_gen = this
 {
    assume "a>1"
    have "a \<le> p - 1" using a by auto
    hence "coprime a p" using `a > 1` by (metis "1" diff_0_eq_0 diff_diff_cancel diff_is_0_eq dvd_imp_le gcd_commute_nat less_imp_diff_less one_neq_zero order_less_imp_le order_neq_le_trans prime_imp_coprime_nat prime_nat_def)
    hence "coprime (int a) (int p)" by (metis int_1 transfer_int_nat_gcd(1))
    have "phi (int p) = p - 1" by (metis (full_types) "1" nat_int phi_prime prime_int_def)
    hence "[a^(p - 1) = 1] (mod p)" using euler_theorem[of "int p" "int a"] `coprime (int a) (int p)`  by (metis of_nat_0_le_iff of_nat_1 of_nat_power transfer_int_nat_cong)
  }
  moreover
  {
    assume "a = 1"
    hence "[a^(p - 1) = 1] (mod p)" by auto
  }
  ultimately have "[a^(p - 1) = 1] (mod p)" using a by fastforce
  thus ?thesis using a_is_gen by auto
 qed

theorem lehmer_extended_backwards:
 assumes 1:"prime(p)"
 shows "\<exists> a . [a^(p - 1) = 1] (mod p) \<and> (\<forall> q. q \<in> prime_factors (p - 1) \<longrightarrow> [a^((p - 1) div q) \<noteq> 1] (mod p))"
 proof -
  have "p \<ge> 2" using 1 by (metis prime_ge_2_nat)
  obtain a where a:"[a^(p - 1) = 1] (mod p) \<and> (\<forall> x . 0 < x \<longrightarrow> x \<le> p - 2 \<longrightarrow> [a^x \<noteq> 1] (mod p))" using lehmer_backwards 1 by auto
  {
   fix q
   assume q:"q \<in> prime_factors (p - 1)"
   hence "q \<le> p - 1" by (metis "1" One_nat_def Suc_eq_plus1_left dvd_imp_le le_add_diff_inverse neq0_conv one_not_prime_nat prime_factors_dvd_nat prime_ge_1_nat)
   hence "(p - 1) div q \<ge> 1" by (metis (full_types) div_le_mono div_self gr_implies_not0 prime_factors_gt_0_nat q)
   have "q \<ge> 2" using q by (metis prime_factors_prime_nat prime_ge_2_nat)
   hence "(p - 1) div q < p - 1" using `p \<ge> 2` by (metis "1" div_less_dividend prime_factors_prime_nat prime_gt_1_nat q zero_less_diff)
   hence "[a^((p - 1) div q) \<noteq> 1] (mod p)" using a `(p - 1) div q \<ge> 1` by fastforce
  }
  hence "\<forall> q. q \<in> prime_factors (p - 1) \<longrightarrow> [a^((p - 1) div q) \<noteq> 1] (mod p)" by auto
  thus ?thesis using a by auto
 qed

fun verify_pratt :: "pratt list \<Rightarrow> bool" where
  1:"verify_pratt [] = True"
| 2:"verify_pratt (Prime p#xs) \<longleftrightarrow> 1<p \<and> (\<exists> a . [a^(p - 1) = 1] (mod p) \<and> Triple p a (p - 1) \<in> set xs) \<and> verify_pratt xs"
| 3:"verify_pratt (Triple p a x # xs) \<longleftrightarrow> 0<x  \<and> (x=1 \<or>
                                       (\<exists>q y. x=q*y\<and> Prime q \<in> set xs \<and> Triple p a y \<in> set xs
                                        \<and> [a^((p - 1) div q) \<noteq> 1] (mod p)))
                                        \<and> verify_pratt xs"

lemma pratt_append: 
  assumes "verify_pratt r"
  assumes "verify_pratt s"
  shows "verify_pratt (r @ s)"
  using assms
  proof (induction r)
  case Nil then show ?case by simp
  next
  case (Cons y ys) show ?case using Cons by (cases y) auto
  qed

lemma verify_pratt_1 : 
   assumes "verify_pratt (y # ys)" 
   shows "verify_pratt ys"
   using assms
   by (cases y) auto

lemma prime_factors_one[simp]: shows "prime_factors (Suc 0) = {}"
  by rule (auto simp add:prime_factors_altdef2_nat)

lemma prime_factors_prime: fixes p :: nat assumes "prime p" shows "prime_factors p = {p}"
proof        
  have "0 < p" using assms by auto
  then show "{p} \<subseteq> prime_factors p" using assms  by (auto simp add:prime_factors_altdef2_nat)

  {
    fix q
    assume "q \<in> prime_factors p"
    then have "q dvd p" "prime q" using `0<p`  by (auto simp add:prime_factors_altdef2_nat)
    with assms have "q=p" by (auto simp: prime_nat_def)
    }
  then
  show "prime_factors p \<subseteq> {p}" by auto
qed

theorem pratt1:
  assumes 1: "verify_pratt c"
  assumes 2: "t \<in> set c"
  shows "(t = Prime p \<longrightarrow> prime p) \<and>
         (t = Triple p a x \<longrightarrow> ((\<forall> q \<in> prime_factors x . [a^((p - 1) div q) \<noteq> 1] (mod p)) \<and> 0<x))"
using assms
proof (induction c arbitrary: p a x t)
  case Nil then show ?case by force
  next
  case (Cons y ys)
  {
    have Schweinshaxn:"prime_factors (1::nat) = {}" by (simp add:prime_factors_one)
    assume "y=Triple p a x" "x=1"
    then have "(\<forall> q \<in> prime_factors x . [a^((p - 1) div q) \<noteq> 1] (mod p)) \<and> 0<x" using Schweinshaxn by simp
    }
  moreover
  {
    assume Brezn: "y=Triple p a x" "x~=1" then
    have Gnedl:"(\<exists>q y. x=q*y \<and> Prime q \<in> set ys \<and> Triple p a y \<in> set ys \<and> [a^((p - 1) div q) \<noteq> 1] (mod p))" "0 < x"  "verify_pratt ys"
      using Cons.prems by auto
    obtain q z where "x=q*z" "Prime q \<in> set ys \<and> Triple p a z \<in> set ys" and Obatzda:"[a^((p - 1) div q) \<noteq> 1] (mod p)" using Gnedl  by blast
    then have Bier:"(\<forall> r \<in> prime_factors z . [a^((p - 1) div r) \<noteq> 1] (mod p))" "prime q" "z>0"
      using Cons.IH Gnedl by auto
    then have "prime_factors x = prime_factors z \<union> {q}"  using `x =q*z` `x>0` by (simp add:prime_factors_product_nat prime_factors_prime)
    then have "(\<forall> q \<in> prime_factors x . [a^((p - 1) div q) \<noteq> 1] (mod p)) \<and> 0<x"
      using `x =q*z` Obatzda Bier `x>0` by simp
    }
  ultimately have Radisal:"y=Triple p a x \<Longrightarrow> (\<forall> q \<in> prime_factors x . [a^((p - 1) div q) \<noteq> 1] (mod p)) \<and> 0<x" by linarith

  {
    assume Brezn: "y=Prime p" "p>2" then
    have Gnedl:"(\<exists> a . [a^(p - 1) = 1] (mod p) \<and> Triple p a (p - 1) \<in> set ys)"  "verify_pratt ys"
       using Cons.prems by auto
    obtain a where  "[a^(p - 1) = 1] (mod p)"  "Triple p a (p - 1) \<in> set ys" using Gnedl by blast
    then have Bier:"(\<forall> q \<in> prime_factors (p - 1) . [a^((p - 1) div q) \<noteq> 1] (mod p))"
      using Cons.IH Gnedl by simp
    then have "prime(p)" using lehmer_extended[of "p" "a"] Gnedl Brezn by (metis `[a ^ (p - 1) = 1] (mod p)` le_eq_less_or_eq)
    }
  moreover
  {
    assume "y=Prime p" "p=2" then have "prime p" by simp
    }
  moreover
  {
    assume "y=Prime p" then have "p>1"  using Cons.prems  by simp
  }
  ultimately have  "y=Prime p ==> prime p" by linarith
  
  then show ?case using Radisal Cons.prems Cons.IH verify_pratt_1  by auto
qed


lemma concat_verify: "(\<forall>x \<in> set xs . verify_pratt x) \<Longrightarrow> verify_pratt (concat xs)"
 proof (induction xs)
 case Nil 
  thus ?case by simp
 next
 case (Cons y ys)
  have "verify_pratt y" using Cons.prems by auto
  moreover have "verify_pratt (concat ys)" using Cons by auto
  ultimately show ?case using "pratt_append" by simp
 qed

lemma cert_cons:
 assumes 1:"verify_pratt xs"
 assumes 2:"Prime q \<in> set xs"
 assumes 3:"Triple p a x \<in> set xs"
 assumes 4: "[a^((p - 1) div q) \<noteq> 1] (mod p)"
 assumes 5: "y=x*q"
 assumes 6: "x\<ge>1"
 shows "verify_pratt (Triple p a y # xs)"
 proof -
 have "q > 1" using 1 2 "pratt.2" "pratt.1" "pratt.3" by (metis "4" cong_refl_nat div_by_0 div_by_1 div_less nat_neq_iff one_not_prime_nat power_0 pratt1)
 hence "q>0" by auto
 have "y > 1" using 5 6 `q > 1` by (metis le_neq_implies_less less_1_mult mult_1 nat_mult_commute)
 thus ?thesis using assms "pratt.3" `q>0` by auto
qed

fun build_fpc' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> cert" where
  "build_fpc' p a r [] = [Triple p a r]" |
  "build_fpc' p a r (y # ys) = Triple p a r # build_fpc' p a (r div y) ys"

abbreviation (input) "build_fpc p a ys \<equiv> build_fpc' p a (p - 1) ys"

definition "listprod \<equiv> \<lambda>xs. foldr (op *) xs 1"

lemma listprod_Nil[simp]: "listprod [] = 1" by (simp add: listprod_def)
lemma listprod_Cons[simp]: "listprod (x # xs) = x * listprod xs" by (simp add: listprod_def)

lemma correct_fpc:
  assumes "verify_pratt xs"
  assumes "listprod qs = r" "r \<noteq> 0"
  assumes "\<forall> q \<in> set qs . Prime q \<in> set xs"
  assumes "\<forall> q \<in> set qs . [a^((p - 1) div q) \<noteq> 1] (mod p)"
  shows "verify_pratt (build_fpc' p a r qs @ xs)"
  using assms
proof (induction qs arbitrary: r)
  case Nil thus ?case by auto
next
  case (Cons y ys)
  have "listprod ys = r div y" using Cons.prems by auto
  then have T_in: "Triple p a (listprod ys) \<in> set (build_fpc' p a (r div y) ys @ xs)"
    by (cases ys) auto

  have "verify_pratt (build_fpc' p a (r div y) ys @ xs)"
    using Cons.prems by (intro Cons.IH) auto
  then have "verify_pratt (Triple p a r # build_fpc' p a (r div y) ys @ xs)"
    using `r \<noteq> 0` T_in Cons.prems by (intro cert_cons) auto (* XXX slow *)
  then show ?case by simp
qed

lemma concat_set:
 assumes 1: "\<forall> q \<in> qs . \<exists> c \<in> set cs . Prime q \<in> set c"
 shows "\<forall> q \<in> qs . Prime q \<in> set (concat cs)"
 using assms
 proof (induction cs)
 case Nil
  thus ?case by auto
 next
 case (Cons y ys)
  thus ?case by auto
 qed

lemma set_list:
  fixes "q"::nat
  shows "\<exists>qs. prime_factors q = set qs" by (metis finite_list finite_set_of prime_factors_nat_def)

lemma set_list':
  fixes "q"::nat
  shows "\<exists>qs. prime_factors q = set qs \<and> distinct qs" by (metis distinct_remdups set_list set_remdups)

fun oneof :: "'a set \<Rightarrow> 'a" where
 "oneof s = (SOME x . x \<in> s)" 

lemma set4:
 assumes 1:"finite p"
 assumes 2:"\<forall> q \<in> p. \<exists> e . P e q"
 shows "\<exists> s. finite s \<and> (\<forall> q \<in> p. \<exists> e \<in> s . P e q)" using assms
 proof -
  obtain s where s : "s = {oneof {e . P e q} | q . q \<in> p}" by auto
  {
   fix q
   assume q:"q \<in> p"
   obtain s' where s':"s' = {e . P e q}" by auto
   have "s' \<noteq> {}" using s' 2 q by auto
   obtain e where "e \<in> s'" using ` s' \<noteq> {}` by auto
   hence "oneof s' \<in> s'" using someI_ex[of "\<lambda> x. x \<in> s'"] by auto
   then obtain e' where e'1:"e' = oneof s'" and e'2:"e' \<in> s'" by auto
   hence e'3:"P e' q" using s' by auto
   have "e' = oneof {e . P e q}" using s' e'1 by auto
   hence "e' \<in> s" using q s by auto
   hence "\<exists> e \<in> s . P e q" using  e'3 by auto
  }
  hence s1:"\<forall> q \<in> p. \<exists> e \<in> s . P e q" by auto
  obtain f where "f = (\<lambda> x . oneof {e . P e x})" by auto
  hence "s = f ` p" using s by auto
  hence "finite s" using 1 by auto
 thus ?thesis using s1 by auto
 qed

lemma set_list2:
 fixes "p"::nat
 assumes "\<forall> q \<in> prime_factors (p - 1) . \<exists> e . P e q"
 shows "\<exists> s . \<forall> q \<in> prime_factors (p - 1) . \<exists> e \<in> set s . P e q"
 proof -
  have "finite (prime_factors (p - 1))" by blast
  then obtain s' where 1:"finite s' \<and> (\<forall> q \<in> prime_factors (p - 1) . \<exists> e \<in> s' . P e q)" using assms set4[of "prime_factors(p - 1)" "P"] by auto
  thus ?thesis by (metis finite_list)
 qed

lemma replicate_power :
 shows "foldr op * (replicate n p) 1 = p ^ n"
 apply (induction n)
 apply auto
 done

lemma product_distrb:
 shows "foldr op * xs (n::nat) = foldr op * xs 1 * n"
 apply (induction xs)
 apply auto
 done

lemma concat_map_product :
 shows "foldr op * (concat (l:: nat list list)) 1 = foldr op * (map (\<lambda> xs . foldr op * xs 1) l) 1" 
 proof (induction l)
 case Nil
  thus ?case by auto
 next
 case (Cons y ys)
 thus ?case using  product_distrb[of y "foldr op * (map (\<lambda>xs. foldr op * xs (Suc 0)) ys) (Suc 0)"] by auto
 qed

lemma foldr_prod:
 fixes "n"::nat
 assumes "distinct qs"
 shows "foldr op * (map (\<lambda> p . f p) qs) 1 = (\<Prod>p\<in>set qs. f p)"
 using assms
 apply (induction qs)
 apply auto
 done

lemma prime_factors_list:
 fixes "n"::nat
 assumes "0 < n"
 shows "\<exists> qs . prime_factors n = set qs \<and> foldr op * qs 1 = n"
 proof -
  obtain qs where qs:"set qs = prime_factors n \<and> distinct qs" using set_list'[of n] by auto
  obtain l where l:"l = concat (map (\<lambda>p . replicate (multiplicity p n) p) qs)" by auto
  {
   fix "p"::nat
   fix "n"::nat
   have "foldr op * (replicate (multiplicity p n) p) 1 = p ^ (multiplicity p n)" using replicate_power by fast
  } note multiplicity_replicate = this
  have 1:"foldr op * l 1 = foldr op * (map (\<lambda> p . p ^ (multiplicity p n)) qs) 1"
   proof -
    have "foldr op * l 1 = foldr op * (map (\<lambda> xs . foldr op * xs 1) (map (\<lambda>p . replicate (multiplicity p n) p) qs)) 1" using l concat_map_product by auto
    hence "foldr op * l 1 = foldr op * (map ((\<lambda>xs. foldr op * xs 1) \<circ> (\<lambda>p. replicate (multiplicity p n) p)) qs) 1" by auto
    hence "foldr op * l 1 = foldr op * (map (\<lambda>p. foldr op * (replicate (multiplicity p n) p) 1) qs) 1" using comp_def[of "\<lambda>xs. foldr op * xs 1" "\<lambda>p. replicate (multiplicity p n) p"] by auto
    thus ?thesis using multiplicity_replicate by auto
   qed
  have "foldr op * (map (\<lambda> p . p ^ (multiplicity p n)) qs) 1 = (\<Prod>p\<in>prime_factors n. p ^ multiplicity p n)" using qs foldr_prod[of "qs" "(\<lambda> p . p ^ (multiplicity p n))"] by auto
  hence 2:"foldr op * l 1 = n" using 1 prime_factorization_nat[of n] assms by auto
  have "set l = prime_factors n"
   proof
    {
     fix xs :: "nat list"
     fix x :: nat
     assume 1:"x \<in> set xs"
     assume 2:"\<forall> p \<in> set xs . multiplicity p n > 0"
     have "x \<in> set (concat (map (\<lambda>p . replicate (multiplicity p n) p) xs))"
      using 1 2
      apply (induction xs)
      apply auto
      done
    } note replicate_map_mem = this
    have 1:"\<forall> q \<in> set qs . multiplicity q n > 0" using qs by (metis One_nat_def Zero_not_Suc assms dvd_multiplicity_nat le0 multiplicity_prime_nat neq0_conv order_antisym prime_factors_dvd_nat prime_factors_prime_nat)
    hence "\<forall> q \<in> set qs . q \<in> set l" using l replicate_map_mem by auto
    thus "prime_factors n \<subseteq> set l" using qs by auto
    {
     fix xs :: "nat list"
     fix x :: nat
     assume 1:"x \<in> set (concat (map (\<lambda>p . replicate (multiplicity p n) p) xs))"
     have "x \<in> set xs"
      using 1
      apply (induction xs)
      apply auto
      done
    } 
    hence "\<forall> q \<in> set l . q \<in> set qs" using l by auto
    thus "set l \<subseteq> prime_factors n" using qs by auto
   qed
  thus ?thesis using 2 by auto
 qed

lemma bua:
  assumes 1:"prime p" 
  assumes 2:"\<forall>q \<in> prime_factors (p - 1) . (\<exists>c . ((Prime q \<in> set c) \<and> (verify_pratt c)))"
  assumes 3:"[a^(p - 1) = 1] (mod p) \<and> (\<forall> q. q \<in> prime_factors (p - 1) \<longrightarrow> [a^((p - 1) div q) \<noteq> 1] (mod p))"
  shows "\<exists>c. ((Triple p a (p - 1)  \<in> set c) \<and> (verify_pratt c))"
proof -
  have "p - 1 > 0" using "1" prime_gt_1_nat by auto
  obtain qs' where Kasgrilla:"(foldr (\<lambda> x acc . x*acc) qs' 1)=(p - 1)" and Kasgrilla2:"(set qs' = prime_factors (p - 1))" using prime_factors_list[of "p - 1"] `p - 1 > 0` by auto
  then have Kasgrilla': "listprod qs'= p - 1" by (simp add: listprod_def)
  obtain qs where Grillwurst:"set qs = prime_factors (p - 1)" using set_list[of "p - 1"] by fast
  obtain cs' where cs'_1:"\<forall>q \<in> prime_factors (p - 1) . (\<exists>c \<in> set cs' . ((Prime q \<in> set c) \<and> (verify_pratt c)))" using set_list2[OF 2] by auto
  obtain cs where cs_1:"cs = filter verify_pratt cs'" by auto
  have cs_3: "\<forall>q \<in> prime_factors (p - 1) . (\<exists>c \<in> set cs . ((Prime q \<in> set c) \<and> (verify_pratt c)))" using cs'_1 cs_1 by auto
  have "\<forall> x \<in> set cs . verify_pratt x" using cs'_1 cs_1 by auto
  then have c_fpc1:"verify_pratt (concat cs)" using concat_verify [of "cs"] by blast
  have c_fpc2: "\<forall> q \<in> set qs' . [a^((p - 1) div q) \<noteq> 1] (mod p)" using Kasgrilla2 Grillwurst 3 by auto
  have c_fpc3: "\<forall> q \<in> set qs' . Prime q \<in> set (concat cs)" using concat_set cs_3 Kasgrilla2 by auto
  then have Weisswurst2:"verify_pratt ((build_fpc p a qs')@concat cs)"
    using `_ > 0` correct_fpc[OF c_fpc1 Kasgrilla' _ c_fpc3 c_fpc2] by simp
  have "(Triple p a (p - 1)) \<in> set ((build_fpc p a qs')@concat cs)" by (cases qs') auto
  then show ?thesis using Weisswurst2 by blast
qed

lemma bla: 
  assumes 1:"prime (p::nat)"
  assumes 2:"\<forall>q \<in> prime_factors (p - 1) . (\<exists>c . ((Prime q \<in> set c) \<and> (verify_pratt c)))"
  shows "\<exists>c . ((Prime p \<in> set c) \<and> (verify_pratt c))"
  proof -
  obtain a' where  Reibadatsche:"([a'^(p - 1) = 1] (mod p) \<and> (\<forall> q. q \<in> prime_factors (p - 1) \<longrightarrow> [a'^((p - 1) div q) \<noteq> 1] (mod p)))" using lehmer_extended_backwards[OF 1] by blast
  then obtain c' where Schweinshax:"(Triple p a' (p - 1)  \<in> set c')" and Reibagnedl:"(verify_pratt c')" using bua[OF 1 2 Reibadatsche] by blast
  then have Gickal:"verify_pratt (Prime p#c')" using Reibadatsche 1 by auto
  show ?thesis using Gickal by (metis hd.simps hd_in_set list.simps(2))
  qed

lemma size_primefactors:
fixes "x"::nat
fixes "n"::nat
assumes "x\<in>prime_factors n"
assumes "n>0"
shows "x<=n" using prime_factors_altdef2_nat[of "n" "x"] assms by (metis dvd_imp_le)

theorem pratt_complete:
  assumes 1:"prime p"
  shows "\<exists>c . ((Prime p \<in> set c) \<and> (verify_pratt c))"
  using assms
  proof (induction p rule: less_induct)
  have 2:"p \<ge> 2" using 1 by fast
  case (less x)
    then have "x>1" by (metis prime_gt_1_nat)
    then have "\<forall>q \<in> prime_factors (x - 1) . q < x" using size_primefactors by fastforce
    then have "\<forall>q \<in> prime_factors (x - 1) . (\<exists>c . ((Prime q \<in> set c) \<and> (verify_pratt c)))" using less.IH by blast
    then show ?case using bla less.prems by fast
qed

unused_thms
