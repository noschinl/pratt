theory Algebra_Stuff
imports
  Main
  "~~/src/HOL/Algebra/Group"
  "~~/src/HOL/GCD"
  "~~/src/HOL/Number_Theory/MiscAlgebra"
  "~~/src/HOL/Algebra/Coset"
  "~~/src/HOL/Algebra/UnivPoly"
begin

section {* Stuff *}

lemma dvd_gcd :
  fixes a b :: nat
  obtains q where "a * (b div gcd a b) = b*q"
proof
  have "a * (b div gcd a b) = (a div gcd a b) * b" by (simp add:  div_mult_swap dvd_div_mult)
  also have "\<dots> = b * (a div gcd a b)" by simp
  finally show "a * (b div gcd a b) = b * (a div gcd a b) " .
qed

(* XXX to Nat.thy? *)
lemma nat_div_eq: "a \<noteq> 0 \<Longrightarrow> (a :: nat) div b = a \<longleftrightarrow> b = 1"
  apply rule
  apply (cases "b = 0")
  apply simp_all
  apply (metis (full_types) One_nat_def Suc_lessI div_less_dividend less_not_refl3)
  done


section {* Properties of the Euler @{text \<phi>} function *}

lemma dvd_div_ge_1 :
  fixes a b :: nat
  assumes "a \<ge> 1" "b dvd a"
  shows "a div b \<ge> 1" 
  by (metis assms div_by_1 div_dvd_div div_less gcd_lcm_complete_lattice_nat.top_greatest
      gcd_lcm_complete_lattice_nat.top_le not_less)

lemma dvd_nat_bounds :
 fixes n p :: nat
 assumes "p > 0" "n dvd p"
 shows "n > 0 \<and> n \<le> p" 
 using assms by (simp add: dvd_pos_nat dvd_imp_le)

text {* Deviates from the definition given in the library in number theory *} 
definition phi' :: "nat => nat"
  where "phi' m = card {x. 1 \<le> x \<and> x \<le> m \<and> gcd x m = 1}"

lemma phi'_nonzero :
  assumes "m > 0"
  shows "phi' m > 0"
proof -
  have "1 \<in> {x. 1 \<le> x \<and> x \<le> m \<and> gcd x m = 1}" using assms by simp
  hence "card {x. 1 \<le> x \<and> x \<le> m \<and> gcd x m = 1} > 0" by (auto simp: card_gt_0_iff)
  thus ?thesis unfolding phi'_def by simp
qed 

lemma sum_phi'_factors :
 fixes n :: nat
 assumes "n > 0"
 shows "(\<Sum>d \<in> {d . d dvd n} . phi' d) = n"
proof -
  let ?f = "\<lambda> d . {m . m \<in> {1 .. n} \<and> n div gcd m n = d}"
  { fix d :: nat
    assume d:"d dvd n"
    { fix m::nat
      assume m:"m \<in> {1 .. n} \<and> n div gcd m n = d"
      hence gcd_1:"gcd (m div gcd m n) d = 1" using assms div_gcd_coprime_nat by blast
      have ge_1:"1 \<le> m div gcd m n" using m dvd_div_ge_1 by auto
      have le_d:"m div gcd m n \<le> d" using m by (auto simp add: div_le_mono)
      have "m div gcd m n * n = m * n div gcd m n" 
        by (simp add: nat_mult_commute div_mult_swap[OF gcd_dvd1_nat[of m n], of n])
      also have "\<dots> = m * d" 
        by (simp add: m div_mult_swap[OF gcd_dvd2_nat[of m n], of m, symmetric])
      finally have "m div gcd m n * n div d = m" 
        using d assms by (auto simp add:)
      hence "m \<in> {a * n div d | a . 1 \<le> a \<and> a \<le> d \<and> gcd a d = 1}" using gcd_1 le_d ge_1 by force }
     moreover
     { fix a :: nat
       assume a:"1 \<le> a \<and> a \<le> d \<and> gcd a d = 1"
       hence "a * (n div d) \<ge> 1" using assms dvd_div_ge_1[OF _ d] by simp
       hence ge_1:"a * n div d \<ge> 1" by (simp add: d div_mult_swap)
       have "a * n div d \<le> a * (n div d)" using a by (simp add: d div_mult_swap)
       also have "\<dots> \<le> d * (n div d)" using a by simp
       finally have le_n:"a * n div d \<le> n" by (simp add: d dvd_mult_div_cancel)
       have "gcd (a * n div d) n = gcd (a * n div d) (d * n div d)" 
        using dvd_div_mult_self[OF d] by auto
       also have "\<dots> = gcd (n div d * a) (n div d * d)"
        by (simp add: d div_mult_swap nat_mult_commute)
       also have "\<dots> = n div d * gcd a d" by (simp add: gcd_mult_distrib_nat)
       finally have "gcd (a * n div d) n = n div d" using a by simp
       hence "n div gcd (a * n div d) n = d*n div (d*(n div d))" by simp
       also have "\<dots> = d" using assms by (simp add: d dvd_mult_div_cancel)
       finally have "a * n div d \<in> {m . m \<in> {1 .. n} \<and> n div gcd m n = d}"
        using ge_1 le_n by fastforce }
     ultimately have "{a * n div d | a . 1 \<le> a \<and> a \<le> d \<and> gcd a d = 1} 
                      = {m . m \<in> {1 .. n} \<and> n div gcd m n = d}" by blast
  }
  hence d_seteq:"\<And> d . d dvd n \<Longrightarrow> card {a * n div d | a . 1 \<le> a \<and> a \<le> d \<and> gcd a d = 1}
                                   = card {m . m \<in> {1 .. n} \<and> n div gcd m n = d}" by presburger
  { fix d
    assume d:"d dvd n"
    have "card {a * n div d | a . 1 \<le> a \<and> a \<le> d \<and> gcd a d = 1}
          = card {a . 1 \<le> a \<and> a \<le> d \<and> gcd a d = 1}"
    proof -
      {
        fix x y assume "x * n div d =  y * n div d"
        hence "x * (n div d) = y * (n div d)" by (simp add: div_mult_swap[OF d])
        have "0 < d \<and> d \<le> n" using d dvd_nat_bounds `n>0` by blast
        hence "n div d > 0" using `n>0` dvd_div_ge_1[OF _ d] by linarith
        hence "x = y" using d `x * (n div d) = y * (n div d)` by auto
      }
      hence "inj_on (\<lambda> a . a * n div d) {a . 1 \<le> a \<and> a \<le> d \<and> gcd a d = 1}" 
         using inj_on_def by blast
      hence "bij_betw (\<lambda> a . a * n div d) {a . 1 \<le> a \<and> a \<le> d \<and> gcd a d = 1}
             {a * n div d | a . 1 \<le> a \<and> a \<le> d \<and> gcd a d = 1}" by (auto simp add: bij_betw_def)
      thus ?thesis using bij_betw_same_card by force
    qed
  }
  hence "\<And> d . d dvd n \<Longrightarrow> card {a . 1 \<le> a \<and> a \<le> d \<and> gcd a d = 1}
         = card {m . m \<in> {1 .. n} \<and> n div gcd m n = d}" using d_seteq by auto
  hence "\<And> d . d dvd n \<Longrightarrow> phi' d = card {m . m \<in> {1 .. n} \<and> n div gcd m n = d}" 
     using phi'_def by auto
  hence sum_eq1:"(\<Sum>d \<in> {d . d \<in> (UNIV :: nat set) \<and> d dvd n} . phi' d)  =
                 (\<Sum>d \<in> {d . d \<in> (UNIV :: nat set) \<and> d dvd n}.
                         card {m . m \<in> {1 .. n} \<and> n div gcd m n = d})" by auto
  {
    fix i j :: nat assume ij:"i \<noteq> j"
    hence "{m. m \<in> {1 .. n} \<and> n div gcd m n = i} \<inter> {m . m \<in> {1 .. n} \<and> n div gcd m n = j} = {}" 
          by auto
  } note sets_disjoint = this
  have fin:"finite {d . d \<in> UNIV \<and> d dvd n}" using dvd_nat_bounds `n>0` by force
  have sum_card:"(\<Sum>d \<in> {d . d \<in> UNIV \<and> d dvd n} . phi' d) = card (UNION {d . d \<in> UNIV \<and> d dvd n}
                  (\<lambda> d . {m . m \<in> {1 .. n} \<and> n div gcd m n = d}))" 
                  using Big_Operators.card_UN_disjoint[OF fin,
                        of "(\<lambda> d . {m . m \<in> {1 .. n} \<and> n div gcd m n = d})"] sets_disjoint sum_eq1
                  by auto
  have "UNION {d . d \<in> UNIV \<and> d dvd n} (\<lambda> d . {m . m \<in> {1 .. n} \<and> n div gcd m n = d}) = {1 .. n}"
  proof
    show "(\<Union>d\<in>{d \<in> UNIV. d dvd n}. {m \<in> {1..n}. n div gcd m n = d}) \<subseteq> {1..n}" by fast
    { fix m assume m : "m \<in> {1 .. n}"
      hence  "(n div gcd m n) dvd n" 
        using dvd_triv_right[of "n div gcd m n" "gcd m n"] by (simp add: dvd_mult_div_cancel)
      hence "m \<in> (\<Union>d\<in>{d \<in> UNIV. d dvd n}. {m \<in> {1..n}. n div gcd m n = d})" using m by blast }
    thus "{1..n} \<subseteq> (\<Union>d\<in>{d \<in> UNIV. d dvd n}. {m \<in> {1..n}. n div gcd m n = d})" by auto
  qed
  thus ?thesis using sum_card by force
qed


section {* Order of an element *}

context group begin

lemma pow_eq_div2 :
  fixes m n :: nat
  assumes x_car: "x \<in> carrier G"
  assumes pow_eq: "x (^) m = x (^) n"
  shows "x (^) (m - n) = \<one>"
proof (cases "m < n")
  case False
  have "\<one> \<otimes> x (^) m = x (^) m" by (simp add: x_car)
  also have "\<dots> = x (^) (m - n) \<otimes> x (^) n"
    using False by (simp add: nat_pow_mult x_car)
  also have "\<dots> = x (^) (m - n) \<otimes> x (^) m"
    by (simp add: pow_eq)
  finally show ?thesis by (simp add: x_car)
qed simp

definition ord where "ord a = Min {d \<in> {1 .. order G} . a (^) d = \<one>}"

lemma
  assumes finite:"finite (carrier G)"
  assumes a:"a \<in> carrier G"
  shows ord_ge_1: "1 \<le> ord a" and ord_le_group_order: "ord a \<le> order G"
    and pow_ord_eq_1: "a (^) ord a = \<one>" 
proof -
  have "\<not>inj_on (\<lambda>x . a (^) x) {0 .. order G}"
  proof (rule notI)
    assume A: "inj_on (\<lambda>x . a (^) x) {0 .. order G}"
    have "order G + 1 = card {0 .. order G}" by simp
    also have "\<dots> = card ((\<lambda>x . a (^) x) ` {0 .. order G})" (is "_ = card ?S")
      using A by (simp add: card_image)
    also have "?S = {a (^) x | x . x \<in> {0 .. order G}}" by blast
    also have "\<dots> \<subseteq> carrier G" (is "?S \<subseteq> _") using a by blast
    then have "card ?S \<le> order G" unfolding order_def
      by (rule card_mono[OF finite])
    finally show False by arith
  qed

  then obtain x y where x_y:"x \<noteq> y" "x \<in> {0 .. order G}" "y \<in> {0 .. order G}"
                        "a (^) x = a (^) y" unfolding inj_on_def by blast
  obtain d where "1 \<le> d" "a (^) d = \<one>" "d \<le> order G"
  proof cases
    assume "y < x" with x_y show ?thesis
      by (intro that[where d="x - y"]) (auto simp add: pow_eq_div2[OF a])
  next
    assume "\<not>y < x" with x_y show ?thesis
      by (intro that[where d="y - x"]) (auto simp add: pow_eq_div2[OF a])
  qed
  hence "ord a \<in> {d \<in> {1 .. order G} . a (^) d = \<one>}"
    unfolding ord_def using Min_in[of "{d \<in> {1 .. order G} . a (^) d = \<one>}"]
    by fastforce
  then show "1 \<le> ord a" and "ord a \<le> order G" and "a (^) ord a = \<one>"
    by (auto simp: order_def)
qed

lemma finite_group_elem_finite_ord :
  assumes "finite (carrier G)" "x \<in> carrier G"
  shows "\<exists> d::nat. d \<ge> 1 \<and> x (^) d = \<one>"
  using assms ord_ge_1 pow_ord_eq_1 by auto

lemma ord_min:
  assumes  "finite (carrier G)" "1 \<le> d" "a \<in> carrier G" "a (^) d = \<one>" shows "ord a \<le> d"
proof -
  def Ord \<equiv> "{d \<in> {1..order G}. a (^) d = \<one>}"
  have fin: "finite Ord" by (auto simp: Ord_def)
  have in_ord: "ord a \<in> Ord"
    using assms pow_ord_eq_1 ord_ge_1 ord_le_group_order by (auto simp: Ord_def)
  then have "Ord \<noteq> {}" by auto

  show ?thesis
  proof (cases "d \<le> order G")
    case True
    then have "d \<in> Ord" using assms by (auto simp: Ord_def)
    with fin in_ord show ?thesis
      unfolding ord_def Ord_def[symmetric] by simp
  next
    case False
    then show ?thesis using in_ord by (simp add: Ord_def)
  qed
qed

lemma ord_inj :
  assumes finite: "finite (carrier G)"
  assumes a: "a \<in> carrier G"
  shows "inj_on (\<lambda> x . a (^) x) {0 .. ord a - 1}"
proof (rule inj_onI, rule ccontr)
  fix x y assume A: "x \<in> {0 .. ord a - 1}" "y \<in> {0 .. ord a - 1}" "a (^) x= a (^) y" "x \<noteq> y"

  have "finite {d \<in> {1..order G}. a (^) d = \<one>}" by auto

  { fix x y assume A: "x < y" "x \<in> {0 .. ord a - 1}" "y \<in> {0 .. ord a - 1}"
        "a (^) x = a (^) y"
    hence "y - x < ord a" by auto
    also have "\<dots> \<le> order G" using assms by (simp add: ord_le_group_order)
    finally have y_x_range:"y - x \<in> {1 .. order G}" using A by force
    have "a (^) (y-x) = \<one>" using a A by (simp add: pow_eq_div2)
    
    hence y_x:"y - x \<in> {d \<in> {1.. order G}. a (^) d = \<one>}" using y_x_range by blast
    have "min (y - x) (ord a) = ord a"
      using Min.in_idem[OF `finite {d \<in> {1 .. order G} . a (^) d = \<one>}` y_x] ord_def by auto
    with `y - x < ord a` have False by linarith
  }
  note X = this

  { assume "x < y" with A X have False by blast }
  moreover
  { assume "x > y" with A X  have False by metis }
  moreover
  { assume "x = y" then have False using A by auto}
  ultimately
  show False by fastforce
qed

lemma ord_elems :
  assumes "finite (carrier G)" "a \<in> carrier G"
  shows "{a(^)x| x . x \<in> (UNIV :: nat set)} = {a(^)x| x . x \<in> {0 .. ord a - 1}}" (is "?L = ?R")
proof
  show "?R \<subseteq> ?L" by blast
  { fix y assume "y \<in> ?L"
    then obtain x::nat where x:"y = a(^)x" by auto
    def r \<equiv> "x mod ord a"
    then obtain q where q:"x = q * ord a + r" using mod_eqD by atomize_elim presburger
    hence "y = (a(^)ord a)(^)q \<otimes> a(^)r" 
      using x assms by (simp add: nat_mult_commute nat_pow_mult nat_pow_pow)
    hence "y = a(^)r" using assms by (simp add: pow_ord_eq_1)
    have "r < ord a" using ord_ge_1[OF assms] by (simp add: r_def)
    hence "r \<in> {0 .. ord a - 1}" by (force simp: r_def)
    hence "y \<in> {a(^)x| x . x \<in> {0 .. ord a - 1}}" using `y=a(^)r` by blast
  }
  thus "?L \<subseteq> ?R" by auto
qed

lemma ord_dvd_pow_eq_1 :
  assumes "finite (carrier G)" "a \<in> carrier G" "a (^) k = \<one>"
  shows "ord a dvd k"
proof -
  def r \<equiv> "k mod ord a"
  then obtain q where q:"k = q*ord a + r" using mod_eqD by atomize_elim presburger
  hence "a(^)k = (a(^)ord a)(^)q \<otimes> a(^)r" 
      using assms by (simp add: nat_mult_commute nat_pow_mult nat_pow_pow)
  hence "a(^)k = a(^)r" using assms by (simp add: pow_ord_eq_1)
  hence "a(^)r = \<one>" using assms(3) by simp
  have "r < ord a" using ord_ge_1[OF assms(1-2)] by (simp add: r_def)
  hence "r = 0" using `a(^)r = \<one>` ord_def[of a] ord_min[of r a] assms(1-2) by linarith
  thus ?thesis using q by simp
qed

lemma ord_pow_dvd_ord_elem :
  assumes finite[simp]: "finite (carrier G)"
  assumes a[simp]:"a \<in> carrier G" 
  shows "ord (a(^)n) = ord a div gcd n (ord a)"
proof -
  have "(a(^)n) (^) ord a = (a (^) ord a) (^) n" 
    by (simp add: nat_mult_commute nat_pow_pow)
  hence "(a(^)n) (^) ord a = \<one>" by (simp add: pow_ord_eq_1)
  obtain q where "n * (ord a div gcd n (ord a)) = ord a * q" by (rule dvd_gcd)
  hence "(a(^)n) (^) (ord a div gcd n (ord a)) = (a (^) ord a)(^)q"  by (simp add : nat_pow_pow)
  hence pow_eq_1: "(a(^)n) (^) (ord a div gcd n (ord a)) = \<one>" 
     by (auto simp add : pow_ord_eq_1[of a])
  have "ord a \<ge> 1" using ord_ge_1 by simp
  have ge_1:"ord a div gcd n (ord a) \<ge> 1"
  proof -
    have "gcd n (ord a) dvd ord a" by blast
    thus ?thesis by (rule dvd_div_ge_1[OF `ord a \<ge> 1`])
  qed
  have "ord a \<le> order G" by (simp add: ord_le_group_order)
  have "ord a div gcd n (ord a) \<le> order G"
  proof -
    have "ord a div gcd n (ord a) \<le> ord a" by simp
    thus ?thesis using `ord a \<le> order G` by linarith
  qed
  hence ord_gcd_elem:"ord a div gcd n (ord a) \<in> {d \<in> {1..order G}. (a(^)n) (^) d = \<one>}" 
    using ge_1 pow_eq_1 by force
  { fix d :: nat
    assume d_elem:"d \<in> {d \<in> {1..order G}. (a(^)n) (^) d = \<one>}"
    assume d_lt:"d < ord a div gcd n (ord a)"
    hence pow_nd:"a(^)(n*d)  = \<one>" using d_elem 
      by (simp add : nat_pow_pow)
    hence "ord a dvd n*d" using assms by (auto simp add : ord_dvd_pow_eq_1)
    then obtain q where "ord a * q = n*d" by (metis dvd_mult_div_cancel)
    hence prod_eq:"(ord a div gcd n (ord a)) * q = (n div gcd n (ord a)) * d" 
      by (simp add: dvd_div_mult)
    have cp:"coprime (ord a div gcd n (ord a)) (n div gcd n (ord a))"
    proof -
      have "coprime (n div gcd n (ord a)) (ord a div gcd n (ord a))" 
        using div_gcd_coprime_nat[of n "ord a"] ge_1 by fastforce
      thus ?thesis by (simp add: gcd_commute_nat)
    qed
    have dvd_d:"(ord a div gcd n (ord a)) dvd d"
    proof -
      have "ord a div gcd n (ord a) dvd (n div gcd n (ord a)) * d" using prod_eq 
        by (metis dvd_triv_right nat_mult_commute)
      hence "ord a div gcd n (ord a) dvd d * (n div gcd n (ord a))" 
        by (simp add:  nat_mult_commute)
      thus ?thesis using coprime_dvd_mult_nat[OF cp, of d] by fastforce
    qed
    have "d > 0" using d_elem by simp
    hence "ord a div gcd n (ord a) \<le> d" using dvd_d by (simp add : Nat.dvd_imp_le)
    hence False using d_lt by simp
  } hence ord_gcd_min: "\<And> d . d \<in> {d \<in> {1..order G}. (a(^)n) (^) d = \<one>}
                        \<Longrightarrow> d\<ge>ord a div gcd n (ord a)" by fastforce
  have fin:"finite {d \<in> {1..order G}. (a(^)n) (^) d = \<one>}" by auto
  thus ?thesis using Min_eqI[OF fin ord_gcd_min ord_gcd_elem] 
    unfolding ord_def by simp
qed

lemma ord_1_eq_1 :
  assumes "finite (carrier G)"
  shows "ord \<one> = 1"
 using assms ord_ge_1 ord_min[of 1 \<one>] by force

theorem lagrange_dvd:
 assumes "finite(carrier G)" "subgroup H G" shows "(card H) dvd (order G)"
 using assms by (simp add: lagrange[symmetric])

lemma element_generates_subgroup:
  assumes finite[simp]: "finite (carrier G)"
  assumes a[simp]: "a \<in> carrier G"
  shows "subgroup {a (^) i | i . i \<in> {0 .. ord a - 1}} G"
proof
  show "{a(^)i | i . i \<in> {0 .. ord a - 1} } \<subseteq> carrier G" by auto
next
  fix x y
  assume A: "x \<in> {a(^)i | i . i \<in> {0 .. ord a - 1}}" "y \<in> {a(^)i | i . i \<in> {0 .. ord a - 1}}"
  obtain i::nat where i:"x = a(^)i" and i2:"i \<in> UNIV" using A by auto
  obtain j::nat where j:"y = a(^)j" and j2:"j \<in> UNIV" using A by auto
  have "a(^)(i+j) \<in> {a(^)i | i . i \<in> {0 .. ord a - 1}}" using ord_elems[OF assms] A by auto
  thus "x \<otimes> y \<in> {a(^)i | i . i \<in> {0 .. ord a - 1}}" 
    using i j a ord_elems assms by (auto simp add: nat_pow_mult)
next
  show "\<one> \<in> {a(^)i | i . i \<in> {0 .. ord a - 1}}" by force
next
  fix x assume x: "x \<in> {a(^)i | i . i \<in> {0 .. ord a - 1}}"
  hence x_in_carrier: "x \<in> carrier G" by auto
  then obtain d::nat where d:"x (^) d = \<one>" and "d\<ge>1" 
    using finite_group_elem_finite_ord by auto
  have inv_1:"x(^)(d - 1) \<otimes> x = \<one>" using `d\<ge>1` d nat_pow_Suc[of x "d - 1"] by simp
  have elem:"x (^) (d - 1) \<in> {a(^)i | i . i \<in> {0 .. ord a - 1}}"
  proof -
    obtain i::nat where i:"x = a(^)i" using x by auto
    hence "x(^)(d - 1) \<in> {a(^)i |i. i \<in> (UNIV::nat set)}" by (auto simp add: nat_pow_pow)
    thus ?thesis using ord_elems[of a] by auto
  qed
  have inv:"inv x = x(^)(d - 1)" using inv_equality[OF inv_1] x_in_carrier by blast
  thus "inv x \<in> {a(^)i | i . i \<in> {0 .. ord a - 1}}" using elem inv by auto
qed

lemma ord_dvd_group_order :
  assumes finite[simp]: "finite (carrier G)"
  assumes a[simp]: "a \<in> carrier G"
  shows "ord a dvd order G"
proof -
  have card_dvd:"card {a(^)i | i . i \<in> {0 .. ord a - 1}} dvd card (carrier G)" 
    using lagrange_dvd element_generates_subgroup unfolding order_def by simp
  have "inj_on (\<lambda> i . a(^)i) {0..ord a - 1}" using ord_inj by simp
  hence cards_eq:"card ( (\<lambda> i . a(^)i) ` {0..ord a - 1}) = card {0..ord a - 1}" 
    using card_image[of "\<lambda> i . a(^)i" "{0..ord a - 1}"] by auto
  have "(\<lambda> i . a(^)i) ` {0..ord a - 1} = {a(^)i |i. i \<in> {0..ord a - 1}}" by auto
  hence "card {a(^)i |i. i \<in> {0..ord a - 1}} = card {0..ord a - 1}" using cards_eq by simp
  also have "\<dots> = ord a" using ord_ge_1[of a] by simp
  finally show ?thesis using card_dvd by (simp add: order_def)
qed

end

section {* Algebra *}

definition mult_of :: "('a, 'b) ring_scheme \<Rightarrow> 'a monoid" where 
  "mult_of R \<equiv> \<lparr> carrier = carrier R - {\<zero>\<^bsub>R\<^esub>}, mult = mult R, one = \<one>\<^bsub>R\<^esub>\<rparr>"

lemma carrier_mult_of: "carrier (mult_of R) = carrier R - {\<zero>\<^bsub>R\<^esub>}"
  by (simp add: mult_of_def)

lemma mult_mult_of: "mult (mult_of R) = mult R"
 by (simp add: mult_of_def)

lemma nat_pow_mult_of: "op (^)\<^bsub>mult_of R\<^esub> = (op (^)\<^bsub>R\<^esub> :: _ \<Rightarrow> nat \<Rightarrow> _)"
  by (simp add: mult_of_def fun_eq_iff nat_pow_def)

lemma one_mult_of: "\<one>\<^bsub>mult_of R\<^esub> = \<one>\<^bsub>R\<^esub>"
  by (simp add: mult_of_def)

lemmas mult_of_simps = carrier_mult_of mult_mult_of nat_pow_mult_of one_mult_of

context field begin

lemma field_mult_group :
  shows "group (mult_of R)"
  apply (rule groupI)
  apply (auto simp: mult_of_simps m_assoc dest: integral)
  by (metis Diff_iff Units_inv_Units Units_l_inv field_Units singletonE)

lemma finite_mult_of: "finite (carrier R) \<Longrightarrow> finite (carrier (mult_of R))"
  by (auto simp: mult_of_simps)

lemma order_mult_of: "finite (carrier R) \<Longrightarrow> order (mult_of R) = order R - 1"
  unfolding order_def carrier_mult_of by (simp add: card.remove)

end



lemma (in monoid) Units_pow_closed :
  fixes d :: nat
  assumes "x \<in> Units G"
  shows "x (^) d \<in> Units G" 
    by (metis assms group.is_monoid monoid.nat_pow_closed units_group units_of_carrier units_of_pow)

lemma (in comm_monoid) is_monoid:
  shows "monoid G" by unfold_locales

declare comm_monoid.is_monoid[intro?]

lemma (in ring) r_right_minus_eq[simp]:
  assumes "a \<in> carrier R" "b \<in> carrier R"
  shows "a \<ominus> b = \<zero> \<longleftrightarrow> a = b"
  using assms by (metis a_minus_def add.inv_closed minus_equality r_neg)

context UP_cring begin

lemma is_UP_cring:"UP_cring R" by (unfold_locales)
lemma is_UP_ring :
  shows "UP_ring R" by (unfold_locales)

end

context UP_domain begin


lemma roots_bound:
  assumes f [simp]: "f \<in> carrier P" 
  assumes f_not_zero: "f \<noteq> \<zero>\<^bsub>P\<^esub>"
  assumes finite: "finite (carrier R)"
  shows "finite {a \<in> carrier R . eval R R id a f = \<zero>} \<and>
         card {a \<in> carrier R . eval R R id a f = \<zero>} \<le> deg R f" using f f_not_zero
proof (induction "deg R f" arbitrary: f)
  case 0
  have "\<And>x. eval R R id x f \<noteq> \<zero>"
  proof -
    fix x
    have "(\<Oplus>i\<in>{..deg R f}. id (coeff P f i) \<otimes> x (^) i) \<noteq> \<zero>" 
      using 0 lcoeff_nonzero_nonzero[where p = f] by simp
    thus "eval R R id x f \<noteq> \<zero>" using 0 unfolding eval_def P_def by simp
  qed
  then have *: "{a \<in> carrier R. eval R R (\<lambda>a. a) a f = \<zero>} = {}"
    by (auto simp: id_def)
  show ?case by (simp add: *)
next
  case (Suc x)
  show ?case
  proof (cases "\<exists> a \<in> carrier R . eval R R id a f = \<zero>")
    case True
    then obtain a where a_carrier[simp]: "a \<in> carrier R" and a_root:"eval R R id a f = \<zero>" by blast
    have R_not_triv: "carrier R \<noteq> {\<zero>}"
      by (metis R.one_zeroI R.zero_not_one)
    obtain q  where q:"(q \<in> carrier P)" and 
      f:"f = (monom P \<one>\<^bsub>R\<^esub> 1 \<ominus>\<^bsub> P\<^esub> monom P a 0) \<otimes>\<^bsub>P\<^esub> q \<oplus>\<^bsub>P\<^esub> monom P (eval R R id a f) 0"
     using remainder_theorem[OF Suc.prems(1) a_carrier R_not_triv] by (atomize_elim)
    hence lin_fac: "f = (monom P \<one>\<^bsub>R\<^esub> 1 \<ominus>\<^bsub> P\<^esub> monom P a 0) \<otimes>\<^bsub>P\<^esub> q" using q by (simp add: a_root)
    have deg:"deg R (monom P \<one>\<^bsub>R\<^esub> 1 \<ominus>\<^bsub> P\<^esub> monom P a 0) = 1"
      using a_carrier by (simp add: deg_minus_eq)
    hence mon_not_zero:"(monom P \<one>\<^bsub>R\<^esub> 1 \<ominus>\<^bsub> P\<^esub> monom P a 0) \<noteq> \<zero>\<^bsub>P\<^esub>"
      by (fastforce simp del: r_right_minus_eq)
    have q_not_zero:"q \<noteq> \<zero>\<^bsub>P\<^esub>" using Suc by (auto simp add : lin_fac)
    hence "deg R q = x" using Suc deg deg_mult[OF mon_not_zero q_not_zero _ q]
      by (simp add : lin_fac)
    hence q_IH:"finite {a \<in> carrier R . eval R R id a q = \<zero>} 
                \<and> card {a \<in> carrier R . eval R R id a q = \<zero>} \<le> x" using Suc q q_not_zero by blast
    have subs:"{a \<in> carrier R . eval R R id a f = \<zero>} 
                \<subseteq> {a \<in> carrier R . eval R R id a q = \<zero>} \<union> {a}" (is "?L \<subseteq> ?R \<union> {a}")
      using a_carrier `q \<in> _`
      by (auto simp: evalRR_simps lin_fac R.integral_iff)
    have "{a \<in> carrier R . eval R R id a f = \<zero>} \<subseteq> insert a {a \<in> carrier R . eval R R id a q = \<zero>}"
     using subs by auto
    hence "card {a \<in> carrier R . eval R R id a f = \<zero>} \<le>
           card (insert a {a \<in> carrier R . eval R R id a q = \<zero>})" using q_IH by (blast intro: card_mono)
    also have "\<dots> \<le> deg R f" using q_IH `Suc x = _`
      by (simp add: card_insert_if)
    finally show ?thesis using q_IH `Suc x = _` using finite by force
  next
    case False
    hence "card {a \<in> carrier R. eval R R id a f = \<zero>} = 0" using finite by auto
    also have "\<dots> \<le>  deg R f" by simp
    finally show ?thesis using finite by auto
  qed
qed

end

lemma (in domain) num_roots_le_deg :
  fixes p d :: nat
  assumes finite:"finite (carrier R)"
  assumes d_neq_zero : "d \<noteq> 0"
  shows "card {x. x \<in> carrier R \<and> x (^) d = \<one>} \<le> d"
proof -
  let ?f = "monom (UP R) \<one>\<^bsub>R\<^esub> d \<ominus>\<^bsub> (UP R)\<^esub> monom (UP R) \<one>\<^bsub>R\<^esub> 0"
  have one_in_carrier:"\<one> \<in> carrier R" by simp
  interpret R: UP_domain R "UP R" by (unfold_locales)
  have "deg R ?f = d"
    using d_neq_zero by (simp add: R.deg_minus_eq)
  hence f_not_zero:"?f \<noteq> \<zero>\<^bsub>UP R\<^esub>" using  d_neq_zero by (auto simp add : R.deg_nzero_nzero)
  have roots_bound:"finite {a \<in> carrier R . eval R R id a ?f = \<zero>} \<and>
                    card {a \<in> carrier R . eval R R id a ?f = \<zero>} \<le> deg R ?f"
                    using finite by (intro R.roots_bound[OF _ f_not_zero]) simp
  have subs:"{x. x \<in> carrier R \<and> x (^) d = \<one>} \<subseteq> {a \<in> carrier R . eval R R id a ?f = \<zero>}"
    by (auto simp: R.evalRR_simps)
  then have "card {x. x \<in> carrier R \<and> x (^) d = \<one>} \<le>
        card {a \<in> carrier R . eval R R id a ?f = \<zero>}" using finite by (simp add : card_mono)
  thus ?thesis using `deg R ?f = d` roots_bound by linarith
qed



section {* All finite multiplicative groups of fields have a generator *}

lemma (in group) pow_order_eq_1:
  assumes "finite (carrier G)" "x \<in> carrier G" shows "x (^) order G = \<one>"
  using assms by (metis nat_pow_pow ord_dvd_group_order pow_ord_eq_1 dvdE nat_pow_one)

lemma (in group)
  assumes finite': "finite (carrier G)"
  assumes "a \<in> carrier G"
  shows pow_ord_eq_ord_iff: "group.ord G (a (^) k) = ord a \<longleftrightarrow> coprime k (ord a)" (is "?L \<longleftrightarrow> ?R")
proof
  assume A: ?L then show ?R
    using assms ord_ge_1[OF assms] by (auto simp: nat_div_eq ord_pow_dvd_ord_elem)
next
  assume ?R then show ?L 
    using ord_pow_dvd_ord_elem[OF assms, of k] by auto
qed

context field begin

lemma N_d_eq_phi'_d: (* XXX rename *)
  assumes finite: "finite (carrier R)" and dvd: "d dvd order (mult_of R)"
    and exists: "\<exists>a\<in>carrier (mult_of R). group.ord (mult_of R) a = d"
  shows "card {a \<in> carrier (mult_of R). group.ord (mult_of R) a = d} = phi' d"
proof -
  note mult_of_simps[simp]
  have finite': "finite (carrier (mult_of R))" using finite by (rule finite_mult_of)

  interpret G:group "mult_of R" where "op (^)\<^bsub>mult_of R\<^esub> = (op (^) :: _ \<Rightarrow> nat \<Rightarrow> _)" and "\<one>\<^bsub>mult_of R\<^esub> = \<one>"
    by (rule field_mult_group) simp_all

  let ?N = "\<lambda> x . card {a . a \<in> carrier (mult_of R) \<and> group.ord (mult_of R) a  = x}"
  have *:"0 < order (mult_of R)"
    unfolding order_mult_of[OF finite] using card_mono[OF finite, of "{\<zero>, \<one>}"] by (simp add: order_def)
  have fin: "finite {d. d dvd order (mult_of R) }" using dvd_nat_bounds[OF *] by force

  from exists
  obtain a where a':"a \<in> carrier (mult_of R)" and ord_a: "group.ord (mult_of R) a = d" by (auto simp add: card_gt_0_iff)
  have d_neq_0:"d\<noteq>0" using * by (simp add : dvd_pos_nat[OF _ `d dvd order (mult_of R)`])
  have "{x . x \<in> carrier (mult_of R) \<and> x (^) d = \<one>} \<subseteq> {x . x \<in> carrier R \<and> x (^) d = \<one>}" by auto
  hence "card {x . x \<in> carrier (mult_of R) \<and> x (^) d = \<one>} \<le> card {x . x \<in> carrier R \<and> x (^) d = \<one>}" using card_mono[of _ "{x . x \<in> carrier (mult_of R) \<and> x (^) d = \<one>}"] finite by force
  hence card_le_d : "card {x . x \<in> carrier (mult_of R) \<and> x (^) d = \<one>} \<le> d" 
      using num_roots_le_deg[OF finite d_neq_0] by simp

  have finite_roots: "finite {x . x \<in> carrier (mult_of R) \<and> x (^) d = \<one>}" using finite by auto
  have subs:"{a(^)n| n . n \<in> {0 ..d - 1}} \<subseteq> {x . x \<in> carrier (mult_of R) \<and> x(^)d = \<one>}"
  proof
    fix x assume "x \<in> {a(^)n| n . n \<in> {0 .. d - 1}}"
    then obtain n where n:"x = a(^)n \<and> n \<in> {0 .. d - 1}" by auto
    hence x_bounds:"x \<in> carrier R" using a' by fastforce
    have a_d:"a(^)d = \<one>" using ord_a G.pow_ord_eq_1[OF finite' a'] a' by metis
    have "x(^)d = a(^)(n*d)" using n a' ord_a by (simp add:nat_pow_pow)
    have "x(^)d = (a(^)d)(^)n" using n a' by (simp add:nat_mult_commute nat_pow_pow)
    hence x_d:"x(^)d = \<one>" using a_d by simp
    have "x \<in> carrier (mult_of R)" using G.nat_pow_closed[OF a'] n a' by auto
    thus "x \<in> {x . x \<in> carrier (mult_of R) \<and> x(^)d = \<one>}" using x_d by blast
  qed
  have inj:"inj_on (\<lambda> n. a(^)n) {0 .. d - 1}"
    using G.ord_inj[OF finite' a'] ord_a by simp
  have "{a(^)n| n . n \<in> {0 .. d - 1}} = ((\<lambda> n. a(^)n) ` {0 .. d - 1})" by auto
  hence cards_eq:"card {a(^)n| n . n \<in> {0 .. d - 1}} = card {0 .. d - 1}" using inj
    by (simp add: card_image)
  have "card {0 .. d - 1} = d" using `d dvd order (mult_of R)` *
    by (simp add: dvd_nat_bounds[of "order (mult_of R)" d])
  hence "card {a(^)n| n . n \<in> {0 .. d - 1}} = d" using cards_eq by auto
  hence set_eq1:"{a(^)n| n . n \<in> {0 .. d - 1}} = {x. x \<in> carrier (mult_of R) \<and> x (^) d = \<one>}" 
    using card_seteq[OF finite_roots subs] card_le_d by presburger

  have set_eq2:"{x \<in> carrier (mult_of R) . group.ord (mult_of R) x = d} 
                = {a(^)n| n . n \<in> {1 .. d} \<and> group.ord (mult_of R) (a(^)n) = d}" (is "?L = ?R")
  proof
    { fix x assume x:"x \<in> (carrier (mult_of R)) \<and> group.ord (mult_of R) x = d"
      hence "x (^) d = \<one>"
        by (simp add: G.pow_ord_eq_1[OF finite', of x, symmetric])
      hence "x \<in> {x. x \<in> carrier (mult_of R) \<and> x (^) d = \<one>}" using x by simp
      then obtain n where n:"x = a(^)n \<and> n \<in> {0 .. d - 1}" using set_eq1 by blast
      def n' \<equiv> "if n = 0 then d else n" 
      have n'1:"n' \<in> {1 .. d}" using n dvd_nat_bounds[OF _ `d dvd order (mult_of R)`] *
        by (auto simp add: n'_def)
      have "x = a(^)n'" unfolding n'_def using a' ord_a n
            by (simp add: G.pow_ord_eq_1[OF finite', of a, symmetric])
      hence "x \<in> ?R" using x n'1 by fast
    } thus "?L \<subseteq> ?R" by blast
    show "?R \<subseteq> ?L" using a' by (auto simp add: carrier_mult_of[symmetric] simp del: carrier_mult_of)
  qed

  { fix i j :: nat assume i : "i \<in> {1 .. d}" assume j : "j \<in> {1 .. d}"
    assume ij : "a(^)i= a(^)j" assume "i = d" "j \<noteq> d"
    hence j':"j \<in> {0 .. d - 1}" using j by auto
    have "a(^)j = a(^)(0::nat)" using ord_a
      by (simp add: ij[symmetric] `i=d` G.pow_ord_eq_1[OF finite' a', symmetric] a') 
    hence "j = 0" using inj inj_on_def[of "\<lambda>n. a (^) n" "{0 .. d - 1}"] j' by auto
    hence "i = j" using j by simp
  } note i_eq_d_j_neq_d = this
  { fix i j :: nat assume i : "i \<in> {1 .. d}" assume j : "j \<in> {1 .. d}"
    assume ij : "a(^)i = a(^)j"
    { assume "j \<noteq> d" "i \<noteq> d"
      hence i':"i \<in> {0 .. d - 1}" using i by force
      have "j \<in> {0 .. d - 1}" using j `j\<noteq>d` by fastforce
      hence "i = j" using ij i' inj inj_on_def[of "(\<lambda>n. a (^) n)" "{0..d - 1}"] by blast
    } hence "i = j" using i_eq_d_j_neq_d[OF j i] i_eq_d_j_neq_d[OF i j ij] ij by force
  }  hence inj2:"inj_on (\<lambda> n . a(^)n) {1 .. d}" using inj_on_def by blast
  hence inj3:"inj_on (\<lambda> n . a(^)n) {n . n \<in> {1 .. d} \<and> group.ord (mult_of R) (a(^)n) = d}"
    using inj_on_def[of "\<lambda> n . a(^)n" "{1 .. d}"] unfolding inj_on_def by fast
  hence card_proj_eq: "card ((\<lambda> n . a(^)n) ` {n . n \<in> {1 .. d} \<and> group.ord (mult_of R) (a(^)n) = d})
                       = card {k . k \<in> {1 .. d} \<and> group.ord (mult_of R) (a(^)k) = d}"
                       using card_image[OF inj3] by fast
  have "{a(^)n| n . n \<in> {1 .. d} \<and> group.ord (mult_of R) (a(^)n) = d}
        = (\<lambda> n . a(^)n) ` {n . n \<in> {1 .. d} \<and> group.ord (mult_of R) (a(^)n) = d}" by blast
  hence card_proj_eq2:"card {a(^)n| n . n \<in> {1 .. d} \<and> group.ord (mult_of R) (a(^)n) = d}
                       = card {k . k \<in> {1 .. d} \<and> group.ord (mult_of R) (a(^)k) = d}" 
                      using card_proj_eq by presburger
  show "?N d = phi' d"
    using set_eq2 card_proj_eq2 G.pow_ord_eq_ord_iff[OF finite' `a \<in> _`, unfolded ord_a]
    by (simp add: phi'_def)
qed

end

theorem (in field) finite_field_mult_group_has_gen :
  assumes finite:"finite (carrier R)"
  shows "\<exists> a \<in> carrier (mult_of R) . carrier (mult_of R) = {a(^)i |i::nat . i \<in> UNIV}"
proof -
  note mult_of_simps[simp]
  have finite': "finite (carrier (mult_of R))" using finite by (rule finite_mult_of)

  interpret G: group "mult_of R" where
      "op (^)\<^bsub>mult_of R\<^esub> = (op (^) :: _ \<Rightarrow> nat \<Rightarrow> _)" and "\<one>\<^bsub>mult_of R\<^esub> = \<one>"
    by (rule field_mult_group) (simp_all add: fun_eq_iff nat_pow_def)

  let ?N = "\<lambda> x . card {a . a \<in> carrier (mult_of R) \<and> group.ord (mult_of R) a  = x}"
  have "0 < order R - 1" unfolding order_def using card_mono[OF finite, of "{\<zero>, \<one>}"] by simp
  then have *: "0 < order (mult_of R)" using assms by (simp add: order_mult_of)
  have fin: "finite {d. d dvd order (mult_of R) }" using dvd_nat_bounds[OF *] by force

  have "(\<Sum> d \<in> {d . d dvd order (mult_of R) } . ?N d)
      = card (UNION {d . d dvd order (mult_of R) } (\<lambda> x . {a . a \<in> carrier (mult_of R) \<and> group.ord (mult_of R) a  = x}))"
      (is "_ = card (UNION ?L ?f)")
    using fin finite by (subst card_UN_disjoint) auto
  also have "UNION ?L ?f = carrier (mult_of R)"
  proof
    { fix x assume x:"x \<in> carrier (mult_of R)"
      hence x':"x\<in>carrier (mult_of R)" by simp
      then have "group.ord (mult_of R) x dvd order (mult_of R)"
          using finite' G.ord_dvd_group_order[OF _ x'] by (simp add: order_mult_of)
      hence "x \<in> UNION ?L ?f" using dvd_nat_bounds[of "order (mult_of R)" "group.ord (mult_of R) x"] x by blast
    } thus "carrier (mult_of R) \<subseteq> UNION ?L ?f" by blast
  qed auto
  also have "card ... = order (mult_of R)"
    using order_mult_of finite' by (simp add: order_def)
  finally have sum_Ns_eq: "(\<Sum> d \<in> {d . d dvd order (mult_of R) } . ?N d) = order (mult_of R)" .

  { fix d assume d:"d dvd order (mult_of R)"
    have "card {a |a. a \<in> carrier (mult_of R) \<and> group.ord (mult_of R) a = d} \<le> phi' d"
    proof cases
      assume "card {a |a. a \<in> carrier (mult_of R) \<and> group.ord (mult_of R) a = d} = 0" thus ?thesis by presburger
      next
      assume "card {a |a. a \<in> carrier (mult_of R) \<and> group.ord (mult_of R) a = d} \<noteq> 0"
      hence "\<exists>a \<in> carrier (mult_of R). group.ord (mult_of R) a = d" by (auto simp: card_eq_0_iff)
      thus ?thesis using N_d_eq_phi'_d[OF finite d] by auto
    qed
  }
  hence all_le:"\<And>i. i \<in> {d | d . d dvd order (mult_of R) } 
        \<Longrightarrow> (\<lambda>i. card {a |a. a \<in> carrier (mult_of R) \<and> group.ord (mult_of R) a = i}) i \<le> (\<lambda>i. phi' i) i" by fast
  hence le:"(\<Sum>i\<in>{d |d. d dvd order (mult_of R)}. ?N i) 
            \<le> (\<Sum>i\<in>{d |d. d dvd order (mult_of R)}. phi' i)"
            using setsum_mono[of "{d | d .  d dvd order (mult_of R)}"
                  "\<lambda>i. card {a |a. a \<in> carrier (mult_of R) \<and> group.ord (mult_of R) a = i}"] by presburger
  have "order (mult_of R) = (\<Sum> d \<in> {d | d . d dvd order (mult_of R) } . phi' d)" using *
    by (simp add: sum_phi'_factors)
  hence eq:"(\<Sum>i\<in>{d|d. d dvd order (mult_of R)}. ?N i)
          = (\<Sum>i\<in>{d|d. d dvd order (mult_of R)}. phi' i)" using le sum_Ns_eq by presburger
  have "\<And>i. i \<in> {d | d . d dvd order (mult_of R) } \<Longrightarrow> ?N i = (\<lambda> i . phi' i) i"
  proof (rule ccontr)
    fix i
    assume i1:"i \<in> {d |d. d dvd order (mult_of R)}" and "?N i \<noteq> phi' i"
    hence "?N i = 0"
      using N_d_eq_phi'_d[OF finite, of i] by (auto simp: card_eq_0_iff)
    moreover  have "0 < i" using * i1 by (simp add: dvd_nat_bounds[of "order (mult_of R)" i])
    ultimately have "?N i < phi' i" using phi'_nonzero by presburger
    hence "(\<Sum>i\<in>{d. d dvd order (mult_of R)}. ?N i)
         < (\<Sum>i\<in>{d. d dvd order (mult_of R)}. phi' i)"
      using setsum_strict_mono_ex1[OF fin, of "?N" "\<lambda> i . phi' i"]
            i1 all_le by auto
    thus False using eq by force
  qed
  hence "?N (order (mult_of R)) > 0" using * by (simp add: phi'_nonzero)
  then obtain a where a:"a \<in> carrier (mult_of R)" and a_ord:"group.ord (mult_of R) a = order (mult_of R)"
    by (auto simp add: card_gt_0_iff)
  hence set_eq:"{a(^)i|i::nat. i \<in> UNIV} = (\<lambda>x. a(^)x) ` {0 .. group.ord (mult_of R) a - 1}"
    using G.ord_elems[OF finite'] by auto
  have card_eq:"card ((\<lambda>x. a(^)x) ` {0 .. group.ord (mult_of R) a - 1}) = card {0 .. group.ord (mult_of R) a - 1}"
    using card_image[of "\<lambda>x. a(^)x" "{0 .. group.ord (mult_of R) a - 1}"] G.ord_inj[OF finite', of a] a
    by simp
  hence "card ((\<lambda> x . a(^)x) ` {0 .. group.ord (mult_of R) a - 1}) = card {0 ..order (mult_of R) - 1}"
    using card_eq assms by (simp add: a_ord order_mult_of)
  hence card_R_minus_1:"card {a(^)i|i::nat. i \<in> UNIV} =  order (mult_of R)" using set_eq * by force
  have **:"{a(^)i|i::nat. i \<in> UNIV} \<subseteq> carrier (mult_of R)" using G.nat_pow_closed[of a] a
    by auto
  have "carrier (mult_of R) = {a(^)i|i::nat. i \<in> UNIV}" 
    using card_seteq[OF _ **] card_R_minus_1 finite unfolding order_def by simp
  thus ?thesis using a by blast
qed


end
