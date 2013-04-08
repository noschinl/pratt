theory pratt
imports Main "~~/src/HOL/Number_Theory/Number_Theory" "Lehmer" "~~/src/HOL/Algebra/Coset"
             "~~/src/HOL/Algebra/UnivPoly" "~~/src/HOL/Library/Multiset"  "~~/src/HOL/Algebra/Group"
begin

lemma (in field) is_domain :
  shows "domain R" by unfold_locales

lemma(in residues) residue_ring_id_eval:
  shows "UP_pre_univ_prop R R id"
proof -
  show ?thesis by (fast intro: UP_pre_univ_propI cring id_ring_hom)
qed

sublocale residues \<subseteq> UP_pre_univ_prop R R id "UP R"
  using residue_ring_id_eval by simp_all

sublocale residues_prime \<subseteq> UP_domain R "UP R"
  using is_domain by (unfold_locales)

lemma (in residues) is_UP_ring :
  shows "UP_ring R" by (unfold_locales)

lemma(in residues) remainder_theorem_trans:
  assumes f [simp]: "f \<in> carrier (UP R)" and a [simp]: "a \<in> carrier R"
  and R_not_trivial: "m\<ge>2"
  shows "\<exists> q . (q \<in> carrier (UP R)) \<and> 
     f = (monom (UP R) \<one>\<^bsub>R\<^esub> 1 \<ominus>\<^bsub> (UP R)\<^esub> monom (UP R) a 0) \<otimes>\<^bsub>(UP R)\<^esub> q \<oplus>\<^bsub>(UP R)\<^esub> monom (UP R) (eval R R id a f) 0"
proof -
 have "carrier R \<noteq> {\<zero>}" using R_not_trivial by (simp add : res_carrier_eq zero_cong)
 thus ?thesis using remainder_theorem[OF f a] by blast
qed

lemma(in UP_cring) deg_monom_minus_const:
  fixes d :: nat
  assumes a: "a \<in> carrier R"
  and R_not_trivial: "(carrier R \<noteq> {\<zero>})"
  shows "deg R (monom P \<one>\<^bsub>R\<^esub> d \<ominus>\<^bsub>P\<^esub> monom P a 0) = d"
  (is "deg R ?g = d")
proof -
  have "deg R ?g \<le> d"
  proof (rule deg_aboveI)
    fix m
    assume "d < m" 
    then show "coeff P ?g m = \<zero>" 
      using coeff_minus a by auto algebra
  qed (simp add: a)
  moreover have "deg R ?g \<ge> d"
  proof (rule deg_belowI)
    assume "d\<noteq>0"
    hence "coeff P ?g d = \<one>\<^bsub>R\<^esub>" using `d\<noteq>0` by (simp add : P.minus_eq a) 
    thus "coeff P ?g d \<noteq> \<zero>"
      using a using R.carrier_one_not_zero R_not_trivial by simp
  qed (simp add: a)
  ultimately show ?thesis by simp
qed

lemma (in residues_prime) carrier_not_trivial :
  shows "carrier R \<noteq> {\<zero>}"
proof -
  have "p\<ge>2" by (simp add : p_prime prime_ge_2_int)
  thus ?thesis by (simp add : zero_cong res_carrier_eq)
qed
              
lemma(in UP_cring) eval_monom_expr_neq:
  assumes a: "a \<in> carrier R"
  assumes x: "x \<in> carrier R"
  assumes x_a : "a \<noteq> x"
  shows "eval R R id x (monom P \<one>\<^bsub>R\<^esub> 1 \<ominus>\<^bsub>P\<^esub> monom P a 0) \<noteq> \<zero>"
  (is "eval R R id x ?g \<noteq>  _")
proof -
  interpret UP_pre_univ_prop R R id by unfold_locales simp
  have eval_ring_hom: "eval R R id x \<in> ring_hom P R" using eval_ring_hom [OF x] by simp
  interpret ring_hom_cring P R "eval R R id x" by unfold_locales (rule eval_ring_hom)
  have mon1_closed: "monom P \<one>\<^bsub>R\<^esub> 1 \<in> carrier P" 
    and mon0_closed: "monom P a 0 \<in> carrier P" 
    and min_mon0_closed: "\<ominus>\<^bsub>P\<^esub> monom P a 0 \<in> carrier P"
    using a R.a_inv_closed by auto
  have "eval R R id x ?g = eval R R id x (monom P \<one> 1) \<ominus> eval R R id x (monom P a 0)"
    unfolding P.minus_eq [OF mon1_closed mon0_closed]
    unfolding hom_add [OF mon1_closed min_mon0_closed]
    unfolding hom_a_inv [OF mon0_closed] 
    using R.minus_eq [symmetric] mon1_closed mon0_closed by auto
  also have "\<dots> = x \<ominus> a"
    using eval_monom [OF R.one_closed x, of 1] using eval_monom [OF a x, of 0] using a x by simp
  also have "\<dots> \<noteq> \<zero>"
    using x_a x a by (metis R.a_comm R.a_inv_closed R.add.r_one R.minus_eq R.r_neg2)
  finally show ?thesis by simp
qed

lemma (in UP_domain) UP_prod_zero :
  assumes f : "f \<in> carrier P"
  assumes g : "g \<in> carrier P"
  assumes x: "x \<in> carrier R"
  assumes prod_eq_zero : "eval R R id x (f \<otimes>\<^bsub>P\<^esub> g) = \<zero>\<^bsub>R\<^esub>"
  assumes f_neq_zero : "eval R R id x f \<noteq> \<zero>\<^bsub>R\<^esub>"
  shows "eval R R id x g = \<zero>\<^bsub>R\<^esub>"
proof -
  interpret UP_pre_univ_prop R R id by unfold_locales simp
  have eval_ring_hom: "eval R R id x \<in> ring_hom P R" using eval_ring_hom [OF x] by simp
  interpret ring_hom_cring P R "eval R R id x" by unfold_locales (rule eval_ring_hom)
  have "eval R R id x (f \<otimes>\<^bsub>P\<^esub> g) = eval R R id x f \<otimes>\<^bsub>R\<^esub> eval R R id x g"
    unfolding hom_mult [OF f g] by auto
  hence prod_zero:"eval R R id x f \<otimes>\<^bsub>R\<^esub> eval R R id x g = \<zero>\<^bsub>R\<^esub>" by (simp add : prod_eq_zero)
  show ?thesis using R.integral[OF prod_zero] f_neq_zero f g x by blast
qed

lemma(in residues_prime) roots_bound :
  assumes f [simp]: "f \<in> carrier (UP R)" 
  assumes f_not_zero : "f \<noteq> \<zero>\<^bsub>UP R\<^esub>"
  shows "finite {a \<in> carrier R . eval R R id a f = 0} \<and>
         card {a \<in> carrier R . eval R R id a f = 0} \<le> deg R f" using f f_not_zero
proof (induction "deg R f" arbitrary: f)
  case zero
    then have "\<And>x. eval R R id x f \<noteq> 0"
      using lcoeff_nonzero[where p=f]
      by (simp add: eval_def zero_cong[symmetric])
    then have *: "{a \<in> carrier R. eval R R (\<lambda>a. a) a f = 0} = {}"
      by (auto simp: id_def)
    show ?case by (simp add: *)
  next
  case (plus1 x)
  show ?case
  proof (cases "\<exists> a \<in> carrier R . eval R R id a f = 0")
  have "p\<ge>2" by (simp add : p_prime prime_ge_2_int)
  case True
    then obtain a where a_carrier[simp]: "a \<in> carrier R" and a_root:"eval R R id a f = 0" by blast
    obtain q  where q:"(q \<in> carrier (UP R))"  and 
     f:"f = (monom (UP R) \<one>\<^bsub>R\<^esub> 1 \<ominus>\<^bsub> (UP R)\<^esub> monom (UP R) a 0) \<otimes>\<^bsub>(UP R)\<^esub> q 
             \<oplus>\<^bsub>(UP R)\<^esub> monom (UP R) (eval R R id a f) 0"
     using remainder_theorem_trans[OF plus1.prems(1) a_carrier `2\<le>p`] by (atomize_elim)
    hence "f = (monom (UP R) \<one>\<^bsub>R\<^esub> 1 \<ominus>\<^bsub> (UP R)\<^esub> monom (UP R) a 0) \<otimes>\<^bsub>(UP R)\<^esub> q 
                \<oplus>\<^bsub>(UP R)\<^esub> monom (UP R) \<zero> 0" by (simp add : res_zero_eq a_root)
    hence lin_fac:"f = (monom (UP R) \<one>\<^bsub>R\<^esub> 1 \<ominus>\<^bsub> (UP R)\<^esub> monom (UP R) a 0) \<otimes>\<^bsub>(UP R)\<^esub> q" 
      using q by simp
    have deg:"deg R (monom (UP R) \<one>\<^bsub>R\<^esub> 1 \<ominus>\<^bsub> (UP R)\<^esub> monom (UP R) a 0) = 1" 
      by (simp add : deg_monom_minus_const[OF a_carrier] carrier_not_trivial)
    hence mon_not_zero:"(monom (UP R) \<one>\<^bsub>R\<^esub> 1 \<ominus>\<^bsub> (UP R)\<^esub> monom (UP R) a 0) \<noteq> \<zero>\<^bsub>UP R\<^esub>" by fastforce
    have q_not_zero:"q \<noteq> \<zero>\<^bsub>UP R\<^esub>" using plus1 by (auto simp add : lin_fac)
    have "UP_domain R" by (simp add : UP_domain_def is_field field.is_domain)
    hence "deg R q = x" using plus1 deg UP_domain.deg_mult[OF _ mon_not_zero q_not_zero _ q] 
      by (simp add : lin_fac)
    hence q_IH:"finite {a \<in> carrier R . eval R R id a q = 0} 
                \<and> card {a \<in> carrier R . eval R R id a q = 0} \<le> x" using plus1 q q_not_zero by blast
    have subs:"{a \<in> carrier R . eval R R id a f = 0} 
                \<subseteq> {a \<in> carrier R . eval R R id a q = 0} \<union> {a}" (is "?L \<subseteq> ?R \<union> {a}")
    proof
      fix x
      assume x : "x \<in> ?L"
      hence x_carrier:"x \<in> carrier R" and x_root : "eval R R id x f = 0" by auto
      thus "x \<in> ?R \<union> {a}"
      proof (cases "x=a")
        case True thus ?thesis by blast
        next
        case False
          hence "eval R R id x (monom (UP R) \<one>\<^bsub>R\<^esub> 1 \<ominus>\<^bsub>(UP R)\<^esub> monom (UP R) a 0) \<noteq> \<zero>\<^bsub>R\<^esub>"
            using eval_monom_expr_neq[OF a_carrier x_carrier] by blast
          thus ?thesis using x_root 
            by (simp add: x_carrier lin_fac zero_cong 
                UP_prod_zero[of "monom (UP R) \<one> 1 \<ominus>\<^bsub>UP R\<^esub> monom (UP R) a 0" q x, OF _ q])
      qed
   qed
   have fin:"finite (insert a {a \<in> carrier R . eval R R id a q = 0})" using q_IH by force
   have "{a \<in> carrier R . eval R R id a f = 0} \<subseteq> insert a {a \<in> carrier R . eval R R id a q = 0}"
    using subs by auto
   hence "card {a \<in> carrier R . eval R R id a f = 0} \<le>
          card (insert a {a \<in> carrier R . eval R R id a q = 0})" using  card_mono[OF fin] by blast
   also have "\<dots> \<le> deg R f" using q_IH `x+1 = deg R f` by simp
   finally show ?thesis by auto
 next
 case False
   hence "card {a \<in> carrier R. eval R R id a f = 0} = 0" by auto
   hence "card {a \<in> carrier R. eval R R id a f = 0} \<le> deg R f" using `x+1 = deg R f` by linarith
   thus ?thesis by auto
 qed
qed

lemma (in residues_prime) is_residues :
  shows "residues p" by (unfold_locales)

lemma (in residues) is_UP_cring :
  shows "UP_cring R" by (unfold_locales)

lemma(in UP_cring) eval_monom_pow_expr :
  fixes d :: nat
  assumes d_neq_zero : "d \<noteq> 0"
  assumes x:"x \<in> carrier R"
  shows "eval R R id x (monom P \<one> d \<ominus>\<^bsub>P\<^esub> monom P \<one> 0) = x (^)\<^bsub>R\<^esub> d \<ominus>\<^bsub>R\<^esub> \<one>" 
    (is "eval R R id x ?g = _")
proof -
  interpret UP_pre_univ_prop R R id by unfold_locales simp
  have eval_ring_hom: "eval R R id x \<in> ring_hom P R" using eval_ring_hom [OF x] by simp
  interpret ring_hom_cring P R "eval R R id x" by unfold_locales (rule eval_ring_hom)
  have mon1_closed: "monom P \<one> d \<in> carrier P" 
    and mon0_closed: "monom P \<one> 0 \<in> carrier P" 
    and min_mon0_closed: "\<ominus>\<^bsub>P\<^esub> monom P \<one> 0 \<in> carrier P"
    using R.a_inv_closed by auto
  have "eval R R id x ?g = eval R R id x (monom P \<one> d) \<ominus> eval R R id x (monom P \<one> 0)"
    unfolding P.minus_eq [OF mon1_closed mon0_closed]
    unfolding hom_add [OF mon1_closed min_mon0_closed]
    unfolding hom_a_inv [OF mon0_closed] 
    using R.minus_eq [symmetric] mon1_closed mon0_closed by auto
  thus ?thesis
    using eval_monom [OF R.one_closed x, of d] using eval_monom [OF _ x, of \<one> 0] using x by simp
qed

lemma mod_cong_nat_diff_eq_zero :
  fixes a b p :: nat
  assumes "[a = b] (mod p)"
  shows "[a - b = 0] (mod p)"
    using assms  by (cases "a\<le>b") (simp_all add: cong_diff_cong_0'_nat[of a b p])

lemma int_minus_def:
  fixes a :: int
  shows "a - 1 = a + (-1)" by simp

lemma num_roots_le_deg :
  fixes p d :: nat
  assumes prime_p:"prime p"
  assumes d_neq_zero : "d \<noteq> 0"
  shows "finite {x. x \<in> {0 .. p - 1} \<and> x ^ d mod p = 1} \<and> card {x. x \<in> {0 .. p - 1} \<and> x ^ d mod p = 1} \<le> d"
proof -
  let ?R = "residue_ring (int p)"
  let ?f = "monom (UP ?R) \<one>\<^bsub>?R\<^esub> d \<ominus>\<^bsub> (UP ?R)\<^esub> monom (UP ?R) \<one>\<^bsub>?R\<^esub> 0"
  have res_p:"residues_prime (int p)" using prime_p 
    by (simp add: residues_prime_def transfer_int_nat_prime)
  hence res:"residues (int p)" by (rule residues_prime.is_residues)
  hence one_in_carrier:"\<one>\<^bsub>?R\<^esub> \<in> carrier ?R" by (simp add: residues.mod_in_carrier residues.one_cong)
  interpret R:  UP_ring ?R "UP ?R"  using res by (rule residues.is_UP_ring)
  interpret cR: UP_cring ?R "UP ?R" using res by (rule residues.is_UP_cring)
  have "deg ?R ?f = d" 
  by (rule cR.deg_monom_minus_const[OF one_in_carrier residues_prime.carrier_not_trivial[OF res_p]])
  hence f_not_zero:"?f \<noteq> \<zero>\<^bsub>UP ?R\<^esub>" using  d_neq_zero by (auto simp add : cR.deg_nzero_nzero)
  have roots_bound:"finite {a \<in> carrier ?R . eval ?R ?R id a ?f = 0} \<and>
                    card {a \<in> carrier ?R . eval ?R ?R id a ?f = 0} \<le> deg ?R ?f"
                    using `residues_prime (int p)`
                    by (intro residues_prime.roots_bound[OF `residues_prime _` _ f_not_zero]) simp
  have "p\<ge>2" by (rule prime_ge_2_nat[OF prime_p])
  have subs:"{x. x \<in> {0 .. p - 1} \<and> x ^ d mod p = 1}
              \<subseteq> nat ` {a \<in> carrier ?R . eval ?R ?R id a ?f = 0}" (is "?L \<subseteq> nat ` ?RS")
  proof -
    { fix x
      assume "x \<in> ?L"
      hence x_carrier:"x\<in>{0 .. p - 1}" and x_eq:"x^d mod p = 1" by auto
      hence "[x^d = 1] (mod p)" using `p\<ge>2`  by (simp add : cong_nat_def)
      hence "[x^d - 1 = 0] (mod p)" by (simp add : mod_cong_nat_diff_eq_zero)
      hence x_d_1:"(x^d - 1) mod p = 0" by (simp add : cong_nat_def)
      have "int (x^d mod p) = int x^d mod (int p)" by (simp add: int_power zmod_int)
      hence closed_pow:"int x^d mod (int p) \<in> carrier ?R" using `p\<ge>2`
        by (simp add: x_eq residues.res_carrier_eq[OF res])
      have closed_1:"1 mod (int p) \<in> carrier ?R" using R.R.one_closed
        by (simp add: residues.one_cong[OF res])
      have "0 = (int x^d - 1) mod (int p)" using x_d_1
        by (metis Divides.transfer_int_nat_functions(2) diff_self mod_0 mod_diff_left_eq
            of_nat_1 of_nat_power x_eq)
      also have "\<dots> = ((int x mod (int p))(^)\<^bsub>?R\<^esub> d) \<ominus>\<^bsub>?R\<^esub> \<one>\<^bsub>?R\<^esub>"
        by (simp add: R.R.minus_eq[OF closed_pow closed_1]  residues.add_cong residues.neg_cong res 
            residues.one_cong residues.pow_cong int_minus_def)
      finally have "0 = eval ?R ?R id (int x) ?f" using cR.eval_monom_pow_expr[OF d_neq_zero] `p\<ge>2`
        x_carrier by (simp add : residues.res_carrier_eq[OF res])
      hence "int x \<in> ?RS" using x_carrier `p\<ge>2` by (simp add: residues.res_carrier_eq[OF res])
      hence "x \<in> nat ` ?RS" by force
    } thus ?thesis by blast
  qed
  have "finite (nat ` {a \<in> carrier ?R . eval ?R ?R id a ?f = 0})" using roots_bound by fast
  hence "card {x. x \<in> {0 .. p - 1} \<and> x ^ d mod p = 1} \<le>
        card (nat ` {a \<in> carrier ?R . eval ?R ?R id a ?f = 0})" using subs by (simp add : card_mono)
  also have "\<dots> \<le> card {a \<in> carrier ?R . eval ?R ?R id a ?f = 0}"
    using roots_bound by (simp add : card_image_le) 
  finally have "card {x. x \<in> {0 .. p - 1} \<and> x ^ d mod p = 1}
                \<le> card {a \<in> carrier ?R . eval ?R ?R id a ?f = 0}" .
  thus ?thesis using `deg ?R ?f = d` roots_bound by simp
qed



datatype pratt =
 Prime nat
 |Triple nat nat nat

type_synonym cert = "pratt list"

theorem(in group) lagrange_ex:
 assumes "finite(carrier G)" 
 assumes "subgroup H G"
 shows "(card H) dvd (order G)"
proof
 show "order G = card H * card (rcosets H)" using lagrange[OF assms] nat_mult_commute by force
qed

lemma (in group) nat_inv_pow_mult :
 fixes m :: nat
 fixes n :: nat
 assumes "x \<in> carrier G"
 shows "inv (x (^) m)  \<otimes> inv (x (^) n) = inv (x (^) (m + n))" using assms 
    by (simp add: inv_mult_group[symmetric] nat_pow_mult nat_add_commute)

lemma (in group) int_pow_mult :
 fixes m :: int
 fixes n :: int
 assumes [simp]:"x \<in> carrier G"
 shows "x (^) m  \<otimes> x (^) n = x (^) (m + n)"
 proof -
  {
   assume 1:"m\<ge>0 \<and> n \<ge> 0"
   hence "nat m + nat n = nat (m+n)" by auto
   hence ?thesis using 1 by (simp add: int_pow_def2 nat_pow_mult)
  }
  moreover
  {
   assume 1:"m < 0 \<and> n < 0"
   hence "nat (-m) + nat (-n) = nat (-m -n)" by auto
   hence ?thesis using 1 by (simp add: int_pow_def2 nat_inv_pow_mult)
  }
  moreover
  {
   assume 1:"m < 0 \<and> n \<ge> 0"
   hence 3:"x (^) m  \<otimes> x (^) n = inv (x (^) nat (- m)) \<otimes> x (^) nat n"  by (simp add: int_pow_def2)
   {
    assume 2:"-m < n"
    hence "nat n = nat (-m) + nat (m + n)" using 1 by auto
    hence "x (^) m  \<otimes> x (^) n = inv (x (^) nat (- m)) \<otimes> x (^) nat (-m) \<otimes> x (^) nat (m + n)" 
          by (simp add: nat_pow_mult[of x, symmetric] 3 m_assoc[symmetric])
    hence ?thesis using 2 by (simp add: int_pow_def2)
   }
   moreover
   {
    assume 2:"-m \<ge> n"
    hence "nat (-m) = nat (-(m + n)) + nat (n)" using 1 by auto
    hence "x (^) m  \<otimes> x (^) n = inv (x (^) nat (-(m+n))) \<otimes> (inv (x (^) nat (n)) \<otimes> x (^) nat n)" 
        by (simp add: 3 nat_add_commute inv_mult_group nat_pow_mult[of x, symmetric] m_assoc)
    hence ?thesis using 2 by (simp add: int_pow_def2)
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
    hence "x (^) m  \<otimes> x (^) n = x (^) nat (m+n) \<otimes> (x (^) nat (-n)  \<otimes> inv (x (^) nat (- n)))" 
        by (simp add: 3 nat_pow_mult[of x, symmetric] m_assoc)
    hence ?thesis using 2 by (simp add: int_pow_def2)
   }
   moreover
   {
    assume 2:"-n \<ge> m"
    hence "nat (-n) =  nat (m) + nat (-(m + n))" using 1 by auto
    hence "x (^) m  \<otimes> x (^) n =  x (^) nat m \<otimes> inv (x (^) nat (m)) \<otimes> inv (x (^) nat (-(m+n)))" 
      by (simp add: 3 nat_add_commute[of "nat m" "nat (- m - n)"] nat_pow_mult[of x,symmetric] 
          inv_mult_group m_assoc[symmetric]) 
    hence ?thesis using 2 by (simp add: int_pow_def2)
   }
   ultimately have ?thesis by linarith
  }
  ultimately show ?thesis by linarith
 qed 

lemma (in group) pow_eq_div2 :
  fixes m n :: nat
  assumes x_car: "x \<in> carrier G"
  assumes pow_eq: "x (^) m = x (^) n"
  shows "x (^) (m - n) = \<one>"
proof (cases "m < n")
  case True then show ?thesis by simp
next
  case False
  have "\<one> \<otimes> x (^) m = x (^) m" by (simp add: x_car)
  also have "\<dots> = x (^) (m - n) \<otimes> x (^) n"
    using False by (simp add: nat_pow_mult x_car)
  also have "\<dots> = x (^) (m - n) \<otimes> x (^) m"
    by (simp add: pow_eq)
  finally show ?thesis by (simp add: x_car)
qed

lemma (in group) finite_group_elem_finite_ord :
 assumes finite_G:"finite (carrier G)"
 assumes x:"x \<in> carrier G"
 shows "\<exists> d::nat . d \<ge> 1 \<and> x (^) d = \<one>"
 proof -
  let ?H = "{x (^) i |i. i \<in> (UNIV :: nat set)}"
  def f \<equiv> "(\<lambda> i . x (^) i)::(nat \<Rightarrow> 'a)"
  hence f_pic:"?H = f ` UNIV" by auto
  have "?H \<subseteq> carrier G" using x nat_pow_closed by auto
  hence "finite ?H" using finite_G by (simp add: finite_subset) 
  hence "finite (f ` UNIV)" using f_pic by metis
  then obtain n1::nat where "\<not> finite {a \<in> (UNIV :: nat set). f a = f n1}"
      using Finite_Set.pigeonhole_infinite[of "UNIV" f] by auto
  then obtain n2 where n1n2_neq:"n2 \<noteq> n1" and n1n2:"f n1 = f n2" 
       by (metis (lifting, full_types) CollectD finite_nat_set_iff_bounded_le linorder_linear)
  hence x_n1n2:"x (^) (if n1 > n2 then n1 - n2 else n2 - n1) = \<one>" 
       by (simp add : pow_eq_div2[OF x] f_def)
  show ?thesis
  proof (cases "n1 > n2")
    case True 
      hence "n1 - n2 \<ge> 1" by auto
      thus ?thesis using x_n1n2  by (auto simp add : True)
    next
    case False
      hence "n2 - n1 \<ge> 1" using n1n2_neq by linarith
      thus ?thesis using x_n1n2 by (auto simp add : False)
  qed
qed

lemma dvd_nat_bounds :
 fixes n :: nat
 fixes p :: nat
 assumes "p > 0"
 assumes "n dvd p"
 shows "n > 0 \<and> n \<le> p" 
 using assms by (simp add: dvd_pos_nat dvd_imp_le)

definition ord where "ord a p = Min {d . d\<in> {1 .. p} \<and> (a ^ d) mod p = 1}"

lemma (in monoid) Units_pow_closed :
  fixes d :: nat
  assumes "x \<in> Units G"
  shows "x (^) d \<in> Units G" 
    by (metis assms group.is_monoid monoid.nat_pow_closed units_group units_of_carrier units_of_pow)

lemma (in comm_monoid) is_monoid:
  shows "monoid G" by unfold_locales

declare comm_monoid.is_monoid[intro?]

lemma p_prime_impl_mult_group_closed :
  fixes p :: nat
  fixes a :: nat
  fixes d :: nat
  assumes a:"a \<in> {1 .. p - 1}"
  assumes prime_p:"prime p"
  shows "a^d mod p \<in> {1 .. p - 1}"
proof -
  interpret R: residues_prime "int p" "residue_ring (int p)" 
      by (simp add: transfer_int_nat_prime prime_p residues_prime_def)
  have "Group.monoid (residue_ring (int p))" by (auto intro: comm_monoid.is_monoid R.comm_monoid)
  hence "int a (^)\<^bsub>residue_ring (int p)\<^esub> d \<in> Units (residue_ring (int p))" 
      using monoid.Units_pow_closed[of "residue_ring (int p)"] R.res_prime_units_eq a by auto
  hence "int a ^ d mod (int p) \<in> Units (residue_ring (int p))" 
      using R.pow_cong[of "int a" d] a by force
  also have "\<dots> = {1 .. int p - 1}" by (simp add: R.res_prime_units_eq)
  finally show ?thesis using nat_int[of "a ^ d mod p"] by (auto simp add: zmod_int int_power)
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
    interpret R: residues_prime "int p" "residue_ring (int p)" 
      by (simp add: transfer_int_nat_prime prime_p residues_prime_def)
    have card:"card (Units (residue_ring (int p))) = p - 1" using R.res_prime_units_eq by auto
    have "int a \<in> Units (residue_ring (int p))" using assms by (auto simp add: R.res_prime_units_eq)
    hence pow_eq:"int a (^)\<^bsub>residue_ring (int p)\<^esub> (p - 1)  = \<one>\<^bsub>residue_ring (int p)\<^esub>" 
      using cring.units_power_order_eq_one[OF R.cring, of "int a"] by (simp add: card)
    have "int a ^ (p - 1) mod (int p) = 1 " using assms
      by (simp add: pow_eq[symmetric] R.res_one_eq[symmetric] R.pow_cong[of "int a", symmetric])
    hence 1:"a ^ (p - 1) mod p = 1" 
      by (metis Divides.transfer_int_nat_functions(2) int_1 of_nat_eq_iff of_nat_power)
    thus ?thesis using  prime_ge_2_int[of "int p"] 
      by (auto simp add: transfer_int_nat_prime[of p] prime_p)
  qed

lemma pow_ord_eq_1 :
  fixes p::nat
  fixes a::nat
  assumes prime_p:"prime p"
  assumes "1 \<le>a \<and> a < p"
  shows "a ^ (ord a p) mod p = 1"
  proof -
    obtain d where d:"d\<ge>1 \<and> (a ^ d) mod p = 1 \<and> d \<le> p" using prime_has_ord assms by fastforce
    have "{d . d\<in> {1 .. p} \<and> (a ^ d) mod p = 1} \<noteq> {}" using d by auto
    thus ?thesis
      using Min_in[of "{d . d\<in> {1 .. p} \<and> (a ^ d) mod p = 1}"] by (simp add: ord_def)
  qed

lemma
  fixes p a :: nat
  assumes prime_p:"prime p"
  assumes "1 \<le>a \<and> a < p"
  shows ord_ge_1: "ord a p \<ge> 1" and ord_less_p: "ord a p \<le> p"
proof -
  obtain d where d:"d\<ge>1 \<and> (a ^ d) mod p = 1 \<and> d \<le> p" using prime_has_ord[OF assms] by fastforce
  have "{d . d\<in> {1 .. p} \<and> (a ^ d) mod p = 1} \<noteq> {}" using d by auto
  hence "ord a p \<in> {d . d\<in> {1 .. p} \<and> (a ^ d) mod p = 1}" 
    using Min_in[of "{d . d\<in> {1 .. p} \<and> (a ^ d) mod p = 1}"] ord_def[of a p] by force
  thus "ord a p \<ge> 1" "ord a p \<le> p" by auto
qed


lemma ord_min:
  assumes "prime p" "1 \<le> d" "1 \<le>a" "a < p" "a ^ d mod p = 1" shows "ord a p \<le> d"
proof -
  def Ord \<equiv> "{d \<in> {1..p}. a ^ d mod p = 1}"
  have fin: "finite Ord" by (auto simp: Ord_def)
  have in_ord: "ord a p \<in> Ord"
    using assms pow_ord_eq_1 ord_ge_1 ord_less_p by (auto simp: Ord_def)
  then have "Ord \<noteq> {}" by auto

  show ?thesis
  proof (cases "d \<le> p")
    case True
    then have "d \<in> Ord" using assms by (auto simp: Ord_def)
    with fin in_ord show ?thesis
      unfolding ord_def Ord_def[symmetric] by simp
  next
    case False
    then show ?thesis using in_ord by (simp add: Ord_def)
  qed
qed


lemma ord_elems :
  fixes p::nat
  fixes a::nat
  assumes prime_p:"prime p"
  assumes "1\<le>a \<and> a < p"
  shows "{a^x mod p | x . x \<in> UNIV} = {a^x mod p | x . x \<in> {0 .. ord a p - 1}}"
proof
  show "{a ^ x mod p |x. x \<in> {0..ord a p - 1}} \<subseteq> {a ^ x mod p |x. x \<in> UNIV}" by fast
  {
    fix y
    assume "y \<in> {a ^ x mod p |x. x \<in> UNIV}"
    then obtain x where x:"y = a^x mod p" by auto
    def r \<equiv> "x mod ord a p"
    then obtain q where q:"x = q * ord a p + r" using mod_eqD by atomize_elim presburger
    hence "y = (a^(q * ord a p) mod p * (a^r mod p)) mod p" 
      by (simp add: x mod_mult_eq[symmetric] comm_semiring_1_class.normalizing_semiring_rules(26)) 
    hence y:"y = (((a^ord a p mod p)^q) mod p * (a^r mod p)) mod p" 
      by (simp add: comm_semiring_1_class.normalizing_semiring_rules(7) 
          power_mod power_mult[symmetric])
    hence "y = a^r mod p" using assms prime_ge_2_nat[OF prime_p] by (simp add: pow_ord_eq_1)
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
  shows "(nat a ^ n) mod (nat p) = nat ((a ^ n) mod p)"
  using assms 
  by (simp add: int_one_le_iff_zero_less nat_mod_distrib order_less_imp_le nat_power_eq[symmetric])

lemma mod_nat_int_pow_eq2 :
  fixes n :: nat
  fixes p :: int
  fixes a :: int
  assumes "a > 1"
  assumes "p > 1"
  assumes "nat a ^ n mod (nat p) = 1"
  shows "a^n mod p = 1"
proof -
  have "nat ((a^n) mod p) = 1" using assms by (simp add: mod_nat_int_pow_eq)
  thus ?thesis by linarith
qed
  
lemma ord_elems_int :
  fixes p::int
  fixes a::int
  assumes prime_p:"prime p"
  assumes "1\<le>a \<and> a < p"
  shows "{a^x mod p | x . x \<in> UNIV} = {a^x mod p | x . x \<in> {0 .. ord (nat a) (nat p) - 1}}"
  (is "?L = ?R")
proof
  show "?R \<subseteq> ?L" by blast
  have "p\<ge>2" by (rule prime_ge_2_int[OF prime_p])
  {
    fix y
    assume "y \<in> {a ^ x mod p |x. x \<in> UNIV}"
    then obtain x where x:"y = a^x mod p" by auto
    then have y:"nat y = nat a^x mod (nat p)" using assms 
        by (metis less_le mod_nat_int_pow_eq nat_1' power_0 power_one prime_gt_1_int)
    have "prime (nat p)" using prime_p by (simp add: prime_int_def)
    have "1 \<le> nat a \<and> nat a < nat p" using assms(2) by linarith
    hence  nat_elem:"nat a^x mod (nat p) \<in>
                     {nat a^x mod (nat p) | x . x \<in> {0 .. ord (nat a) (nat p) - 1}}"
           using ord_elems[OF `prime (nat p)`] by blast
    have "{nat a^x mod (nat p) | x . x \<in> {0 .. ord (nat a) (nat p) - 1}} 
          \<subseteq> nat ` {a^x mod p | x . x \<in> {0 .. ord (nat a) (nat p) - 1}}"
    proof
      fix y
      assume "y \<in> {nat a^x mod (nat p) | x . x \<in> {0 .. ord (nat a) (nat p) - 1}}"
      then obtain x where x:"y = nat a^x mod (nat p) \<and> x\<in>{0 .. ord (nat a) (nat p) - 1}" by blast
      hence "nat a^x mod (nat p) = nat (a^x mod p)" using assms(2) `p\<ge>2` 
        by (metis Divides.transfer_nat_int_functions(2) 
            Nat_Transfer.transfer_nat_int_function_closures(4) 
            Nat_Transfer.transfer_nat_int_functions(4) int_one_le_iff_zero_less less_le not_less 
            zless_nat_conj)
      thus "y \<in> nat ` {a^x mod p | x . x \<in> {0 .. ord (nat a) (nat p) - 1}}" using x by blast
    qed
    hence "nat y \<in> nat ` {a^x mod p | x . x \<in> {0 .. ord (nat a) (nat p) - 1}}" 
      using y nat_elem by auto
    then obtain k where k:"nat y = nat (a^k mod p) \<and> k \<in> {0 .. ord (nat a) (nat p) - 1}" by blast
    hence "y = a^k mod p" using `p\<ge>2` by (simp add: transfer_nat_int_relations(1) x assms(1))
    hence "y \<in> ?R" using k by blast
  }
  thus "{a^x mod p | x . x\<in>(UNIV::nat set)} \<subseteq> {a^x mod p | x . x \<in> {0 .. ord (nat a) (nat p) - 1}}"
    by blast
qed
    
lemma ord_inj :
  fixes p::nat
  fixes a::nat
  assumes prime_p:"prime p"
  assumes "1<a \<and> a < p"
  shows "inj_on (\<lambda> x . a^x mod p) {0 .. ord a p - 1}"
proof (rule inj_onI, rule ccontr)
  fix x y assume A: "x \<in> {0 .. ord a p - 1}" "y \<in> {0 .. ord a p - 1}" "a ^ x mod p = a ^ y mod p" "x \<noteq> y"

  have "1 \<le> a \<and> a < p" using assms by auto
  have "1 mod p = 1" by (metis mod_less prime_gt_1_nat prime_p)
  have "finite {d \<in> {1..p}. a ^ d mod p = 1}" by auto

  { fix x y assume A: "x < y" "x \<in> {0 .. ord a p - 1}" "y \<in> {0 .. ord a p - 1}" "[a ^ x = a ^ y] (mod p) " "x \<noteq> y"
    hence "y - x < ord a p" by auto
    hence "y - x \<le> p" using `y - x < ord a p` assms ord_less_p[of p a] by force
    hence "y - x \<in> {1 .. p}" using A by force
    have cp:"coprime (a^x) p"
    proof (cases "x > 0")
      case True
        thus ?thesis using assms prime_imp_coprime_nat[OF prime_p] by (simp add : nat_dvd_not_less coprime_exp_nat gcd_semilattice_nat.inf_commute)
      next
      case False
        thus ?thesis by simp
    qed
    from A have "[a ^ x = a ^ (y - x) * a ^ x] (mod p)" by (simp add: power_add[symmetric])
    then have "[1 * a ^ x = a ^ (y - x) * a ^ x] (mod p)" by simp
    then have "[1 = a ^ (y - x)] (mod p)" using cp by (simp only: cong_mult_rcancel_nat)
    hence "a ^ (y - x) mod p = 1" using `1 mod p = 1` by (simp add : cong_nat_def)
    hence y_x:"y - x \<in> {d \<in> {1..p}. a ^ d mod p = 1}" using `y - x \<in> {1 .. p}` by blast
    have "min (y - x) (ord a p) = ord a p" using Min.in_idem[OF `finite {d \<in> {1 .. p} . a ^ d mod p = 1}` y_x] ord_def by auto
    with `y - x < ord a p` have False by linarith
  }
  note X = this

  { assume "x < y" with A X have False by (simp add: cong_nat_def) }
  moreover
  { assume "x > y" with A X cong_nat_def have False by fastforce }
  moreover
  { assume "x = y" then have False using A by auto}
  ultimately
  show False by fastforce
qed
  
lemma ord_inj_int :
  fixes p::nat
  fixes a::nat
  assumes prime_p:"prime p"
  assumes "1<a \<and> a < p"
  shows "inj_on (\<lambda> x . int a^x mod int p) {0 .. ord a p - 1}"
proof -
  {  fix x :: nat
    fix y :: nat
    assume x : "x \<in> {0 .. ord a p - 1}"
    assume y : "y \<in> {0 .. ord a p - 1}"
    assume "int a^x mod int p = int a^y mod int p"
    hence "int (a^x mod p) = int (a^y mod p)" 
      using Divides.transfer_int_nat_functions(2) of_nat_power by metis
    hence "a^x mod p = a^y mod p" by (simp add: int_int_eq)
    hence "x = y" using ord_inj[OF assms] inj_on_def[of "(\<lambda>x. a ^ x mod p)" "{0..ord a p - 1}"] x y 
      by blast
  } thus ?thesis using inj_on_def[of "(\<lambda> x . int a^x mod int p)" "{0..ord a p - 1}"] by blast
qed

lemma ord_dvd_pow_eq_1 :
  fixes a p k :: nat
  assumes "prime p" "1\<le>a \<and> a < p" "a ^ k mod p= 1"
  shows "ord a p dvd k"
proof -
  have "p\<ge>2" using `prime p` by (rule prime_ge_2_nat)
  def r \<equiv> "k mod ord a p"
  then obtain q where q:"k = r + q*ord a p" by (atomize_elim, simp add : mod_eqD)
  hence "[a^k = (a^r) * (a^(ord a p*q) mod p)] (mod p)" by (simp add : power_add cong_nat_def zmod_simps(3) nat_mult_commute)
  hence "[a^k = (a^r) * ((a^ord a p mod p)^q mod p)] (mod p)" by (simp add : power_mult power_mod)
  hence "[a^k = a^r] (mod p)" using `p\<ge>2` by (simp add : pow_ord_eq_1[OF assms(1-2)])
  hence "a^r mod p = 1" using assms(3) by (simp add : cong_nat_def)
  have "r < ord a p" using ord_ge_1[OF assms(1-2)] by (simp add: r_def)
  hence "r = 0" using `a^r mod p = 1` ord_def[of a p] ord_min[of p r a] assms(1-2) by linarith
  thus ?thesis using q by simp
qed

lemma dvd_gcd :
  fixes a b :: nat
  obtains q where "a * (b div gcd a b) = b*q"
proof
  have "a * (b div gcd a b) = (a div gcd a b) * b" by (simp add:  div_mult_swap dvd_div_mult)
  also have "\<dots> = b * (a div gcd a b)" by simp
  finally show "a * (b div gcd a b) = b * (a div gcd a b) " .
qed

lemma dvd_div_ge_1 :
  fixes a b :: nat
  assumes "a \<ge> 1" "b dvd a"
  shows "a div b \<ge> 1" 
  by (metis assms div_by_1 div_dvd_div div_less gcd_lcm_complete_lattice_nat.top_greatest
      gcd_lcm_complete_lattice_nat.top_le not_less)

lemma ord_pow_dvd_ord_elem :
  fixes p :: nat
  fixes a :: nat
  fixes n :: nat
  assumes a:"a \<in> {1 .. p - 1}"
  assumes prime_p:"prime p"
  shows "ord ((a^n) mod p) p = ord a p div gcd n (ord a p)"
proof -
  have "p\<ge>2" using prime_p by auto
  have "(a^n) ^ ord a p mod p = (a ^ ord a p) ^ n mod p" 
    by (simp add: nat_mult_commute[symmetric] power_mult[symmetric])
  hence "(a^n) ^ ord a p mod p = ((a ^ ord a p) mod p) ^ n mod p" by (simp add: power_mod)
  hence "(a^n) ^ ord a p mod p = 1 ^ n mod p" using assms by (auto simp add : pow_ord_eq_1[of p a])
  have eq:"(a^n) ^ (ord a p div gcd n (ord a p)) mod p 
           = a ^ (n * (ord a p div gcd n (ord a p))) mod p" by (simp add : power_mult[symmetric])
  obtain q where "n * (ord a p div gcd n (ord a p)) = ord a p * q" by (rule dvd_gcd)
  hence "(a^n) ^ (ord a p div gcd n (ord a p)) mod p = ((a ^ ord a p) mod p)^q mod p" 
    using eq by (simp add : power_mult power_mod)
  hence "(a^n) ^ (ord a p div gcd n (ord a p)) mod p = 1" 
    using  assms by (auto simp add : pow_ord_eq_1[of p a])
  hence pow_eq_1:"(a^n mod p) ^ (ord a p div gcd n (ord a p)) mod p = 1" by (simp add : power_mod)
  have "ord a p \<ge> 1" using ord_ge_1[of p a] assms by auto
  have ge_1:"ord a p div gcd n (ord a p) \<ge> 1"
  proof -
    have "gcd n (ord a p) dvd ord a p" by blast
    thus ?thesis by (rule dvd_div_ge_1[OF `ord a p \<ge> 1`])
  qed
  have "ord a p \<le> p" using ord_less_p[of p a] assms by auto
  have "ord a p div gcd n (ord a p) \<le> p"
  proof -
    have "ord a p div gcd n (ord a p) \<le> ord a p" by simp
    thus ?thesis using `ord a p\<le> p` by linarith
  qed
  hence ord_gcd_elem:"ord a p div gcd n (ord a p) \<in> {d \<in> {1..p}. (a^n mod p) ^ d mod p = 1}" 
    using ge_1 pow_eq_1 by force
  { fix d :: nat
    assume d_elem:"d \<in> {d \<in> {1..p}. ((a^n) mod p) ^ d mod p = 1}"
    assume d_lt:"d < ord a p div gcd n (ord a p)"
    hence pow_nd:"a^(n*d) mod p = 1" using d_elem 
      by (auto simp add : power_mult[symmetric] power_mod)
    hence "ord a p dvd n*d" using assms by (auto simp add : ord_dvd_pow_eq_1)
    then obtain q where "ord a p * q = n*d" by (metis dvd_mult_div_cancel)
    hence prod_eq:"(ord a p div gcd n (ord a p)) * q = (n div gcd n (ord a p)) * d" 
      by (simp add: dvd_div_mult)
    have cp:"coprime (ord a p div gcd n (ord a p)) (n div gcd n (ord a p))"
    proof -
      have "coprime (n div gcd n (ord a p)) (ord a p div gcd n (ord a p))" 
        using div_gcd_coprime_nat[of n "ord a p"] ge_1 by fastforce
      thus ?thesis by (simp add: gcd_commute_nat)
    qed
    have dvd_d:"(ord a p div gcd n (ord a p)) dvd d"
    proof -
      have "ord a p div gcd n (ord a p) dvd (n div gcd n (ord a p)) * d" using prod_eq 
        by (metis dvd_triv_right nat_mult_commute)
      hence "ord a p div gcd n (ord a p) dvd d * (n div gcd n (ord a p))" 
        by (simp add:  nat_mult_commute)
      thus ?thesis using coprime_dvd_mult_nat[OF cp, of d] by fastforce
    qed
    have "d > 0" using d_elem by simp
    hence "ord a p div gcd n (ord a p) \<le> d" using dvd_d by (simp add : Nat.dvd_imp_le)
    hence False using d_lt by simp
  } hence ord_gcd_min: "\<And> d . d \<in> {d \<in> {1..p}. ((a^n) mod p) ^ d mod p = 1} 
                        \<Longrightarrow> d\<ge>ord a p div gcd n (ord a p)" by fastforce
  have fin:"finite {d \<in> {1..p}. (a^n mod p) ^ d mod p = 1}" by auto
  thus ?thesis using Min_eqI[OF fin ord_gcd_min ord_gcd_elem] 
    by (simp add : ord_def[of "a^n mod p" p])
qed

lemma prime_p_impl_ord_1_eq_1 :
  fixes p :: nat
  assumes prime_p:"prime p"
  shows "ord 1 p = 1"
proof -
  have "p \<ge> 2" using prime_p by (simp add: prime_ge_2_nat)
  thus ?thesis using ord_ge_1[OF prime_p] ord_min[OF prime_p, of 1 1] by force
qed  

lemma ord_dvd_group_order :
  fixes p :: nat
  fixes a :: nat
  assumes a:"a \<in> {1 .. p - 1}"
  assumes prime_p:"prime p"
  shows "ord a p dvd p - 1"
proof (cases "a = 1")
  case True
    thus ?thesis  using prime_p_impl_ord_1_eq_1[OF prime_p] by simp
  next
  case False
    hence "a > 1" using a by simp
    show ?thesis
  proof -
    interpret R: residues_prime "int p" "residue_ring (int p)"
      by (simp add: transfer_int_nat_prime prime_p residues_prime_def)
    let ?G = "\<lparr> carrier = carrier (residue_ring (int p)) - {\<zero>\<^bsub>residue_ring (int p)\<^esub>}, 
                mult = op \<otimes>\<^bsub>residue_ring (int p)\<^esub>, one = \<one>\<^bsub>residue_ring (int p)\<^esub>\<rparr>"
    have "prime (int p)" by (simp add: transfer_int_nat_prime assms)
    have "field (residue_ring (int p))" by (simp add: R.is_field)
    hence "group ?G" by (rule field.field_mult_group)
    have res: "residues (int p)" by (simp add: R.is_residues) 
    have ops_eq:"\<forall> (x :: int) (y :: nat) . x (^) \<^bsub>residue_ring (int p)\<^esub> y = x (^) \<^bsub>?G\<^esub> y" 
      by (simp add: nat_pow_def)
    have "1 \<le> int a \<and> int a < int p" using assms by auto
    have "p \<ge> 2" using assms by auto
    {
       fix x
       assume x : "x \<in> {(int a) ^ i mod (int p) | i . i \<in> {0 .. ord a p - 1}}"
       then obtain i where i:"i \<in> {0 .. ord a p - 1} \<and> x = int a ^ i mod (int p)" by auto
       hence "a ^ i mod p \<in> {1 .. p - 1}" using assms p_prime_impl_mult_group_closed by presburger
       have nat_trans : "a ^ i mod p = nat (int a ^ i mod (int p))" 
        by (simp add: zmod_int[symmetric] zpower_int)
       hence "int a ^ i mod (int p) \<in> {1 .. int p - 1}" using nat_trans `a ^ i mod p \<in> {1 .. p - 1}` 
        by force
       hence "x \<in> carrier ?G" by (simp add: i R.zero_cong)
    } hence subs : "{int a ^ i mod (int p) | i . i \<in> {0 .. ord a p - 1}} \<subseteq> carrier ?G" by auto
    have sub_p:"subgroup {(int a) ^ i mod (int p) | i . i \<in> {0 .. ord a p - 1}} ?G"
    proof
     show "{(int a) ^ i mod (int p) | i . i \<in> {0 .. ord a p - 1}} \<subseteq> carrier ?G" using subs by auto
     next
      fix x
      fix y
      assume x:"x \<in> {(int a) ^ i mod (int p) | i . i \<in> {0 .. ord a p - 1}}"
      assume y:"y \<in> {(int a) ^ i mod (int p) | i . i \<in> {0 .. ord a p - 1}}"
      obtain i where i:"x = (int a) ^ i mod (int p)" and i2:"i \<in> UNIV" using x by auto
      obtain j where j:"y = (int a) ^ j mod (int p)" and j2:"j \<in> UNIV" using y by auto
      hence xy:"x \<otimes>\<^bsub>?G\<^esub> y = (int a^(i+j)) mod (int p)" by (simp add: power_add R.mult_cong i)
      hence "(int a^(i+j)) mod (int p) \<in> {int a ^ x mod int p |x. x \<in> {0..ord a p - 1}}" 
        using ord_elems_int[of "int p" "int a"] `prime (int p)` `1 \<le> int a \<and> int a < int p` by auto
      thus "x \<otimes>\<^bsub>?G\<^esub> y \<in> {(int a) ^ i mod (int p) | i . i \<in> {0 .. ord a p - 1}}" 
        using xy ord_elems assms by auto
     next
      have "1 mod (int p)= int a ^ 0 mod int p" by simp
      hence "1 mod (int p) \<in> {int a ^ i mod int p |i. i \<in> {0..ord a p - 1}}" by force
      thus "\<one>\<^bsub>?G\<^esub> \<in> {int a ^ i mod int p |i. i \<in> {0..ord a p - 1}}" by (simp add: R.one_cong)
    next
     fix x
     assume x:"x \<in> {int a ^ i mod int p |i. i \<in> {0..ord a p - 1}}"
     hence x_in_carrier:"x \<in> carrier ?G" using subs by auto
     then obtain d::nat where d:"x (^)\<^bsub>?G\<^esub> d = \<one>\<^bsub>?G\<^esub>" and "d\<ge>1" 
      using group.finite_group_elem_finite_ord[OF `group ?G`] by auto
     hence "(x mod int p) (^)\<^bsub>residue_ring (int p)\<^esub> d = 1 mod int p" 
      using ops_eq x by (auto simp add: R.one_cong)
     hence x_d: "x ^ d mod int p = 1" by (simp add: R.one_cong[symmetric] R.res_one_eq R.pow_cong)
     have inv_1:"x^d mod int p = (x^(d - 1) * x) mod int p"
     proof -
      have "x^d = x^(d - 1)*x" using `d\<ge>1` by (simp add: power_eq_if[of x d])
      thus ?thesis by simp
     qed
     have inv_2:"x^d mod int p = (x * x^(d - 1)) mod int p" 
      using `d\<ge>1` by (simp add: power_eq_if[of x d])
     have inv_1':"\<one>\<^bsub>?G\<^esub>=(x^(d - 1) mod int p) \<otimes>\<^bsub>?G\<^esub> (x mod int p)" 
      using x_d by (simp add: R.mult_cong[symmetric] R.res_one_eq inv_1)
     have inv_2':"\<one>\<^bsub>?G\<^esub>=(x mod int p) \<otimes>\<^bsub>?G\<^esub> (x^(d - 1) mod int p)" 
      using x_d by (simp add: R.mult_cong[symmetric] R.res_one_eq inv_2)
     have elem:"x ^ (d - 1) mod int p \<in> {int a ^ i mod int p |i. i \<in> {0..ord a p - 1}}"
      proof -
       obtain i::nat where i:"x = int a ^ i mod int p" using x by auto
       hence "x ^ (d - 1) mod int p \<in> {int a ^ i mod int p |i. i \<in> UNIV}" 
        by (auto simp add: comm_semiring_1_class.normalizing_semiring_rules(31) power_mod)
       thus ?thesis using ord_elems_int[of "int p" "int a"] `prime (int p)` 
                          `1 \<le> int a \<and> int a < int p` by auto
      qed
      have "x = x mod int p" using `p\<ge>2` x by force
      hence inv:"inv\<^bsub>?G\<^esub> x = x^(d - 1) mod int p" 
        using inv_1' inv_2' m_inv_def[of ?G "x mod int p"] res `group ?G` group.inv_equality 
              x_in_carrier by fastforce
      thus "inv\<^bsub>?G\<^esub> x \<in> {int a ^ i mod int p |i. i \<in> {0..ord a p - 1}}" using elem inv by auto
   qed
   hence card_dvd:"card {int a ^ i mod int p |i. i \<in> {0..ord a p - 1}} dvd order ?G" 
    using group.lagrange_ex[OF `group ?G`, of "{int a ^ i mod int p |i. i \<in> {0..ord a p - 1}}"] 
    by simp
   have "carrier ?G = {1 .. int p - 1}" by (auto simp add: R.res_carrier_eq R.zero_cong)
   hence "order ?G = p - 1" using order_def[of ?G] by simp
   have "inj_on (\<lambda> i . int a ^ i mod int p) {0..ord a p - 1}" using ord_inj_int assms `a>1` by simp
   hence cards_eq:"card ((\<lambda> i . int a ^ i mod int p) ` {0..ord a p - 1}) = card {0..ord a p - 1}" 
    using card_image[of "(\<lambda> i . int a ^ i mod int p)" "{0..ord a p - 1}"] by auto
   have "(\<lambda> i . int a ^ i mod int p) ` {0..ord a p - 1} 
         = {int a ^ i mod int p |i. i \<in> {0..ord a p - 1}}" by auto
   hence "card {int a ^ i mod int p |i. i \<in> {0..ord a p - 1}} = card {0..ord a p - 1}"
          using cards_eq by simp
   hence "card {int a ^ i mod int p |i. i \<in> {0..ord a p - 1}} = ord a p"
          using ord_ge_1 assms by fastforce
   thus ?thesis using card_dvd  by (simp add: `order ?G = p - 1`)
  qed
qed

definition phi' :: "nat => nat"
  where "phi' m = card({ x. 0 < x \<and> x \<le> m \<and> gcd x m = 1})"

lemma phi'_altdef :
  shows "phi' m = card {x. 1\<le> x \<and> x \<le> m \<and> gcd x m = 1}"
proof -
  have "{x. 1 \<le> x \<and> x \<le> m \<and> gcd x m = 1} = {x. 0 < x \<and> x \<le> m \<and> gcd x m = 1}" by force
  thus ?thesis using phi'_def by presburger
qed

lemma phi'_nonzero :
  assumes "m > 0"
  shows "phi' m > 0"
proof -
  have "1 \<in> {x. 1 \<le> x \<and> x \<le> m \<and> gcd x m = 1}" using assms by simp
  hence "card {x. 1 \<le> x \<and> x \<le> m \<and> gcd x m = 1} > 0" using  card_gt_0_iff by fast
  thus ?thesis using phi'_altdef by simp
qed

lemma phi'_1_eq_1 :
  shows "phi' 1 = 1"
proof -
  have "{x . 0 < x \<and> x \<le> 1 \<and> gcd x 1 = 1} = {1::nat}"
  proof
    case goal1
    {
      fix x :: nat
      assume "x \<in> {x. 0 < x \<and> x \<le> 1 \<and> gcd x 1 = 1}"
      hence "x \<in> {1}" by auto
    } thus ?case by blast
    case goal2
      thus ?case by simp
  qed
  thus ?thesis by (simp add: phi'_def)
qed  

lemma gcd_ge_common_divisor:
  fixes m n d :: nat
  assumes "d dvd m" "d dvd n" "m>0"
  shows "gcd m n \<ge> d" using assms by (simp add: dvd_nat_bounds)

lemma sum_phi_factors :
 fixes n :: nat
 assumes "n > 0"
 shows "(\<Sum>d \<in> {d . d dvd n} . phi' d) = n"
 proof -
   let ?f = "\<lambda> d . {m . m \<in> {1 .. n} \<and> n div gcd m n = d}"
   { fix d :: nat
     assume d:"d dvd n"
     {
       fix m::nat
       assume m:"m \<in> {1 .. n} \<and> n div gcd m n = d"
       hence gcd_1:"gcd (m div gcd m n) d = 1" using assms div_gcd_coprime_nat by blast
       have ge_1:"1 \<le> m div gcd m n" using m dvd_div_ge_1 by auto
       have le_d:"m div gcd m n \<le> d" using m by (auto simp add: div_le_mono)
       have "m div gcd m n * n = m * n div gcd m n" 
        by (simp add: nat_mult_commute div_mult_swap[OF gcd_dvd1_nat[of m n], of n])
       also have "\<dots> = m * d" 
        by (simp add: m div_mult_swap[OF gcd_dvd2_nat[of m n], of m, symmetric])
       finally have "m div gcd m n * n div d = m" 
        using  d  assms by (auto simp add:)
       hence "m \<in> {a * n div d | a . 1 \<le> a \<and> a \<le> d \<and> gcd a d = 1}" using gcd_1 le_d ge_1 by force
     }
     moreover
     {
       fix a :: nat
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
        using ge_1 le_n by fastforce
     }
     ultimately have "{a * n div d | a . 1 \<le> a \<and> a \<le> d \<and> gcd a d = 1} 
                      = {m . m \<in> {1 .. n} \<and> n div gcd m n = d}" by blast
   }
   hence d_seteq:"\<And> d . d dvd n \<Longrightarrow> card {a * n div d | a . 1 \<le> a \<and> a \<le> d \<and> gcd a d = 1}
                                    = card {m . m \<in> {1 .. n} \<and> n div gcd m n = d}" by presburger
   {
     fix d
     assume d:"d dvd n"
     have "card {a * n div d | a . 1 \<le> a \<and> a \<le> d \<and> gcd a d = 1}
           = card {a . 1 \<le> a \<and> a \<le> d \<and> gcd a d = 1}" using inj_on_def
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
      using phi'_altdef by auto
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
      {
        fix m assume m : "m \<in> {1 .. n}"
        hence  "(n div gcd m n) dvd n" 
          using dvd_triv_right[of "n div gcd m n" "gcd m n"] by (simp add: dvd_mult_div_cancel)
        hence "m \<in> (\<Union>d\<in>{d \<in> UNIV. d dvd n}. {m \<in> {1..n}. n div gcd m n = d})" using m by blast
      }
      thus "{1..n} \<subseteq> (\<Union>d\<in>{d \<in> UNIV. d dvd n}. {m \<in> {1..n}. n div gcd m n = d})" by auto
    qed
   thus ?thesis using sum_card by force
 qed

theorem residue_prime_mult_group_has_gen :
 fixes p :: nat
 assumes prime_p : "prime p"
 shows "\<exists> a \<in> {1 .. p - 1} . {1 .. p - 1} = {a^i mod p|i . i \<in> UNIV}"
 proof -
  have "p\<ge>2" using prime_p by (metis prime_ge_2_nat)
  let ?N = "\<lambda> x . card {a . a \<in> {1 .. p - 1} \<and> ord a p = x}"
  have fin: "finite {d . d \<in> UNIV \<and> d dvd p - 1 }" using `p\<ge>2` by (simp add: dvd_nat_bounds)
  { fix i j :: nat assume "i \<noteq> j"
    hence "(\<lambda> x . {a . a \<in> {1 .. p - 1} \<and> ord a p = x}) i 
           \<inter> (\<lambda> x . {a . a \<in> {1 .. p - 1} \<and> ord a p = x}) j = {}" by auto
  } hence sum_disjoint_card:"(\<Sum> d \<in> {d . d \<in> UNIV \<and> d dvd p - 1 } . ?N d)
     = card (UNION {d . d \<in> UNIV \<and> d dvd p - 1 } (\<lambda> x . {a . a \<in> {1 .. p - 1} \<and> ord a p = x}))"
     using card_UN_disjoint[OF fin, of "\<lambda> x . {a . a \<in> {1 .. p - 1} \<and> ord a p = x}"] by simp
  have "UNION {d . d \<in> UNIV \<and> d dvd p - 1 } (\<lambda> x . {a . a \<in> {1 .. p - 1} \<and> ord a p = x})
        = {1 .. p - 1}" (is "UNION ?L ?f = ?R")
  proof
    show "UNION ?L ?f \<subseteq> ?R" by auto
    { fix x :: nat assume x:"x \<in> {1 .. p - 1}"
      have "ord x p dvd p - 1" by (rule ord_dvd_group_order[OF x prime_p])
      hence "x \<in> UNION ?L ?f" using `p\<ge>2` dvd_nat_bounds[of "p - 1" "ord x p"] x by blast
    } thus "?R \<subseteq> UNION ?L ?f" by blast
  qed
  hence sum_Ns_eq:"(\<Sum> d \<in> {d . d \<in> UNIV \<and> d dvd p - 1 } . ?N d) = p - 1"
    using sum_disjoint_card by auto
  { fix d :: nat
    assume "d dvd p - 1" "?N d > 0" 
    then obtain a where a:"a \<in> {1 .. p - 1} \<and> ord a p = d" by (auto simp add: card_gt_0_iff)
    have d_neq_0:"d\<noteq>0" using `p\<ge>2` by (simp add : dvd_pos_nat[OF _ `d dvd p - 1`])
    {
    assume "a > 1"
    have card_le_d : "finite {x . x \<in> {0 .. p - 1} \<and> x ^ d mod p = 1} 
                       \<and> card {x . x \<in> {0 .. p - 1} \<and> x ^ d mod p = 1} \<le> d" 
          using d_neq_0 num_roots_le_deg[OF prime_p] by blast
     have subs:"{a^n mod p| n . n \<in> {0 .. d - 1}} \<subseteq> {x . x \<in> {0 .. p - 1} \<and> x ^ d mod p = 1}"
      proof
        fix x assume "x \<in> {a ^ n mod p|n. n \<in> {0..d - 1}}"
        then obtain n where n:"x = a^n mod p \<and> n \<in> {0.. d - 1}" by auto
        hence "x < p" using `p\<ge>2` by simp
        hence x_bounds:"x \<in> {0 .. p - 1}" by fastforce
        have a_d:"a^d mod p = 1" using a by (auto simp add: pow_ord_eq_1[OF prime_p])
        have "x^d mod p = a^(n*d) mod p" using n by (simp add: power_mod power_mult)
        also have "\<dots> = (a^d mod p)^n mod p" by (simp add: nat_mult_commute power_mult power_mod)
        finally have "x^d mod p = 1" using a_d `p\<ge>2` by simp
        thus "x \<in> {x . x \<in> {0 .. p - 1} \<and> x ^ d mod p = 1}" using x_bounds by blast
      qed
    have inj:"inj_on (\<lambda> n. a^n mod p) {0 .. d - 1}" using ord_inj[OF prime_p] a `a > 1` by auto
    have "{a^n mod p| n . n \<in> {0 .. d - 1}} = ((\<lambda> n. a^n mod p) ` {0 .. d - 1})" by auto
    hence cards_eq:"card {a^n mod p| n . n \<in> {0 .. d - 1}} = card {0 .. d - 1}" using inj 
      by (simp add: card_image)
    have "card {0 .. d - 1} = d" using `p\<ge>2` `d dvd p - 1`
      by (simp add: dvd_nat_bounds[of "p - 1" d])
    hence "card {a^n mod p| n . n \<in> {0 .. d - 1}} = d" using cards_eq by auto
    hence set_eq1:"{a^n mod p| n . n \<in> {0 .. d - 1}} = {x. x \<in> {0 .. p - 1} \<and> x ^ d mod p = 1}" 
      using card_seteq[OF _ subs] card_le_d by presburger
    have set_eq2:"{a \<in> {1 .. p - 1} . ord a p = d} 
                  = {a^n mod p| n . n \<in> {1 .. d} \<and> ord (a^n mod p) p = d}"
    proof
    { fix x :: nat
      assume x:"x \<in> {1 .. p - 1} \<and> ord x p = d"
      hence "x \<in> {x. x \<in> {0 .. p - 1} \<and> x ^ d mod p = 1}"
        by (auto simp add: pow_ord_eq_1[OF prime_p])
      then obtain n where n:"x = a^n mod p \<and> n \<in> {0 .. d - 1}" using set_eq1 by blast
      def n' \<equiv> "if n = 0 then d else n" 
      have n'1:"n' \<in> {1 .. d}" using n dvd_nat_bounds[OF _ `d dvd p - 1`] `p\<ge>2`
        by (auto simp add: n'_def)
      hence "x = a^n' mod p" using a n by (auto simp add: pow_ord_eq_1[OF prime_p] n'_def)
      hence "x \<in> {a^n mod p| n . n \<in> {1 .. d} \<and> ord (a^n mod p) p = d}" using x n'1 by fast
    } thus "{a \<in> {1 .. p - 1} . ord a p = d} 
            \<subseteq> {a^n mod p| n . n \<in> {1 .. d} \<and> ord (a^n mod p) p = d}" by blast
    { fix x :: nat
      assume x:"x \<in> {a^n mod p| n . n \<in> {1 .. d} \<and> ord (a^n mod p) p = d}"
      hence "x \<in> {a \<in> {1 .. p - 1} . ord a p = d}"
        using p_prime_impl_mult_group_closed[OF _ prime_p] a by auto
    } thus "{a^n mod p| n . n \<in> {1 .. d} \<and> ord (a^n mod p) p = d}
            \<subseteq> {a \<in> {1 .. p - 1} . ord a p = d}" by blast
    qed

    have inj1:"inj_on (\<lambda> n . a^n mod p) {0 .. d - 1}" using prime_p ord_inj a `a>1` by auto
    {
        fix i j :: nat
        assume i : "i \<in> {1 .. d}"
        assume j : "j \<in> {1 .. d}"
        assume ij : "a^i mod p = a^j mod p"
        assume "i = d" "j \<noteq> d"
        hence j':"j \<in> {0 .. d - 1}" using j by auto
        have "a^j mod p = a^0 mod p" using a `p\<ge>2`
          by (auto simp add: ij[symmetric] `i=d` pow_ord_eq_1[OF prime_p])
        hence "j = 0" using inj1 inj_on_def[of "\<lambda>n. a ^ n mod p" "{0 .. d - 1}"] j' by auto
        hence "i = j" using j by simp
    } note i_eq_d_j_neq_d = this
    {
      fix i j :: nat
      assume i : "i \<in> {1 .. d}"
      assume j : "j \<in> {1 .. d}"
      assume ij : "a^i mod p = a^j mod p"
      {
        assume "j \<noteq> d" "i \<noteq> d"
        hence i':"i \<in> {0 .. d - 1}" using i by force
        have "j \<in> {0 .. d - 1}" using j `j\<noteq>d` by fastforce
        hence "i = j" using ij i' inj1 inj_on_def[of "(\<lambda>n. a ^ n mod p)" "{0..d - 1}"] by blast
      } hence "i = j" using i_eq_d_j_neq_d[OF j i] i_eq_d_j_neq_d[OF i j ij] ij by force
    }  hence inj2:"inj_on (\<lambda> n . a^n mod p) {1 .. d}" using inj_on_def by blast
    hence inj3:"inj_on (\<lambda> n . a^n mod p) {n . n \<in> {1 .. d} \<and> ord (a^n mod p) p = d}"
      using inj_on_def[of "\<lambda> n . a^n mod p" "{1 .. d}"] inj_on_def by fast
    hence card_proj_eq: "card ((\<lambda> n . a^n mod p) ` {n . n \<in> {1 .. d} \<and> ord (a^n mod p) p = d})
                         = card {k . k \<in> {1 .. d} \<and> ord (a^k mod p) p = d}"
                         using card_image[OF inj3] by fast
    have "{a^n mod p| n . n \<in> {1 .. d} \<and> ord (a^n mod p) p = d}
          = (\<lambda> n . a^n mod p) ` {n . n \<in> {1 .. d} \<and> ord (a^n mod p) p = d}" by blast
    hence card_proj_eq2:"card {a^n mod p| n . n \<in> {1 .. d} \<and> ord (a^n mod p) p = d}
                         = card {k . k \<in> {1 .. d} \<and> ord (a^k mod p) p = d}" 
                        using card_proj_eq by presburger
    { fix k assume k:"k \<in> {1 .. d} \<and> ord (a^k mod p) p = d"
      hence *:"d = d div (gcd k d)" using ord_pow_dvd_ord_elem[OF _ prime_p] a by simp
      have "gcd k d = 1"
      proof (rule ccontr)
        assume "gcd k d \<noteq> 1" thus False
        proof (cases "gcd k d = 0")
          case True thus False by (simp add: d_neq_0  *[symmetric])
          next
          case False
            hence "gcd k d > 1" using `gcd k d \<noteq> 1` by linarith
            hence "d div (gcd k d) < d" using d_neq_0 by simp
            thus False using * by simp
        qed
      qed
    } moreover
    { fix k assume k:"k \<in> {1 .. d} \<and> gcd k d = 1"
      hence "ord (a^k mod p) p = d" using ord_pow_dvd_ord_elem[OF _ prime_p] a by presburger
    }
    ultimately have "{k \<in> {1 .. d} . gcd k d = 1} = {k . k \<in> {1 .. d} \<and> ord (a^k mod p) p = d}"
      by fast
    hence "?N d = phi' d" using set_eq2 card_proj_eq2 by (simp add: phi'_altdef)
    }
    moreover
    {
      assume "\<not> a > 1"
      hence "a ^ 1 mod p = 1" using `p\<ge>2` a by auto
      hence "d = 1" using ord_min[OF prime_p, of 1 a] a d_neq_0 by force
      have "{a |a. a \<in> {1..p - 1} \<and> ord a p = d} = {1}"
      proof
        case goal1
          { fix x assume x:"x \<in> {a |a. a \<in> {1..p - 1} \<and> ord a p = d}"
            hence "x = 1" using `p\<ge>2` x pow_ord_eq_1[OF prime_p, of x] `d = 1`  by force
          } thus ?case by blast
        case goal2 
          show ?case using prime_p_impl_ord_1_eq_1[OF prime_p] `p \<ge> 2` `d = 1` by force
      qed
      hence "?N d = phi' d" using `d = 1` phi'_1_eq_1 by simp
    }
    ultimately have "?N d = phi' d" by linarith
  } note N_d_eq_phi'_d = this
  { fix d assume d:"d dvd (p - 1)"
    have "card {a |a. a \<in> {1..p - 1} \<and> ord a p = d} \<le> phi' d"
    proof cases
      assume "card {a |a. a \<in> {1..p - 1} \<and> ord a p = d} = 0" thus ?thesis by presburger
      next
      assume "card {a |a. a \<in> {1..p - 1} \<and> ord a p = d} \<noteq> 0"
      hence "card {a |a. a \<in> {1..p - 1} \<and> ord a p = d} > 0" by fast
      thus ?thesis using N_d_eq_phi'_d d by auto
    qed
  }
  hence all_le:"\<And>i. i \<in> {d | d . d \<in> UNIV \<and> d dvd p - 1 } 
        \<Longrightarrow> (\<lambda> i . card {a |a. a \<in> {1..p - 1} \<and> ord a p = i}) i \<le> (\<lambda> i . phi' i) i" by fast
  hence le:"(\<Sum>i\<in>{d |d. d \<in> UNIV \<and> d dvd p - 1}. ?N i) 
            \<le> (\<Sum>i\<in>{d |d. d \<in> UNIV \<and> d dvd p - 1}. phi' i)"
            using setsum_mono[of "{d | d . d \<in> UNIV \<and> d dvd p - 1}"
                  "\<lambda> i . card {a |a. a \<in> {1..p - 1} \<and> ord a p = i}"] by presburger
  have "p - 1 = (\<Sum> d \<in> {d | d . d \<in> UNIV \<and> d dvd p - 1 } . phi' d)" using `p\<ge>2`
    by (simp add: sum_phi_factors)
  hence eq:"(\<Sum>i\<in>{d |d. d \<in> UNIV \<and> d dvd p - 1}. ?N i) = (\<Sum>i\<in>{d |d. d \<in> UNIV \<and> d dvd p - 1}. phi' i)" using le sum_Ns_eq by presburger
  have "\<And>i. i \<in> {d | d . d \<in> UNIV \<and> d dvd p - 1 } \<Longrightarrow> ?N i = (\<lambda> i . phi' i) i"
  proof (rule ccontr)
    fix i
    assume i1:"i \<in> {d |d. d \<in> UNIV \<and> d dvd p - 1}"
    assume "?N i \<noteq> phi' i"
    hence N_eq_0:"?N i = 0" using N_d_eq_phi'_d[of i] i1 by fast
    have "0 < i" using `p\<ge>2` i1 by (simp add: dvd_nat_bounds[of "p - 1" i])
    hence "?N i < phi' i" using phi'_nonzero N_eq_0 by presburger
    hence "(\<Sum>i\<in>{d. d \<in> UNIV \<and> d dvd p - 1}. ?N i) < (\<Sum>i\<in>{d. d \<in> UNIV \<and> d dvd p - 1}. phi' i)"
      using setsum_strict_mono_ex1[OF `finite {d. d \<in> UNIV \<and> d dvd p - 1}`, of "?N" "\<lambda> i . phi' i"]
            i1 all_le by auto
    thus False using eq by force
  qed
  hence "?N (p - 1) > 0" using `p\<ge>2` by (simp add: phi'_nonzero)
  then obtain a where a:"a \<in> {1..p - 1}" and a_ord:"ord a p = p - 1"
    by (auto simp add: card_gt_0_iff)
  hence a':"1 \<le> a \<and> a < p" by auto
  hence set_eq:"{a^i mod p|i . i \<in> UNIV} = (\<lambda> x . a^x mod p) ` {0 .. ord a p - 1}"
    using ord_elems[OF prime_p, of a] by auto
  have card_eq:"card ((\<lambda> x . a^x mod p) ` {0 .. ord a p - 1}) = card {0 .. ord a p - 1}"
  proof (cases "a > 1")
    case True
     thus ?thesis using card_image[of "(\<lambda>x. a ^ x mod p)" "{0..ord a p - 1}"]
                        ord_inj[OF prime_p, of a] a' by blast
    next
    case False
      thus ?thesis using a' prime_p_impl_ord_1_eq_1[OF prime_p] by simp
  qed
  hence "card ((\<lambda> x . a^x mod p) ` {0 .. ord a p - 1}) = card {0 ..p - 2}"
    using card_eq by (simp add: a_ord)
  hence card_p_minus_1:"card {a^i mod p|i . i \<in> UNIV} =  p - 1" using set_eq `p\<ge>2` by auto
  have "{a^i mod p|i . i \<in> UNIV} \<subseteq> {1 .. p - 1}" 
    using p_prime_impl_mult_group_closed[OF _ prime_p] a by blast
  hence "{1 .. p - 1} = {a^i mod p|i . i \<in> UNIV}" 
    using card_seteq[of "{1 .. p - 1}" "{a^i mod p|i . i \<in> UNIV}"] card_p_minus_1 `p\<ge>2` by simp
  thus ?thesis using a by blast
 qed

theorem lehmer_backwards:
 assumes prime_p:"prime p"
 shows "\<exists> a. [a^(p - 1) = 1] (mod p) \<and> (\<forall> x . 0 < x \<longrightarrow> x \<le> p - 2 \<longrightarrow> [a^x \<noteq> 1] (mod p))"
 proof -
   have "p \<ge> 2" by (rule prime_ge_2_nat[OF prime_p])
   obtain a where a:"a \<in> {1 .. p - 1} \<and> {1 .. p - 1} = {a^i mod p|i . i \<in> UNIV}"
    using residue_prime_mult_group_has_gen[OF prime_p] by blast
  {
   { fix x::nat assume x:"0 < x \<and> x \<le> p - 2 \<and> [a^x = 1] (mod p)"
     have "{a^i mod p|i . i \<in> UNIV} = {a^i mod p | i . 0 < i \<and> i \<le> x}"
     proof
      show "{a ^ i mod p |i. 0 < i \<and> i \<le> x} \<subseteq> {a ^ i mod p |i. i \<in> UNIV}" by blast
      { fix y assume y:"y \<in> {a^i mod p|i . i \<in> UNIV}"
        then obtain i where i:"y = a^i mod p" by auto
        def q \<equiv> "i div x" def r \<equiv> "i mod x"
        have "i = q*x + r" by (simp add: r_def q_def)
        hence y_q_r:"y = (((a ^ (q*x)) mod p) * ((a ^ r) mod p)) mod p"
          by (simp add: i power_add mod_mult_eq[symmetric])
        have "a ^ (q*x) mod p = (a ^ x mod p) ^ q mod p"
          by (simp add: power_mod nat_mult_commute power_mult[symmetric])
        hence y_r:"y = a ^ r mod p" using `p\<ge>2` x by (simp add: cong_nat_def y_q_r)
        have "y \<in> {a ^ i mod p |i. 0 < i \<and> i \<le> x}"
        proof (cases)
          assume "r = 0"
            hence "y = a^x mod p" using `p\<ge>2` x by (simp add: cong_nat_def y_r)
            thus ?thesis using x by blast
          next
          assume "r \<noteq> 0"
            thus ?thesis using x by (auto simp add: y_r r_def)
        qed
      }
      thus " {a ^ i mod p|i. i \<in> UNIV} \<subseteq> {a ^ i mod p |i. 0 < i \<and> i \<le> x}" by auto
    qed
    hence gen_eq:"{1 .. p - 1} = {a^i mod p | i . 1 \<le> i \<and> i \<le> x}" using a by auto
    have "{a^i mod p | i . 1 \<le> i \<and> i \<le> x} = (\<lambda> i. a^i mod p) ` {1..x}" by auto
    hence "card {a^i mod p | i . 1 \<le> i \<and> i \<le> x} = card ((\<lambda> i. a^i mod p) ` {1..x})" by auto
    hence "card {a^i mod p | i . 1 \<le> i \<and> i \<le> x} \<le> p - 2"
      using Finite_Set.card_image_le[of "{1..x}" "\<lambda> i. a^i mod p"] x by auto
    hence "card {1 .. p - 1} \<noteq> card {a^i mod p | i. 1 \<le> i \<and> i \<le> x}" using `p\<ge>2` by auto
    hence False using gen_eq by metis
   }
   hence "\<forall> x . 0 < x \<longrightarrow> x \<le> p - 2 \<longrightarrow> [a^x \<noteq> 1] (mod p)" by auto
 } note a_is_gen = this
 {
    assume "a>1"
    have "\<not> p dvd a "
    proof (rule ccontr)
      assume "\<not> \<not> p dvd a"
      hence "p dvd a" by auto
      have "p \<le> a" using dvd_nat_bounds[OF _ `p dvd a`] a by simp
      thus False using `a>1` a by force
    qed
    hence "coprime a p" using prime_imp_coprime_nat[OF prime_p]  by (simp add: gcd_commute_nat)
    hence "coprime (int a) (int p)" by (simp add: transfer_int_nat_gcd(1))
    have "phi (int p) = p - 1" by (simp add: prime_int_def phi_prime prime_p)
    hence "[a^(p - 1) = 1] (mod p)" using euler_theorem[OF _ `coprime (int a) (int p)`]
      by (simp add: of_nat_power transfer_int_nat_cong[symmetric])
  }
  hence "[a^(p - 1) = 1] (mod p)" using a by fastforce
  thus ?thesis using a_is_gen by auto
 qed

theorem lehmer_extended_backwards:
 assumes prime_p:"prime(p)"
 shows "\<exists> a . [a^(p - 1) = 1] (mod p) \<and> 
              (\<forall> q. q \<in> prime_factors (p - 1) \<longrightarrow> [a^((p - 1) div q) \<noteq> 1] (mod p))"
 proof -
  have "p \<ge> 2" by (rule prime_ge_2_nat[OF prime_p])
  obtain a where a:"[a^(p - 1) = 1] (mod p) \<and> (\<forall> x . 0 < x \<longrightarrow> x \<le> p - 2 \<longrightarrow> [a^x \<noteq> 1] (mod p))" 
    using lehmer_backwards[OF prime_p] by blast
  { fix q assume q:"q \<in> prime_factors (p - 1)"
    hence "0 < q \<and> q \<le> p - 1" using `p\<ge>2` by (auto simp add: dvd_nat_bounds prime_factors_dvd_nat)
    hence "(p - 1) div q \<ge> 1" using div_le_mono[of "q" "p - 1" q] div_self[of q] by linarith
    have "q \<ge> 2" using q by (simp add: prime_factors_prime_nat prime_ge_2_nat)
    hence "(p - 1) div q < p - 1" using `p \<ge> 2` by simp
    hence "[a^((p - 1) div q) \<noteq> 1] (mod p)" using a `(p - 1) div q \<ge> 1` by fastforce
  }
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

lemma verify_pratt_tail : 
  assumes "verify_pratt (y # ys)" 
  shows "verify_pratt ys"
  using assms
  by (cases y) auto

lemma prime_factors_one[simp]: shows "prime_factors (Suc 0) = {}"
  by (auto simp add:prime_factors_altdef2_nat)

lemma prime_factors_prime: fixes p :: nat assumes "prime p" shows "prime_factors p = {p}"
proof        
  have "0 < p" using assms by auto
  then show "{p} \<subseteq> prime_factors p" using assms by (auto simp add:prime_factors_altdef2_nat)
  { fix q assume "q \<in> prime_factors p"
    then have "q dvd p" "prime q" using `0<p` by (auto simp add:prime_factors_altdef2_nat)
    with assms have "q=p" by (auto simp: prime_nat_def)
    }
  then
  show "prime_factors p \<subseteq> {p}" by auto
qed

theorem pratt_correct:
  assumes 1: "verify_pratt c"
  assumes 2: "t \<in> set c"
  shows "(t = Prime p \<longrightarrow> prime p) \<and>
         (t = Triple p a x \<longrightarrow> ((\<forall> q \<in> prime_factors x . [a^((p - 1) div q) \<noteq> 1] (mod p)) \<and> 0<x))"
using assms
proof (induction c arbitrary: p a x t)
  case Nil then show ?case by force
  next
  case (Cons y ys)
  { assume "y=Triple p a x" "x=1"
    then have "(\<forall> q \<in> prime_factors x . [a^((p - 1) div q) \<noteq> 1] (mod p)) \<and> 0<x" by simp
    }
  moreover
  { assume x_y: "y=Triple p a x" "x~=1"
    hence "x>0" using Cons.prems by auto
    obtain q z where "x=q*z" "Prime q \<in> set ys \<and> Triple p a z \<in> set ys"
               and cong:"[a^((p - 1) div q) \<noteq> 1] (mod p)" using Cons.prems x_y by auto
    then have factors_IH:"(\<forall> r \<in> prime_factors z . [a^((p - 1) div r) \<noteq> 1] (mod p))" "prime q" "z>0"
      using Cons.IH Cons.prems `x>0` `y=Triple p a x` by auto
    then have "prime_factors x = prime_factors z \<union> {q}"  using `x =q*z` `x>0`
      by (simp add:prime_factors_product_nat prime_factors_prime)
    then have "(\<forall> q \<in> prime_factors x . [a^((p - 1) div q) \<noteq> 1] (mod p)) \<and> 0 < x"
      using factors_IH cong by (simp add: `x>0`)
    }
  ultimately have y_Triple:"y=Triple p a x \<Longrightarrow> (\<forall> q \<in> prime_factors x . 
                                                [a^((p - 1) div q) \<noteq> 1] (mod p)) \<and> 0<x" by linarith
  { assume y: "y=Prime p" "p>2" then
    obtain a where a:"[a^(p - 1) = 1] (mod p)" "Triple p a (p - 1) \<in> set ys" 
      using Cons.prems by auto
    then have Bier:"(\<forall> q \<in> prime_factors (p - 1) . [a^((p - 1) div q) \<noteq> 1] (mod p))"
      using Cons.IH Cons.prems(1) by (simp add:y(1))
    then have "prime p" using lehmer_extended[OF _ _a(1)] `p>2` by fastforce
    }
  moreover
  { assume "y=Prime p" "p=2" hence "prime p" by simp }
  moreover
  { assume "y=Prime p" then have "p>1"  using Cons.prems  by simp }
  ultimately have y_Prime:"y=Prime p ==> prime p" by linarith
  
  show ?case
  proof (cases "t \<in> set ys")
    case True
      show ?thesis using Cons.IH[OF _ True] Cons.prems(1) verify_pratt_tail by blast
    next
    case False
      thus ?thesis using Cons.prems(2) y_Prime y_Triple by force
  qed
qed


lemma concat_verify: "(\<forall>x \<in> set xs . verify_pratt x) \<Longrightarrow> verify_pratt (concat xs)"
  by (induction xs) (auto simp add: pratt_append)

lemma cert_cons:
 assumes 1:"verify_pratt xs"
 assumes 2:"Prime q \<in> set xs"
 assumes 3:"Triple p a x \<in> set xs"
 assumes 4: "[a^((p - 1) div q) \<noteq> 1] (mod p)"
 assumes 5: "y=x*q"
 assumes 6: "x\<ge>1"
 shows "verify_pratt (Triple p a y # xs)"
proof -
  have "prime q" by (auto simp add: pratt_correct[OF 1 2, of q])
  hence "q > 1" using prime_ge_2_nat[of q] by fast
  hence "q > 0" by simp
  have "y > 1" using 6 `q>1` by (simp add: le_neq_implies_less 5)
  thus ?thesis using assms "pratt.3"[of p a y xs] `q>0` by auto
qed

fun build_fpc' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> cert" where
  "build_fpc' p a r [] = [Triple p a r]" |
  "build_fpc' p a r (y # ys) = Triple p a r # build_fpc' p a (r div y) ys"

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
  shows "\<exists>qs. prime_factors q = set qs" using finite_list[of "prime_factors q"] by auto

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
 assumes "\<forall> q \<in> prime_factors p . \<exists> e . P e q"
 shows "\<exists> s . \<forall> q \<in> prime_factors p . \<exists> e \<in> set s . P e q"
 proof -
  have "finite (prime_factors p)" by blast
  then obtain s' where 1:"finite s' \<and> (\<forall> q \<in> prime_factors p . \<exists> e \<in> s' . P e q)"
    using assms set4[of "prime_factors p" "P"] by auto
  thus ?thesis by (metis finite_list)
 qed

lemma p_in_prime_factorsE:
  fixes n :: nat
  assumes "p \<in> prime_factors n" "0 < n"
  obtains "2 \<le> p" "p \<le> n" "p dvd n" "prime p"
proof
  from assms show "prime p" by auto
  then show "2 \<le> p" by (auto dest: prime_gt_1_nat)
  
  from assms show "p dvd n" by (intro prime_factors_dvd_nat)
  then show "p \<le> n" using  `0 < n` by (rule dvd_imp_le)
qed

lemma div_gt_0:
  fixes m n :: nat assumes "m \<le> n" "0 < m" shows "0 < n div m"
proof -
  have "0 < m div m" using `0 < m` div_self by auto
  also have "m div m \<le> n div m" using `m \<le> n` by (rule div_le_mono)
  finally show ?thesis .
qed

lemma prime_factors_list:
  fixes n :: nat assumes "0 < n"
  shows "\<exists>qs. prime_factors n = set qs \<and> listprod qs = n"
  using assms
proof (induct n rule: less_induct)
  case (less n)
  show ?case
  proof cases
    assume "n = 1" then show ?thesis by auto
  next
    assume "n \<noteq> 1"
    then have "1 < n" using `0 < n` by auto
    then obtain p where "p \<in> prime_factors n" using prime_factors_elem by auto
    then have "2 \<le> p" "p \<le> n" "p dvd n" "prime p"
      using `0 < n` by (auto elim: p_in_prime_factorsE)
    then obtain qs where "prime_factors (n div p) = set qs" "listprod qs = (n div p)"
      using `1 < n` by atomize_elim (auto intro: less simp: div_gt_0)
    moreover
    have "prime_factors (p * (n div p)) = insert p (prime_factors (n div p))"
      using `0 < n` `2 \<le> p` `p \<le> n` `prime p`
      by (auto simp: prime_factors_product_nat div_gt_0 prime_factors_prime)
    ultimately
    have "prime_factors n = set (p # qs)" "listprod (p # qs) = n"
      using `p dvd n` by (simp_all add: dvd_mult_div_cancel)
    then show ?thesis by blast
  qed
qed

lemma pratt_complete_step':
  assumes 1:"prime p" 
  assumes 2:"\<forall>q \<in> prime_factors (p - 1) . (\<exists>c . ((Prime q \<in> set c) \<and> (verify_pratt c)))"
  assumes 3:"[a^(p - 1) = 1] (mod p) \<and> (\<forall> q. q \<in> prime_factors (p - 1) \<longrightarrow> [a^((p - 1) div q) \<noteq> 1] (mod p))"
  obtains c where "Triple p a (p - 1) \<in> set c" "verify_pratt c"
proof -
  have "p - 1 > 0" using "1" prime_gt_1_nat by auto
  obtain qs' where Kasgrilla:"listprod qs' = p - 1" and Kasgrilla2:"(set qs' = prime_factors (p - 1))" using prime_factors_list[of "p - 1"] `p - 1 > 0` by auto
  obtain qs where Grillwurst:"set qs = prime_factors (p - 1)" using set_list[of "p - 1"] by fast
  obtain cs' where cs'_1:"\<forall>q \<in> prime_factors (p - 1) . (\<exists>c \<in> set cs' . ((Prime q \<in> set c) \<and> (verify_pratt c)))" using set_list2[OF 2] by auto
  let ?cs = "filter verify_pratt cs'"
  have cs_3: "\<forall>q \<in> prime_factors (p - 1) . (\<exists>c \<in> set ?cs . ((Prime q \<in> set c) \<and> (verify_pratt c)))" using cs'_1 by auto

  have "(Triple p a (p - 1)) \<in> set ((build_fpc' p a (p - 1) qs')@ concat ?cs)" by (cases qs') auto
  moreover
  have "verify_pratt ((build_fpc' p a (p - 1) qs')@ concat ?cs)"
  proof (rule correct_fpc)
    show "verify_pratt (concat ?cs)"
      using cs'_1 by (auto intro: concat_verify)
    show "listprod qs' = p - 1" by (rule Kasgrilla)
    show "p - 1 \<noteq> 0" using `p - 1 > 0` by simp
    show "\<forall> q \<in> set qs' . Prime q \<in> set (concat ?cs)" using concat_set cs_3 Kasgrilla2 by auto
    show "\<forall> q \<in> set qs' . [a^((p - 1) div q) \<noteq> 1] (mod p)" using Kasgrilla2 Grillwurst 3 by auto
  qed
  ultimately show ?thesis ..
qed

lemma pratt_complete_step: 
  fixes p :: nat
  assumes 1: "prime p"
  assumes "\<forall>q \<in> prime_factors (p - 1) . (\<exists>c . ((Prime q \<in> set c) \<and> (verify_pratt c)))"
  shows "\<exists>c . ((Prime p \<in> set c) \<and> (verify_pratt c))"
proof -
  obtain a where gen: "([a^(p - 1) = 1] (mod p) \<and> (\<forall> q. q \<in> prime_factors (p - 1) \<longrightarrow> [a^((p - 1) div q) \<noteq> 1] (mod p)))"
    using lehmer_extended_backwards[OF 1] by blast
  with assms obtain c where "Triple p a (p - 1)  \<in> set c" and "verify_pratt c"
    by (rule pratt_complete_step')
  then have "Prime p \<in> set (Prime p # c)" "verify_pratt (Prime p # c)" using gen 1 by auto
  then show ?thesis by blast
qed

theorem pratt_complete:
  assumes 1:"prime p"
  shows "\<exists>c . ((Prime p \<in> set c) \<and> (verify_pratt c))"
  using assms
proof (induction p rule: less_induct)
  case (less x)
  then have "\<forall>q \<in> prime_factors (x - 1) . q < x" by (fastforce elim: p_in_prime_factorsE)
  then have "\<forall>q \<in> prime_factors (x - 1) . (\<exists>c . ((Prime q \<in> set c) \<and> (verify_pratt c)))"
    by (blast intro: less.IH)
  then show ?case using less.prems by (blast intro: pratt_complete_step)
qed

end
