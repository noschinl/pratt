theory Pratt
imports
  Main
  Lehmer
  Algebra_Stuff_2
begin

section {* Lehmer *}

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
    note X = this

    have "p - 1 = card {1 .. p - 1}" by auto
    also have "{1 .. p - 1} = {a^i mod p | i . 1 \<le> i \<and> i \<le> x}" using X a by auto
    also have "\<dots> = (\<lambda> i. a^i mod p) ` {1..x}" by auto
    also have "card \<dots> \<le> p - 2"
      using Finite_Set.card_image_le[of "{1..x}" "\<lambda> i. a^i mod p"] x by auto
    finally have False using `2 \<le> p` by arith
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

section {* Pratt's Prime Number Certificates *}

text {*
  Pratt's proof system is described in the following section.
  The certificates use two types of predicates:
  \begin{itemize}
    \item Prime(p): p is a prime number
    \item (p, a, x): @{text "\<forall>q \<in> prime_factors(x). [a^((p - 1) div q) \<noteq> 1] (mod p)"}
  \end{itemize}
  We represent these predicates with the following datatype:
*}

datatype pratt = Prime nat | Triple nat nat nat

text {*
  We have the axiom (p, a, 1) and the following inference rules:
  \begin{itemize}
  \item R1: If we know that (p, a, x) and @{text "[a^((p - 1) div q) \<noteq> 1] (mod p)"} hold for some
              prime number q we can conclude (p, a, q*x) from that.
  \item R2: If we know that (p, a, p - 1) and  @{text "[a^(p - 1) = 1] (mod p)"} hold, we can
              infer Prime(p).
  \end{itemize}
  Both rules follow from Lehmer's theorem as we will show later on.
  The function @{text verify_pratt} checks a given certificate according to rules R1 and R2.
*}

fun verify_pratt :: "pratt list \<Rightarrow> bool" where
  "verify_pratt [] = True"
| R2:"verify_pratt (Prime p#xs) \<longleftrightarrow> 1<p \<and> (\<exists> a . [a^(p - 1) = 1] (mod p) \<and> Triple p a (p - 1) \<in> set xs) \<and> verify_pratt xs"
| R1:"verify_pratt (Triple p a x # xs) \<longleftrightarrow> 0<x  \<and> (x=1 \<or>
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

text {*
  We now show that every statement that we obtain by building a certificate according to rules R1
  and R2 really fulfills the predicates we definded in the beginning,
  i.e. we show the soundness of Pratt's primality certificates.
*}

theorem pratt_sound:
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
  have "prime q" by (auto simp add: pratt_sound[OF 1 2, of q])
  hence "q > 1" using prime_ge_2_nat[of q] by fast
  hence "q > 0" by simp
  have "y > 1" using 6 `q>1` by (simp add: le_neq_implies_less 5)
  thus ?thesis using assms "pratt.R1"[of p a y xs] `q>0` by auto
qed

text {*
  We show the completeness of Pratt's primality certificates, i.e. that for every prime number
  @{text p} a certificate exists, that is correct in terms of R1 and R2 and ends with
  Prime(@{text p}), by construction.
  We assume that we have some correct certificate that contains the statements Prime(@{text q}) for
  all prime factors @{text q} of @{text "p - 1"} for some prime number @{text p}.
  We extend this certificate to a certificate that ends with (p, a, p - 1) by starting with 
  (p, a, 1) and subsequently deducing (p, a, qx) from (p, a, x) according to R1.
  This construction is carried out by @{text "build_fpc p a 1 qs"}, if qs is a list that
  contains every prime factor @{text "q\<^bsub>i\<^esub>"} of @{text "p - 1"} exactly @{text "x\<^bsub>i\<^esub>"} times, if
  @{text "p - 1 = q\<^bsub>1\<^esub>\<^bsup>x\<^bsub>1\<^esub>\<^esup> \<dots> q\<^bsub>n\<^esub>\<^bsup>x\<^bsub>n\<^esub>\<^esup>"}.
*}

fun build_fpc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> pratt list" where
  "build_fpc p a r [] = [Triple p a r]" |
  "build_fpc p a r (y # ys) = Triple p a r # build_fpc p a (r div y) ys"

definition "listprod \<equiv> \<lambda>xs. foldr (op *) xs 1"

lemma listprod_Nil[simp]: "listprod [] = 1" by (simp add: listprod_def)
lemma listprod_Cons[simp]: "listprod (x # xs) = x * listprod xs" by (simp add: listprod_def)

text {*
  This lemma shows that @{text "build_fpc"} extends a certificate that fulfills the preconditions
  described before to a correct certifiacte. 
*}

lemma correct_fpc:
  assumes "verify_pratt xs"
  assumes "listprod qs = r" "r \<noteq> 0"
  assumes "\<forall> q \<in> set qs . Prime q \<in> set xs"
  assumes "\<forall> q \<in> set qs . [a^((p - 1) div q) \<noteq> 1] (mod p)"
  shows "verify_pratt (build_fpc p a r qs @ xs)"
  using assms
proof (induction qs arbitrary: r)
  case Nil thus ?case by auto
next
  case (Cons y ys)
  have "listprod ys = r div y" using Cons.prems by auto
  then have T_in: "Triple p a (listprod ys) \<in> set (build_fpc p a (r div y) ys @ xs)"
    by (cases ys) auto

  have "verify_pratt (build_fpc p a (r div y) ys @ xs)"
    using Cons.prems by (intro Cons.IH) auto
  then have "verify_pratt (Triple p a r # build_fpc p a (r div y) ys @ xs)"
    using `r \<noteq> 0` T_in Cons.prems by (intro cert_cons) auto
  then show ?case by simp
qed

lemma concat_set:
 assumes 1: "\<forall> q \<in> qs . \<exists> c \<in> set cs . Prime q \<in> set c"
 shows "\<forall> q \<in> qs . Prime q \<in> set (concat cs)" using assms by (induction cs) auto

fun oneof :: "'a set \<Rightarrow> 'a" where
  "oneof s = (SOME x . x \<in> s)" 

lemma finite_set_predicate_combination:
  assumes 1:"finite p"
  assumes 2:"\<forall> q \<in> p. \<exists> e . P e q"
  shows "\<exists> s. finite s \<and> (\<forall> q \<in> p. \<exists> e \<in> s . P e q)" using assms
proof -
  obtain s where s : "s = {oneof {e . P e q} | q . q \<in> p}" by auto
  { fix q assume q:"q \<in> p"
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

lemma prime_factors_predicate_combination:
  fixes p::nat
  assumes "\<forall> q \<in> prime_factors p . \<exists> e . P e q"
  shows "\<exists> s . \<forall> q \<in> prime_factors p . \<exists> e \<in> set s . P e q"
proof -
  have "finite (prime_factors p)" by blast
  then obtain s' where 1:"finite s' \<and> (\<forall> q \<in> prime_factors p . \<exists> e \<in> s' . P e q)"
    using assms finite_set_predicate_combination[of "prime_factors p" "P"] by auto
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
  assumes prime_p:"prime p" 
  assumes factor_certs:"\<forall>q \<in> prime_factors (p - 1) . (\<exists>c . ((Prime q \<in> set c) \<and> (verify_pratt c)))"
  assumes a:"[a^(p - 1) = 1] (mod p) \<and> (\<forall> q. q \<in> prime_factors (p - 1) \<longrightarrow> [a^((p - 1) div q) \<noteq> 1] (mod p))"
  obtains c where "Triple p a (p - 1) \<in> set c" "verify_pratt c"
proof -
  have "p - 1 > 0" using prime_p prime_gt_1_nat by auto
  obtain qs where prod_qs_eq:"listprod qs = p - 1" and qs_eq:"(set qs = prime_factors (p - 1))"
    using prime_factors_list[of "p - 1"] `p - 1 > 0` by auto
  obtain cs' where cs':"\<forall>q \<in> prime_factors (p - 1) . (\<exists>c \<in> set cs' . ((Prime q \<in> set c) \<and> (verify_pratt c)))"
    using prime_factors_predicate_combination[OF factor_certs] by auto
  let ?cs = "filter verify_pratt cs'"
  have cs: "\<forall>q \<in> prime_factors (p - 1) . (\<exists>c \<in> set ?cs . ((Prime q \<in> set c) \<and> (verify_pratt c)))"
    using cs' by auto

  have "(Triple p a (p - 1)) \<in> set ((build_fpc p a (p - 1) qs)@ concat ?cs)" by (cases qs) auto
  moreover
  have "verify_pratt ((build_fpc p a (p - 1) qs)@ concat ?cs)"
  proof (rule correct_fpc)
    show "verify_pratt (concat ?cs)"
      using cs' by (auto intro: concat_verify)
    show "listprod qs = p - 1" by (rule prod_qs_eq)
    show "p - 1 \<noteq> 0" using `p - 1 > 0` by simp
    show "\<forall> q \<in> set qs . Prime q \<in> set (concat ?cs)" using concat_set cs qs_eq by auto
    show "\<forall> q \<in> set qs . [a^((p - 1) div q) \<noteq> 1] (mod p)" using qs_eq a by auto
  qed
  ultimately show ?thesis ..
qed

text {*
    This lemma shows that our construction using @{term build_fpc'} yields a correct certificate,
    which certifies the primality of p,
    if the certificates for all prime factors of p - 1 are given.
*}

lemma pratt_complete_step: 
  fixes p :: nat
  assumes prime_p:"prime p"
  assumes "\<forall>q \<in> prime_factors (p - 1) . (\<exists>c . ((Prime q \<in> set c) \<and> (verify_pratt c)))"
  shows "\<exists>c . ((Prime p \<in> set c) \<and> (verify_pratt c))"
proof -
  obtain a where gen: "([a^(p - 1) = 1] (mod p) \<and> (\<forall> q. q \<in> prime_factors (p - 1) \<longrightarrow> [a^((p - 1) div q) \<noteq> 1] (mod p)))"
    using lehmer_extended_backwards[OF prime_p] by blast
  with assms obtain c where "Triple p a (p - 1)  \<in> set c" and "verify_pratt c"
    by (rule pratt_complete_step')
  then have "Prime p \<in> set (Prime p # c)" "verify_pratt (Prime p # c)" using gen prime_p by auto
  then show ?thesis by blast
qed

text {*
  By induction on p we can now conclude that a correct certificate that ends with Prime(p) exists
  for every prime number p. This follows easily from our construction argument.
*}

theorem pratt_complete:
  assumes 1:"prime p"
  shows "\<exists>c . Prime p \<in> set c \<and> verify_pratt c"
  using assms
proof (induction p rule: less_induct)
  case (less x)
  then have "\<forall>q \<in> prime_factors (x - 1) . q < x" by (fastforce elim: p_in_prime_factorsE)
  then have "\<forall>q \<in> prime_factors (x - 1) . (\<exists>c . ((Prime q \<in> set c) \<and> (verify_pratt c)))"
    by (blast intro: less.IH)
  then show ?case using less.prems by (blast intro: pratt_complete_step)
qed

corollary pratt:
  "prime p \<longleftrightarrow> (\<exists>c . Prime p \<in> set c \<and> verify_pratt c)"
  using pratt_complete pratt_sound(1) by auto

 
end
