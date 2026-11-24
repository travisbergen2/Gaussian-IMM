import Mathlib

/-!
# GaussianIdealCounting — Step 1–2: the counting function and the norm bridge

Works in Mathlib's `QuadraticAlgebra ℤ (-1) 0` (= ℤ[i] with ω² = −1), which carries
an ℤ-basis, so Mathlib's ideal norm `Ideal.absNorm` applies.
-/

open Ideal

abbrev Zi := QuadraticAlgebra ℤ (-1) 0

/-- Algebra.norm ℤ z equals the quadratic norm re² + im². -/
theorem algebraNorm_eq (z : Zi) : Algebra.norm ℤ z = z.re ^ 2 + z.im ^ 2 := by
  rw [Algebra.norm_apply]
  have h := QuadraticAlgebra.det_toLinearMap_eq_norm (R := ℤ) (a := -1) (b := 0) z
  rw [QuadraticAlgebra.norm_def] at h
  have e : Algebra.lmul ℤ Zi z = DistribSMul.toLinearMap ℤ Zi z := rfl
  rw [e, h]; ring

instance : Fact (¬ IsSquare (QuadraticAlgebra.discr (-1 : ℤ) 0)) := by
  refine ⟨?_⟩
  rw [QuadraticAlgebra.discr_def]
  rintro ⟨r, hr⟩
  nlinarith [sq_nonneg r]

example : IsDomain Zi := inferInstance

/-- Coordinate ring equivalence with Mathlib's `GaussianInt`. -/
def ziEquiv : Zi ≃+* GaussianInt where
  toFun z := ⟨z.re, z.im⟩
  invFun z := ⟨z.re, z.im⟩
  left_inv z := by cases z; rfl
  right_inv z := by cases z; rfl
  map_mul' x y := by ext <;> simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;> ring
  map_add' x y := by ext <;> simp

instance : IsPrincipalIdealRing Zi :=
  IsPrincipalIdealRing.of_surjective ziEquiv.symm.toRingHom ziEquiv.symm.surjective

example : IsDedekindDomain Zi := inferInstance

instance : Ring.HasFiniteQuotients Zi := .of_module_finite ℤ _

/-- a(n): the number of ideals of ℤ[i] of norm n. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {I : Ideal Zi // absNorm I = n}

/-- The norm of a principal ideal is the Gaussian norm of its generator. -/
theorem absNorm_span (z : Zi) :
    absNorm (span ({z} : Set Zi)) = (z.re ^ 2 + z.im ^ 2).natAbs := by
  rw [absNorm_span_singleton, algebraNorm_eq]

/-- a(1) = 1: the only ideal of norm 1 is the whole ring. -/
theorem a_one : a 1 = 1 := by
  rw [a, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun I J => Subtype.ext ?_⟩, ⟨⟨⊤, absNorm_top⟩⟩⟩
  rw [absNorm_eq_one_iff.mp I.2, absNorm_eq_one_iff.mp J.2]

/-- a(0) = 1: only the zero ideal has norm 0 (the L-series ignores n = 0 anyway). -/
theorem a_zero : a 0 = 1 := by
  rw [a, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun I J => Subtype.ext ?_⟩, ⟨⟨⊥, absNorm_bot⟩⟩⟩
  rw [absNorm_eq_zero_iff.mp I.2, absNorm_eq_zero_iff.mp J.2]

/-- Every ideal is principal, so its norm is a sum of two squares. -/
theorem absNorm_is_sum_two_squares (I : Ideal Zi) :
    ∃ z : Zi, absNorm I = (z.re ^ 2 + z.im ^ 2).natAbs := by
  obtain ⟨z, hz⟩ := (IsPrincipalIdealRing.principal I).principal
  exact ⟨z, by rw [hz, ← absNorm_span]⟩


/-! ## Step 3a: how rational primes factor, as ideal equalities -/

open QuadraticAlgebra

/-- The unit ω (ω² = −1). -/
theorem omega_isUnit : IsUnit (ω : Zi) :=
  isUnit_iff_exists_inv.mpr ⟨-ω, by ext <;> simp [re_mul, im_mul]⟩

/-- **2 ramifies:** (2) = (1 + ω)². -/
theorem two_ramifies : span ({(2 : Zi)} : Set Zi) = span {(1 + ω : Zi)} ^ 2 := by
  rw [span_singleton_pow, span_singleton_eq_span_singleton]
  have h : (1 + ω : Zi) ^ 2 = 2 * ω := by ext <;> simp [pow_two, re_mul, im_mul] <;> ring
  rw [h]
  exact (associated_mul_unit_right 2 ω omega_isUnit)

/-- The coordinate map sends natural numbers to natural numbers. -/
theorem ziEquiv_natCast (n : ℕ) : ziEquiv (n : Zi) = (n : GaussianInt) := map_natCast ziEquiv n

/-- **p ≡ 3 mod 4 stays prime:** (p) is a prime ideal. -/
theorem inert_prime {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    (span ({(p : Zi)} : Set Zi)).IsPrime := by
  have hG : Prime (p : GaussianInt) :=
    (GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime p).mpr hp
  have hZ : Prime (p : Zi) := by
    have := (MulEquiv.prime_iff ziEquiv.symm.toMulEquiv).mpr hG
    simpa using this
  exact (span_singleton_prime hZ.ne_zero).mpr hZ

/-- **p ≡ 1 mod 4 splits:** (p) = (π)(π̄) with π = a + bω, a² + b² = p,
and the two factors are different ideals. -/
theorem split_prime {p : ℕ} [hp : Fact p.Prime] (h1 : p % 4 = 1) :
    ∃ a b : ℤ, a ^ 2 + b ^ 2 = p ∧
      span ({(p : Zi)} : Set Zi) =
        span {(⟨a, b⟩ : Zi)} * span {(⟨a, -b⟩ : Zi)} ∧
      span ({(⟨a, b⟩ : Zi)} : Set Zi) ≠ span {(⟨a, -b⟩ : Zi)} := by
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
  refine ⟨a, b, by exact_mod_cast hab, ?_, ?_⟩
  · rw [span_singleton_mul_span_singleton]
    have : ((a : ℤ) ^ 2 + (b : ℤ) ^ 2 : ℤ) = p := by exact_mod_cast hab
    have e : (p : Zi) = ⟨a, b⟩ * ⟨a, -b⟩ := by
      ext <;> simp [re_mul, im_mul] <;> nlinarith [this]
    rw [e]
  · intro heq
    -- π̄ ∈ (π), so π divides π + π̄ = 2a and (π − π̄) = 2bω
    have hdvd : (⟨a, b⟩ : Zi) ∣ ⟨a, -b⟩ := by
      rw [← mem_span_singleton, heq]; exact mem_span_singleton_self _
    have hN : ∀ x y : Zi, x ∣ y → x.norm ∣ y.norm := fun x y h => map_dvd QuadraticAlgebra.norm h
    have h2a : (⟨a, b⟩ : Zi) ∣ (2 * a : ℤ) := by
      have : ((2 * a : ℤ) : Zi) = ⟨a, b⟩ + ⟨a, -b⟩ := by ext <;> simp; ring
      rw [this]; exact dvd_add dvd_rfl hdvd
    have h2b : (⟨a, b⟩ : Zi) ∣ (2 * b : ℤ) := by
      have : ((2 * b : ℤ) : Zi) = (⟨a, b⟩ - ⟨a, -b⟩) * (-ω) := by
        ext <;> simp [re_mul, im_mul]; ring
      rw [this]; exact dvd_mul_of_dvd_left (dvd_sub dvd_rfl hdvd) _
    have hnp : (⟨a, b⟩ : Zi).norm = p := by
      rw [norm_def]; simp; push_cast [← hab]; ring
    have ha := hN _ _ h2a
    have hb := hN _ _ h2b
    rw [hnp, norm_def] at ha hb
    simp at ha hb
    -- p ∣ 4a² and p ∣ 4b², p odd prime ⇒ p ∣ a and p ∣ b ⇒ p² ∣ a² + b² = p
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
    have hp2 : ¬ (p : ℤ) ∣ 2 := by
      intro h; have := Int.le_of_dvd (by norm_num) h
      have : (5 : ℤ) ≤ p := by
        have := hp.out.two_le; have : p ≠ 2 := by omega
        have : p ≠ 3 := by omega
        have : p ≠ 4 := by omega
        omega
      omega
    have key : ∀ c : ℤ, (p : ℤ) ∣ 2 * c * (2 * c) → (p : ℤ) ∣ c := by
      intro c hc
      rcases hpZ.dvd_or_dvd hc with h | h
      · rcases hpZ.dvd_or_dvd h with h' | h'
        · exact absurd h' hp2
        · exact h'
      · rcases hpZ.dvd_or_dvd h with h' | h'
        · exact absurd h' hp2
        · exact h'
    have hpa : (p : ℤ) ∣ a := key a (by convert ha using 1)
    have hpb : (p : ℤ) ∣ b := key b (by convert hb using 1)
    have : (p : ℤ) ^ 2 ∣ (a : ℤ) ^ 2 + (b : ℤ) ^ 2 :=
      dvd_add (pow_dvd_pow_of_dvd hpa 2) (pow_dvd_pow_of_dvd hpb 2)
    rw [show ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) = (p : ℤ) by exact_mod_cast hab] at this
    have hpos : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
    have := Int.le_of_dvd hpos this
    have : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
    nlinarith


/-- An ideal whose norm is a rational prime is a prime ideal. -/
theorem isPrime_of_absNorm_prime {I : Ideal Zi} {p : ℕ} (hp : p.Prime) (h : absNorm I = p) :
    I.IsPrime :=
  isPrime_of_irreducible_absNorm (by rw [h]; exact Nat.prime_iff.mp hp |>.irreducible)

/-- **Split factors are prime ideals of norm p.** For a² + b² = p prime,
both (a + bω) and (a − bω) have norm p and are prime ideals. -/
theorem split_factors_prime {p : ℕ} (hp : p.Prime) {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) :
    absNorm (span ({(⟨a, b⟩ : Zi)} : Set Zi)) = p ∧
    absNorm (span ({(⟨a, -b⟩ : Zi)} : Set Zi)) = p ∧
    (span ({(⟨a, b⟩ : Zi)} : Set Zi)).IsPrime ∧
    (span ({(⟨a, -b⟩ : Zi)} : Set Zi)).IsPrime := by
  have h1 : absNorm (span ({(⟨a, b⟩ : Zi)} : Set Zi)) = p := by
    rw [absNorm_span]; simp only; rw [hab]; rfl
  have h2 : absNorm (span ({(⟨a, -b⟩ : Zi)} : Set Zi)) = p := by
    rw [absNorm_span]; simp only [neg_sq]; rw [hab]; rfl
  exact ⟨h1, h2, isPrime_of_absNorm_prime hp h1, isPrime_of_absNorm_prime hp h2⟩

/-- The inert prime ideal (p) has norm p², not p. -/
theorem inert_norm (p : ℕ) : absNorm (span ({(p : Zi)} : Set Zi)) = p ^ 2 := by
  rw [absNorm_span]; simp

/-- The ramified prime ideal (1 + ω) has norm 2. -/
theorem ramified_norm : absNorm (span ({(1 + ω : Zi)} : Set Zi)) = 2 := by
  rw [absNorm_span]; simp


/-! ## Step 3b: from the norm condition to ideal factorization -/

/-- **Bridge:** an ideal of norm n divides (n). In particular, an ideal of norm pᵏ
divides (p)ᵏ. Reusable for all three prime classes. -/
theorem ideal_dvd_span_absNorm (I : Ideal Zi) :
    I ∣ span ({((absNorm I : ℕ) : Zi)} : Set Zi) := by
  rw [Ideal.dvd_iff_le, span_le, Set.singleton_subset_iff]
  exact absNorm_mem I

theorem ideal_norm_prime_power_dvd {I : Ideal Zi} {p k : ℕ} (h : absNorm I = p ^ k) :
    I ∣ span ({(p : Zi)} : Set Zi) ^ k := by
  have := ideal_dvd_span_absNorm I
  rwa [h, Nat.cast_pow, ← span_singleton_pow] at this

/-- In the ideal monoid, a divisor of 𝔭ᵏ·𝔮ᵏ (𝔭, 𝔮 prime) is 𝔭ʲ·𝔮ˡ with j, l ≤ k. -/
theorem dvd_two_prime_pows {P Q I : Ideal Zi} (hP : Prime P) (hQ : Prime Q) {k : ℕ}
    (h : I ∣ P ^ k * Q ^ k) : ∃ j ≤ k, ∃ l ≤ k, I = P ^ j * Q ^ l := by
  obtain ⟨y, z, hy, hz, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul h
  obtain ⟨j, hj, hyj⟩ := (dvd_prime_pow hP k).mp hy
  obtain ⟨l, hl, hzl⟩ := (dvd_prime_pow hQ k).mp hz
  exact ⟨j, hj, l, hl, by rw [associated_iff_eq.mp hyj, associated_iff_eq.mp hzl]⟩

/-- **Split factorization:** for p = a² + b² prime, every ideal of norm pᵏ is
(a+bω)ʲ (a−bω)ᵏ⁻ʲ for some j ≤ k. -/
theorem split_ideal_factorization {p : ℕ} (hp : p.Prime) {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p)
    (hsplit : span ({(p : Zi)} : Set Zi) = span {(⟨a, b⟩ : Zi)} * span {(⟨a, -b⟩ : Zi)})
    {I : Ideal Zi} {k : ℕ} (hI : absNorm I = p ^ k) :
    ∃ j ≤ k, I = span {(⟨a, b⟩ : Zi)} ^ j * span {(⟨a, -b⟩ : Zi)} ^ (k - j) := by
  obtain ⟨n1, n2, hP, hQ⟩ := split_factors_prime hp hab
  have hPne : span ({(⟨a, b⟩ : Zi)} : Set Zi) ≠ ⊥ := by
    intro h; rw [h, absNorm_bot] at n1; exact hp.ne_zero n1.symm
  have hQne : span ({(⟨a, -b⟩ : Zi)} : Set Zi) ≠ ⊥ := by
    intro h; rw [h, absNorm_bot] at n2; exact hp.ne_zero n2.symm
  have hdvd := ideal_norm_prime_power_dvd hI
  rw [hsplit, mul_pow] at hdvd
  obtain ⟨j, hj, l, hl, rfl⟩ :=
    dvd_two_prime_pows (prime_of_isPrime hPne hP) (prime_of_isPrime hQne hQ) hdvd
  have hnorm : p ^ (j + l) = p ^ k := by
    rw [← hI, map_mul, map_pow, map_pow, n1, n2, pow_add]
  have := Nat.pow_right_injective hp.two_le hnorm
  exact ⟨j, hj, by rw [show l = k - j by omega]⟩


/-- Exponents are determined: with 𝔭 ≠ 𝔮 prime, 𝔭ʲ𝔮ᵏ⁻ʲ = 𝔭ᵐ𝔮ᵏ⁻ᵐ forces j = m. -/
theorem exps_unique_aux {P Q : Ideal Zi} (hP : Prime P) (hQ : Prime Q) (hne : P ≠ Q)
    {k j m : ℕ} (hjm : j < m) (hm : m ≤ k)
    (h : P ^ j * Q ^ (k - j) = P ^ m * Q ^ (k - m)) : False := by
  have hm' : P ^ m = P ^ j * P ^ (m - j) := by rw [← pow_add]; congr 1; omega
  rw [hm', mul_assoc] at h
  have hc := mul_left_cancel₀ (pow_ne_zero j hP.ne_zero) h
  have hdvd : P ∣ Q ^ (k - j) := by
    rw [hc]
    exact dvd_mul_of_dvd_left (dvd_pow_self P (by omega)) _
  have hPQ : P ∣ Q := hP.dvd_of_dvd_pow hdvd
  exact hne (associated_iff_eq.mp (hP.associated_of_dvd hQ hPQ))

theorem exps_unique {P Q : Ideal Zi} (hP : Prime P) (hQ : Prime Q) (hne : P ≠ Q)
    {k j m : ℕ} (hj : j ≤ k) (hm : m ≤ k)
    (h : P ^ j * Q ^ (k - j) = P ^ m * Q ^ (k - m)) : j = m := by
  rcases lt_trichotomy j m with hlt | heq | hgt
  · exact (exps_unique_aux hP hQ hne hlt hm h).elim
  · exact heq
  · exact (exps_unique_aux hP hQ hne hgt hj h.symm).elim

/-- **Split count: a(pᵏ) = k + 1** for p ≡ 1 mod 4. -/
theorem a_split_prime_power {p : ℕ} [hp : Fact p.Prime] (h1 : p % 4 = 1) (k : ℕ) :
    a (p ^ k) = k + 1 := by
  obtain ⟨x, y, hxy, hsplit, hne⟩ := split_prime h1
  obtain ⟨n1, n2, hPi, hQi⟩ := split_factors_prime hp.out hxy
  set P := span ({(⟨x, y⟩ : Zi)} : Set Zi)
  set Q := span ({(⟨x, -y⟩ : Zi)} : Set Zi)
  have hP0 : P ≠ ⊥ := by intro h; rw [h, absNorm_bot] at n1; exact hp.out.ne_zero n1.symm
  have hQ0 : Q ≠ ⊥ := by intro h; rw [h, absNorm_bot] at n2; exact hp.out.ne_zero n2.symm
  have hP := prime_of_isPrime hP0 hPi
  have hQ := prime_of_isPrime hQ0 hQi
  let f : Fin (k + 1) → {I : Ideal Zi // absNorm I = p ^ k} := fun j =>
    ⟨P ^ (j : ℕ) * Q ^ (k - j), by
      rw [map_mul, map_pow, map_pow, n1, n2, ← pow_add]; congr 1; omega⟩
  have hf : Function.Bijective f := by
    constructor
    · intro j m h
      have := congrArg Subtype.val h
      exact Fin.ext (exps_unique hP hQ hne (by omega) (by omega) this)
    · rintro ⟨I, hI⟩
      obtain ⟨j, hj, rfl⟩ := split_ideal_factorization hp.out hxy hsplit hI
      exact ⟨⟨j, by omega⟩, rfl⟩
  rw [a, ← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fin]


/-! ## Step 3c: inert and ramified counts -/

/-- A divisor of 𝔭ⁿ (𝔭 prime) is 𝔭ʲ with j ≤ n. -/
theorem dvd_one_prime_pow {P I : Ideal Zi} (hP : Prime P) {n : ℕ} (h : I ∣ P ^ n) :
    ∃ j ≤ n, I = P ^ j := by
  obtain ⟨j, hj, hI⟩ := (dvd_prime_pow hP n).mp h
  exact ⟨j, hj, associated_iff_eq.mp hI⟩

/-- **Inert count:** for p ≡ 3 mod 4, a(pᵏ) = 1 if k is even and 0 if k is odd. -/
theorem a_inert_prime_power {p : ℕ} [hp : Fact p.Prime] (h3 : p % 4 = 3) (k : ℕ) :
    a (p ^ k) = if Even k then 1 else 0 := by
  set P := span ({(p : Zi)} : Set Zi)
  have hN : absNorm P = p ^ 2 := inert_norm p
  have hP0 : P ≠ ⊥ := by
    intro h; rw [h, absNorm_bot] at hN
    exact pow_ne_zero 2 hp.out.ne_zero hN.symm
  have hP := prime_of_isPrime hP0 (inert_prime h3)
  -- every ideal of norm pᵏ is Pʲ with k = 2j
  have hform : ∀ I : Ideal Zi, absNorm I = p ^ k → ∃ j, k = 2 * j ∧ I = P ^ j := by
    intro I hI
    obtain ⟨j, -, rfl⟩ := dvd_one_prime_pow hP (ideal_norm_prime_power_dvd hI)
    refine ⟨j, ?_, rfl⟩
    rw [map_pow, hN, ← pow_mul] at hI
    exact (Nat.pow_right_injective hp.out.two_le hI).symm.trans (by ring)
  split_ifs with hk
  · obtain ⟨j, rfl⟩ := hk
    rw [a, Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun I J => Subtype.ext ?_⟩, ⟨⟨P ^ j, ?_⟩⟩⟩
    · obtain ⟨j1, h1, e1⟩ := hform I.1 I.2
      obtain ⟨j2, h2, e2⟩ := hform J.1 J.2
      rw [e1, e2, show j1 = j2 by omega]
    · rw [map_pow, hN, ← pow_mul]; congr 1; ring
  · rw [a, Nat.card_eq_zero]
    left
    refine ⟨fun I => ?_⟩
    obtain ⟨j, hj, -⟩ := hform I.1 I.2
    exact hk ⟨j, by omega⟩

/-- **Ramified count:** a(2ᵏ) = 1 for every k. -/
theorem a_ramified_prime_power (k : ℕ) : a (2 ^ k) = 1 := by
  set P := span ({(1 + ω : Zi)} : Set Zi)
  have hN : absNorm P = 2 := ramified_norm
  have hP0 : P ≠ ⊥ := by intro h; rw [h, absNorm_bot] at hN; omega
  have hP := prime_of_isPrime hP0 (isPrime_of_absNorm_prime Nat.prime_two hN)
  have hform : ∀ I : Ideal Zi, absNorm I = 2 ^ k → I = P ^ k := by
    intro I hI
    have hdvd := ideal_norm_prime_power_dvd (p := 2) hI
    rw [show ((2 : ℕ) : Zi) = 2 by norm_num, two_ramifies, ← pow_mul] at hdvd
    obtain ⟨j, -, rfl⟩ := dvd_one_prime_pow hP hdvd
    rw [map_pow, hN] at hI
    rw [Nat.pow_right_injective le_rfl hI]
  rw [a, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun I J => Subtype.ext (by rw [hform I.1 I.2, hform J.1 J.2])⟩, ⟨⟨P ^ k, ?_⟩⟩⟩
  rw [map_pow, hN]


/-! ## Step 4: multiplicativity of a(n) -/

/-- Coprime rational integers generate comaximal ideals of ℤ[i]. -/
theorem span_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    span ({(m : Zi)} : Set Zi) ⊔ span {(n : Zi)} = ⊤ := by
  rw [eq_top_iff_one, Submodule.mem_sup]
  have hb := Nat.gcd_eq_gcd_ab m n
  rw [h] at hb
  refine ⟨(m.gcdA n : Zi) * m, ?_, (m.gcdB n : Zi) * n, ?_, ?_⟩
  · exact mul_mem_left _ _ (mem_span_singleton_self _)
  · exact mul_mem_left _ _ (mem_span_singleton_self _)
  · have := congrArg (Int.cast : ℤ → Zi) hb
    push_cast at this
    rw [this]; ring

/-- An ideal of norm n contains n. -/
theorem span_le_of_absNorm {J : Ideal Zi} {n : ℕ} (h : absNorm J = n) :
    span ({(n : Zi)} : Set Zi) ≤ J := by
  rw [← h, span_le, Set.singleton_subset_iff]; exact absNorm_mem J

/-- **Recovery:** if N(I) = m, N(J) = n and gcd(m, n) = 1, then I = IJ ⊔ (m).
So the factor of norm m is determined by the product. -/
theorem factor_recover {I J : Ideal Zi} {m n : ℕ} (hmn : Nat.Coprime m n)
    (hI : absNorm I = m) (hJ : absNorm J = n) :
    I * J ⊔ span {(m : Zi)} = I := by
  apply le_antisymm
  · exact sup_le mul_le_left (span_le_of_absNorm hI)
  · have hJM : J ⊔ span {(m : Zi)} = ⊤ := by
      apply eq_top_iff.mpr
      rw [← span_coprime hmn]
      exact sup_le le_sup_right (le_trans (span_le_of_absNorm hJ) le_sup_left)
    calc I = I * (J ⊔ span {(m : Zi)}) := by rw [hJM, mul_top]
      _ = I * J ⊔ I * span {(m : Zi)} := mul_sup _ _ _
      _ ≤ I * J ⊔ span {(m : Zi)} := sup_le_sup_left mul_le_right _

/-- **Multiplicativity:** a(mn) = a(m)·a(n) for coprime positive m, n. -/
theorem a_mul_of_coprime {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) :
    a (m * n) = a m * a n := by
  let f : {I : Ideal Zi // absNorm I = m} × {J : Ideal Zi // absNorm J = n} →
      {K : Ideal Zi // absNorm K = m * n} :=
    fun x => ⟨x.1.1 * x.2.1, by rw [map_mul, x.1.2, x.2.2]⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨I, hI⟩, ⟨J, hJ⟩⟩ ⟨⟨I', hI'⟩, ⟨J', hJ'⟩⟩ h
      have h' : I * J = I' * J' := congrArg Subtype.val h
      have e1 : I = I' := by
        rw [← factor_recover hmn hI hJ, ← factor_recover hmn hI' hJ', h']
      have e2 : J = J' := by
        rw [← factor_recover hmn.symm hJ hI, ← factor_recover hmn.symm hJ' hI', mul_comm J,
          mul_comm J', h']
      subst e1; subst e2; rfl
    · rintro ⟨K, hK⟩
      have hdvd : K ∣ span {(m : Zi)} * span {(n : Zi)} := by
        have := ideal_dvd_span_absNorm K
        rwa [hK, Nat.cast_mul, ← span_singleton_mul_span_singleton] at this
      obtain ⟨I, J, hI, hJ, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hdvd
      have hNI : absNorm I ∣ m ^ 2 := by
        have := map_dvd absNorm hI; rwa [absNorm_span, show ((m : Zi).re ^ 2 + (m : Zi).im ^ 2) = (m : ℤ) ^ 2 by simp] at this
      have hNJ : absNorm J ∣ n ^ 2 := by
        have := map_dvd absNorm hJ; rwa [absNorm_span, show ((n : Zi).re ^ 2 + (n : Zi).im ^ 2) = (n : ℤ) ^ 2 by simp] at this
      have hprod : absNorm I * absNorm J = m * n := by rw [← map_mul, hK]
      have d1 : absNorm I ∣ m :=
        (Nat.Coprime.coprime_dvd_left hNI (Nat.Coprime.pow_left 2 hmn)).dvd_of_dvd_mul_right
          (hprod ▸ dvd_mul_right _ _)
      have d2 : absNorm J ∣ n :=
        (Nat.Coprime.coprime_dvd_left hNJ (Nat.Coprime.pow_left 2 hmn.symm)).dvd_of_dvd_mul_left
          (hprod ▸ dvd_mul_left _ _)
      have l1 := Nat.le_of_dvd hm d1
      have l2 := Nat.le_of_dvd hn d2
      have eI : absNorm I = m := by nlinarith
      have eJ : absNorm J = n := by nlinarith
      exact ⟨(⟨I, eI⟩, ⟨J, eJ⟩), rfl⟩
  rw [a, ← Nat.card_eq_of_bijective f hf, Nat.card_prod, a, a]

#print axioms algebraNorm_eq
#print axioms absNorm_span
#print axioms a_one
#print axioms a_zero
#print axioms absNorm_is_sum_two_squares
#print axioms two_ramifies
#print axioms inert_prime
#print axioms split_prime
#print axioms split_factors_prime
#print axioms inert_norm
#print axioms ramified_norm
#print axioms ideal_norm_prime_power_dvd
#print axioms dvd_two_prime_pows
#print axioms split_ideal_factorization
#print axioms a_split_prime_power
#print axioms ideal_dvd_span_absNorm
#print axioms exps_unique_aux
#print axioms exps_unique
#print axioms dvd_one_prime_pow
#print axioms a_inert_prime_power
#print axioms a_ramified_prime_power
#print axioms span_coprime
#print axioms factor_recover
#print axioms a_mul_of_coprime
