import GaussianSynthesis

/-!
# GaussianNormObstruction — when is a(n) = 0?

Additive module on the frozen baseline (imports `GaussianSynthesis`; changes nothing).
Uses the already-proved prime-power counts and multiplicativity of a(n); nothing is re-proved.

* `A_prime_pow_eq_zero_iff`: a(pᵏ) = 0 ⟺ p ≡ 3 mod 4 and k odd.
* `a_eq_zero_iff`: for n > 0, a(n) = 0 ⟺ some prime p ≡ 3 mod 4 has odd exponent in n.
* `a_pos_iff_sum_two_squares`: a(n) > 0 ⟺ n = x² + y² (through principal ideals, ℤ[i] a PID).
* `sum_two_squares_iff`: the classical criterion, *derived* from the two above, then
  cross-checked against Mathlib's independent `Nat.eq_sq_add_sq_iff`.
Purely arithmetic: no L-functions, no zeros, no RH/GRH content.
-/

open Ideal ArithmeticFunction GaussianSynthesis

/-- **Local obstruction:** a(pᵏ) = 0 exactly for inert p and odd k. -/
theorem a_prime_pow_eq_zero_iff {p : ℕ} (hp : p.Prime) (k : ℕ) :
    a (p ^ k) = 0 ↔ p % 4 = 3 ∧ Odd k := by
  have := Fact.mk hp
  rcases hp.eq_two_or_odd' with rfl | hodd
  · rw [a_ramified_prime_power]; simp
  · have h4 : p % 4 = 1 ∨ p % 4 = 3 := by rcases hodd with ⟨m, hm⟩; omega
    rcases h4 with h1 | h3
    · rw [a_split_prime_power h1]; simp [h1]
    · rw [a_inert_prime_power h3]
      split_ifs with hk
      · simp [h3, Nat.not_odd_iff_even.mpr hk]
      · simp [h3, Nat.not_even_iff_odd.mp hk]

/-- **The obstruction:** for n > 0, a(n) = 0 ⟺ some prime p ≡ 3 mod 4 divides n to an odd power. -/
theorem a_eq_zero_iff {n : ℕ} (hn : 0 < n) :
    a n = 0 ↔ ∃ p, p.Prime ∧ p % 4 = 3 ∧ Odd (n.factorization p) := by
  have hA : (a n : ℤ) = n.factorization.prod fun p k => A (p ^ k) := by
    rw [← A_apply hn.ne']; exact IsMultiplicative.multiplicative_factorization A A_mult hn.ne'
  rw [← Int.natCast_eq_zero, hA, Finsupp.prod, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨p, hps, hz⟩
    have hp := Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hps)
    rw [A_apply (pow_ne_zero _ hp.ne_zero), Int.natCast_eq_zero, a_prime_pow_eq_zero_iff hp] at hz
    exact ⟨p, hp, hz⟩
  · rintro ⟨p, hp, h3, hodd⟩
    refine ⟨p, ?_, ?_⟩
    · rw [Finsupp.mem_support_iff]; exact hodd.pos.ne'
    · rw [A_apply (pow_ne_zero _ hp.ne_zero), Int.natCast_eq_zero, a_prime_pow_eq_zero_iff hp]
      exact ⟨h3, hodd⟩

/-- **Ideals ↔ representations:** a(n) > 0 ⟺ n is a sum of two squares (ℤ[i] is a PID). -/
theorem a_pos_iff_sum_two_squares (n : ℕ) :
    0 < a n ↔ ∃ x y : ℤ, x ^ 2 + y ^ 2 = n := by
  have hfin : Finite {I : Ideal Zi // absNorm I = n} :=
    (Ring.HasFiniteQuotients.finite_absNorm_eq n).to_subtype
  rw [a, Nat.card_pos_iff]
  constructor
  · rintro ⟨⟨⟨I, hI⟩⟩, -⟩
    obtain ⟨z, hz⟩ := absNorm_is_sum_two_squares I
    refine ⟨z.re, z.im, ?_⟩
    rw [hI] at hz
    have h0 : 0 ≤ z.re ^ 2 + z.im ^ 2 := by positivity
    omega
  · rintro ⟨x, y, hxy⟩
    refine ⟨⟨⟨span {(⟨x, y⟩ : Zi)}, ?_⟩⟩, hfin⟩
    rw [absNorm_span]; simp only; rw [hxy]; rfl

/-- **The classical two-squares criterion, derived from the ideal count.** For n > 0:
n = x² + y² ⟺ every prime p ≡ 3 mod 4 has even exponent in n. -/
theorem sum_two_squares_iff {n : ℕ} (hn : 0 < n) :
    (∃ x y : ℤ, x ^ 2 + y ^ 2 = n) ↔ ∀ p, p.Prime → p % 4 = 3 → Even (n.factorization p) := by
  rw [← a_pos_iff_sum_two_squares, Nat.pos_iff_ne_zero, Ne, a_eq_zero_iff hn]
  simp only [not_exists, not_and, Nat.not_odd_iff_even]

/-- Cross-check: the derived criterion agrees with Mathlib's independent `Nat.eq_sq_add_sq_iff`. -/
theorem agrees_with_mathlib {n : ℕ} (hn : 0 < n) :
    (∀ p, p.Prime → p % 4 = 3 → Even (n.factorization p)) ↔
      ∀ q ∈ n.primeFactors, q % 4 = 3 → Even (padicValNat q n) := by
  constructor
  · intro h q hq h3
    rw [Nat.padicValNat_def, ← Nat.factorization_def n (Nat.prime_of_mem_primeFactors hq)]
    exact h q (Nat.prime_of_mem_primeFactors hq) h3
  · intro h p hp h3
    by_cases hpn : p ∣ n
    · have hq : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, hn.ne'⟩
      have := h p hq h3
      rwa [Nat.padicValNat_def, ← Nat.factorization_def n hp] at this
    · rw [Nat.factorization_eq_zero_of_not_dvd hpn]; exact ⟨0, rfl⟩

#print axioms a_prime_pow_eq_zero_iff
#print axioms a_eq_zero_iff
#print axioms a_pos_iff_sum_two_squares
#print axioms sum_two_squares_iff
#print axioms agrees_with_mathlib
