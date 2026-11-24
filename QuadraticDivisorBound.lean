import QuadraticLocalIdealCount
import DedekindIdealCountMultiplicative

/-!
# QuadraticDivisorBound — step 4: A_K(n) ≤ d(n) for Galois quadratic fields

Generic over any number field K with [K : ℚ] = 2 and `IsGalois ℚ K` (every quadratic field is
Galois; here that is a hypothesis, not proved). Nothing Gaussian or Eisenstein, no characters.

* The local estimate is derived from the generic allocation theorem
  `LocalCount.card_ideals_norm_prime_pow`, fed by Mathlib's fundamental identity
  #primesOver · e · f = 2: the possible patterns are (g, f) = (2, 1), (1, 1), (1, 2), giving
  k + 1, 1, [k even] — all ≤ k + 1 = d(pᵏ).
* `A_le_sigma0`: A_K(n) ≤ d(n) for n ≠ 0, through `IdealCount.A_mul`.

Degree-sensitive: for g = 3 the local count is C(k+2, 2) > k + 1, so this is a degree-two theorem.
-/

open Ideal NumberField LocalCount IdealCount
open scoped ArithmeticFunction.sigma

namespace QuadBound

variable {K : Type*} [Field K] [NumberField K]

theorem span_nat_isMaximal {p : ℕ} (hp : p.Prime) : (span {(p : ℤ)}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible

theorem mem_primesOver_of_dvd {p : ℕ} (hp : p.Prime) {Q : Ideal (𝓞 K)} (hQ : Prime Q)
    (hdvd : Q ∣ span {((p : ℕ) : 𝓞 K)}) : Q ∈ (span {(p : ℤ)}).primesOver (𝓞 K) := by
  have hQp : Q.IsPrime := isPrime_of_prime hQ
  refine ⟨hQp, ⟨?_⟩⟩
  have hle : span {(p : ℤ)} ≤ Q.under ℤ := by
    rw [span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_comap]
    have : ((p : ℕ) : 𝓞 K) ∈ Q := (Ideal.dvd_iff_le.mp hdvd) (mem_span_singleton_self _)
    simpa using this
  exact (span_nat_isMaximal hp).eq_of_le (IsPrime.under ℤ Q).ne_top hle

theorem prime_of_mem_primesOver {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)}
    (hP : P ∈ (span {(p : ℤ)}).primesOver (𝓞 K)) : Prime P := by
  obtain ⟨hPp, hlies⟩ := hP
  refine prime_of_isPrime ?_ hPp
  intro hb
  have := hlies.over
  rw [hb, under_bot] at this
  exact absurd this (by simpa using hp.ne_zero)

variable [IsGalois ℚ K]

/-- Every prime over p has norm p^f, f = `inertiaDegIn` (uniform, by Galois). -/
theorem absNorm_eq {p : ℕ} [Fact p.Prime] {P : Ideal (𝓞 K)}
    (hP : P ∈ (span {(p : ℤ)}).primesOver (𝓞 K)) :
    absNorm P = p ^ (span {(p : ℤ)}).inertiaDegIn (𝓞 K) := by
  obtain ⟨_, _⟩ := hP
  rw [inertiaDegIn_eq_inertiaDeg (span {(p : ℤ)}) P Gal(K/ℚ), ← natAbs_pow_inertiaDeg (p : ℤ) P]
  simp

theorem fundamental (hK : Module.finrank ℚ K = 2) (p : ℕ) [Fact p.Prime] :
    ((span {(p : ℤ)}).primesOver (𝓞 K)).ncard *
      ((span {(p : ℤ)}).ramificationIdxIn (𝓞 K) * (span {(p : ℤ)}).inertiaDegIn (𝓞 K)) = 2 := by
  rw [ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn _ (𝓞 K) Gal(K/ℚ),
    IsGaloisGroup.card_eq_finrank Gal(K/ℚ) ℚ K, hK]

/-- **Local estimate:** A_K(pᵏ) ≤ k + 1. -/
theorem A_prime_pow_le (hK : Module.finrank ℚ K = 2) {p : ℕ} [hp : Fact p.Prime] (k : ℕ) :
    A (𝓞 K) (p ^ k) ≤ k + 1 := by
  set s := (span {(p : ℤ)}).primesOver (𝓞 K)
  set f := (span {(p : ℤ)}).inertiaDegIn (𝓞 K)
  have hfun := fundamental hK (K := K) p
  have hexh : ∀ Q : Ideal (𝓞 K), Prime Q → Q ∣ span {((p : ℕ) : 𝓞 K)} → Q ∈ s :=
    fun Q hQ hd => mem_primesOver_of_dvd hp.out hQ hd
  have hns : s.ncard = 1 ∨ s.ncard = 2 := by
    have h1 : s.ncard ∣ 2 := ⟨_, hfun.symm⟩
    have h2 : s.ncard ≤ 2 := Nat.le_of_dvd (by norm_num) h1
    interval_cases h : s.ncard <;> simp_all
  rcases hns with h1 | h2
  · -- one prime above p
    obtain ⟨P₀, hs⟩ := Set.ncard_eq_one.mp h1
    have m0 : P₀ ∈ s := by rw [hs]; simp
    have hef : (span {(p : ℤ)}).ramificationIdxIn (𝓞 K) * f = 2 := by rw [h1, one_mul] at hfun; exact hfun
    have hcount := card_ideals_norm_prime_pow (P := ![P₀]) (f := f) hp.out.one_lt
      (fun i => by fin_cases i; exact prime_of_mem_primesOver hp.out m0)
      (fun i j _ => Subsingleton.elim i j)
      (fun Q hQ hdvd => ⟨0, by have := hexh Q hQ hdvd; rw [hs] at this; simpa using this⟩)
      (fun i => by fin_cases i; exact absNorm_eq m0) k
    rw [A, hcount]
    have hf : f = 1 ∨ f = 2 := by
      have : f ∣ 2 := ⟨_, by rw [← hef]; ring⟩
      have : f ≤ 2 := Nat.le_of_dvd (by norm_num) this
      interval_cases f <;> simp_all
    rcases hf with hf | hf
    · rw [hf, card_ramified]; omega
    · rw [hf, card_inert]; split_ifs <;> omega
  · -- two primes above p, each with f = 1
    obtain ⟨P₀, P₁, hne, hs⟩ := Set.ncard_eq_two.mp h2
    have m0 : P₀ ∈ s := by rw [hs]; simp
    have m1 : P₁ ∈ s := by rw [hs]; simp
    have hf : f = 1 := by
      rw [h2] at hfun
      have : (span {(p : ℤ)}).ramificationIdxIn (𝓞 K) * f = 1 :=
        Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (hfun.trans (mul_one 2).symm)
      exact Nat.eq_one_of_mul_eq_one_left this
    have hcount := card_ideals_norm_prime_pow (P := ![P₀, P₁]) (f := f) hp.out.one_lt
      (fun i => by fin_cases i
                   · exact prime_of_mem_primesOver hp.out m0
                   · exact prime_of_mem_primesOver hp.out m1)
      (fun i j hij => by
        fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> first | exact hne hij | exact hne hij.symm)
      (fun Q hQ hdvd => by
        have := hexh Q hQ hdvd
        rw [hs] at this
        rcases this with h | h
        · exact ⟨0, by simpa using h⟩
        · exact ⟨1, by simpa using h⟩)
      (fun i => by fin_cases i
                   · exact absNorm_eq m0
                   · exact absNorm_eq m1) k
    rw [A, hcount, hf, card_split]

/-- **A_K(n) ≤ d(n)** for every n ≠ 0, in a Galois quadratic field. -/
theorem A_le_sigma0 (hK : Module.finrank ℚ K = 2) {n : ℕ} (hn : n ≠ 0) :
    A (𝓞 K) n ≤ σ 0 n := by
  rw [Nat.multiplicative_factorization (A (𝓞 K)) (fun _ _ h => A_mul h) A_one hn,
    ArithmeticFunction.isMultiplicative_sigma.multiplicative_factorization (σ 0) hn,
    Finsupp.prod, Finsupp.prod]
  refine Finset.prod_le_prod fun p hp => ?_
  have hp' := Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)
  have := Fact.mk hp'
  rw [ArithmeticFunction.sigma_zero_apply_prime_pow hp']
  exact A_prime_pow_le hK _

end QuadBound

#print axioms QuadBound.A_prime_pow_le
#print axioms QuadBound.A_le_sigma0
