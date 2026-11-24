import QuadraticLocalIdealCount
import EisensteinCharacter

/-!
# EisensteinLocalInstance — step 3b: the generic local count for ℚ(ζ₃) = ℚ(√−3)

Imports only `QuadraticLocalIdealCount`, `EisensteinCharacter` and Mathlib: nothing Gaussian.
Works for any number field `K` with `IsCyclotomicExtension {3} ℚ K`; the ring is `𝓞 K`.

No explicit generators for the split primes are constructed. Instead:
* the prime ideals over p are *exactly* Mathlib's `primesOver (span {p}) (𝓞 K)` (exhaustion);
* their number comes from the fundamental identity  #primesOver · e · f = [K : ℚ] = 2,
  with Mathlib's cyclotomic values of e and f;
* their norms are p^f with f = `inertiaDeg` (Mathlib's `natAbs_pow_inertiaDeg`).

Results: a₋₃(3ᵏ) = 1, a₋₃(pᵏ) = k + 1 for p ≡ 1 mod 3, a₋₃(pᵏ) = [k even] for p ≡ 2 mod 3,
and χ₋₃(p) = (−1)^(f_p − 1) for p ≠ 3.
-/

open Ideal NumberField IsCyclotomicExtension.Rat LocalCount

variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]

/-- The ideal count of 𝓞 K. -/
noncomputable def a3 (n : ℕ) : ℕ := Nat.card {I : Ideal (𝓞 K) // absNorm I = n}

variable {K}

/-! ## From `primesOver` to the generic hypotheses -/

theorem span_nat_isMaximal {p : ℕ} (hp : p.Prime) : (span {(p : ℤ)}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible

/-- Exhaustion: a prime ideal dividing (p) lies in `primesOver`. -/
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

theorem absNorm_of_mem_primesOver {p : ℕ} (hP : P ∈ (span {(p : ℤ)}).primesOver (𝓞 K)) :
    absNorm P = p ^ P.inertiaDeg ℤ := by
  obtain ⟨hPp, hlies⟩ := hP
  rw [← natAbs_pow_inertiaDeg (p : ℤ) P]; simp

/-! ## The number of primes over p -/

theorem fundamental (p : ℕ) [Fact p.Prime] :
    ((span {(p : ℤ)}).primesOver (𝓞 K)).ncard *
      ((span {(p : ℤ)}).ramificationIdxIn (𝓞 K) * (span {(p : ℤ)}).inertiaDegIn (𝓞 K)) = 2 := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {3} ℚ K
  rw [ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn _ (𝓞 K) Gal(K/ℚ),
    IsGaloisGroup.card_eq_finrank Gal(K/ℚ) ℚ K, finrank (k := 3) K]
  rfl

theorem not_dvd_three {p : ℕ} [hp : Fact p.Prime] (hp3 : p % 3 ≠ 0) : ¬ p ∣ 3 := by
  intro h
  rcases (Nat.prime_three.eq_one_or_self_of_dvd p h) with h1 | h3
  · exact hp.out.ne_one h1
  · omega

theorem ncard_split {p : ℕ} [Fact p.Prime] (h1 : p % 3 = 1) :
    ((span {(p : ℤ)}).primesOver (𝓞 K)).ncard = 2 := by
  have := fundamental (K := K) p
  rw [ramificationIdxIn_eq_of_not_dvd p K (not_dvd_three (by omega)),
    inertiaDegIn_eq_of_not_dvd p K (not_dvd_three (by omega))] at this
  rcases natCast_zmod3_cases (p := p) (by omega) with ⟨hz, -⟩ | ⟨-, hm⟩
  · rw [hz, orderOf_one] at this; simpa using this
  · omega

theorem ncard_inert {p : ℕ} [Fact p.Prime] (h2 : p % 3 = 2) :
    ((span {(p : ℤ)}).primesOver (𝓞 K)).ncard = 1 := by
  have := fundamental (K := K) p
  rw [ramificationIdxIn_eq_of_not_dvd p K (not_dvd_three (by omega)),
    inertiaDegIn_eq_of_not_dvd p K (not_dvd_three (by omega))] at this
  rcases natCast_zmod3_cases (p := p) (by omega) with ⟨-, hm⟩ | ⟨hz, -⟩
  · omega
  · rw [hz, orderOf_two_zmod3] at this; omega

theorem inertiaDeg_of_cases {p : ℕ} [Fact p.Prime] (hp3 : p % 3 ≠ 0) {P : Ideal (𝓞 K)}
    (hP : P ∈ (span {(p : ℤ)}).primesOver (𝓞 K)) :
    P.inertiaDeg ℤ = orderOf (p : ZMod 3) := by
  obtain ⟨_, _⟩ := hP
  exact inertiaDeg_eq_of_not_dvd p K P (not_dvd_three hp3)

/-! ## The three counts -/

/-- **Split, p ≡ 1 mod 3:** a₋₃(pᵏ) = k + 1. -/
theorem eis_split {p : ℕ} [hp : Fact p.Prime] (h1 : p % 3 = 1) (k : ℕ) : a3 K (p ^ k) = k + 1 := by
  obtain ⟨P₀, P₁, hne, hs⟩ := Set.ncard_eq_two.mp (ncard_split (K := K) h1)
  have m0 : P₀ ∈ (span {(p : ℤ)}).primesOver (𝓞 K) := by rw [hs]; simp
  have m1 : P₁ ∈ (span {(p : ℤ)}).primesOver (𝓞 K) := by rw [hs]; simp
  have hz : (p : ZMod 3) = 1 := by
    rcases natCast_zmod3_cases (p := p) (by omega) with ⟨hz, -⟩ | ⟨-, hm⟩
    · exact hz
    · omega
  have hf : ∀ P ∈ (span {(p : ℤ)}).primesOver (𝓞 K), absNorm P = p ^ 1 := fun P hP => by
    rw [absNorm_of_mem_primesOver hP, inertiaDeg_of_cases (by omega) hP, hz, orderOf_one]
  rw [a3, card_ideals_norm_prime_pow (P := ![P₀, P₁]) (f := 1) hp.out.one_lt
    (fun i => by fin_cases i
                 · exact prime_of_mem_primesOver hp.out m0
                 · exact prime_of_mem_primesOver hp.out m1)
    (fun i j hij => by
      fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> first | exact hne hij | exact hne hij.symm)
    (fun Q hQ hdvd => by
      have hm := mem_primesOver_of_dvd hp.out hQ hdvd
      rw [hs] at hm
      rcases hm with h | h
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩)
    (fun i => by fin_cases i
                 · exact hf _ m0
                 · exact hf _ m1) k]
  exact card_split k

/-- **Inert, p ≡ 2 mod 3:** a₋₃(pᵏ) = 1 if k is even, 0 if k is odd. -/
theorem eis_inert {p : ℕ} [hp : Fact p.Prime] (h2 : p % 3 = 2) (k : ℕ) :
    a3 K (p ^ k) = if Even k then 1 else 0 := by
  obtain ⟨P₀, hs⟩ := Set.ncard_eq_one.mp (ncard_inert (K := K) h2)
  have m0 : P₀ ∈ (span {(p : ℤ)}).primesOver (𝓞 K) := by rw [hs]; simp
  have hz : (p : ZMod 3) = 2 := by
    rcases natCast_zmod3_cases (p := p) (by omega) with ⟨-, hm⟩ | ⟨hz, -⟩
    · omega
    · exact hz
  have hf : absNorm P₀ = p ^ 2 := by
    rw [absNorm_of_mem_primesOver m0, inertiaDeg_of_cases (by omega) m0, hz, orderOf_two_zmod3]
  rw [a3, card_ideals_norm_prime_pow (P := ![P₀]) (f := 2) hp.out.one_lt
    (fun i => by fin_cases i; exact prime_of_mem_primesOver hp.out m0)
    (fun i j _ => Subsingleton.elim i j)
    (fun Q hQ hdvd => by
      have hm := mem_primesOver_of_dvd hp.out hQ hdvd
      rw [hs] at hm
      exact ⟨0, by simpa using hm⟩)
    (fun i => by fin_cases i; exact hf) k]
  exact card_inert k

/-- **Ramified, p = 3:** a₋₃(3ᵏ) = 1. -/
theorem eis_ramified (k : ℕ) : a3 K (3 ^ k) = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P₀, hs⟩ := Set.ncard_eq_one.mp (ncard_primesOver_of_prime 3 K)
  have m0 : P₀ ∈ (span {((3 : ℕ) : ℤ)}).primesOver (𝓞 K) := by rw [hs]; simp
  have hf : absNorm P₀ = 3 ^ 1 := by
    obtain ⟨_, _⟩ := id m0
    rw [absNorm_of_mem_primesOver m0, inertiaDeg_eq_of_prime 3 K P₀]
  rw [a3, card_ideals_norm_prime_pow (P := ![P₀]) (f := 1) (by norm_num)
    (fun i => by fin_cases i; exact prime_of_mem_primesOver Nat.prime_three m0)
    (fun i j _ => Subsingleton.elim i j)
    (fun Q hQ hdvd => by
      have hm := mem_primesOver_of_dvd Nat.prime_three hQ hdvd
      rw [hs] at hm
      exact ⟨0, by simpa using hm⟩)
    (fun i => by fin_cases i; exact hf) k]
  exact card_ramified k

/-! ## χ₋₃(p) = (−1)^(f_p − 1) -/

/-- For p ≠ 3 and any prime P of 𝓞 K over p: χ₋₃(p) = (−1)^(f(P) − 1). -/
theorem chi3_eq_neg_one_pow_inertiaDeg {p : ℕ} [Fact p.Prime] (hp3 : p % 3 ≠ 0)
    {P : Ideal (𝓞 K)} (hP : P ∈ (span {(p : ℤ)}).primesOver (𝓞 K)) :
    chi3C (p : ZMod 3) = (-1) ^ (P.inertiaDeg ℤ - 1) := by
  rw [inertiaDeg_of_cases hp3 hP]
  rcases natCast_zmod3_cases hp3 with ⟨hz, hm⟩ | ⟨hz, hm⟩
  · rw [chi3C_one_mod_three hm, hz, orderOf_one]; simp
  · rw [chi3C_two_mod_three hm, hz, orderOf_two_zmod3]; simp

#print axioms eis_split
#print axioms eis_inert
#print axioms eis_ramified
#print axioms chi3_eq_neg_one_pow_inertiaDeg
