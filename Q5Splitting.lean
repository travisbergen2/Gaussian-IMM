import Q5Field
import Q5Character
import QuadraticFactorizationNoGalois

/-!
# Q5Splitting — splitting of primes in ℚ(√−5) and χ₋₂₀(p) = c_p

Kummer–Dedekind (Mathlib, `primesOverSpanEquivMonicFactorsMod`) applies at *every* prime p,
because 𝓞 K5 = ℤ[θ5] (`exponent θ5 = 1`). The primes over p correspond to the monic irreducible
factors of X² + 5 mod p, and residue degrees are the factor degrees.

* −5 a nonzero square mod p (p ∤ 20): X² + 5 = (X − r)(X + r), two factors → split, c_p = 1;
* −5 not a square mod p: no linear factor → f = 2, g = 1 → inert, c_p = −1;
* p = 2, 5: X² + 5 ≡ (X − a)² → one prime, f = 1 → ramified, c_p = 0.

No Gaussian or Eisenstein module is imported.
-/

open Polynomial NumberField Ideal QuadEuler NumberField.RingOfIntegers
open scoped Classical

namespace Q5

instance : IsGalois ℚ K5 := isGalois_of_finrank_eq_two finrank_K5

theorem not_dvd_exponent (p : ℕ) [hp : Fact p.Prime] : ¬ p ∣ exponent θ5 := by
  rw [show θ5.exponent = 1 from exponent_θ5]; exact hp.out.not_dvd_one

theorem map_minpoly (p : ℕ) :
    (minpoly ℤ θ5).map (Int.castRingHom (ZMod p)) = X ^ 2 + 5 := by
  rw [minpoly_θ5]; simp

theorem mem_factors_iff {p : ℕ} [Fact p.Prime] {Q : (ZMod p)[X]} :
    Q ∈ monicFactorsMod θ5 p ↔ Irreducible Q ∧ Q.Monic ∧ Q ∣ X ^ 2 + 5 := by
  rw [mem_monicFactorsMod_iff, map_minpoly]

theorem gP_eq_card (p : ℕ) [Fact p.Prime] : gP K5 p = (monicFactorsMod θ5 p).card := by
  rw [gP, ← Nat.card_coe_set_eq,
    Nat.card_congr (primesOverSpanEquivMonicFactorsMod (not_dvd_exponent p))]
  simp

theorem fP_eq_natDegree (p : ℕ) [Fact p.Prime] (P : (span {(p : ℤ)}).primesOver (𝓞 K5)) :
    fP K5 p =
      ((primesOverSpanEquivMonicFactorsMod (not_dvd_exponent p) P : (ZMod p)[X])).natDegree := by
  have := P.2.1; have := P.2.2
  rw [fP, inertiaDegIn_eq_inertiaDeg (span {(p : ℤ)}) P.1 Gal(K5/ℚ),
    inertiaDeg_primesOverSpanEquivMonicFactorsMod_apply]

theorem exists_prime_over (p : ℕ) [Fact p.Prime] :
    Nonempty ((span {(p : ℤ)}).primesOver (𝓞 K5)) := by
  obtain ⟨⟨P, h1, h2⟩⟩ := (span {(p : ℤ)}).nonempty_primesOver (S := 𝓞 K5)
  exact ⟨⟨P, h1, h2⟩⟩

theorem gP_le_two (p : ℕ) [Fact p.Prime] : gP K5 p ≤ 2 := by
  have h := QuadBound.fundamental finrank_K5 (K := K5) p
  exact Nat.le_of_dvd (by norm_num) ⟨_, h.symm⟩

/-! ## Polynomial facts over ZMod p -/

theorem natDegree_target (p : ℕ) [Fact p.Prime] : (X ^ 2 + 5 : (ZMod p)[X]).natDegree = 2 := by
  compute_degree!

theorem natDegree_factor {p : ℕ} [Fact p.Prime] {Q : (ZMod p)[X]} (hQ : Q ∈ monicFactorsMod θ5 p) :
    Q.natDegree = 1 ∨ Q.natDegree = 2 := by
  obtain ⟨hirr, _, hdvd⟩ := mem_factors_iff.mp hQ
  have h0 : (X ^ 2 + 5 : (ZMod p)[X]) ≠ 0 := by
    intro h; have := natDegree_target p; rw [h] at this; simp at this
  have hle := natDegree_le_of_dvd hdvd h0
  rw [natDegree_target] at hle
  have hpos := Irreducible.natDegree_pos hirr
  omega

theorem isSquare_of_linear_factor {p : ℕ} [Fact p.Prime] {Q : (ZMod p)[X]}
    (hQ : Q ∈ monicFactorsMod θ5 p) (h1 : Q.natDegree = 1) : IsSquare ((-5 : ℤ) : ZMod p) := by
  obtain ⟨_, hm, hdvd⟩ := mem_factors_iff.mp hQ
  rw [hm.eq_X_add_C h1, ← sub_neg_eq_add, ← C_neg, dvd_iff_isRoot] at hdvd
  simp only [IsRoot, eval_add, eval_pow, eval_X, eval_ofNat] at hdvd
  refine ⟨-Q.coeff 0, ?_⟩
  push_cast
  linear_combination -hdvd

theorem factor_eq_of_dvd_sq {F : Type*} [Field F] (a : F) {Q : F[X]} (hQ : Irreducible Q)
    (hQm : Q.Monic) (h : Q ∣ (X - C a) ^ 2) : Q = X - C a :=
  eq_of_monic_of_associated hQm (monic_X_sub_C a)
    (hQ.associated_of_dvd (irreducible_X_sub_C a) (hQ.prime.dvd_of_dvd_pow h))

/-- If X² + 5 ≡ (X − a)² mod p, then p has one prime above it, of residue degree 1. -/
theorem ramified_of_sq {p : ℕ} [Fact p.Prime] (a : ZMod p) (ha : (X ^ 2 + 5 : (ZMod p)[X]) = (X - C a) ^ 2) :
    gP K5 p ≠ 2 ∧ fP K5 p ≠ 2 := by
  have hall : ∀ Q ∈ monicFactorsMod θ5 p, Q = X - C a := fun Q hQ => by
    obtain ⟨hirr, hm, hdvd⟩ := mem_factors_iff.mp hQ
    exact factor_eq_of_dvd_sq a hirr hm (ha ▸ hdvd)
  refine ⟨?_, ?_⟩
  · rw [gP_eq_card]
    have : (monicFactorsMod θ5 p).card ≤ 1 :=
      Finset.card_le_one.mpr fun Q hQ R hR => (hall Q hQ).trans (hall R hR).symm
    omega
  · obtain ⟨P⟩ := exists_prime_over p
    rw [fP_eq_natDegree p P, hall _ (primesOverSpanEquivMonicFactorsMod _ P).2, natDegree_X_sub_C]
    norm_num

/-! ## The three cases -/

theorem split_case {p : ℕ} [hp : Fact p.Prime] (h2 : p ≠ 2) (h5 : p ≠ 5)
    (hsq : IsSquare ((-5 : ℤ) : ZMod p)) : gP K5 p = 2 := by
  obtain ⟨r, hr⟩ := hsq
  push_cast at hr
  have hmem : ∀ t : ZMod p, t * t = -5 → X - C t ∈ monicFactorsMod θ5 p := fun t ht =>
    mem_factors_iff.mpr ⟨irreducible_X_sub_C t, monic_X_sub_C t,
      ⟨X - C (-t), by
        calc (X ^ 2 + 5 : (ZMod p)[X]) = X ^ 2 - C (t * t) := by
              rw [ht, C_neg, sub_neg_eq_add]; exact congrArg _ (map_ofNat C 5).symm
          _ = (X - C t) * (X - C (-t)) := by rw [C_mul, C_neg]; ring⟩⟩
  have hne : X - C r ≠ X - C (-r) := by
    intro h
    have hrr : r = -r := C_injective (sub_right_injective h)
    have h2r : (2 : ZMod p) * r = 0 := by linear_combination hrr
    have h2ne : (2 : ZMod p) ≠ 0 := by
      intro h0
      have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
      rw [ZMod.natCast_eq_zero_iff] at this
      exact h2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
    have hr0 : r = 0 := (mul_eq_zero.mp h2r).resolve_left h2ne
    have h50 : ((5 : ℕ) : ZMod p) = 0 := by
      have : (-5 : ZMod p) = 0 := by rw [hr, hr0, mul_zero]
      exact_mod_cast neg_eq_zero.mp this
    rw [ZMod.natCast_eq_zero_iff] at h50
    exact h5 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_five).mp h50)
  have hcard : 1 < (monicFactorsMod θ5 p).card :=
    Finset.one_lt_card.mpr ⟨_, hmem r hr.symm, _, hmem (-r) (by rw [neg_mul_neg]; exact hr.symm), hne⟩
  have := gP_le_two p
  rw [gP_eq_card] at this ⊢
  omega

theorem inert_case {p : ℕ} [Fact p.Prime] (hsq : ¬ IsSquare ((-5 : ℤ) : ZMod p)) :
    gP K5 p ≠ 2 ∧ fP K5 p = 2 := by
  obtain ⟨P⟩ := exists_prime_over p
  have hf : fP K5 p = 2 := by
    rw [fP_eq_natDegree p P]
    have hQ := (primesOverSpanEquivMonicFactorsMod (not_dvd_exponent p) P).2
    rcases natDegree_factor hQ with h | h
    · exact absurd (isSquare_of_linear_factor hQ h) hsq
    · exact h
  refine ⟨fun hg => ?_, hf⟩
  have h := QuadBound.fundamental finrank_K5 (K := K5) p
  rw [← gP, ← fP, hg, hf] at h
  have : 4 ∣ 2 := ⟨_, by rw [← h]; ring⟩
  omega

theorem two_ramified : (X ^ 2 + 5 : (ZMod 2)[X]) = (X - C 1) ^ 2 := by
  have h2 : (2 : (ZMod 2)[X]) = 0 := by
    rw [← map_ofNat C 2, show (2 : ZMod 2) = 0 by decide, map_zero]
  rw [map_one]
  linear_combination (X + 2) * h2

theorem five_ramified : (X ^ 2 + 5 : (ZMod 5)[X]) = (X - C 0) ^ 2 := by
  have h5 : (5 : (ZMod 5)[X]) = 0 := by
    rw [← map_ofNat C 5, show (5 : ZMod 5) = 0 by decide, map_zero]
  rw [map_zero, h5]; ring

/-- **χ₋₂₀ matches the splitting of every prime in ℚ(√−5).** -/
theorem chi20C_eq_splitChar (p : ℕ) (hp : p.Prime) : chi20C (p : ZMod 20) = splitChar K5 p := by
  have : Fact p.Prime := ⟨hp⟩
  rw [chi20C_prime hp, splitChar]
  by_cases h25 : p = 2 ∨ p = 5
  · rw [if_pos h25]
    have hr : gP K5 p ≠ 2 ∧ fP K5 p ≠ 2 := by
      rcases h25 with rfl | rfl
      · exact ramified_of_sq 1 two_ramified
      · exact ramified_of_sq 0 five_ramified
    rw [if_neg hr.1, if_neg hr.2]
  · rw [if_neg h25]
    push_neg at h25
    by_cases hsq : IsSquare ((-5 : ℤ) : ZMod p)
    · rw [if_pos hsq, if_pos (split_case h25.1 h25.2 hsq)]
    · obtain ⟨hg, hf⟩ := inert_case hsq
      rw [if_neg hsq, if_neg hg, if_pos hf]

end Q5

#print axioms Q5.chi20C_eq_splitChar
