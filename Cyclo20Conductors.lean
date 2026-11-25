import Cyclo20Biquadratic
import ConductorCongruence

/-!
# Cyclo20Conductors — the exact conductors 4, 5, 20 for ℚ(i, √5)

* `conductor_chiM4 : conductor χ₋₄ = 4`, `conductor_chi5 : conductor χ₅ = 5`,
  `conductor_chiM20 : conductor χ₋₂₀ = 20` (all as characters mod 20).
Method: the conductor c divides the level and χ factors through c (Mathlib); every proper divisor
is excluded by two units congruent mod it with different χ-values (`CondCong.not_factorsThrough`):
* χ₋₄ (level 4): 3 ≡ 1 mod 2, χ(3) = −1 ≠ 1;
* χ₅ (level 5): only 1 to exclude;
* χ₋₂₀: 11 ≡ 1 mod 10 (excludes 1, 2, 5, 10), 13 ≡ 1 mod 4 (excludes 4).
So the primitive characters χ₋₄*, χ₅*, χ₋₂₀* in `LSeries_K_explicit` have moduli 4, 5, 20.
-/

open DirichletCharacter CondCong

namespace Cyclo20

theorem c4_ne : c4 ((3 : ℕ) : ZMod 4) ≠ c4 ((1 : ℕ) : ZMod 4) := by
  have h3 : c4 ((3 : ℕ) : ZMod 4) = -1 := by
    rw [show ((3 : ℕ) : ZMod 4) = 3 by rfl]; simp [c4] <;> decide
  rw [h3, Nat.cast_one, map_one]; norm_num

theorem c5_ne : c5 ((3 : ℕ) : ZMod 5) ≠ c5 ((1 : ℕ) : ZMod 5) := by
  rw [show ((3 : ℕ) : ZMod 5) = 3 by rfl, q5_nsq _ (by decide) (by rintro ⟨r, hr⟩; revert r; decide)]
  simp; norm_num

theorem conductor_c4 : conductor c4 = 4 := by
  have hf := factorsThrough_conductor c4
  have hmem : conductor c4 ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨conductor_dvd_level c4, by norm_num⟩
  rw [show Nat.divisors 4 = {1, 2, 4} by decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h <;> rw [h] at hf ⊢
  · exact absurd hf (not_factorsThrough c4 (by norm_num) (by norm_num) (by decide) c4_ne)
  · exact absurd hf (not_factorsThrough c4 (by norm_num) (by norm_num) (by decide) c4_ne)

theorem conductor_c5 : conductor c5 = 5 := by
  have hf := factorsThrough_conductor c5
  rcases (Nat.prime_five.eq_one_or_self_of_dvd _ (conductor_dvd_level c5)) with h | h
  · rw [h] at hf
    exact absurd hf (not_factorsThrough c5 (by norm_num) (by norm_num) (by decide) c5_ne)
  · exact h

/-- **conductor χ₋₄ = 4.** -/
theorem conductor_chiM4 : conductor chiM4 = 4 := by
  rw [chiM4, conductor_changeLevel, conductor_c4]

/-- **conductor χ₅ = 5.** -/
theorem conductor_chi5 : conductor chi5 = 5 := by
  rw [chi5, conductor_changeLevel, conductor_c5]

theorem m20_vals : chiM20 ((11 : ℕ) : ZMod 20) ≠ chiM20 ((1 : ℕ) : ZMod 20) ∧
    chiM20 ((13 : ℕ) : ZMod 20) ≠ chiM20 ((1 : ℕ) : ZMod 20) := by
  have v43 : chiM4 (3 : ZMod 20) = -1 := by simpa using chiM4_3
  have v411 : chiM4 (11 : ZMod 20) = -1 := by simpa using chiM4_11
  have v53 : chi5 (3 : ZMod 20) = -1 := by simpa using chi5_3
  have v511 : chi5 (11 : ZMod 20) = 1 := by simpa using chi5_11
  have h13 : (13 : ZMod 20) = 3 * 11 := by decide
  simp only [Nat.cast_ofNat, Nat.cast_one, chiM20, MulChar.coeToFun_mul, Pi.mul_apply, map_one,
    h13, map_mul, v43, v411, v53, v511]
  norm_num

/-- **conductor χ₋₂₀ = 20.** -/
theorem conductor_chiM20 : conductor chiM20 = 20 := by
  have hf := factorsThrough_conductor chiM20
  have hmem : conductor chiM20 ∈ Nat.divisors 20 :=
    Nat.mem_divisors.mpr ⟨conductor_dvd_level chiM20, by norm_num⟩
  rw [show Nat.divisors 20 = {1, 2, 4, 5, 10, 20} by decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  obtain ⟨h11, h13⟩ := m20_vals
  rcases hmem with h | h | h | h | h | h <;> rw [h] at hf ⊢
  · exact absurd hf (not_factorsThrough chiM20 (by norm_num) (by norm_num) (by decide) h11)
  · exact absurd hf (not_factorsThrough chiM20 (by norm_num) (by norm_num) (by decide) h11)
  · exact absurd hf (not_factorsThrough chiM20 (by norm_num) (by norm_num) (by decide) h13)
  · exact absurd hf (not_factorsThrough chiM20 (by norm_num) (by norm_num) (by decide) h11)
  · exact absurd hf (not_factorsThrough chiM20 (by norm_num) (by norm_num) (by decide) h11)

end Cyclo20

#print axioms Cyclo20.conductor_chiM4
#print axioms Cyclo20.conductor_chi5
#print axioms Cyclo20.conductor_chiM20
