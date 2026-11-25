import Cyclo7Cubic

/-!
# Cyclo7CubicField — the cubic subfield of ℚ(ζ₇) is ℚ(ζ₇ + ζ₇⁻¹)

With θ = ζ + ζ⁶ (= ζ + ζ⁻¹):
* `theta_mem`: θ lies in K = L^H (H = {σ : σ(ζ) = ζ^{±1}});
* `theta_root`: θ³ + θ² − 2θ − 1 = 0 (from ζ⁷ = 1 and 1 + ζ + ⋯ + ζ⁶ = 0);
* `theta_not_rat`: θ ∉ ℚ (a rational algebraic integer is an integer; ±1 are not roots);
* `adjoin_eq`: ℚ(θ) = K, since [K : ℚ] = 3 is prime;
* `minpoly_theta`: minpoly ℚ θ = X³ + X² − 2X − 1 (so it is irreducible).
-/

open NumberField IsCyclotomicExtension IsCyclotomicExtension.Rat Polynomial IntermediateField

namespace Cyclo7Cubic

variable {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {7} ℚ L]

local notation "ζ" => IsCyclotomicExtension.zeta 7 ℚ L

/-- θ = ζ + ζ⁻¹ = ζ + ζ⁶. -/
noncomputable def θ : L := ζ + ζ ^ 6

theorem hζ : IsPrimitiveRoot (ζ) 7 := zeta_spec 7 ℚ L

theorem theta_mem : (θ : L) ∈ IntermediateField.fixedField (H (L := L)) := by
  rw [mem_fixedField_iff]
  intro σ hσ
  have hz7 : (ζ) ^ 7 = 1 := (hζ (L := L)).pow_eq_one
  have hσζ := galEquivZMod_apply_of_pow_eq 7 L σ hz7
  have hmem : ((galEquivZMod 7 L σ : (ZMod 7)ˣ) : ZMod 7) = 1 ∨
      ((galEquivZMod 7 L σ : (ZMod 7)ˣ) : ZMod 7) = -1 := hσ
  rw [θ, map_add, map_pow, hσζ]
  rcases hmem with h | h <;> rw [h]
  · rw [show ZMod.val (1 : ZMod 7) = 1 from rfl, pow_one]
  · show (ζ) ^ 6 + ((ζ) ^ 6) ^ 6 = (ζ) + (ζ) ^ 6
    rw [← pow_mul, show 6 * 6 = 7 * 5 + 1 by norm_num, pow_add, pow_mul, hz7, one_pow, one_mul,
      pow_one, add_comm]

theorem theta_root : (θ : L) ^ 3 + θ ^ 2 - 2 * θ - 1 = 0 := by
  have hz7 : (ζ) ^ 7 = 1 := (hζ (L := L)).pow_eq_one
  have hsum := (hζ (L := L)).geom_sum_eq_zero (by norm_num : 1 < 7)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one] at hsum
  rw [θ]
  linear_combination ((ζ) ^ 11 + 3 * (ζ) ^ 6 + (ζ) ^ 5 + (ζ) ^ 4 + 3 * (ζ) + 2) * hz7 + hsum

theorem theta_isIntegral : IsIntegral ℤ (θ : L) := by
  have h := (hζ (L := L)).isIntegral (by norm_num : 0 < 7)
  exact h.add (h.pow 6)

theorem theta_not_rat : (θ : L) ∉ Set.range (algebraMap ℚ L) := by
  rintro ⟨q, hq⟩
  have hqi : IsIntegral ℤ q := by
    rw [← isIntegral_algebraMap_iff (B := L), hq]
    exact theta_isIntegral
  obtain ⟨z, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hqi
  have hroot := theta_root (L := L)
  rw [← hq] at hroot
  have hz : (z : ℚ) ^ 3 + (z : ℚ) ^ 2 - 2 * z - 1 = 0 := by
    apply (algebraMap ℚ L).injective
    simpa using hroot
  have hzz : z ^ 3 + z ^ 2 - 2 * z - 1 = 0 := by exact_mod_cast hz
  have hunit : z * (z ^ 2 + z - 2) = 1 := by linear_combination hzz
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hunit with rfl | rfl <;> norm_num at hzz

/-- **ℚ(θ) is the cubic subfield.** -/
theorem adjoin_eq : ℚ⟮(θ : L)⟯ = IntermediateField.fixedField (H (L := L)) := by
  have hle : ℚ⟮(θ : L)⟯ ≤ IntermediateField.fixedField (H (L := L)) :=
    (adjoin_simple_le_iff).mpr theta_mem
  have hdvd := finrank_dvd_of_le_right (K := ℚ) hle
  rw [finrank_K] at hdvd
  have hne : Module.finrank ℚ ℚ⟮(θ : L)⟯ ≠ 1 := by
    rw [Ne, IntermediateField.finrank_eq_one_iff, adjoin_simple_eq_bot_iff, mem_bot]
    exact theta_not_rat
  have h3 : Module.finrank ℚ ℚ⟮(θ : L)⟯ = 3 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
    · exact absurd h hne
    · exact h
  exact eq_of_le_of_finrank_eq hle (by rw [h3, finrank_K])

/-- **minpoly ℚ θ = X³ + X² − 2X − 1.** -/
theorem minpoly_theta : minpoly ℚ (θ : L) = X ^ 3 + X ^ 2 - 2 * X - 1 := by
  have hint : IsIntegral ℚ (θ : L) := theta_isIntegral.tower_top
  have hdeg : (minpoly ℚ (θ : L)).natDegree = 3 := by
    rw [← adjoin.finrank hint, adjoin_eq, finrank_K]
  have hP : (X ^ 3 + X ^ 2 - 2 * X - 1 : ℚ[X]).Monic := by monicity!
  have hPdeg : (X ^ 3 + X ^ 2 - 2 * X - 1 : ℚ[X]).natDegree = 3 := by compute_degree!
  have hroot : aeval (θ : L) (X ^ 3 + X ^ 2 - 2 * X - 1 : ℚ[X]) = 0 := by
    simp only [map_sub, map_add, map_pow, aeval_X, map_mul, map_one, map_ofNat]
    exact theta_root
  exact (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hP (minpoly.dvd ℚ _ hroot)
    (by rw [hPdeg, hdeg])).symm

end Cyclo7Cubic

#print axioms Cyclo7Cubic.adjoin_eq
#print axioms Cyclo7Cubic.minpoly_theta
