import CyclotomicSubfieldSplitting

/-!
# Cyclo9CubicField — the cubic subfield of ℚ(ζ₉)

L = ℚ(ζ₉), G = Gal(L/ℚ) ≅ (ZMod 9)ˣ ≅ C₆, H = {σ : σ(ζ) = ζ^{±1}} = {1, 8} (order 2), K = L^H.
* `index_H`, `finrank_K`: [G : H] = [K : ℚ] = 3, and G/H ≅ C₃ (`cubes_mem_Hsub`: u³ ∈ H for all u);
* θ = ζ + ζ⁸ = ζ + ζ⁻¹: `theta_mem` (θ ∈ K), `theta_root` (θ³ − 3θ + 1 = 0), `theta_not_rat`;
* `adjoin_eq`: ℚ(θ) = K; `minpoly_theta`: minpoly ℚ θ = X³ − 3X + 1.
-/

open NumberField IsCyclotomicExtension IsCyclotomicExtension.Rat Polynomial IntermediateField

namespace Cyclo9Cubic

/-- {1, 8} = {±1} in (ZMod 9)ˣ. -/
def Hsub : Subgroup (ZMod 9)ˣ where
  carrier := {u | (u : ZMod 9) = 1 ∨ (u : ZMod 9) = 8}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul] at *
    rcases ha with h | h <;> rcases hb with h' | h' <;> rw [h, h'] <;> decide
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rcases ha with h | h
    · left; rw [← Units.val_one, ← Units.ext_iff] at h ⊢; rw [h, inv_one]
    · right
      have : (a⁻¹ : (ZMod 9)ˣ) = a := by
        rw [inv_eq_iff_mul_eq_one]; apply Units.ext; rw [Units.val_mul, Units.val_one, h]; decide
      rw [this, h]

instance : DecidablePred (· ∈ Hsub) := fun u =>
  inferInstanceAs (Decidable ((u : ZMod 9) = 1 ∨ (u : ZMod 9) = 8))

theorem units_cases : ∀ x : (ZMod 9)ˣ, (x : ZMod 9) = 1 ∨ (x : ZMod 9) = 2 ∨ (x : ZMod 9) = 4 ∨
    (x : ZMod 9) = 5 ∨ (x : ZMod 9) = 7 ∨ (x : ZMod 9) = 8 := by decide

/-- G/H has exponent 3: every cube lies in H. -/
theorem cubes_mem_Hsub : ∀ u : (ZMod 9)ˣ, u ^ 3 ∈ Hsub := by decide

theorem card_Hsub : Nat.card Hsub = 2 := by
  rw [Nat.card_eq_fintype_card]; decide

theorem index_Hsub : Hsub.index = 3 := by
  have h := Hsub.card_mul_index
  rw [card_Hsub, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] at h
  have : Nat.totient 9 = 6 := by decide
  omega

variable {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {9} ℚ L]

/-- H = automorphisms with σ(ζ) = ζ^{±1}. -/
noncomputable def H : Subgroup Gal(L/ℚ) := Hsub.comap (galEquivZMod 9 L).toMonoidHom

instance : (H (L := L)).Normal := CycloSub.normal 9 _

theorem index_H : (H (L := L)).index = 3 := by
  rw [H, Subgroup.index_comap_of_surjective (f := (galEquivZMod 9 L).toMonoidHom) Hsub
    (galEquivZMod 9 L).surjective, index_Hsub]

theorem finrank_K : Module.finrank ℚ (fixedField (H (L := L))) = 3 := by
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {9} ℚ L
  rw [CycloSub.finrank_K, index_H]

local notation "ζ" => IsCyclotomicExtension.zeta 9 ℚ L

theorem hζ : IsPrimitiveRoot (ζ) 9 := zeta_spec 9 ℚ L

/-- θ = ζ + ζ⁻¹ = ζ + ζ⁸. -/
noncomputable def θ : L := ζ + ζ ^ 8

theorem theta_mem : (θ : L) ∈ fixedField (H (L := L)) := by
  rw [mem_fixedField_iff]
  intro σ hσ
  have hz9 : (ζ) ^ 9 = 1 := (hζ (L := L)).pow_eq_one
  have hσζ := galEquivZMod_apply_of_pow_eq 9 L σ hz9
  have hmem : ((galEquivZMod 9 L σ : (ZMod 9)ˣ) : ZMod 9) = 1 ∨
      ((galEquivZMod 9 L σ : (ZMod 9)ˣ) : ZMod 9) = 8 := hσ
  rw [θ, map_add, map_pow, hσζ]
  rcases hmem with h | h <;> rw [h]
  · rw [show ZMod.val (1 : ZMod 9) = 1 from rfl, pow_one]
  · show (ζ) ^ 8 + ((ζ) ^ 8) ^ 8 = (ζ) + (ζ) ^ 8
    rw [← pow_mul, show 8 * 8 = 9 * 7 + 1 by norm_num, pow_add, pow_mul, hz9, one_pow, one_mul,
      pow_one, add_comm]

theorem theta_root : (θ : L) ^ 3 - 3 * θ + 1 = 0 := by
  have hz9 : (ζ) ^ 9 = 1 := (hζ (L := L)).pow_eq_one
  have h3 : IsPrimitiveRoot ((ζ) ^ 3) 3 := (hζ (L := L)).pow (by norm_num) (by norm_num)
  have hsum := h3.geom_sum_eq_zero (by norm_num : 1 < 3)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
    ← pow_mul] at hsum
  rw [θ]
  linear_combination ((ζ) ^ 15 + 3 * (ζ) ^ 8 + (ζ) ^ 6 + 3 * (ζ)) * hz9 + hsum

theorem theta_isIntegral : IsIntegral ℤ (θ : L) := by
  have h := (hζ (L := L)).isIntegral (by norm_num : 0 < 9)
  exact h.add (h.pow 8)

theorem theta_not_rat : (θ : L) ∉ Set.range (algebraMap ℚ L) := by
  rintro ⟨q, hq⟩
  have hqi : IsIntegral ℤ q := by
    rw [← isIntegral_algebraMap_iff (B := L), hq]
    exact theta_isIntegral
  obtain ⟨z, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hqi
  have hroot := theta_root (L := L)
  rw [← hq] at hroot
  have hz : (z : ℚ) ^ 3 - 3 * z + 1 = 0 := by
    apply (algebraMap ℚ L).injective
    simpa using hroot
  have hzz : z ^ 3 - 3 * z + 1 = 0 := by exact_mod_cast hz
  have hunit : z * (3 - z ^ 2) = 1 := by linear_combination -hzz
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hunit with rfl | rfl <;> norm_num at hzz

/-- **ℚ(θ) is the cubic subfield.** -/
theorem adjoin_eq : ℚ⟮(θ : L)⟯ = fixedField (H (L := L)) := by
  have hle : ℚ⟮(θ : L)⟯ ≤ fixedField (H (L := L)) := (adjoin_simple_le_iff).mpr theta_mem
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

/-- **minpoly ℚ θ = X³ − 3X + 1.** -/
theorem minpoly_theta : minpoly ℚ (θ : L) = X ^ 3 - 3 * X + 1 := by
  have hint : IsIntegral ℚ (θ : L) := theta_isIntegral.tower_top
  have hdeg : (minpoly ℚ (θ : L)).natDegree = 3 := by
    rw [← adjoin.finrank hint, adjoin_eq, finrank_K]
  have hP : (X ^ 3 - 3 * X + 1 : ℚ[X]).Monic := by monicity!
  have hPdeg : (X ^ 3 - 3 * X + 1 : ℚ[X]).natDegree = 3 := by compute_degree!
  have hroot : aeval (θ : L) (X ^ 3 - 3 * X + 1 : ℚ[X]) = 0 := by
    simp only [map_sub, map_add, map_pow, aeval_X, map_mul, map_one, map_ofNat]
    exact theta_root
  exact (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hP (minpoly.dvd ℚ _ hroot)
    (by rw [hPdeg, hdeg])).symm

end Cyclo9Cubic

#print axioms Cyclo9Cubic.cubes_mem_Hsub
#print axioms Cyclo9Cubic.adjoin_eq
#print axioms Cyclo9Cubic.minpoly_theta
