import Cyclo9CubicRamification
import CompositeCyclotomicEulerProduct
import CyclotomicCharacterCorrespondence
import ConductorCongruence

/-!
# Cyclo9CubicEulerProduct — ζ_K = ζ · L(χ) · L(χ̄) for the cubic subfield of ℚ(ζ₉)

K = ℚ(ζ₉)^H, H = {1, 8}. H^⊥ has |G/H| = 3 elements (`CycloCharCorr.card_perp`):
* `perpNontriv_eq`: H^⊥ ∖ {1} = {χ, χ²} for any nontrivial χ ∈ H^⊥, with χ³ = 1 (u³ ∈ H for
  every unit u) and χ² ≠ χ;
* `sq_eq_conj`: χ² = χ̄ (values are cube roots of unity);
* `conductor_eq_nine`: every nontrivial ψ ∈ H^⊥ is primitive of conductor 9 (not 1: ψ ≠ 1;
  not 3: 4 ≡ 1 (mod 3) but ψ(4) ≠ 1, because 4 and H generate (ZMod 9)ˣ);
* `primitive_apply`: so ψ* = ψ on ℕ;
* `local_three`: at the wildly ramified prime 3, χ(3) = χ̄(3) = 0 and the local factor is
  (1 − x^f)^g = 1 − x = (1 − x)(1 − χ(3)x)(1 − χ̄(3)x);
* `zeta_K`: Σ A_K(m) m⁻ˢ = ζ(s) · L(s, χ) · L(s, χ̄) for Re s > 1, χ primitive of conductor 9.
-/

open NumberField IsCyclotomicExtension.Rat GaloisEuler DirichletCharacter

namespace Cyclo9Cubic

variable {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {9} ℚ L]

local notation "K" => IntermediateField.fixedField (H (L := L))

theorem H'_eq : CycloSubEuler.H' 9 L (H (L := L)) = Hsub :=
  Subgroup.map_comap_eq_self_of_surjective (galEquivZMod 9 L).surjective _

theorem mem_perp {ψ : DirichletCharacter ℂ 9} :
    ψ ∈ CycloSubEuler.perp 9 L (H (L := L)) ↔ ∀ u ∈ Hsub, ψ u = 1 := by
  rw [CycloSubEuler.mem_perp_iff, H'_eq]

theorem cube_eq_one {ψ : DirichletCharacter ℂ 9} (hψ : ψ ∈ CycloSubEuler.perp 9 L (H (L := L))) :
    ψ ^ 3 = 1 := by
  apply MulChar.ext
  intro u
  rw [MulChar.pow_apply' _ (by norm_num), ← map_pow, ← Units.val_pow_eq_pow_val,
    (mem_perp.mp hψ) _ (cubes_mem_Hsub u), MulChar.one_apply (Units.isUnit _)]

theorem sq_mem {ψ : DirichletCharacter ℂ 9} (hψ : ψ ∈ CycloSubEuler.perp 9 L (H (L := L))) :
    ψ ^ 2 ∈ CycloSubEuler.perp 9 L (H (L := L)) := by
  rw [mem_perp] at hψ ⊢
  intro u hu
  rw [MulChar.pow_apply' _ (by norm_num), hψ u hu, one_pow]

/-- **H^⊥ ∖ {1} = {χ, χ²}.** -/
theorem perpNontriv_eq {χ : DirichletCharacter ℂ 9}
    (hχ : χ ∈ CycloSubEuler.perpNontriv 9 L (H (L := L))) :
    CycloSubEuler.perpNontriv 9 L (H (L := L)) = {χ, χ ^ 2} := by
  classical
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {9} ℚ L
  rw [CycloSubEuler.perpNontriv, Finset.mem_erase] at hχ
  obtain ⟨hne, hp⟩ := hχ
  have h3 := cube_eq_one hp
  have hsq1 : χ ^ 2 ≠ 1 := by
    intro h
    apply hne
    rw [show χ = χ ^ 3 * (χ ^ 2)⁻¹ by group, h3, h, inv_one, mul_one]
  have hsqχ : χ ^ 2 ≠ χ := by
    intro h
    apply hne
    rw [pow_two, mul_eq_left] at h
    exact h
  have hsub : ({χ, χ ^ 2} : Finset _) ⊆ (CycloSubEuler.perp 9 L (H (L := L))).erase 1 := by
    intro ψ hψ
    rw [Finset.mem_insert, Finset.mem_singleton] at hψ
    rcases hψ with rfl | rfl
    · exact Finset.mem_erase.mpr ⟨hne, hp⟩
    · exact Finset.mem_erase.mpr ⟨hsq1, sq_mem hp⟩
  have hcard : ((CycloSubEuler.perp 9 L (H (L := L))).erase 1).card = 2 := by
    rw [Finset.card_erase_of_mem (CycloSubEuler.one_mem_perp 9 L _),
      (CycloCharCorr.card_perp 9 L (H (L := L))).1, index_H]
  have hcard2 : ({χ, χ ^ 2} : Finset _).card = 2 := by
    rw [Finset.card_pair (Ne.symm hsqχ)]
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hcard2])).symm

/-- **χ² = χ̄.** -/
theorem sq_eq_conj {χ : DirichletCharacter ℂ 9}
    (hχ : χ ∈ CycloSubEuler.perp 9 L (H (L := L))) (a : ZMod 9) :
    (χ ^ 2) a = starRingEnd ℂ (χ a) := by
  by_cases ha : IsUnit a
  · have h3 : (χ a) ^ 3 = 1 := by
      rw [← MulChar.pow_apply' _ (by norm_num), cube_eq_one hχ, MulChar.one_apply ha]
    have hnorm := Complex.norm_eq_one_of_pow_eq_one h3 (by norm_num)
    have hne : χ a ≠ 0 := by intro h; rw [h] at h3; norm_num at h3
    rw [MulChar.pow_apply' _ (by norm_num), ← Complex.inv_eq_conj hnorm]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h3])
  · rw [MulChar.map_nonunit _ ha, MulChar.map_nonunit _ ha, map_zero]

/-- **Every nontrivial ψ ∈ H^⊥ is primitive of conductor 9.** -/
theorem conductor_eq_nine {ψ : DirichletCharacter ℂ 9}
    (hψ : ψ ∈ CycloSubEuler.perpNontriv 9 L (H (L := L))) : conductor ψ = 9 := by
  rw [CycloSubEuler.perpNontriv, Finset.mem_erase] at hψ
  obtain ⟨hne, hp⟩ := hψ
  have hH := mem_perp.mp hp
  have h8 : ψ (8 : ZMod 9) = 1 := hH (ZMod.unitOfCoprime 8 (by norm_num)) (Or.inr rfl)
  have h4 : ψ (4 : ZMod 9) ≠ 1 := by
    intro h4
    apply hne
    apply MulChar.ext
    intro u
    rw [MulChar.one_apply (Units.isUnit _)]
    rcases units_cases u with h | h | h | h | h | h <;> rw [h]
    · exact map_one ψ
    · rw [show (2 : ZMod 9) = 4 * 4 * 8 by decide, map_mul, map_mul, h4, h8]; norm_num
    · exact h4
    · rw [show (5 : ZMod 9) = 4 * 8 by decide, map_mul, h4, h8]; norm_num
    · rw [show (7 : ZMod 9) = 4 * 4 by decide, map_mul, h4]; norm_num
    · exact h8
  have hdvd := conductor_dvd_level ψ
  have hmem : conductor ψ ∈ Nat.divisors 9 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  rw [show Nat.divisors 9 = {1, 3, 9} by decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h
  · exact absurd (eq_one_iff_conductor_eq_one.mpr h) hne
  · exfalso
    have hf := factorsThrough_conductor ψ
    rw [h] at hf
    exact CondCong.not_factorsThrough ψ (a := 4) (b := 1) (by norm_num) (by norm_num) (by decide)
      (by simpa using h4) hf
  · exact h

/-- For ψ of conductor 9 = its level, ψ* = ψ on ℕ. -/
theorem primitive_apply {ψ : DirichletCharacter ℂ 9} (hc : conductor ψ = 9) (m : ℕ) :
    ψ.primitiveCharacter m = ψ m := by
  by_cases hm : m.Coprime 9
  · have := primitiveCharacter_apply_of_isCoprime ψ (a := m)
      (Nat.isCoprime_iff_coprime.mpr hm)
    simpa using this
  · rw [MulChar.map_nonunit _ (by rw [ZMod.isUnit_iff_coprime, hc]; exact hm),
      MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])]

/-- **The wildly ramified prime 3:** χ(3) = χ̄(3) = 0 and (1 − x^f)^g = 1 − x. -/
theorem local_three {χ : DirichletCharacter ℂ 9} (x : ℂ) :
    χ (3 : ZMod 9) = 0 ∧ (1 - x ^ fK K 3) ^ gK K 3 = (1 - x) * (1 - χ 3 * x) *
      (1 - starRingEnd ℂ (χ 3) * x) := by
  have h3 : χ (3 : ZMod 9) = 0 := MulChar.map_nonunit _ (by
    rw [show (3 : ZMod 9) = ((3 : ℕ) : ZMod 9) by rfl, ZMod.isUnit_iff_coprime]; decide)
  refine ⟨h3, ?_⟩
  rw [(data_three (L := L)).1, (data_three (L := L)).2.1, h3]
  simp

/-- **ζ_K(s) = ζ(s) · L(s, χ) · L(s, χ̄)**, Re s > 1, χ primitive of conductor 9, χ³ = 1. -/
theorem zeta_K {s : ℂ} (hs : 1 < s.re) :
    ∃ χ : DirichletCharacter ℂ 9, χ ≠ 1 ∧ χ ^ 3 = 1 ∧ conductor χ = 9 ∧
      LSeries (fun m => (IdealCount.A (𝓞 K) m : ℂ)) s =
        riemannZeta s * LSeries (fun m => χ m) s *
          LSeries (fun m => starRingEnd ℂ (χ m)) s := by
  classical
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {9} ℚ L
  have hcard : (CycloSubEuler.perpNontriv 9 L (H (L := L))).card = 2 := by
    rw [CycloSubEuler.perpNontriv, Finset.card_erase_of_mem (CycloSubEuler.one_mem_perp 9 L _),
      (CycloCharCorr.card_perp 9 L (H (L := L))).1, index_H]
  obtain ⟨χ, hχ⟩ : (CycloSubEuler.perpNontriv 9 L (H (L := L))).Nonempty := by
    rw [← Finset.card_pos, hcard]; norm_num
  have heq := perpNontriv_eq hχ
  have hχ' := hχ
  rw [CycloSubEuler.perpNontriv, Finset.mem_erase] at hχ'
  obtain ⟨hne, hp⟩ := hχ'
  have hsq : χ ^ 2 ∈ CycloSubEuler.perpNontriv 9 L (H (L := L)) := by
    rw [heq]; simp
  have hc1 := conductor_eq_nine hχ
  have hc2 := conductor_eq_nine hsq
  have hsqχ : χ ^ 2 ≠ χ := by
    intro h; apply hne; rw [pow_two, mul_eq_left] at h; exact h
  refine ⟨χ, hne, cube_eq_one hp, hc1, ?_⟩
  rw [CompositeEuler.LSeries_eq_zeta_mul_prod_primitive 9 L (H (L := L)) hs,
    Finset.prod_coe_sort (CycloSubEuler.perpNontriv 9 L (H (L := L)))
      (fun ψ => LSeries (fun m => ψ.primitiveCharacter m) s), heq,
    Finset.prod_pair (Ne.symm hsqχ), mul_assoc]
  congr 2
  · congr 1; funext m; rw [primitive_apply hc1]
  · congr 1; funext m; rw [primitive_apply hc2, sq_eq_conj hp]

end Cyclo9Cubic

#print axioms Cyclo9Cubic.perpNontriv_eq
#print axioms Cyclo9Cubic.conductor_eq_nine
#print axioms Cyclo9Cubic.local_three
#print axioms Cyclo9Cubic.zeta_K
