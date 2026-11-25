import QuadraticKroneckerWeber
import DedekindZetaIsomorphism
import CompositeCyclotomicEulerProduct
import CyclotomicCharacterCorrespondence

/-!
# QuadraticZeta — ζ_K = ζ · L(χ*) for every quadratic field K

K a number field with [K : ℚ] = 2. From `QuadKW.quadratic_kronecker_weber`, K ≅ ℚ(ζ_N)^H with
[G : H] = 2; `IdealCountIso.LSeries_eq_of_equiv` transfers ζ_K; the composite-conductor theorem
factors ζ of ℚ(ζ_N)^H; |H^⊥| = [G : H] = 2 (`CycloCharCorr.card_perp`), so H^⊥ = {1, χ}.
* `quadratic_zeta`: there are N ≠ 0 and a Dirichlet character χ mod N with χ ≠ 1, χ² = 1 and
  Σ A_K(m) m⁻ˢ = ζ(s) · L(s, χ*) for Re s > 1.
Not proved here: that χ* is the Kronecker symbol (D/·) of the discriminant D of K.
-/

open NumberField IntermediateField

namespace QuadZeta

/-- For index-2 H in a cyclotomic Galois group: H^⊥ = {1, χ} with χ² = 1. -/
theorem perp_two {N : ℕ} [NeZero N] {L : Type*} [Field L] [NumberField L]
    [IsCyclotomicExtension {N} ℚ L] (H : Subgroup Gal(L/ℚ)) [H.Normal] (hH : H.index = 2) :
    ∃ χ : DirichletCharacter ℂ N, χ ≠ 1 ∧ χ ^ 2 = 1 ∧ CycloSubEuler.perpNontriv N L H = {χ} := by
  classical
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {N} ℚ L
  have hcard : (CycloSubEuler.perpNontriv N L H).card = 1 := by
    rw [CycloSubEuler.perpNontriv, Finset.card_erase_of_mem (CycloSubEuler.one_mem_perp N L H),
      (CycloCharCorr.card_perp N L H).1, hH]
  obtain ⟨χ, hχ⟩ := Finset.card_eq_one.mp hcard
  have hmem : χ ∈ CycloSubEuler.perpNontriv N L H := by rw [hχ]; exact Finset.mem_singleton_self χ
  rw [CycloSubEuler.perpNontriv, Finset.mem_erase] at hmem
  obtain ⟨hne, hp⟩ := hmem
  refine ⟨χ, hne, ?_, hχ⟩
  have hsq : χ ^ 2 ∈ CycloSubEuler.perp N L H := by
    rw [CycloSubEuler.mem_perp_iff] at hp ⊢
    intro u hu
    rw [pow_two, MulChar.mul_apply, hp u hu, mul_one]
  by_contra h1
  have : χ ^ 2 ∈ CycloSubEuler.perpNontriv N L H :=
    Finset.mem_erase.mpr ⟨h1, hsq⟩
  rw [hχ, Finset.mem_singleton, pow_two] at this
  exact hne (by simpa using congrArg (· * χ⁻¹) this)

/-- **Every quadratic field: ζ_K(s) = ζ(s) · L(s, χ*)** with χ a quadratic Dirichlet character. -/
theorem quadratic_zeta {K : Type*} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2) :
    ∃ N : ℕ, ∃ _ : NeZero N, ∃ χ : DirichletCharacter ℂ N, χ ≠ 1 ∧ χ ^ 2 = 1 ∧
      ∀ s : ℂ, 1 < s.re →
        LSeries (fun m => (IdealCount.A (𝓞 K) m : ℂ)) s =
          riemannZeta s * LSeries (fun m => χ.primitiveCharacter m) s := by
  obtain ⟨N, hN0, hkw⟩ := QuadKW.quadratic_kronecker_weber hK
  have : NeZero N := ⟨hN0⟩
  have : NeZero (N : ℚ) := ⟨by exact_mod_cast hN0⟩
  let L := CyclotomicField N ℚ
  have := QuadKW.cyclotomicField_isCyclotomic N
  have : NumberField L := inferInstance
  obtain ⟨H, hH, ⟨e⟩⟩ := hkw L
  have : H.Normal := CycloSub.normal N H
  obtain ⟨χ, hne, hsq, hχ⟩ := perp_two (N := N) H hH
  refine ⟨N, ⟨hN0⟩, χ, hne, hsq, fun s hs => ?_⟩
  rw [IdealCountIso.LSeries_eq_of_equiv e.toRingEquiv s,
    CompositeEuler.LSeries_eq_zeta_mul_prod_primitive N L H hs,
    Finset.prod_coe_sort (CycloSubEuler.perpNontriv N L H)
      (fun χ => LSeries (fun m => χ.primitiveCharacter m) s), hχ, Finset.prod_singleton]

end QuadZeta

#print axioms QuadZeta.perp_two
#print axioms QuadZeta.quadratic_zeta
