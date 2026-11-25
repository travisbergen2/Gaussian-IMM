import CompositeCyclotomicEulerProduct
import CyclotomicCharacterCorrespondence

/-!
# GaloisCharacterEulerProduct — ζ_K as a product over the characters of Gal(K/ℚ)

K = ℚ(ζₙ)^H. For Re s > 1:
  Σ A_K(m) m⁻ˢ = ∏_{ρ : Gal(K/ℚ) → ℂˣ} L(s, χ_ρ*),
where χ_ρ ∈ H^⊥ is the Dirichlet character matched to ρ by `CycloCharCorr.perpEquivGal`
(ρ(σ|_K) = χ_ρ(a_σ)) and χ* is its primitive character. The trivial ρ contributes
L(s, 1*) = ζ(s) (`LSeries_primitive_one`). Each Galois character appears exactly once.
-/

open NumberField

namespace GaloisCharEuler

variable (n : ℕ) [NeZero n] (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {n} ℚ L]
  [IsGalois ℚ L] (H : Subgroup Gal(L/ℚ)) [H.Normal]

local notation "K" => IntermediateField.fixedField H

include n in
/-- Gal(K/ℚ) has finitely many characters (so the product below is a finite product, for any
`Fintype` instance, e.g. `Fintype.ofFinite`). -/
theorem finite_galChar : Finite (Gal(K/ℚ) →* ℂˣ) :=
  Finite.of_equiv _ (CycloCharCorr.perpEquivGal n L H)

/-- L(s, 1*) = ζ(s) for the trivial character of any level. -/
theorem LSeries_primitive_one {N : ℕ} [NeZero N] {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun m => (1 : DirichletCharacter ℂ N).primitiveCharacter m) s = riemannZeta s := by
  have key : ∀ {M : ℕ} (ψ : DirichletCharacter ℂ M), M = 1 → ψ = 1 →
      LSeries (fun m => ψ m) s = riemannZeta s := by
    rintro M ψ rfl rfl
    rw [DirichletCharacter.LSeries_modOne_eq, LSeries_one_eq_riemannZeta hs]
  exact key _ DirichletCharacter.conductor_one DirichletCharacter.primitiveCharacter_one

/-- **ζ_K = ∏ over the characters ρ of Gal(K/ℚ) of L(s, χ_ρ*)**, Re s > 1. -/
theorem LSeries_eq_prod_galChar [Fintype (Gal(K/ℚ) →* ℂˣ)] {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun m => (IdealCount.A (𝓞 K) m : ℂ)) s =
      ∏ ρ : Gal(K/ℚ) →* ℂˣ,
        LSeries (fun m => ((CycloCharCorr.perpEquivGal n L H).symm ρ).1.primitiveCharacter m) s := by
  classical
  set f : DirichletCharacter ℂ n → ℂ := fun χ => LSeries (fun m => χ.primitiveCharacter m) s
  rw [Equiv.prod_comp (CycloCharCorr.perpEquivGal n L H).symm (fun χ => f χ.1),
    Finset.prod_coe_sort (CycloSubEuler.perp n L H) f,
    ← Finset.insert_erase (CycloSubEuler.one_mem_perp n L H),
    Finset.prod_insert (Finset.notMem_erase _ _),
    CompositeEuler.LSeries_eq_zeta_mul_prod_primitive n L H hs]
  simp only [f]
  rw [LSeries_primitive_one hs, CycloSubEuler.perpNontriv,
    ← Finset.prod_coe_sort ((CycloSubEuler.perp n L H).erase 1)]

end GaloisCharEuler

#print axioms GaloisCharEuler.finite_galChar
#print axioms GaloisCharEuler.LSeries_primitive_one
#print axioms GaloisCharEuler.LSeries_eq_prod_galChar
