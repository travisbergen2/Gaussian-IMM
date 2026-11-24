import Cyclo5Characters

/-!
# Cyclo5Galois — Galois characters of ℚ(ζ₅) = Dirichlet characters mod 5

* `galEquiv`: Gal(K/ℚ) ≃* (ZMod 5)ˣ (Mathlib's `autEquivPow`; σ ↦ a with σ(ζ) = ζᵃ).
* `galCharEquiv`: Dirichlet characters mod 5 ≃ homomorphisms Gal(K/ℚ) →* ℂˣ, by composing with it.
* `galChar_sigma_p`: for p ∤ 5 and σ_p the automorphism with σ_p(ζ) = ζᵖ, the Galois character
  of ψ takes the value ψ(p) at σ_p.
* `LSeries_A_eq_zeta_mul_prod_galois`: ζ_{ℚ(ζ₅)} = ζ · ∏ over the nontrivial characters of Gal(K/ℚ).
Not claimed: that σ_p is Mathlib's arithmetic Frobenius at p (true, not formalized here).
-/

open Polynomial IsCyclotomicExtension DirichletCharacter NumberField

namespace Cyclo5

variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K]

/-- Gal(ℚ(ζ₅)/ℚ) ≃* (ZMod 5)ˣ. -/
noncomputable def galEquiv : Gal(K/ℚ) ≃* (ZMod 5)ˣ :=
  autEquivPow K (cyclotomic.irreducible_rat (by norm_num : 0 < 5))

theorem galEquiv_spec (σ : Gal(K/ℚ)) :
    σ (zeta 5 ℚ K) = zeta 5 ℚ K ^ ((galEquiv K σ : ZMod 5).val) :=
  autEquivPow_spec K _ σ

/-- **Dirichlet characters mod 5 ≃ characters of the Galois group.** -/
noncomputable def galCharEquiv : DirichletCharacter ℂ 5 ≃ (Gal(K/ℚ) →* ℂˣ) :=
  MulChar.equivToUnitHom.trans (MulEquiv.monoidHomCongrLeftEquiv (galEquiv K).symm)

theorem galCharEquiv_apply (ψ : DirichletCharacter ℂ 5) (σ : Gal(K/ℚ)) :
    (galCharEquiv K ψ σ : ℂ) = ψ (galEquiv K σ) := by
  show (MulChar.equivToUnitHom ψ ((galEquiv K).symm.symm σ) : ℂ) = _
  rw [MulChar.coe_equivToUnitHom, MulEquiv.symm_symm]

theorem galCharEquiv_eq_one_iff (ψ : DirichletCharacter ℂ 5) : galCharEquiv K ψ = 1 ↔ ψ = 1 := by
  constructor
  · intro h
    apply MulChar.ext
    intro u
    have := congrArg (fun φ : Gal(K/ℚ) →* ℂˣ => (φ ((galEquiv K).symm u) : ℂ)) h
    simpa [galCharEquiv_apply] using this
  · rintro rfl
    ext σ
    simp [galCharEquiv_apply]

/-- σ_p: the automorphism with σ_p(ζ) = ζᵖ, for p ∤ 5. -/
noncomputable def sigma (p : ℕ) (hp : Nat.Coprime p 5) : Gal(K/ℚ) :=
  (galEquiv K).symm (ZMod.unitOfCoprime p hp)

theorem sigma_zeta (p : ℕ) (hp : Nat.Coprime p 5) :
    sigma K p hp (zeta 5 ℚ K) = zeta 5 ℚ K ^ p := by
  rw [galEquiv_spec, sigma, MulEquiv.apply_symm_apply, ZMod.coe_unitOfCoprime, ZMod.val_natCast]
  rw [← Nat.mod_add_div p 5, pow_add, pow_mul, (zeta_spec 5 ℚ K).pow_eq_one, one_pow, mul_one,
    Nat.mod_add_div]

/-- **The Galois character of ψ takes the value ψ(p) at σ_p.** -/
theorem galChar_sigma_p (ψ : DirichletCharacter ℂ 5) (p : ℕ) (hp : Nat.Coprime p 5) :
    (galCharEquiv K ψ (sigma K p hp) : ℂ) = ψ p := by
  rw [galCharEquiv_apply, sigma, MulEquiv.apply_symm_apply, ZMod.coe_unitOfCoprime]

/-- Nontrivial Galois characters ≃ nontrivial Dirichlet characters mod 5. -/
noncomputable def nontrivialGalEquiv :
    {ψ : DirichletCharacter ℂ 5 // ψ ≠ 1} ≃ {φ : Gal(K/ℚ) →* ℂˣ // φ ≠ 1} :=
  (galCharEquiv K).subtypeEquiv fun ψ => (galCharEquiv_eq_one_iff K ψ).not.symm

noncomputable instance : Fintype {φ : Gal(K/ℚ) →* ℂˣ // φ ≠ 1} :=
  Fintype.ofEquiv _ (nontrivialGalEquiv K)

theorem card_nontrivial_gal : Fintype.card {φ : Gal(K/ℚ) →* ℂˣ // φ ≠ 1} = 3 := by
  rw [← Fintype.card_congr (nontrivialGalEquiv K), ← Fintype.card_congr nontrivialEquiv,
    Fintype.card_fin]

/-- **ζ_{ℚ(ζ₅)} = ζ · ∏ over the nontrivial characters of Gal(ℚ(ζ₅)/ℚ)**, each read as a
Dirichlet character through `galCharEquiv`. -/
theorem LSeries_A_eq_zeta_mul_prod_galois {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (IdealCount.A (𝓞 K) n : ℂ)) s =
      riemannZeta s * ∏ φ : {φ : Gal(K/ℚ) →* ℂˣ // φ ≠ 1},
        LSeries (fun n => (galCharEquiv K).symm φ.1 n) s := by
  rw [LSeries_A_eq_zeta_mul_prod_nontrivial hs, ← (nontrivialGalEquiv K).prod_comp]
  refine congrArg (riemannZeta s * ·) (Finset.prod_congr rfl fun ψ _ => ?_)
  show _ = LSeries (fun n => (galCharEquiv K).symm (galCharEquiv K ψ.1) n) s
  rw [Equiv.symm_apply_apply]

end Cyclo5

#print axioms Cyclo5.galCharEquiv_eq_one_iff
#print axioms Cyclo5.galChar_sigma_p
#print axioms Cyclo5.card_nontrivial_gal
#print axioms Cyclo5.LSeries_A_eq_zeta_mul_prod_galois
