import AbelianEulerProduct

/-!
# AbelianEulerProductLevels — the abelian Euler product with characters of different levels

Same statement and proof as `GaloisEuler.LSeries_A_eq_zeta_mul_prod`, but the characters χⱼ may
have different levels Nⱼ. This is what primitive characters need: each has its own conductor,
so its Euler factor at p is nonzero exactly when p ∤ conductor. `AbelianEulerProduct.lean` is
left unchanged.
-/

open ArithmeticFunction LSeries Complex IdealCount NumberField GaloisEuler

namespace GaloisEuler

variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]

/-- **Abelian Euler product, characters of varying levels** (e.g. primitive characters). -/
theorem LSeries_A_eq_zeta_mul_prod_levels {ι : Type*} [Fintype ι] {N : ι → ℕ}
    (χ : (j : ι) → DirichletCharacter ℂ (N j))
    (hloc : ∀ p : ℕ, p.Prime → ∀ x : ℂ,
      (1 - x ^ fK K p) ^ gK K p = (1 - x) * ∏ j, (1 - χ j (p : ZMod (N j)) * x))
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (A (𝓞 K) n : ℂ)) s =
      riemannZeta s * ∏ j, LSeries (fun n => χ j n) s := by
  classical
  have halg := (QuadEuler.T_mult (K := K) s).eulerProduct_hasProd (summable_norm_term hs)
  simp only [local_tsum hs] at halg
  have hL : HasProd (fun p : Nat.Primes => ∏ j, (1 - χ j (p : ℕ) * (p : ℂ) ^ (-s))⁻¹)
      (∏ j, LSeries (fun n => χ j n) s) :=
    hasProd_prod fun j _ => DirichletCharacter.LSeries_eulerProduct_hasProd (χ j) hs
  have hana := (riemannZeta_eulerProduct_hasProd hs).mul hL
  have hfac : (fun p : Nat.Primes => ((1 - ((p : ℂ) ^ (-s)) ^ fK K p) ^ gK K p)⁻¹)
      = (fun p : Nat.Primes =>
          (1 - (p : ℂ) ^ (-s))⁻¹ * ∏ j, (1 - χ j (p : ℕ) * (p : ℂ) ^ (-s))⁻¹) := by
    funext p
    rw [hloc p p.prop, mul_inv, Finset.prod_inv_distrib]
  rw [hfac] at halg
  exact halg.unique hana

end GaloisEuler

#print axioms GaloisEuler.LSeries_A_eq_zeta_mul_prod_levels
