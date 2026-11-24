import GaloisLocalEulerFactor
import DedekindSummable
import QuadraticEulerProduct

/-!
# AbelianEulerProduct — Σ A_K(n) n⁻ˢ = ζ(s) · ∏ⱼ L(s, χⱼ) for Galois K of any degree

Hypotheses: K/ℚ Galois, and a finite family of Dirichlet characters χⱼ whose local factors match
the splitting data at every prime p:

    (1 − xᶠ)^g = (1 − x) · ∏ⱼ (1 − χⱼ(p) x)      for all x,

with g = #primes over p, f = residue degree. The (1 − x) factor is ζ; it keeps the trivial
character separate, so no normalization issue arises at ramified primes (χⱼ may vanish there).

Route: convergence from `DedekindSum` (degree- and character-free), multiplicativity
(`IdealCount.A_mul`), Mathlib's Euler product, the local factor from `GaloisLocalEulerFactor`,
and comparison with the Euler products of ζ and each L(χⱼ).
-/

open ArithmeticFunction LSeries Complex IdealCount NumberField GaloisEuler

namespace GaloisEuler

variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]

theorem summable_norm_term {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n => ‖term (fun n => (A (𝓞 K) n : ℂ)) s n‖) :=
  (DedekindSum.LSeriesSummable_idealCount K hs).norm

theorem local_tsum {s : ℂ} (hs : 1 < s.re) (p : Nat.Primes) :
    ∑' e, QuadEuler.T K s ((p : ℕ) ^ e) = ((1 - ((p : ℂ) ^ (-s)) ^ fK K p) ^ gK K p)⁻¹ := by
  have := Fact.mk p.prop
  rw [← (localFactor_hasSum (K := K) (p := p)
    (QuadEuler.norm_prime_cpow_lt_one (by linarith) p.prop)).tsum_eq]
  congr 1; funext e
  rw [QuadEuler.T_apply, term_of_ne_zero (pow_ne_zero _ p.prop.ne_zero), div_eq_mul_inv, ← cpow_neg,
    QuadEuler.prime_pow_cpow]

/-- **Abelian Euler product.** -/
theorem LSeries_A_eq_zeta_mul_prod {ι : Type*} [Fintype ι] {N : ℕ}
    (χ : ι → DirichletCharacter ℂ N)
    (hloc : ∀ p : ℕ, p.Prime → ∀ x : ℂ,
      (1 - x ^ fK K p) ^ gK K p = (1 - x) * ∏ j, (1 - χ j (p : ZMod N) * x))
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

#print axioms GaloisEuler.LSeries_A_eq_zeta_mul_prod
