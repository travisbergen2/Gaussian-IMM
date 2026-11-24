import QuadraticEulerProduct
import QuadraticGalois

/-!
# QuadraticFactorizationNoGalois — the quadratic theorems with only [K : ℚ] = 2

`IsGalois ℚ K` is no longer an assumption: it is derived by `isGalois_of_finrank_eq_two`.
The remaining hypotheses are degree 2 and (for the factorization) that χ matches the splitting.
-/

open NumberField IdealCount QuadEuler
open scoped ArithmeticFunction.sigma

variable {K : Type*} [Field K] [NumberField K]

/-- A_K(n) ≤ d(n) for every quadratic number field. -/
theorem quad_A_le_sigma0 (hK : Module.finrank ℚ K = 2) {n : ℕ} (hn : n ≠ 0) :
    A (𝓞 K) n ≤ σ 0 n := by
  have := isGalois_of_finrank_eq_two hK
  exact QuadBound.A_le_sigma0 hK hn

/-- Local Euler factor for every quadratic number field. -/
theorem quad_localFactor_hasSum (hK : Module.finrank ℚ K = 2) {p : ℕ} [Fact p.Prime] {x : ℂ}
    (hx : ‖x‖ < 1) :
    HasSum (fun k : ℕ => (A (𝓞 K) (p ^ k) : ℂ) * x ^ k)
      ((1 - x)⁻¹ * (1 - splitChar K p * x)⁻¹) := by
  have := isGalois_of_finrank_eq_two hK
  exact localFactor_hasSum hK hx

/-- **Quadratic Dedekind factorization**, hypotheses: [K : ℚ] = 2 and χ(p) = c_p for all primes p. -/
theorem quad_LSeries_A_eq_zeta_mul_L (hK : Module.finrank ℚ K = 2) {N : ℕ}
    (χ : DirichletCharacter ℂ N) (hχ : ∀ p : ℕ, p.Prime → χ (p : ZMod N) = splitChar K p)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (A (𝓞 K) n : ℂ)) s = riemannZeta s * LSeries (fun n => χ n) s := by
  have := isGalois_of_finrank_eq_two hK
  exact LSeries_A_eq_zeta_mul_L hK χ hχ hs

#print axioms quad_A_le_sigma0
#print axioms quad_localFactor_hasSum
#print axioms quad_LSeries_A_eq_zeta_mul_L
