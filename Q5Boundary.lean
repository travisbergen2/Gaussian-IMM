import Q5EulerProduct
import Q5NotPrincipal

/-!
# Q5Boundary — the non-PID factorization as one statement

The generic theorem `quad_LSeries_A_eq_zeta_mul_L` has exactly two hypotheses: [K : ℚ] = 2 and
χ(p) = c_p at every prime. No principal-ideal or class-number hypothesis appears at its interface.
This file records a field where both hold and the ring of integers is not a PID.
-/

open NumberField

/-- **A non-PID quadratic field satisfying the Euler-product factorization.** -/
theorem Q5.nonPID_factorization :
    ¬ IsPrincipalIdealRing (𝓞 Q5.K5) ∧
      ∀ s : ℂ, 1 < s.re →
        LSeries (fun n => (IdealCount.A (𝓞 Q5.K5) n : ℂ)) s
          = riemannZeta s * LSeries (fun n => Q5.chi20C n) s :=
  ⟨Q5.not_isPrincipalIdealRing, fun _ hs => Q5.LSeries_A_eq_zeta_mul_L hs⟩

#print axioms Q5.nonPID_factorization
