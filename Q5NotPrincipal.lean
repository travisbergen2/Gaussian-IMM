import Q5Splitting

/-!
# Q5NotPrincipal — 𝓞 ℚ(√−5) is not a principal ideal domain

The prime above 2 has norm 2, while N(a + b√−5) = a² + 5b² never equals 2.
So the ℚ(√−5) Euler product in `Q5EulerProduct` is a genuine class-number > 1 instance.
-/

open Polynomial NumberField Ideal QuadEuler QuadraticAlgebra

namespace Q5

theorem algebraNorm_eq (y : Z5) : Algebra.norm ℤ y = y.norm := by
  rw [Algebra.norm_apply, ← det_toLinearMap_eq_norm]
  congr 1

theorem algebraNorm_e5 (y : Z5) : Algebra.norm ℤ (e5 y) = y.re * y.re + 5 * y.im * y.im := by
  rw [Algebra.norm_eq_of_algEquiv, algebraNorm_eq, norm_def]; ring

theorem norm_ne_two (a b : ℤ) : a * a + 5 * b * b ≠ 2 := by
  intro h
  have hb1 : -1 < b ∧ b < 1 := by constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]
  have hb : b = 0 := by omega
  subst hb
  have ha : -2 < a ∧ a < 2 := by constructor <;> nlinarith
  obtain ⟨h1, h2⟩ := ha
  interval_cases a <;> omega

theorem fP_two : fP K5 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ := exists_prime_over 2
  have hne := (ramified_of_sq 1 two_ramified).2
  rw [fP_eq_natDegree 2 P] at hne ⊢
  rcases natDegree_factor (primesOverSpanEquivMonicFactorsMod (not_dvd_exponent 2) P).2 with h | h
  · exact h
  · exact absurd h hne

/-- **The prime of ℚ(√−5) above 2 is not principal.** -/
theorem prime_over_two_not_principal (P : Ideal (𝓞 K5))
    (hP : P ∈ (span {((2 : ℕ) : ℤ)}).primesOver (𝓞 K5)) : ¬ P.IsPrincipal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨x, rfl⟩
  have hN := QuadBound.absNorm_eq hP
  rw [show (span {((2 : ℕ) : ℤ)}).inertiaDegIn (𝓞 K5) = fP K5 2 from rfl, fP_two, pow_one,
    show (𝓞 K5 ∙ x) = span {x} from rfl, absNorm_span_singleton,
    ← e5.apply_symm_apply x, algebraNorm_e5] at hN
  set y := e5.symm x
  have hnn : 0 ≤ y.re * y.re + 5 * y.im * y.im := by nlinarith [mul_self_nonneg y.re, mul_self_nonneg y.im]
  have hz : y.re * y.re + 5 * y.im * y.im = 2 := by
    rw [← Int.natAbs_of_nonneg hnn, hN]; rfl
  exact norm_ne_two _ _ hz

theorem not_isPrincipalIdealRing : ¬ IsPrincipalIdealRing (𝓞 K5) := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ := exists_prime_over 2
  exact prime_over_two_not_principal P.1 P.2 (IsPrincipalIdealRing.principal P.1)

end Q5

#print axioms Q5.not_isPrincipalIdealRing
