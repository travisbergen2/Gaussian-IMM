import Mathlib

/-!
# Q5Field — the field ℚ(√−5), its ring of integers ℤ[√−5], and a monogenic generator

No project imports. K5 := `QuadraticAlgebra ℚ (−5) 0`. Outputs used later:
* `K5` is a number field of degree 2;
* `θ5 : 𝓞 K5` (the image of ω = √−5) generates 𝓞 K5 over ℤ, so `exponent θ5 = 1`;
* `minpoly ℤ θ5 = X² + 5`.
These are exactly the inputs of Mathlib's Kummer–Dedekind theorem for number fields.
-/

open QuadraticAlgebra NumberField Polynomial

namespace Q5

theorem discr_eq : discr (-5 : ℤ) 0 = 4 * (-5) := by rw [discr_def]; norm_num

theorem discr_fundamental : (discr (-5 : ℤ) 0).IsFundamentalDiscr := by
  rw [discr_eq, Int.isFundamentalDiscr_four_mul]
  refine ⟨?_, by decide⟩
  rw [← Int.squarefree_natAbs]
  exact (Nat.prime_five).squarefree

/-- ℚ(√−5), with the cast parameters the Mathlib API uses. -/
abbrev K5 := QuadraticAlgebra ℚ ((-5 : ℤ) : ℚ) ((0 : ℤ) : ℚ)

/-- ℤ[√−5]. -/
abbrev Z5 := QuadraticAlgebra ℤ (-5) 0

instance : Fact (¬ IsSquare (discr ((-5 : ℤ) : ℚ) ((0 : ℤ) : ℚ))) := by
  refine ⟨fun ⟨r, hr⟩ => ?_⟩
  rw [discr_def] at hr
  push_cast at hr
  nlinarith [sq_nonneg r]

instance : NumberField K5 where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance

theorem finrank_K5 : Module.finrank ℚ K5 = 2 := QuadraticAlgebra.finrank_eq_two _ _

/-- ℤ[√−5] ≃ₐ[ℤ] 𝓞 ℚ(√−5). -/
noncomputable def e5 : Z5 ≃ₐ[ℤ] 𝓞 K5 := Int.algEquivIntegralClosure discr_fundamental

/-- The generator √−5 of 𝓞 K5. -/
noncomputable def θ5 : 𝓞 K5 := e5 ω

theorem adjoin_θ5 : Algebra.adjoin ℤ {θ5} = ⊤ := by
  rw [θ5, show e5 ω = (e5 : Z5 →ₐ[ℤ] 𝓞 K5) ω from rfl,
    ← AlgHom.map_adjoin_singleton (e5 : Z5 →ₐ[ℤ] 𝓞 K5), adjoin_omega_eq_top, Algebra.map_top]
  exact eq_top_iff.mpr fun x _ => ⟨e5.symm x, by simp⟩

theorem exponent_θ5 : RingOfIntegers.exponent θ5 = 1 :=
  RingOfIntegers.exponent_eq_one_iff.mpr adjoin_θ5

theorem aeval_omega : aeval (ω : Z5) (X ^ 2 + C 5 : ℤ[X]) = 0 := by
  simp only [map_add, map_pow, aeval_X, map_ofNat]
  ext <;> simp [sq]

theorem aeval_θ5 : aeval θ5 (X ^ 2 + C 5 : ℤ[X]) = 0 := by
  rw [θ5, show e5 ω = (e5 : Z5 →ₐ[ℤ] 𝓞 K5) ω from rfl, aeval_algHom_apply, aeval_omega, map_zero]

theorem finrank_O : Module.finrank ℤ (𝓞 K5) = 2 :=
  e5.toLinearEquiv.finrank_eq.symm.trans (QuadraticAlgebra.finrank_eq_two _ _)

theorem minpoly_θ5 : minpoly ℤ θ5 = X ^ 2 + C 5 := by
  have hint : IsIntegral ℤ θ5 := RingOfIntegers.isIntegral θ5
  have hmon : (X ^ 2 + C 5 : ℤ[X]).Monic := by monicity!
  have hdeg : (X ^ 2 + C 5 : ℤ[X]).natDegree = 2 := by compute_degree!
  have hdvd := minpoly.isIntegrallyClosed_dvd hint aeval_θ5
  have hmd : (minpoly ℤ θ5).natDegree = 2 := by
    rw [← PowerBasis.ofAdjoinEqTop'_dim hint adjoin_θ5, ← PowerBasis.finrank, finrank_O]
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmon hdvd
    (by rw [hdeg, hmd])).symm

end Q5

#print axioms Q5.minpoly_θ5
