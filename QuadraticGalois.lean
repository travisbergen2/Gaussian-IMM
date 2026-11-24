import Mathlib

/-!
# QuadraticGalois — every degree-2 extension of ℚ is Galois

Small, self-contained. No project imports.
Route: finrank 2 ⇒ `Algebra.IsQuadraticExtension ℚ K` (a vector space over a field is free);
ℚ has characteristic 0, so K/ℚ is separable; Mathlib's `IsQuadraticExtension.isGalois` finishes
(that instance is the normality argument: the second root of the minimal polynomial is
trace − first root).
-/

theorem isQuadraticExtension_of_finrank_eq_two {K : Type*} [Field K] [Algebra ℚ K]
    (hK : Module.finrank ℚ K = 2) : Algebra.IsQuadraticExtension ℚ K :=
  { finrank_eq_two' := hK }

/-- **Degree two implies Galois** over ℚ. -/
theorem isGalois_of_finrank_eq_two {K : Type*} [Field K] [Algebra ℚ K]
    (hK : Module.finrank ℚ K = 2) : IsGalois ℚ K := by
  have := isQuadraticExtension_of_finrank_eq_two hK
  infer_instance

#print axioms isGalois_of_finrank_eq_two
