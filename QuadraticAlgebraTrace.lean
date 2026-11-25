import Mathlib

/-!
# QuadraticAlgebraTrace — Algebra.trace and Algebra.discr for `QuadraticAlgebra R a b`

Generic (imports only Mathlib). In `QuadraticAlgebra R a b` (ω² = a + bω):
* `algebraTrace_eq`: the module-theoretic trace `Algebra.trace R _ z` is
  `QuadraticAlgebra.trace z = 2·re z + b·im z` (left multiplication by z has matrix
  [[re, a·im], [im, re + b·im]] in the basis 1, ω);
* `discr_basis`: the discriminant of the basis 1, ω is `discr a b = b² + 4a`.
-/

open QuadraticAlgebra

namespace QuadTrace

variable {R : Type*} [CommRing R] (a b : R)

theorem algebraTrace_eq (z : QuadraticAlgebra R a b) :
    Algebra.trace R (QuadraticAlgebra R a b) z = QuadraticAlgebra.trace z := by
  rw [Algebra.trace_eq_matrix_trace (basis a b), Matrix.trace_fin_two, trace_def]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, basis_repr_apply, basis_apply_zero, mul_one]
  have h1 : basis a b 1 = (ω : QuadraticAlgebra R a b) := by ext <;> simp [basis]
  rw [h1]
  simp
  ring

theorem discr_basis :
    Algebra.discr R (basis a b) = QuadraticAlgebra.discr a b := by
  have h1 : basis a b 1 = (ω : QuadraticAlgebra R a b) := by ext <;> simp [basis]
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, basis_apply_zero, h1, one_mul,
    mul_one, algebraTrace_eq, trace_one, trace_omega, discr_def]
  have : (ω : QuadraticAlgebra R a b) * ω = algebraMap R (QuadraticAlgebra R a b) a + b • ω := by
    ext <;> simp
  rw [this, map_add, map_smul, trace_omega, trace_algebraMap]
  simp
  ring

end QuadTrace

#print axioms QuadTrace.algebraTrace_eq
#print axioms QuadTrace.discr_basis
