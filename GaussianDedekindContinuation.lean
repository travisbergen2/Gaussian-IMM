import GaussianDedekindBridge

/-!
# GaussianDedekindContinuation — milestones 1–2

Defines the continuation ζ_{ℚ(i)}^cont(s) := ζ(s) · L(s, χ₄), using Mathlib's continued
`riemannZeta` and `DirichletCharacter.LFunction`, and proves it agrees with Mathlib's
`NumberField.dedekindZeta Qi` on Re s > 1. Also: holomorphic on ℂ \ {1}.

Imports the frozen layer + bridge; modifies neither. No zero statements, no RH/GRH content.
-/

open NumberField Complex

/-- χ₄ as a complex Dirichlet character mod 4. -/
noncomputable def chi4C : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

theorem chi4C_apply (n : ℕ) : chi4C (n : ZMod 4) = GaussianLSeries.chi4 n := by
  simp [chi4C, MulChar.ringHomComp_apply, GaussianLSeries.chi4]

theorem chi4C_ne_one : chi4C ≠ 1 := by
  intro h
  have hu : IsUnit ((3 : ℕ) : ZMod 4) := by
    rw [ZMod.isUnit_iff_coprime]; norm_num
  have h3 := congrArg (fun χ : DirichletCharacter ℂ 4 => χ ((3 : ℕ) : ZMod 4)) h
  simp only [MulChar.one_apply hu] at h3
  rw [chi4C_apply] at h3
  simp [GaussianLSeries.chi4] at h3
  norm_num at h3

/-- **Milestone 1: the continuation.** -/
noncomputable def dedekindZetaCont (s : ℂ) : ℂ := riemannZeta s * DirichletCharacter.LFunction chi4C s

/-- The continued L(s, χ₄) agrees with the frozen `LSeries chi4` on Re s > 1. -/
theorem LFunction_chi4_eq {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction chi4C s = LSeries GaussianLSeries.chi4 s := by
  rw [DirichletCharacter.LFunction_eq_LSeries chi4C hs]
  congr 1

/-- **Milestone 2: agreement with Mathlib's Dedekind zeta on Re s > 1.** -/
theorem dedekindZetaCont_eq {s : ℂ} (hs : 1 < s.re) :
    dedekindZetaCont s = dedekindZeta Qi s := by
  rw [dedekindZetaCont, LFunction_chi4_eq hs, dedekindZeta_Qi hs]

/-- L(s, χ₄) is entire (χ₄ is non-trivial). -/
theorem LFunction_chi4_differentiable : Differentiable ℂ (DirichletCharacter.LFunction chi4C) :=
  DirichletCharacter.differentiable_LFunction chi4C_ne_one

/-- The continuation is holomorphic at every s ≠ 1 (the pole of ζ). -/
theorem dedekindZetaCont_differentiableAt {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ dedekindZetaCont s :=
  (differentiableAt_riemannZeta hs).mul (LFunction_chi4_differentiable s)

#print axioms dedekindZetaCont_eq
#print axioms LFunction_chi4_differentiable
#print axioms dedekindZetaCont_differentiableAt
#print axioms chi4C_ne_one
#print axioms LFunction_chi4_eq
