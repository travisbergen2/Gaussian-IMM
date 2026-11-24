import GaussianDedekindZeros

/-!
# GaussianDedekindRH — milestone 4: a conditional corollary

CONDITIONAL. Nothing here proves RH or GRH. Both appear as explicit hypotheses in the
theorem signature. The result is the composition:
  (zero-line for ζ) ∧ (zero-line for L(s, χ₄)) ⇒ every `NontrivialZero` of ζ_{ℚ(i)} has Re s = ½.
-/

open DirichletCharacter

/-- Zero-line hypothesis for ζ, using the project's trivial-zero predicate. -/
def ZetaZeroLine : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → s ≠ 1 → ¬ ZetaTrivial s → s.re = 1 / 2

/-- Zero-line hypothesis for L(s, χ₄), using the project's trivial-zero predicate.
Hand-written: Mathlib (at the audited commit) has no named GRH definition. -/
def Chi4ZeroLine : Prop :=
  ∀ s : ℂ, LFunction chi4C s = 0 → ¬ LTrivial s → s.re = 1 / 2

/-- `ZetaZeroLine` is *exactly* Mathlib's `RiemannHypothesis` (same trivial set, same pole
exclusion; only the argument order differs). So the ζ-hypothesis is not a paraphrase. -/
theorem zetaZeroLine_iff_RH : ZetaZeroLine ↔ RiemannHypothesis := by
  constructor
  · intro h s hz htriv hs1; exact h s hz hs1 htriv
  · intro h s hz hs1 htriv; exact h s hz htriv hs1

/-- **Conditional corollary.** Under both zero-line hypotheses, every nontrivial zero of the
continued Dedekind zeta of ℚ(i) lies on Re s = ½. -/
theorem nontrivialZero_re_half (hζ : ZetaZeroLine) (hL : Chi4ZeroLine)
    {s : ℂ} (hs : NontrivialZero s) : s.re = 1 / 2 := by
  obtain ⟨hs1, hzt, hlt, hz | hz⟩ := (nontrivialZero_iff s).mp hs
  · exact hζ s hz hs1 hzt
  · exact hL s hz hlt

/-- The same corollary with Mathlib's own `RiemannHypothesis` as the ζ-hypothesis. -/
theorem nontrivialZero_re_half_of_RH (hRH : RiemannHypothesis) (hL : Chi4ZeroLine)
    {s : ℂ} (hs : NontrivialZero s) : s.re = 1 / 2 :=
  nontrivialZero_re_half (zetaZeroLine_iff_RH.mpr hRH) hL hs

#print axioms zetaZeroLine_iff_RH
#print axioms nontrivialZero_re_half
#print axioms nontrivialZero_re_half_of_RH
