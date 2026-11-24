import GaussianDedekindContinuation

/-!
# GaussianDedekindZeros — milestone 3, and the pole at s = 1

Imports the continuation; modifies nothing frozen. No RH/GRH hypotheses are used here.
-/

open Complex Filter Topology DirichletCharacter

/-! ## The genuine pole at s = 1 -/

/-- L(1, χ₄) ≠ 0 (Mathlib's non-vanishing at 1 for non-trivial characters). -/
theorem LFunction_chi4_one_ne_zero : LFunction chi4C 1 ≠ 0 :=
  LFunction_apply_one_ne_zero chi4C_ne_one

/-- **s = 1 is a simple pole:** (s − 1)·ζ_{ℚ(i)}(s) → L(1, χ₄) ≠ 0 as s → 1. -/
theorem dedekindZetaCont_residue :
    Tendsto (fun s => (s - 1) * dedekindZetaCont s) (𝓝[≠] 1) (𝓝 (LFunction chi4C 1)) := by
  have hL : Tendsto (LFunction chi4C) (𝓝[≠] 1) (𝓝 (LFunction chi4C 1)) :=
    (LFunction_chi4_differentiable 1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have := riemannZeta_residue_one.mul hL
  rw [one_mul] at this
  refine this.congr fun s => ?_
  simp only [dedekindZetaCont]; ring

/-! ## Milestone 3a: the unrestricted product-zero equivalence -/

/-- Pointwise zero-product property. Holds at every s, including s = 1; it is a statement
about the function value, not about the meromorphic continuation at its pole. -/
theorem dedekindZetaCont_zero_iff (s : ℂ) :
    dedekindZetaCont s = 0 ↔ riemannZeta s = 0 ∨ LFunction chi4C s = 0 :=
  mul_eq_zero

/-! ## Milestone 3b: the two trivial-zero sets -/

/-- χ₄ is odd: χ₄(−1) = −1. -/
theorem chi4C_odd : chi4C.Odd := by
  show chi4C (-1) = -1
  rw [show (-1 : ZMod 4) = ((3 : ℕ) : ZMod 4) by decide, chi4C_apply]
  simp [GaussianLSeries.chi4]

/-- Trivial zeros of ζ: the negative even integers. -/
def ZetaTrivial (s : ℂ) : Prop := ∃ n : ℕ, s = -2 * (n + 1)

/-- Trivial zeros of L(s, χ₄): the negative odd integers. -/
def LTrivial (s : ℂ) : Prop := ∃ n : ℕ, s = -(2 * n) - 1

theorem zeta_trivial_is_zero {s : ℂ} (h : ZetaTrivial s) : riemannZeta s = 0 := by
  obtain ⟨n, rfl⟩ := h; exact riemannZeta_neg_two_mul_nat_add_one n

theorem L_trivial_is_zero {s : ℂ} (h : LTrivial s) : LFunction chi4C s = 0 := by
  obtain ⟨n, rfl⟩ := h; exact chi4C_odd.LFunction_neg_two_mul_nat_sub_one n

/-- Every point of either trivial set is a zero of the continuation. -/
theorem trivial_is_zero {s : ℂ} (h : ZetaTrivial s ∨ LTrivial s) : dedekindZetaCont s = 0 := by
  rw [dedekindZetaCont_zero_iff]
  exact h.imp zeta_trivial_is_zero L_trivial_is_zero

/-- The two trivial sets are disjoint (even vs odd negative integers). -/
theorem trivial_disjoint {s : ℂ} (h1 : ZetaTrivial s) (h2 : LTrivial s) : False := by
  obtain ⟨n, rfl⟩ := h1
  obtain ⟨m, hm⟩ := h2
  have := congrArg Complex.re hm
  simp at this
  have h' : (2 * (n : ℤ) + 2 : ℤ) = 2 * m + 1 := by exact_mod_cast (by linarith : (2 * (n:ℝ) + 2) = 2 * m + 1)
  omega

/-! ## Milestone 3c: nontrivial zeros of the continuation -/

/-- A nontrivial zero of ζ_{ℚ(i)}: a zero, away from the pole, outside both trivial sets. -/
def NontrivialZero (s : ℂ) : Prop :=
  dedekindZetaCont s = 0 ∧ s ≠ 1 ∧ ¬ ZetaTrivial s ∧ ¬ LTrivial s

/-- A nontrivial zero of ζ_{ℚ(i)} is a nontrivial zero of ζ or a nontrivial zero of L(s, χ₄),
with "nontrivial" in each case meaning outside *both* trivial sets. -/
theorem nontrivialZero_iff (s : ℂ) :
    NontrivialZero s ↔ s ≠ 1 ∧ ¬ ZetaTrivial s ∧ ¬ LTrivial s ∧
      (riemannZeta s = 0 ∨ LFunction chi4C s = 0) := by
  unfold NontrivialZero
  rw [dedekindZetaCont_zero_iff]
  tauto

#print axioms dedekindZetaCont_residue
#print axioms dedekindZetaCont_zero_iff
#print axioms chi4C_odd
#print axioms trivial_is_zero
#print axioms trivial_disjoint
#print axioms nontrivialZero_iff
#print axioms LFunction_chi4_one_ne_zero
