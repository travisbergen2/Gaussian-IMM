import GaussianDedekindRH

/-!
# GaussianChi4GRHForm — the left half-plane zeros of L(s, χ₄), and the GRH form of `Chi4ZeroLine`

Follows Mathlib's own definitions: `completedLFunction`, `gammaFactor χ s = Gammaℝ (s + 1)` for odd χ,
`rootNumber`, and the functional equation `IsPrimitive.completedLFunction_one_sub`. No textbook
normalisation is imported. Imports `GaussianDedekindRH`; modifies nothing earlier.
-/

open Complex DirichletCharacter

/-! ## Step 2: χ₄ is primitive -/

theorem chi4C_three : chi4C ((3 : ℕ) : ZMod 4) = -1 := by
  rw [chi4C_apply]; simp [GaussianLSeries.chi4]

/-- χ₄ does not factor through level 2. -/
theorem chi4C_not_factorsThrough_two : ¬ FactorsThrough chi4C 2 := by
  rw [factorsThrough_iff_ker_unitsMap (by norm_num : (2 : ℕ) ∣ 4)]
  intro h
  let u : (ZMod 4)ˣ := ZMod.unitOfCoprime 3 (by norm_num)
  have hu : u ∈ (ZMod.unitsMap (by norm_num : (2 : ℕ) ∣ 4)).ker := by
    rw [MonoidHom.mem_ker]; decide
  have := h hu
  rw [MonoidHom.mem_ker] at this
  have h3 := congrArg (fun x : ℂˣ => (x : ℂ)) this
  simp only [MulChar.coe_toUnitHom, Units.val_one] at h3
  have hu3 : ((u : ZMod 4)) = ((3 : ℕ) : ZMod 4) := rfl
  rw [hu3, chi4C_three] at h3
  norm_num at h3

/-- **χ₄ is primitive mod 4.** -/
theorem chi4C_isPrimitive : chi4C.IsPrimitive := by
  rw [isPrimitive_def]
  have hd := conductor_dvd_level chi4C
  have h1 : conductor chi4C ≠ 1 := fun h => chi4C_ne_one (eq_one_iff_conductor_eq_one.mpr h)
  have h2 : conductor chi4C ≠ 2 := fun h =>
    chi4C_not_factorsThrough_two (h ▸ factorsThrough_conductor chi4C)
  have h0 : conductor chi4C ≠ 0 := conductor_ne_zero _
  have hle := Nat.le_of_dvd (by norm_num) hd
  interval_cases h : conductor chi4C <;> simp_all

/-! ## Step 4: the completed L-function is nonzero on Re s ≤ 0 -/

theorem gammaFactor_inv_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    gammaFactor chi4C⁻¹ s ≠ 0 := by
  unfold gammaFactor
  split_ifs
  · rw [Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    have := congrArg Complex.re hn
    simp at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · rw [Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    have := congrArg Complex.re hn
    simp at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

/-- On Re s ≥ 1 the completed L-function of χ₄⁻¹ does not vanish. -/
theorem completed_inv_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    completedLFunction chi4C⁻¹ s ≠ 0 := by
  intro h
  have hL := LFunction_eq_completed_div_gammaFactor chi4C⁻¹ s (Or.inr (by norm_num))
  rw [h, zero_div] at hL
  exact LFunction_ne_zero_of_one_le_re chi4C⁻¹ (Or.inl (inv_ne_one.mpr chi4C_ne_one)) hs hL

/-- **Reflection:** the completed L-function of χ₄ is nonzero on Re s ≤ 0. -/
theorem completed_ne_zero_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0) :
    completedLFunction chi4C s ≠ 0 := by
  have hfe := chi4C_isPrimitive.completedLFunction_one_sub (1 - s)
  rw [sub_sub_cancel] at hfe
  rw [hfe]
  refine mul_ne_zero (mul_ne_zero ?_ (rootNumber_ne_zero chi4C_isPrimitive)) ?_
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  · apply completed_inv_ne_zero_of_one_le_re
    simp; linarith

/-! ## Step 6: the central theorem -/

/-- **On Re s ≤ 0, L(s, χ₄) = 0 exactly at the negative odd integers.** -/
theorem LFunction_chi4_zero_iff_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0) :
    LFunction chi4C s = 0 ↔ LTrivial s := by
  rw [LFunction_eq_completed_div_gammaFactor chi4C s (Or.inr (by norm_num)), div_eq_zero_iff,
    or_iff_right (completed_ne_zero_of_re_nonpos hs), gammaFactor_eq_zero_iff_of_odd chi4C_odd]
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, by linear_combination hn⟩
  · rintro ⟨n, hn⟩; exact ⟨n, by linear_combination hn⟩

/-! ## Step 7: the critical-strip form -/

/-- Conventional critical-strip formulation of GRH for χ₄. -/
def Chi4StripLine : Prop :=
  ∀ s : ℂ, LFunction chi4C s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2

theorem LTrivial_re_neg {s : ℂ} (h : LTrivial s) : s.re < 0 := by
  obtain ⟨n, rfl⟩ := h
  simp; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith

/-- **`Chi4ZeroLine` is exactly the critical-strip GRH for χ₄.** -/
theorem chi4ZeroLine_iff_strip : Chi4ZeroLine ↔ Chi4StripLine := by
  constructor
  · intro h s hz h0 _
    exact h s hz fun ht => absurd (LTrivial_re_neg ht) (not_lt.mpr h0.le)
  · intro h s hz hnt
    rcases le_or_gt s.re 0 with hle | hpos
    · exact absurd ((LFunction_chi4_zero_iff_of_re_nonpos hle).mp hz) hnt
    rcases lt_or_ge s.re 1 with hlt | hge
    · exact h s hz hpos hlt
    · exact absurd hz (LFunction_ne_zero_of_one_le_re chi4C (Or.inl chi4C_ne_one) hge)

/-- The milestone-4 corollary restated with *conventional* hypotheses only: Mathlib's
`RiemannHypothesis` and the critical-strip GRH for χ₄. Still CONDITIONAL. -/
theorem nontrivialZero_re_half_of_RH_strip (hRH : RiemannHypothesis) (hL : Chi4StripLine)
    {s : ℂ} (hs : NontrivialZero s) : s.re = 1 / 2 :=
  nontrivialZero_re_half_of_RH hRH (chi4ZeroLine_iff_strip.mpr hL) hs

#print axioms chi4C_isPrimitive
#print axioms completed_ne_zero_of_re_nonpos
#print axioms LFunction_chi4_zero_iff_of_re_nonpos
#print axioms chi4ZeroLine_iff_strip
#print axioms chi4C_not_factorsThrough_two
#print axioms gammaFactor_inv_ne_zero_of_one_le_re
#print axioms completed_inv_ne_zero_of_one_le_re
#print axioms nontrivialZero_re_half_of_RH_strip
