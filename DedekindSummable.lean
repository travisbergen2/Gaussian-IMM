import Mathlib

/-!
# DedekindSummable — Σ A_K(n) n⁻ˢ converges absolutely for Re s > 1, any number field

Degree-free and character-free. The partial sums Σ_{n ≤ N} A_K(n) are ~ c·N by Mathlib's ideal
asymptotics (`Ideal.tendsto_norm_le_div_atTop₀`, the input to the class number formula), hence O(N);
`LSeriesSummable_of_sum_norm_bigO_and_nonneg` then gives convergence for Re s > 1.
This replaces the quadratic divisor bound A_K ≤ d for fields of any degree.
-/

open Filter Ideal NumberField Asymptotics
open scoped Topology

namespace DedekindSum

variable (K : Type*) [Field K] [NumberField K]

/-- Partial sums of the ideal count, divided by N, converge (to the Dedekind residue). -/
theorem tendsto_sum_div :
    Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 K) // absNorm I = k} : ℝ)) / n) atTop
      (𝓝 (dedekindZeta_residue K)) := by
  refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by simp,
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq
      (fun k _ ↦ Ring.HasFiniteQuotients.finite_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

/-- **Absolute convergence for Re s > 1**, for every number field. -/
theorem LSeriesSummable_idealCount {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℂ)) s := by
  have := LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (f := fun n ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℝ))
    (isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using tendsto_sum_div K))
    (fun _ ↦ Nat.cast_nonneg _) zero_le_one hs
  simpa using this

end DedekindSum

#print axioms DedekindSum.LSeriesSummable_idealCount
