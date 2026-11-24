import Mathlib

/-!
# GaussianLSeries — the divisor-sum side of ζ_{ℚ(i)} = ζ · L(χ₄)

Defines r(n) = Σ_{d ∣ n} χ₄(d) and proves, for Re s > 1,
  L(r, s) = ζ(s) · L(χ₄, s).
Convergence is proved, not assumed: both coefficient sequences are bounded by 1.

FENCE: this does not yet identify r(n) with the number of Gaussian ideals of
norm n (that is GaussianIdealCounting). Classical; no RH/GRH content.
-/

open LSeries ArithmeticFunction

namespace GaussianLSeries

/-- χ₄ as a complex sequence. -/
noncomputable def chi4 (n : ℕ) : ℂ := (ZMod.χ₄ (n : ZMod 4) : ℂ)

/-- The constant-one sequence (the ζ side). -/
def one : ℕ → ℂ := 1

/-- r = 1 ⍟ χ₄ : the divisor sum of χ₄. -/
noncomputable def r : ℕ → ℂ := LSeries.convolution one chi4

theorem chi4_bounded (n : ℕ) : ‖chi4 n‖ ≤ 1 := by
  unfold chi4
  have h := ZMod.χ₄_int_eq_if_mod_four (n : ℤ)
  rcases Int.emod_two_eq_zero_or_one (n : ℤ) with h2 | h2 <;>
    simp_all <;> split_ifs <;> simp

theorem abscissa_chi4 : abscissaOfAbsConv chi4 ≤ 1 :=
  abscissaOfAbsConv_le_of_le_const ⟨1, fun n _ => chi4_bounded n⟩

theorem abscissa_one : abscissaOfAbsConv one ≤ 1 :=
  abscissaOfAbsConv_le_of_le_const ⟨1, fun n _ => by simp [one]⟩

/-- **L(1 ⍟ χ₄, s) = ζ(s) · L(χ₄, s) for Re s > 1.** -/
theorem LSeries_r {s : ℂ} (hs : 1 < s.re) :
    LSeries r s = riemannZeta s * LSeries chi4 s := by
  have h1 : abscissaOfAbsConv one < s.re :=
    lt_of_le_of_lt abscissa_one (by exact_mod_cast hs)
  have h2 : abscissaOfAbsConv chi4 < s.re :=
    lt_of_le_of_lt abscissa_chi4 (by exact_mod_cast hs)
  rw [r, LSeries_convolution h1 h2, one, LSeries_one_eq_riemannZeta hs]

/-- r(n) really is the divisor sum Σ_{d ∣ n} χ₄(d) (for n = 0 both sides are 0). -/
theorem r_eq_divisor_sum (n : ℕ) :
    r n = ∑ d ∈ n.divisors, chi4 d := by
  rw [r, LSeries.convolution_def]
  simp only [one, Pi.one_apply, one_mul]
  exact Nat.sum_divisorsAntidiagonal' (fun _ b => chi4 b)

end GaussianLSeries

#print axioms GaussianLSeries.LSeries_r
#print axioms GaussianLSeries.r_eq_divisor_sum
