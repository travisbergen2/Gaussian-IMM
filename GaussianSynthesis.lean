import GaussianLSeries
import GaussianIdealCounting

/-!
# GaussianSynthesis — a(n) = r(n) and the ideal-counting L-series

Combines `GaussianIdealCounting` (ideal counts) with `GaussianLSeries`
(divisor sum of χ₄). Result: for Re s > 1,
  Σ_{n≥1} a(n) n^{-s} = ζ(s) · L(s, χ₄),
where a(n) is the number of ideals of ℤ[i] of norm n.

FENCE: classical. This is the Gaussian-integer ideal-counting series; the formal
identification with `NumberField.dedekindZeta ℚ(i)` is not made here. No RH/GRH content.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.zeta

namespace GaussianSynthesis

/-- χ₄ as an arithmetic function over ℤ. -/
def X : ArithmeticFunction ℤ := ⟨fun n => ZMod.χ₄ (n : ZMod 4), by simp⟩

theorem X_apply (n : ℕ) : X n = ZMod.χ₄ (n : ZMod 4) := rfl

theorem X_mult : X.IsMultiplicative := by
  refine ⟨by simp [X_apply], fun {m n} _ => ?_⟩
  simp [X_apply, Nat.cast_mul, map_mul]

/-- R = ζ * χ₄, i.e. R(n) = Σ_{d ∣ n} χ₄(d). -/
def R : ArithmeticFunction ℤ := (ζ : ArithmeticFunction ℤ) * X

theorem R_mult : R.IsMultiplicative := isMultiplicative_zeta.natCast.mul X_mult

theorem R_apply (n : ℕ) : R n = ∑ d ∈ n.divisors, ZMod.χ₄ (d : ZMod 4) := by
  rw [R, coe_zeta_mul_apply]; rfl

/-- The ideal count as an arithmetic function (value 0 at n = 0). -/
noncomputable def A : ArithmeticFunction ℤ :=
  ⟨fun n => if n = 0 then 0 else (a n : ℤ), by simp⟩

theorem A_apply {n : ℕ} (hn : n ≠ 0) : A n = a n := by
  show (if n = 0 then 0 else (a n : ℤ)) = a n; simp [hn]

theorem A_mult : A.IsMultiplicative := by
  refine ⟨by rw [A_apply one_ne_zero, a_one]; rfl, fun {m n} hmn => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [A_apply (by positivity), A_apply hm.ne', A_apply hn.ne', a_mul_of_coprime hm hn hmn]
  push_cast; ring

/-- Prime-power values of R: Σ_{i ≤ k} χ₄(p)ⁱ. -/
theorem R_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    R (p ^ k) = ∑ i ∈ range (k + 1), (ZMod.χ₄ (p : ZMod 4)) ^ i := by
  rw [R_apply, Nat.sum_divisors_prime_pow hp]
  simp [map_pow]

theorem alt_sum (k : ℕ) : ∑ i ∈ range (k + 1), ((-1 : ℤ)) ^ i = if Even k then 1 else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    rcases Nat.even_or_odd k with hk | hk
    · have : ¬ Even (k + 1) := by rw [Nat.even_add_one]; exact not_not.mpr hk
      simp [hk, this, hk.neg_one_pow, (hk.add_one).neg_one_pow]
    · have : Even (k + 1) := hk.add_one
      simp [Nat.not_even_iff_odd.mpr hk, this, this.neg_one_pow]

/-- **A and R agree on every prime power.** -/
theorem A_eq_R_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) : A (p ^ k) = R (p ^ k) := by
  have := Fact.mk hp
  rw [A_apply (pow_ne_zero k hp.ne_zero), R_prime_pow hp]
  rcases hp.eq_two_or_odd' with rfl | hodd
  · rw [a_ramified_prime_power]
    have : ZMod.χ₄ ((2 : ℕ) : ZMod 4) = 0 := by decide
    rw [this, sum_range_succ']; simp
  · have h4 : p % 4 = 1 ∨ p % 4 = 3 := by
      rcases hodd with ⟨m, hm⟩; omega
    rcases h4 with h1 | h3
    · rw [a_split_prime_power h1, ZMod.χ₄_nat_one_mod_four h1]; simp
    · rw [a_inert_prime_power h3, ZMod.χ₄_nat_three_mod_four h3, alt_sum]
      split_ifs <;> rfl

/-- **a(n) = Σ_{d ∣ n} χ₄(d) for every n > 0.** -/
theorem A_eq_R : A = R :=
  (IsMultiplicative.eq_iff_eq_on_prime_powers A A_mult R R_mult).mpr fun _ k hp => A_eq_R_prime_pow hp k

theorem a_eq_divisor_sum {n : ℕ} (hn : 0 < n) :
    (a n : ℤ) = ∑ d ∈ n.divisors, ZMod.χ₄ (d : ZMod 4) := by
  rw [← A_apply hn.ne', A_eq_R, R_apply]

/-- **a(n) = r(n)** (the complex divisor sum from GaussianLSeries), for n > 0. -/
theorem a_eq_r {n : ℕ} (hn : 0 < n) : (a n : ℂ) = GaussianLSeries.r n := by
  rw [GaussianLSeries.r_eq_divisor_sum]
  have := congrArg (Int.cast : ℤ → ℂ) (a_eq_divisor_sum hn)
  push_cast at this
  rw [this]; rfl

/-- **The ideal-counting L-series of ℤ[i] factors:**
  Σ a(n) n^{-s} = ζ(s) · L(s, χ₄)  for Re s > 1. -/
theorem LSeries_ideal_count {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (a n : ℂ)) s = riemannZeta s * LSeries GaussianLSeries.chi4 s := by
  rw [← GaussianLSeries.LSeries_r hs]
  exact LSeries_congr (fun {n} hn => a_eq_r (Nat.pos_of_ne_zero hn)) s

end GaussianSynthesis

#print axioms GaussianSynthesis.A_eq_R
#print axioms GaussianSynthesis.a_eq_r
#print axioms GaussianSynthesis.LSeries_ideal_count
