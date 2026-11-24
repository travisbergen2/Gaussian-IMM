import QuadraticLocalEulerFactor

/-!
# QuadraticEulerProduct — Σ A_K(n) n⁻ˢ = ζ(s)·L(s, χ) for any Galois quadratic field

Generic. Hypotheses: K a number field, [K : ℚ] = 2, `IsGalois ℚ K`, and a Dirichlet character χ
that *matches the splitting*: χ(p) = c_p for every prime p (c_p = 1 split, −1 inert, 0 ramified).

Route (no divisor-sum identity anywhere):
1. absolute convergence for Re s > 1 from `QuadBound.A_le_sigma0` (A_K ≤ d, and Σ d(n)n⁻ˢ = ζ²);
2. Mathlib's Euler product for multiplicative functions, applied to n ↦ A_K(n) n⁻ˢ
   (multiplicative by `IdealCount.A_mul`);
3. each local factor = (1 − p⁻ˢ)⁻¹ (1 − χ(p) p⁻ˢ)⁻¹ by `QuadEuler.localFactor_hasSum`;
4. comparison with Mathlib's Euler products for ζ and L(χ).
The character never enters steps 1–2.
-/

open ArithmeticFunction LSeries Complex IdealCount QuadEuler NumberField
open scoped ArithmeticFunction.sigma ArithmeticFunction.zeta

namespace QuadEuler

theorem LSeriesSummable_sigma0 {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => ((σ 0 n : ℕ) : ℂ)) s := by
  have hz : LSeriesSummable (⇑(ζ : ArithmeticFunction ℂ)) s := by
    rw [LSeriesSummable_congr s (g := 1) (fun hn => by simp [natCoe_apply, zeta_apply, hn])]
    exact LSeriesSummable_one_iff.mpr hs
  have hconv := hz.convolution hz
  rw [coe_mul] at hconv
  have e0 : (ζ : ArithmeticFunction ℕ) * ζ = σ 0 := by
    rw [← zeta_mul_pow_eq_sigma, pow_zero_eq_zeta]
  have e : ((ζ : ArithmeticFunction ℂ) * ζ) = ((σ 0 : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) := by
    rw [← e0, natCoe_mul]
  rw [e] at hconv
  convert hconv using 1
  funext n; simp [natCoe_apply]

variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]

theorem summable_norm_term (hK : Module.finrank ℚ K = 2) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n => ‖term (fun n => (A (𝓞 K) n : ℂ)) s n‖) := by
  have h0 := (summable_norm_iff.mpr (LSeriesSummable_sigma0 hs))
  refine h0.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · apply norm_term_le
    simp only [Complex.norm_natCast]
    exact_mod_cast QuadBound.A_le_sigma0 hK hn

/-- n ↦ A_K(n) n⁻ˢ as an arithmetic function. -/
noncomputable def T (K : Type*) [Field K] [NumberField K] (s : ℂ) : ArithmeticFunction ℂ :=
  ⟨term (fun n => (A (𝓞 K) n : ℂ)) s, term_zero _ _⟩

theorem T_apply (s : ℂ) (n : ℕ) : T K s n = term (fun n => (A (𝓞 K) n : ℂ)) s n := rfl

theorem T_mult (s : ℂ) : (T K s).IsMultiplicative := by
  refine ⟨?_, fun {m n} h => ?_⟩
  · rw [T_apply, term_of_ne_zero one_ne_zero, A_one]; simp
  rcases eq_or_ne m 0 with rfl | hm
  · simp [T_apply]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [T_apply]
  rw [T_apply, T_apply, T_apply, term_of_ne_zero (mul_ne_zero hm hn), term_of_ne_zero hm,
    term_of_ne_zero hn, A_mul h, Nat.cast_mul, Nat.cast_mul, natCast_mul_natCast_cpow,
    mul_div_mul_comm]

theorem prime_pow_cpow (p e : ℕ) (s : ℂ) :
    ((p ^ e : ℕ) : ℂ) ^ (-s) = ((p : ℂ) ^ (-s)) ^ e := by
  induction e with
  | zero => simp
  | succ e ih => rw [pow_succ, Nat.cast_mul, natCast_mul_natCast_cpow, ih, pow_succ]

theorem norm_prime_cpow_lt_one {s : ℂ} (hs : 0 < s.re) {p : ℕ} (hp : p.Prime) :
    ‖(p : ℂ) ^ (-s)‖ < 1 := by
  rw [norm_natCast_cpow_of_pos hp.pos, neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)

theorem local_tsum (hK : Module.finrank ℚ K = 2) {s : ℂ} (hs : 1 < s.re) (p : Nat.Primes) :
    ∑' e, T K s ((p : ℕ) ^ e) =
      (1 - (p : ℂ) ^ (-s))⁻¹ * (1 - splitChar K p * (p : ℂ) ^ (-s))⁻¹ := by
  have := Fact.mk p.prop
  rw [← (localFactor_hasSum hK (p := p) (norm_prime_cpow_lt_one (by linarith) p.prop)).tsum_eq]
  congr 1; funext e
  rw [T_apply, term_of_ne_zero (pow_ne_zero _ p.prop.ne_zero), div_eq_mul_inv, ← cpow_neg,
    prime_pow_cpow]

/-- **Generic quadratic Euler product / Dedekind factorization.** If χ matches the splitting
of every prime, then Σ A_K(n) n⁻ˢ = ζ(s) · L(s, χ) for Re s > 1. -/
theorem LSeries_A_eq_zeta_mul_L (hK : Module.finrank ℚ K = 2) {N : ℕ} (χ : DirichletCharacter ℂ N)
    (hχ : ∀ p : ℕ, p.Prime → χ (p : ZMod N) = splitChar K p) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (A (𝓞 K) n : ℂ)) s = riemannZeta s * LSeries (fun n => χ n) s := by
  have halg := (T_mult (K := K) s).eulerProduct_hasProd (summable_norm_term hK hs)
  simp only [local_tsum hK hs] at halg
  have hana := (riemannZeta_eulerProduct_hasProd hs).mul
    (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs)
  have hfac : (fun p : Nat.Primes => (1 - (p : ℂ) ^ (-s))⁻¹ * (1 - splitChar K p * (p : ℂ) ^ (-s))⁻¹)
      = (fun p : Nat.Primes => (1 - (p : ℂ) ^ (-s))⁻¹ * (1 - χ p * (p : ℂ) ^ (-s))⁻¹) := by
    funext p; rw [hχ p p.prop]
  rw [hfac] at halg
  exact halg.unique hana

end QuadEuler

#print axioms QuadEuler.LSeries_A_eq_zeta_mul_L
