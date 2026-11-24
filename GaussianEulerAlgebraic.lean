import GaussianEulerProduct

/-!
# GaussianEulerAlgebraic — an independent derivation of Σ a(n) n⁻ˢ = ζ(s)·L(s, χ₄)

The baseline derived this identity from the divisor-sum identity a = 1 ⍟ χ₄
(`GaussianSynthesis.A_eq_R` → `LSeries_ideal_count`). Here it is derived a second way:

1. `a_le_sigma0`: a(n) ≤ d(n) (number of divisors), from the three prime-power counts.
2. `LSeriesSummable_ideal_count`: absolute convergence for Re s > 1, by comparison with Σ d(n) n⁻ˢ.
3. `ideal_count_eulerProduct_algebraic`: Mathlib's Euler product for *multiplicative* functions,
   applied to a(n) n⁻ˢ (multiplicative because a is, by `a_mul_of_coprime`), with each local
   factor Σ a(pᵏ)p⁻ᵏˢ identified by `localFactor_hasSum`.
4. `ideal_count_eq_zeta_mul_L_independent`: comparing with Mathlib's Euler products for ζ and L(χ₄).

Independence is checked mechanically at the end (`#check_independent`): the proof terms are scanned
through every project-local constant, and must not reach the divisor-sum route.
Absolute convergence only; no zero statements; no RH/GRH content.
-/

open ArithmeticFunction LSeries Complex
open scoped ArithmeticFunction.sigma ArithmeticFunction.zeta

/-! ## 1. a(n) ≤ d(n) -/

theorem a_mul_all {m n : ℕ} (h : Nat.Coprime m n) : a (m * n) = a m * a n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.coprime_zero_left] at h; subst h; simp [a_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.coprime_zero_right] at h; subst h; simp [a_one]
  exact a_mul_of_coprime hm hn h

theorem a_prime_pow_le {p : ℕ} (hp : p.Prime) (k : ℕ) : a (p ^ k) ≤ k + 1 := by
  have := Fact.mk hp
  rcases hp.eq_two_or_odd' with rfl | hodd
  · rw [a_ramified_prime_power]; omega
  · have h4 : p % 4 = 1 ∨ p % 4 = 3 := by rcases hodd with ⟨m, hm⟩; omega
    rcases h4 with h1 | h3
    · rw [a_split_prime_power h1]
    · rw [a_inert_prime_power h3]; split_ifs <;> omega

/-- **a(n) ≤ d(n)** for n ≠ 0. -/
theorem a_le_sigma0 {n : ℕ} (hn : n ≠ 0) : a n ≤ σ 0 n := by
  rw [Nat.multiplicative_factorization a (fun _ _ h => a_mul_all h) a_one hn,
    isMultiplicative_sigma.multiplicative_factorization (σ 0) hn]
  rw [Finsupp.prod, Finsupp.prod]
  refine Finset.prod_le_prod fun p hp => ?_
  have hp' := Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)
  rw [sigma_zero_apply_prime_pow hp']
  exact a_prime_pow_le hp' _

/-! ## 2. Absolute convergence for Re s > 1 -/

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

theorem LSeriesSummable_ideal_count {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n => ‖term (fun n => (a n : ℂ)) s n‖) := by
  have h0 := (summable_norm_iff.mpr (LSeriesSummable_sigma0 hs))
  refine h0.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · apply norm_term_le
    simp only [Complex.norm_natCast]
    exact_mod_cast a_le_sigma0 hn

/-! ## 3. The multiplicative Euler product -/

/-- n ↦ a(n) n⁻ˢ as an arithmetic function. -/
noncomputable def T (s : ℂ) : ArithmeticFunction ℂ :=
  ⟨term (fun n => (a n : ℂ)) s, term_zero _ _⟩

theorem T_apply (s : ℂ) (n : ℕ) : T s n = term (fun n => (a n : ℂ)) s n := rfl

theorem T_mult (s : ℂ) : (T s).IsMultiplicative := by
  refine ⟨by simp [T_apply, term_def, a_one], fun {m n} h => ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp [T_apply]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [T_apply]
  simp only [T_apply, term_def, mul_ne_zero hm hn, hm, hn, if_false, a_mul_all h]
  push_cast
  rw [natCast_mul_natCast_cpow]
  field_simp

theorem prime_pow_cpow (p e : ℕ) (s : ℂ) :
    ((p ^ e : ℕ) : ℂ) ^ (-s) = ((p : ℂ) ^ (-s)) ^ e := by
  induction e with
  | zero => simp
  | succ e ih => rw [pow_succ, Nat.cast_mul, natCast_mul_natCast_cpow, ih, pow_succ]

theorem local_tsum_eq {s : ℂ} (hs : 1 < s.re) (p : Nat.Primes) :
    ∑' e, T s ((p : ℕ) ^ e) = localFactor s p := by
  rw [← (localFactor_hasSum (by linarith) p.prop).tsum_eq]
  congr 1; funext e
  rw [T_apply, term_def, if_neg (pow_ne_zero _ p.prop.ne_zero), div_eq_mul_inv, ← cpow_neg,
    prime_pow_cpow]

/-- **Algebraic Euler product:** Σ a(n)n⁻ˢ = ∏_p E_p(s), via multiplicativity of a. -/
theorem ideal_count_eulerProduct_algebraic {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => localFactor s p) (LSeries (fun n => (a n : ℂ)) s) := by
  have := (T_mult s).eulerProduct_hasProd (LSeriesSummable_ideal_count hs)
  simp only [local_tsum_eq hs] at this
  exact this

/-! ## 4. Independent recovery of the baseline identity -/

/-- **Σ a(n)n⁻ˢ = ζ(s)·L(s, χ₄) for Re s > 1, without the divisor-sum identity.** -/
theorem ideal_count_eq_zeta_mul_L_independent {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (a n : ℂ)) s = riemannZeta s * LSeries GaussianLSeries.chi4 s := by
  have hana := (riemannZeta_eulerProduct_hasProd hs).mul
    (DirichletCharacter.LSeries_eulerProduct_hasProd chi4C hs)
  have hL : LSeries (fun n => chi4C (n : ZMod 4)) s = LSeries GaussianLSeries.chi4 s := by
    congr 1
  rw [← hL]
  exact (ideal_count_eulerProduct_algebraic hs).unique hana

/-! ## Mechanical independence check -/

open Lean Meta Elab Command in
/-- Collect every constant reachable from `n`, expanding only constants defined in this project
(modules whose name starts with `Gaussian`, or this file). Mathlib/core constants are leaves. -/
partial def projectClosure (env : Environment) (n : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[n]
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    let local? := match env.getModuleIdxFor? c with
      | none => true
      | some idx => (env.header.moduleNames[idx.toNat]!).toString.startsWith "Gaussian"
    if !local? then continue
    if let some ci := env.find? c then
      for d in ci.type.getUsedConstants do todo := todo.push d
      let v? : Option Expr := match ci with
        | .thmInfo v => some v.value
        | .defnInfo v => some v.value
        | .opaqueInfo v => some v.value
        | _ => none
      if let some v := v? then
        for d in v.getUsedConstants do todo := todo.push d
  return seen

open Lean Elab Command in
elab "#check_independent " thm:ident : command => do
  let env ← getEnv
  let forbidden : List Name :=
    [`GaussianSynthesis.A_eq_R, `GaussianSynthesis.a_eq_r, `GaussianSynthesis.a_eq_divisor_sum,
     `GaussianSynthesis.LSeries_ideal_count, `GaussianLSeries.LSeries_r,
     `GaussianLSeries.r_eq_divisor_sum, `ideal_count_eulerProduct, `dedekindZeta_Qi]
  let cl := projectClosure env thm.getId
  let hits := forbidden.filter cl.contains
  if hits.isEmpty then
    logInfo m!"INDEPENDENT: {thm.getId} reaches none of {forbidden}"
  else
    throwError m!"NOT INDEPENDENT: {thm.getId} reaches {hits}"

open Lean Elab Command in
/-- Negative control: assert that `thm` DOES reach the divisor-sum route (so the scanner can see it). -/
elab "#check_dependent " thm:ident : command => do
  let env ← getEnv
  let cl := projectClosure env thm.getId
  unless cl.contains `GaussianSynthesis.A_eq_R do
    throwError m!"CONTROL FAILED: {thm.getId} should reach GaussianSynthesis.A_eq_R"
  logInfo m!"CONTROL OK: {thm.getId} reaches GaussianSynthesis.A_eq_R (divisor-sum route)"

-- Control: the earlier analytic-route Euler product is correctly detected as dependent.
#check_dependent ideal_count_eulerProduct

#check_independent ideal_count_eulerProduct_algebraic
#check_independent ideal_count_eq_zeta_mul_L_independent

#print axioms a_le_sigma0
#print axioms LSeriesSummable_ideal_count
#print axioms ideal_count_eulerProduct_algebraic
#print axioms ideal_count_eq_zeta_mul_L_independent
