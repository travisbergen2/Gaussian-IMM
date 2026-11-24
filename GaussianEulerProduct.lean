import GaussianDedekindContinuation

/-!
# GaussianEulerProduct — the Euler product of Σ a(n) n⁻ˢ and its three local factors

Additive module (imports `GaussianDedekindContinuation`; baseline unchanged). For Re s > 1:

* `ideal_count_eulerProduct`: Σ a(n) n⁻ˢ = ∏'_p E_p(s), with E_p(s) = (1 − p⁻ˢ)⁻¹ (1 − χ₄(p) p⁻ˢ)⁻¹.
* The three local factors, as closed forms:
    p = 2:        E_p = (1 − 2⁻ˢ)⁻¹
    p ≡ 1 (4):    E_p = ((1 − p⁻ˢ)²)⁻¹
    p ≡ 3 (4):    E_p = (1 − (p⁻ˢ)²)⁻¹
* Each local factor is the local generating function of the ideal count:
    E_p(s) = Σ_k a(pᵏ) (p⁻ˢ)ᵏ   (`localFactor_hasSum`, all three classes).
  The inert factor's dependence on (p⁻ˢ)² is the obstruction "only even exponents".

Absolute convergence only. No statement about zeros; no RH/GRH content.
-/

open Complex DirichletCharacter
open scoped LSeries.notation

/-- The local Euler factor at p. -/
noncomputable def localFactor (s : ℂ) (p : ℕ) : ℂ :=
  (1 - (p : ℂ) ^ (-s))⁻¹ * (1 - chi4C p * (p : ℂ) ^ (-s))⁻¹

/-- **Euler product of the ideal-counting series of ℤ[i].** -/
theorem ideal_count_eulerProduct {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => localFactor s p) (LSeries (fun n => (a n : ℂ)) s) := by
  rw [GaussianSynthesis.LSeries_ideal_count hs, ← LFunction_chi4_eq hs,
    LFunction_eq_LSeries chi4C hs]
  exact (riemannZeta_eulerProduct_hasProd hs).mul (LSeries_eulerProduct_hasProd chi4C hs)

/-! ## The three closed forms -/

theorem chi4C_two : chi4C (2 : ZMod 4) = 0 := by
  have := chi4C_apply 2
  simp only [Nat.cast_ofNat] at this
  rw [this]; simp [GaussianLSeries.chi4]

theorem chi4C_one_mod_four {p : ℕ} (h : p % 4 = 1) : chi4C (p : ZMod 4) = 1 := by
  rw [chi4C_apply]; simp [GaussianLSeries.chi4, ZMod.χ₄_nat_one_mod_four h]

theorem chi4C_three_mod_four {p : ℕ} (h : p % 4 = 3) : chi4C (p : ZMod 4) = -1 := by
  rw [chi4C_apply]; simp [GaussianLSeries.chi4, ZMod.χ₄_nat_three_mod_four h]

theorem localFactor_two (s : ℂ) : localFactor s 2 = (1 - (2 : ℂ) ^ (-s))⁻¹ := by
  simp only [localFactor, Nat.cast_ofNat, chi4C_two, zero_mul, sub_zero, inv_one, mul_one]

theorem localFactor_split {s : ℂ} {p : ℕ} (h : p % 4 = 1) :
    localFactor s p = ((1 - (p : ℂ) ^ (-s)) ^ 2)⁻¹ := by
  rw [localFactor, chi4C_one_mod_four h, one_mul, ← mul_inv, sq]

theorem localFactor_inert {s : ℂ} {p : ℕ} (h : p % 4 = 3) :
    localFactor s p = (1 - ((p : ℂ) ^ (-s)) ^ 2)⁻¹ := by
  rw [localFactor, chi4C_three_mod_four h, ← mul_inv]
  congr 1; ring

/-! ## Each local factor is the local generating function Σ a(pᵏ) xᵏ -/

theorem norm_prime_cpow_lt_one {s : ℂ} (hs : 0 < s.re) {p : ℕ} (hp : p.Prime) :
    ‖(p : ℂ) ^ (-s)‖ < 1 := by
  rw [norm_natCast_cpow_of_pos hp.pos, neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)

theorem one_sub_ne_zero_of_norm_lt_one {x : ℂ} (h : ‖x‖ < 1) : 1 - x ≠ 0 := by
  intro h0
  have : x = 1 := by linear_combination -h0
  rw [this, norm_one] at h; exact lt_irrefl _ h

/-- Σ (k+1) xᵏ = ((1−x)²)⁻¹. -/
theorem hasSum_succ_mul_geometric {x : ℂ} (h : ‖x‖ < 1) :
    HasSum (fun k : ℕ => ((k : ℂ) + 1) * x ^ k) (((1 - x) ^ 2)⁻¹) := by
  have hsum := (hasSum_coe_mul_geometric_of_norm_lt_one h).add (hasSum_geometric_of_norm_lt_one h)
  have hne := one_sub_ne_zero_of_norm_lt_one h
  convert hsum using 1
  · funext k; ring
  · field_simp; ring

/-- Σ [k even] xᵏ = (1−x²)⁻¹. -/
theorem hasSum_even_geometric {x : ℂ} (h : ‖x‖ < 1) :
    HasSum (fun k : ℕ => (if Even k then (1 : ℂ) else 0) * x ^ k) ((1 - x ^ 2)⁻¹) := by
  have h' : ‖-x‖ < 1 := by rwa [norm_neg]
  have hsum := ((hasSum_geometric_of_norm_lt_one h).add
    (hasSum_geometric_of_norm_lt_one h')).mul_left (1 / 2 : ℂ)
  have hne1 := one_sub_ne_zero_of_norm_lt_one h
  have hne2 := one_sub_ne_zero_of_norm_lt_one h'
  have hne3 : (1 - x ^ 2) ≠ 0 := by
    rw [show 1 - x ^ 2 = (1 - x) * (1 - -x) by ring]; exact mul_ne_zero hne1 hne2
  convert hsum using 1
  · funext k
    rw [neg_pow]
    rcases Nat.even_or_odd k with he | ho
    · simp [he, he.neg_one_pow]; ring
    · simp [Nat.not_even_iff_odd.mpr ho, ho.neg_one_pow]
  · field_simp; ring

/-- **Local generating functions.** For every prime p and Re s > 0:
  Σ_k a(pᵏ) (p⁻ˢ)ᵏ = E_p(s). -/
theorem localFactor_hasSum {s : ℂ} (hs : 0 < s.re) {p : ℕ} (hp : p.Prime) :
    HasSum (fun k : ℕ => (a (p ^ k) : ℂ) * ((p : ℂ) ^ (-s)) ^ k) (localFactor s p) := by
  have := Fact.mk hp
  have hx1 := norm_prime_cpow_lt_one hs hp
  rcases hp.eq_two_or_odd' with rfl | hodd
  · rw [localFactor_two]
    simpa [a_ramified_prime_power] using hasSum_geometric_of_norm_lt_one hx1
  · have h4 : p % 4 = 1 ∨ p % 4 = 3 := by rcases hodd with ⟨m, hm⟩; omega
    rcases h4 with h1 | h3
    · rw [localFactor_split h1]
      convert hasSum_succ_mul_geometric hx1 using 2 with k
      rw [a_split_prime_power h1]; push_cast; ring
    · rw [localFactor_inert h3]
      convert hasSum_even_geometric hx1 using 2 with k
      rw [a_inert_prime_power h3]; split_ifs <;> simp

#print axioms ideal_count_eulerProduct
#print axioms localFactor_two
#print axioms localFactor_split
#print axioms localFactor_inert
#print axioms localFactor_hasSum
#print axioms hasSum_succ_mul_geometric
#print axioms hasSum_even_geometric
