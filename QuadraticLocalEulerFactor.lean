import QuadraticDivisorBound

/-!
# QuadraticLocalEulerFactor — local factors of a Galois quadratic field from (f, g)

Generic over K with [K : ℚ] = 2 and `IsGalois ℚ K`. No characters, no specific field.

For a prime p let g = #primes over p and f = residue degree (uniform, by Galois). Define the
*splitting value*  c_p = 1 if g = 2,  −1 if (g, f) = (1, 2),  0 if (g, f) = (1, 1).

* `A_prime_pow_eq`: A_K(pᵏ) = k + 1, [k even], 1 in the three patterns (from the allocation theorem).
* `localFactor_hasSum`: Σₖ A_K(pᵏ) xᵏ = (1 − x)⁻¹ (1 − c_p x)⁻¹ for ‖x‖ < 1.
  The ramified case is its own branch: c_p = 0 comes from (g, f) = (1, 1), not from a Frobenius relation.
-/

open Ideal NumberField LocalCount IdealCount QuadBound

namespace QuadEuler

variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]

/-- Number of primes over p. -/
noncomputable def gP (K : Type*) [Field K] [NumberField K] (p : ℕ) : ℕ :=
  ((span {(p : ℤ)}).primesOver (𝓞 K)).ncard

/-- Residue degree over p. -/
noncomputable def fP (K : Type*) [Field K] [NumberField K] (p : ℕ) : ℕ :=
  (span {(p : ℤ)}).inertiaDegIn (𝓞 K)

/-- The splitting value c_p. -/
noncomputable def splitChar (K : Type*) [Field K] [NumberField K] (p : ℕ) : ℂ :=
  if gP K p = 2 then 1 else if fP K p = 2 then -1 else 0

/-- The three patterns. -/
theorem pattern (hK : Module.finrank ℚ K = 2) (p : ℕ) [Fact p.Prime] :
    (gP K p = 2 ∧ fP K p = 1) ∨ (gP K p = 1 ∧ fP K p = 1) ∨ (gP K p = 1 ∧ fP K p = 2) := by
  have hfun := fundamental hK (K := K) p
  unfold gP fP
  set g := ((span {(p : ℤ)}).primesOver (𝓞 K)).ncard
  set e := (span {(p : ℤ)}).ramificationIdxIn (𝓞 K)
  set f := (span {(p : ℤ)}).inertiaDegIn (𝓞 K)
  have hg : g ∣ 2 := ⟨_, hfun.symm⟩
  have hf : f ∣ 2 := ⟨g * e, by rw [← hfun]; ring⟩
  have hg2 : g ≤ 2 := Nat.le_of_dvd (by norm_num) hg
  have hf2 : f ≤ 2 := Nat.le_of_dvd (by norm_num) hf
  interval_cases g <;> interval_cases f <;> simp_all

/-- A_K(pᵏ) in terms of the pattern. -/
theorem A_prime_pow_eq (hK : Module.finrank ℚ K = 2) {p : ℕ} [hp : Fact p.Prime] (k : ℕ) :
    A (𝓞 K) (p ^ k) =
      if gP K p = 2 then k + 1 else if fP K p = 2 then (if Even k then 1 else 0) else 1 := by
  have hexh : ∀ Q : Ideal (𝓞 K), Prime Q → Q ∣ span {((p : ℕ) : 𝓞 K)} → Q ∈ (span {(p : ℤ)}).primesOver (𝓞 K) :=
    fun Q hQ hd => mem_primesOver_of_dvd hp.out hQ hd
  rcases pattern hK (K := K) p with ⟨hg, hf⟩ | ⟨hg, hf⟩ | ⟨hg, hf⟩
  · obtain ⟨P₀, P₁, hne, hs⟩ := Set.ncard_eq_two.mp hg
    have m0 : P₀ ∈ (span {(p : ℤ)}).primesOver (𝓞 K) := by rw [hs]; simp
    have m1 : P₁ ∈ (span {(p : ℤ)}).primesOver (𝓞 K) := by rw [hs]; simp
    rw [if_pos hg, A, card_ideals_norm_prime_pow (P := ![P₀, P₁]) (f := fP K p) hp.out.one_lt
      (fun i => by fin_cases i
                   · exact prime_of_mem_primesOver hp.out m0
                   · exact prime_of_mem_primesOver hp.out m1)
      (fun i j hij => by
        fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> first | exact hne hij | exact hne hij.symm)
      (fun Q hQ hdvd => by
        have := hexh Q hQ hdvd
        rw [hs] at this
        rcases this with h | h
        · exact ⟨0, by simpa using h⟩
        · exact ⟨1, by simpa using h⟩)
      (fun i => by fin_cases i
                   · exact absNorm_eq m0
                   · exact absNorm_eq m1) k, hf, card_split]
  all_goals
    obtain ⟨P₀, hs⟩ := Set.ncard_eq_one.mp hg
    have m0 : P₀ ∈ (span {(p : ℤ)}).primesOver (𝓞 K) := by rw [hs]; simp
    rw [if_neg (by rw [hg]; norm_num), A, card_ideals_norm_prime_pow (P := ![P₀]) (f := fP K p)
      hp.out.one_lt
      (fun i => by fin_cases i; exact prime_of_mem_primesOver hp.out m0)
      (fun i j _ => Subsingleton.elim i j)
      (fun Q hQ hdvd => ⟨0, by have := hexh Q hQ hdvd; rw [hs] at this; simpa using this⟩)
      (fun i => by fin_cases i; exact absNorm_eq m0) k, hf]
  · simp only [if_neg (show (1 : ℕ) ≠ 2 by norm_num)]; simpa using card_ramified k
  · simp only [if_true]; simpa using card_inert k

/-! ## Local generating functions -/

theorem one_sub_ne_zero_of_norm_lt_one {x : ℂ} (h : ‖x‖ < 1) : 1 - x ≠ 0 := by
  intro h0
  have : x = 1 := by linear_combination -h0
  rw [this, norm_one] at h; exact lt_irrefl _ h

theorem hasSum_succ_mul_geometric {x : ℂ} (h : ‖x‖ < 1) :
    HasSum (fun k : ℕ => ((k : ℂ) + 1) * x ^ k) (((1 - x) ^ 2)⁻¹) := by
  have hsum := (hasSum_coe_mul_geometric_of_norm_lt_one h).add (hasSum_geometric_of_norm_lt_one h)
  have hne := one_sub_ne_zero_of_norm_lt_one h
  convert hsum using 1
  · funext k; ring
  · field_simp; ring

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

/-- **Local Euler factor:** Σₖ A_K(pᵏ) xᵏ = (1 − x)⁻¹ (1 − c_p x)⁻¹. -/
theorem localFactor_hasSum (hK : Module.finrank ℚ K = 2) {p : ℕ} [Fact p.Prime] {x : ℂ}
    (hx : ‖x‖ < 1) :
    HasSum (fun k : ℕ => (A (𝓞 K) (p ^ k) : ℂ) * x ^ k)
      ((1 - x)⁻¹ * (1 - splitChar K p * x)⁻¹) := by
  simp only [A_prime_pow_eq hK, splitChar]
  rcases pattern hK (K := K) p with ⟨hg, hf⟩ | ⟨hg, hf⟩ | ⟨hg, hf⟩
  · -- split: (1 − x)⁻²
    simp only [hg, if_true, one_mul]
    rw [← mul_inv, ← sq]
    convert hasSum_succ_mul_geometric hx using 2 with k; push_cast; ring
  · -- ramified: (1 − x)⁻¹
    simp only [hg, hf, show (1 : ℕ) ≠ 2 by norm_num, if_false, zero_mul, sub_zero, inv_one,
      mul_one, Nat.cast_one, one_mul]
    exact hasSum_geometric_of_norm_lt_one hx
  · -- inert: (1 − x²)⁻¹
    simp only [hg, hf, show (1 : ℕ) ≠ 2 by norm_num, if_false, if_true]
    rw [← mul_inv, show (1 - x) * (1 - -1 * x) = 1 - x ^ 2 by ring]
    convert hasSum_even_geometric hx using 2 with k
    split_ifs <;> simp

end QuadEuler

#print axioms QuadEuler.A_prime_pow_eq
#print axioms QuadEuler.localFactor_hasSum
