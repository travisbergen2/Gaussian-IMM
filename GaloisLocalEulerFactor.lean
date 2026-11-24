import QuadraticDivisorBound
import LocalCountBinomial

/-!
# GaloisLocalEulerFactor — local factor (1 − xᶠ)^{−g} for a Galois field of any degree

For K/ℚ Galois (degree arbitrary) and a prime p with g primes above it, all of residue degree f:
* `A_prime_pow_closed`: A_K(pᵏ) = C(k/f + g − 1, g − 1) if f ∣ k, else 0;
* `localFactor_hasSum`: Σₖ A_K(pᵏ) xᵏ = ((1 − xᶠ)^g)⁻¹ for ‖x‖ < 1.
The primes above p are enumerated through `Fintype.equivFin`; no degree-2 input is used.
-/

open Ideal NumberField LocalCount IdealCount QuadBound

namespace GaloisEuler

variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]

instance span_isMaximal (p : ℕ) [hp : Fact p.Prime] : (span {(p : ℤ)}).IsMaximal :=
  span_nat_isMaximal hp.out

/-- Number of primes over p. -/
noncomputable def gK (K : Type*) [Field K] [NumberField K] (p : ℕ) : ℕ :=
  ((span {(p : ℤ)}).primesOver (𝓞 K)).ncard

/-- Residue degree over p (uniform, by Galois). -/
noncomputable def fK (K : Type*) [Field K] [NumberField K] (p : ℕ) : ℕ :=
  (span {(p : ℤ)}).inertiaDegIn (𝓞 K)

theorem gK_eq_card (p : ℕ) [Fact p.Prime] :
    gK K p = Fintype.card ((span {(p : ℤ)}).primesOver (𝓞 K)) := by
  rw [gK, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]

theorem gK_pos (p : ℕ) [Fact p.Prime] : 0 < gK K p :=
  Nat.pos_of_ne_zero (IsDedekindDomain.primesOver_ncard_ne_zero _ _)

theorem fK_pos (p : ℕ) [Fact p.Prime] : 0 < fK K p := by
  obtain ⟨⟨P, h1, h2⟩⟩ := (span {(p : ℤ)}).nonempty_primesOver (S := 𝓞 K)
  rw [fK, inertiaDegIn_eq_inertiaDeg (span {(p : ℤ)}) P Gal(K/ℚ)]
  exact inertiaDeg_pos _ _

/-- **Closed form of A_K(pᵏ)** for Galois K of any degree. -/
theorem A_prime_pow_closed {p : ℕ} [hp : Fact p.Prime] (k : ℕ) :
    A (𝓞 K) (p ^ k) =
      if fK K p ∣ k then (k / fK K p + gK K p - 1).choose (gK K p - 1) else 0 := by
  set s := (span {(p : ℤ)}).primesOver (𝓞 K)
  let e := Fintype.equivFin s
  rw [gK_eq_card, A, card_ideals_norm_prime_pow_closed (P := fun i => (e.symm i).1)
    (by rw [← gK_eq_card]; exact gK_pos p) hp.out.one_lt (fK_pos p)
    (fun i => prime_of_mem_primesOver hp.out (e.symm i).2)
    (fun i j h => e.symm.injective (Subtype.ext h))
    (fun Q hQ hdvd => ⟨e ⟨Q, mem_primesOver_of_dvd hp.out hQ hdvd⟩, by simp⟩)
    (fun i => absNorm_eq (e.symm i).2) k]

/-- **Local Euler factor:** Σₖ A_K(pᵏ) xᵏ = ((1 − xᶠ)^g)⁻¹. -/
theorem localFactor_hasSum {p : ℕ} [Fact p.Prime] {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun k : ℕ => (A (𝓞 K) (p ^ k) : ℂ) * x ^ k) (((1 - x ^ fK K p) ^ gK K p)⁻¹) := by
  set f := fK K p
  set g := gK K p
  have hf := fK_pos (K := K) p
  have hg := gK_pos (K := K) p
  have hr : ‖x ^ f‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hx (by omega)
  have hbase := hasSum_choose_mul_geometric_of_norm_lt_one (g - 1) hr
  rw [show g - 1 + 1 = g by omega, one_div] at hbase
  have hinj : Function.Injective (fun m : ℕ => f * m) := fun a b h => Nat.eq_of_mul_eq_mul_left hf h
  rw [← hinj.hasSum_iff]
  · convert hbase using 1
    funext m
    simp only [Function.comp_apply, A_prime_pow_closed, f, g, dvd_mul_right, ite_true,
      Nat.mul_div_cancel_left m hf]
    rw [pow_mul, show m + gK K p - 1 = m + (gK K p - 1) by omega]
  · intro k hk
    have : ¬ f ∣ k := fun ⟨m, hm⟩ => hk ⟨m, hm.symm⟩
    simp [A_prime_pow_closed, f, this]

end GaloisEuler

#print axioms GaloisEuler.A_prime_pow_closed
#print axioms GaloisEuler.localFactor_hasSum
