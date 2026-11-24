import Mathlib

/-!
# Q5Character — χ₋₂₀ = χ₄ · (·/5) and its values at primes

No project imports. `chi20C : DirichletCharacter ℂ 20` is the product of Mathlib's χ₄ (lifted to level 20)
and the quadratic character of ZMod 5 (lifted to level 20). Main output:

  `chi20C_prime`: for a prime p,
    χ₋₂₀(p) = 0 if p ∣ 20 (p = 2, 5),  1 if −5 is a square mod p,  −1 otherwise.

The bridge is quadratic reciprocity: (−5/p) = (−1/p)(5/p) = χ₄(p) · (p/5)  (5 ≡ 1 mod 4).
-/

open DirichletCharacter

namespace Q5

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

open scoped Classical in

/-- χ₄ as a complex Dirichlet character mod 4. -/
noncomputable def chi4C' : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

/-- (·/5) as a complex Dirichlet character mod 5. -/
noncomputable def chi5C : DirichletCharacter ℂ 5 :=
  (quadraticChar (ZMod 5)).ringHomComp (Int.castRingHom ℂ)

/-- χ₋₂₀ := χ₄ · (·/5) at level 20. -/
noncomputable def chi20C : DirichletCharacter ℂ 20 :=
  changeLevel (by norm_num : 4 ∣ 20) chi4C' * changeLevel (by norm_num : 5 ∣ 20) chi5C

theorem chi20C_apply_of_coprime {n : ℕ} (hn : Nat.Coprime n 20) :
    chi20C n = (ZMod.χ₄ n : ℂ) * (legendreSym 5 n : ℂ) := by
  have hc : IsCoprime (n : ℤ) (20 : ℕ) := Nat.isCoprime_iff_coprime.mpr hn
  rw [chi20C, MulChar.coeToFun_mul, Pi.mul_apply]
  have h1 := changeLevel_eq_cast_of_dvd' chi4C' (by norm_num : 4 ∣ 20) hc
  have h2 := changeLevel_eq_cast_of_dvd' chi5C (by norm_num : 5 ∣ 20) hc
  push_cast at h1 h2
  rw [h1, h2]
  simp [chi4C', chi5C, legendreSym]

theorem chi20C_eq_zero_of_dvd {n : ℕ} (hn : ¬ Nat.Coprime n 20) : chi20C n = 0 := by
  apply MulChar.map_nonunit
  rwa [ZMod.isUnit_iff_coprime]

open scoped Classical in
/-- **χ₋₂₀ at primes.** -/
theorem chi20C_prime {p : ℕ} (hp : p.Prime) :
    chi20C p = if p = 2 ∨ p = 5 then 0 else if IsSquare ((-5 : ℤ) : ZMod p) then 1 else -1 := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases h25 : p = 2 ∨ p = 5
  · rw [if_pos h25]
    apply chi20C_eq_zero_of_dvd
    rcases h25 with rfl | rfl <;> norm_num
  rw [if_neg h25]
  push_neg at h25
  have hcop : Nat.Coprime p 20 := by
    rw [show (20 : ℕ) = 2 ^ 2 * 5 by norm_num, Nat.coprime_mul_iff_right]
    exact ⟨Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr h25.1),
      (Nat.coprime_primes hp Nat.prime_five).mpr h25.2⟩
  rw [chi20C_apply_of_coprime hcop]
  -- (−5/p) = (−1/p)(5/p) = χ₄(p)·(p/5)
  have hrec : legendreSym 5 p = legendreSym p 5 := by
    have := legendreSym.quadratic_reciprocity_one_mod_four (p := 5) (q := p) (by norm_num) h25.1
    exact_mod_cast this.symm
  have hneg : legendreSym p (-5) = ZMod.χ₄ p * legendreSym 5 p := by
    rw [show (-5 : ℤ) = -1 * 5 by norm_num, legendreSym.mul, legendreSym.at_neg_one h25.1, hrec]
  have hne : ((-5 : ℤ) : ZMod p) ≠ 0 := by
    intro h0
    have : (p : ℤ) ∣ -5 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
    have h5' : p ∣ 5 := by
      have := Int.natAbs_dvd_natAbs.mpr this; simpa using this
    exact h25.2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h5')
  rcases legendreSym.eq_one_or_neg_one p hne with h | h
  · rw [if_pos ((legendreSym.eq_one_iff p hne).mp h)]
    rw [hneg] at h; exact_mod_cast h
  · rw [if_neg ((legendreSym.eq_neg_one_iff p).mp h)]
    rw [hneg] at h; exact_mod_cast h

end Q5

#print axioms Q5.chi20C_prime
