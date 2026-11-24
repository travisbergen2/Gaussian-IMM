import Mathlib

/-!
# Cyclo7Character — an order-6 Dirichlet character mod 7

No project imports. 3 generates (ZMod 7)ˣ (3, 2, 6, 4, 5, 1 = 3¹,…,3⁶). With ω = e^{2πi/6}:
χ₇(3ᵏ) = ωᵏ, χ₇(0) = 0. Built from a decidable discrete-log table `dlog`;
multiplicativity reduces to dlog(ab) ≡ dlog a + dlog b (mod 6), checked by `decide`.
-/

open Complex

namespace Cyclo7

instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- ω = e^{2πi/6}, a primitive sixth root of unity. -/
noncomputable def ω : ℂ := exp (2 * Real.pi * I / 6)

theorem ω_prim : IsPrimitiveRoot ω 6 := Complex.isPrimitiveRoot_exp 6 (by norm_num)

theorem ω_pow_six : ω ^ 6 = 1 := ω_prim.pow_eq_one

theorem ω_rel : ω ^ 2 - ω + 1 = 0 := by
  have h3 : ω ^ 3 = -1 := by
    have hsq : (ω ^ 3) ^ 2 = 1 := by rw [← pow_mul]; exact ω_pow_six
    have hne : ω ^ 3 ≠ 1 := ω_prim.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
    rcases mul_self_eq_one_iff.mp (show ω ^ 3 * ω ^ 3 = 1 by rw [← sq]; exact hsq) with h | h
    · exact absurd h hne
    · exact h
  have hne : ω + 1 ≠ 0 := by
    intro h
    have : ω = -1 := by linear_combination h
    have h2 : ω ^ 2 = 1 := by rw [this]; norm_num
    exact ω_prim.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num) h2
  have : (ω + 1) * (ω ^ 2 - ω + 1) = 0 := by linear_combination h3
  exact (mul_eq_zero.mp this).resolve_left hne

/-- Discrete logarithm base 3 on ZMod 7 (0 ↦ 0 by convention). -/
def dlog : ZMod 7 → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | 3 => 1
  | 4 => 4
  | 5 => 5
  | 6 => 3

theorem dlog_mul : ∀ a b : ZMod 7, a ≠ 0 → b ≠ 0 → dlog (a * b) = (dlog a + dlog b) % 6 := by
  decide

theorem ω_pow_mod (m : ℕ) : ω ^ (m % 6) = ω ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m 6, pow_add, pow_mul, ω_pow_six, one_pow, mul_one]

/-- The order-6 character mod 7. -/
noncomputable def chi7 : DirichletCharacter ℂ 7 where
  toFun a := if a = 0 then 0 else ω ^ dlog a
  map_one' := by simp [dlog]
  map_mul' a b := by
    by_cases ha : a = 0
    · simp [ha]
    by_cases hb : b = 0
    · simp [hb]
    simp only [ha, hb, mul_eq_zero, or_self, if_false]
    rw [dlog_mul a b ha hb, ω_pow_mod, pow_add]
  map_nonunit' a ha := by
    have : a = 0 := by
      by_contra h; exact ha (Ne.isUnit h)
    simp [this]

theorem chi7_apply_of_ne {a : ZMod 7} (ha : a ≠ 0) : chi7 a = ω ^ dlog a := by
  show (if a = 0 then 0 else ω ^ dlog a) = _
  rw [if_neg ha]

theorem chi7_zero : chi7 0 = 0 := MulChar.map_zero _
theorem chi7_one : chi7 1 = 1 := by rw [chi7_apply_of_ne (by decide)]; rfl
theorem chi7_two : chi7 2 = ω ^ 2 := by rw [chi7_apply_of_ne (by decide)]; rfl
theorem chi7_three : chi7 3 = ω := by rw [chi7_apply_of_ne (by decide)]; show ω ^ 1 = ω; simp
theorem chi7_four : chi7 4 = ω ^ 4 := by rw [chi7_apply_of_ne (by decide)]; rfl
theorem chi7_five : chi7 5 = ω ^ 5 := by rw [chi7_apply_of_ne (by decide)]; rfl
theorem chi7_six : chi7 6 = ω ^ 3 := by rw [chi7_apply_of_ne (by decide)]; rfl

end Cyclo7

#print axioms Cyclo7.ω_rel
#print axioms Cyclo7.chi7_six
