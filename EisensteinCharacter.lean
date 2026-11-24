import Mathlib

/-!
# EisensteinCharacter — the character χ₋₃ (step 3a of the portability experiment)

Imports Mathlib only: nothing Gaussian.

* `χ₃ : MulChar (ZMod 3) ℤ`, by table: 0 ↦ 0, 1 ↦ 1, 2 ↦ −1 (built like Mathlib's `ZMod.χ₄`).
* `chi3C : DirichletCharacter ℂ 3`, its complex version.
* Values on ℕ by residue mod 3; non-trivial; odd; **primitive mod 3**.
* The link the splitting data will use: for a prime p ≠ 3,
    χ₋₃(p) = 1  ⟺  orderOf (p : ZMod 3) = 1   (Mathlib's residue degree f = 1: split)
    χ₋₃(p) = −1 ⟺  orderOf (p : ZMod 3) = 2   (f = 2: inert)
-/

open DirichletCharacter

/-- The quadratic character mod 3, ℤ-valued. -/
def χ₃ : MulChar (ZMod 3) ℤ where
  toFun a :=
    match a with
    | 0 => 0
    | 1 => 1
    | 2 => -1
  map_one' := rfl
  map_mul' := by decide
  map_nonunit' := by decide

/-- χ₋₃ as a complex Dirichlet character mod 3. -/
def chi3C : DirichletCharacter ℂ 3 := χ₃.ringHomComp (Int.castRingHom ℂ)

theorem chi3C_apply_zmod (a : ZMod 3) : chi3C a = (χ₃ a : ℂ) := rfl

theorem χ₃_nat (n : ℕ) : χ₃ (n : ZMod 3) =
    if n % 3 = 0 then 0 else if n % 3 = 1 then 1 else -1 := by
  have h : (n : ZMod 3) = ((n % 3 : ℕ) : ZMod 3) := (ZMod.natCast_mod n 3).symm
  rw [h]
  have : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hn : n % 3 <;> rfl

theorem chi3C_nat (n : ℕ) : chi3C (n : ZMod 3) =
    if n % 3 = 0 then 0 else if n % 3 = 1 then 1 else -1 := by
  rw [chi3C_apply_zmod, χ₃_nat]; split_ifs <;> simp

theorem chi3C_one_mod_three {p : ℕ} (h : p % 3 = 1) : chi3C (p : ZMod 3) = 1 := by
  rw [chi3C_nat]; simp [h]

theorem chi3C_two_mod_three {p : ℕ} (h : p % 3 = 2) : chi3C (p : ZMod 3) = -1 := by
  rw [chi3C_nat]; simp [h]

theorem chi3C_three : chi3C ((3 : ℕ) : ZMod 3) = 0 := by rw [chi3C_nat]; simp

theorem chi3C_norm_le (n : ℕ) : ‖chi3C (n : ZMod 3)‖ ≤ 1 := by
  rw [chi3C_nat]; split_ifs <;> simp

theorem chi3C_ne_one : chi3C ≠ 1 := by
  intro h
  have hu : IsUnit ((2 : ℕ) : ZMod 3) := by rw [ZMod.isUnit_iff_coprime]; norm_num
  have h2 := congrArg (fun χ : DirichletCharacter ℂ 3 => χ ((2 : ℕ) : ZMod 3)) h
  simp only [MulChar.one_apply hu] at h2
  rw [chi3C_two_mod_three (by norm_num)] at h2
  norm_num at h2

/-- χ₋₃ is odd: χ₋₃(−1) = −1. -/
theorem chi3C_odd : chi3C.Odd := by
  show chi3C (-1) = -1
  rw [show (-1 : ZMod 3) = ((2 : ℕ) : ZMod 3) by decide, chi3C_two_mod_three (by norm_num)]

/-- **χ₋₃ is primitive mod 3** (3 is prime and χ₋₃ is non-trivial). -/
theorem chi3C_isPrimitive : chi3C.IsPrimitive := by
  rw [isPrimitive_def]
  have hd := conductor_dvd_level chi3C
  have h1 : conductor chi3C ≠ 1 := fun h => chi3C_ne_one (eq_one_iff_conductor_eq_one.mpr h)
  have h0 : conductor chi3C ≠ 0 := conductor_ne_zero _
  have hle := Nat.le_of_dvd (by norm_num) hd
  interval_cases h : conductor chi3C <;> simp_all

/-! ## The link to residue degrees -/

theorem orderOf_two_zmod3 : orderOf (2 : ZMod 3) = 2 :=
  orderOf_eq_prime (by decide) (by decide)

theorem natCast_zmod3_cases {p : ℕ} (hp3 : p % 3 ≠ 0) :
    ((p : ZMod 3) = 1 ∧ p % 3 = 1) ∨ ((p : ZMod 3) = 2 ∧ p % 3 = 2) := by
  have h : (p : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := (ZMod.natCast_mod p 3).symm
  have : p % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hp : p % 3
  · exact absurd rfl hp3
  · left; exact ⟨by rw [h]; rfl, rfl⟩
  · right; exact ⟨by rw [h]; rfl, rfl⟩

/-- For p ≢ 0 mod 3: χ₋₃(p) = 1 ⟺ p has order 1 mod 3. -/
theorem chi3C_eq_one_iff_orderOf {p : ℕ} (hp3 : p % 3 ≠ 0) :
    chi3C (p : ZMod 3) = 1 ↔ orderOf (p : ZMod 3) = 1 := by
  rcases natCast_zmod3_cases hp3 with ⟨hz, hm⟩ | ⟨hz, hm⟩
  · rw [chi3C_one_mod_three hm, hz, orderOf_one]; simp
  · rw [chi3C_two_mod_three hm, hz, orderOf_two_zmod3]; norm_num

/-- For p ≢ 0 mod 3: χ₋₃(p) = −1 ⟺ p has order 2 mod 3. -/
theorem chi3C_eq_neg_one_iff_orderOf {p : ℕ} (hp3 : p % 3 ≠ 0) :
    chi3C (p : ZMod 3) = -1 ↔ orderOf (p : ZMod 3) = 2 := by
  rcases natCast_zmod3_cases hp3 with ⟨hz, hm⟩ | ⟨hz, hm⟩
  · rw [chi3C_one_mod_three hm, hz, orderOf_one]; norm_num
  · rw [chi3C_two_mod_three hm, hz, orderOf_two_zmod3]; simp

#print axioms chi3C_isPrimitive
#print axioms chi3C_odd
#print axioms chi3C_eq_one_iff_orderOf
#print axioms chi3C_eq_neg_one_iff_orderOf
#print axioms chi3C_ne_one
#print axioms chi3C_nat
#print axioms chi3C_norm_le
