import Mathlib

/-!
# Cyclo5Character — the quartic Dirichlet character mod 5 and its powers

No project imports. χ₅ is defined by its table with values in ℤ[i] (so `decide` checks
multiplicativity), then sent to ℂ. Since 2 generates (ZMod 5)ˣ: χ₅(2) = i, χ₅(4) = −1, χ₅(3) = −i.
The three nontrivial characters mod 5 are χ₅, χ₅², χ₅³.
-/

open Complex

namespace Cyclo5

/-- The quartic character mod 5 with values in ℤ[i]. -/
def χZ : MulChar (ZMod 5) GaussianInt where
  toFun a :=
    match a with
    | 0 => 0
    | 1 => 1
    | 2 => ⟨0, 1⟩
    | 3 => ⟨0, -1⟩
    | 4 => -1
  map_one' := rfl
  map_mul' := by decide
  map_nonunit' := by decide

/-- The quartic character mod 5 as a complex Dirichlet character. -/
noncomputable def chi5 : DirichletCharacter ℂ 5 := χZ.ringHomComp GaussianInt.toComplex

theorem chi5_zero : chi5 0 = 0 := by
  show GaussianInt.toComplex (χZ 0) = 0
  rw [show χZ 0 = 0 from rfl, map_zero]
theorem chi5_one : chi5 1 = 1 := by simp
theorem chi5_two : chi5 2 = I := by
  show GaussianInt.toComplex (χZ 2) = I
  rw [show χZ 2 = ⟨0, 1⟩ from rfl]; simp [GaussianInt.toComplex_def]
theorem chi5_three : chi5 3 = -I := by
  show GaussianInt.toComplex (χZ 3) = -I
  rw [show χZ 3 = ⟨0, -1⟩ from rfl]; simp [GaussianInt.toComplex_def]
theorem chi5_four : chi5 4 = -1 := by
  show GaussianInt.toComplex (χZ 4) = -1
  rw [show χZ 4 = -1 from rfl]; simp

end Cyclo5

#print axioms Cyclo5.chi5_two
