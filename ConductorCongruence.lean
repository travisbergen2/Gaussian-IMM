import Mathlib

/-!
# ConductorCongruence — a character that factors through d is constant on classes mod d

Generic (imports only Mathlib). If χ mod n factors through d, then χ(a) = χ(b) for a, b coprime to n
with a ≡ b (mod d). Contrapositive (`not_factorsThrough`): two units mod n that agree mod d but
have different χ-values rule out d, which is how exact conductors are pinned down.
-/

namespace CondCong

open DirichletCharacter

variable {R : Type*} [CommMonoidWithZero R] {n : ℕ} [NeZero n]

omit [NeZero n] in
theorem eq_of_modEq (χ : DirichletCharacter R n) {d : ℕ} (h : χ.FactorsThrough d) {a b : ℕ}
    (ha : a.Coprime n) (hb : b.Coprime n) (hab : a ≡ b [MOD d]) :
    χ (a : ZMod n) = χ (b : ZMod n) := by
  rw [h.eq_changeLevel, ← ZMod.coe_unitOfCoprime a ha, ← ZMod.coe_unitOfCoprime b hb,
    changeLevel_eq_cast_of_dvd, changeLevel_eq_cast_of_dvd, ZMod.coe_unitOfCoprime,
    ZMod.coe_unitOfCoprime, ZMod.cast_natCast h.dvd, ZMod.cast_natCast h.dvd,
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr hab]

omit [NeZero n] in
theorem not_factorsThrough (χ : DirichletCharacter R n) {d a b : ℕ} (ha : a.Coprime n)
    (hb : b.Coprime n) (hab : a ≡ b [MOD d]) (hne : χ (a : ZMod n) ≠ χ (b : ZMod n)) :
    ¬ χ.FactorsThrough d := fun h => hne (eq_of_modEq χ h ha hb hab)

/-- If the conductor divides d, χ factors through d. -/
theorem factorsThrough_of_conductor_dvd (χ : DirichletCharacter R n) {d : ℕ}
    (hd : χ.conductor ∣ d) (hdn : d ∣ n) : χ.FactorsThrough d :=
  (mem_conductorSet_iff_conductor_dvd χ hdn).mpr hd

end CondCong

#print axioms CondCong.eq_of_modEq
#print axioms CondCong.not_factorsThrough
