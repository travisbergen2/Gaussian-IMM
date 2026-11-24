import Cyclo7EulerProduct

/-!
# Cyclo7Characters — χ₇ generates all Dirichlet characters mod 7

* `pow_bijective`: k ↦ χ₇ᵏ (k : Fin 6) is a bijection onto `DirichletCharacter ℂ 7`.
* `nontrivial_iff`: the nontrivial characters mod 7 are exactly χ₇, …, χ₇⁵.
* `LSeries_A_eq_zeta_mul_prod_nontrivial`: ζ_{ℚ(ζ₇)} = ζ · ∏ over all nontrivial characters mod 7.
A character mod 7 is determined by its value at the generator 3, a sixth root of unity.
-/

open Complex DirichletCharacter

namespace Cyclo7

theorem isUnit_three : IsUnit (3 : ZMod 7) := ⟨⟨3, 5, by decide, by decide⟩, rfl⟩

theorem chi7_pow_three (k : ℕ) : (chi7 ^ k) 3 = ω ^ k := by
  rcases k with _ | k
  · rw [pow_zero, pow_zero]; exact MulChar.one_apply isUnit_three
  · rw [MulChar.pow_apply' _ (Nat.succ_ne_zero k), chi7_three]

/-- A character mod 7 is determined by its value at 3. -/
theorem eq_of_apply_three {ψ φ : DirichletCharacter ℂ 7} (h : ψ 3 = φ 3) : ψ = φ := by
  apply MulChar.ext
  intro u
  have hu : (u : ZMod 7) ≠ 0 := u.ne_zero
  rcases cases_unit _ hu with h' | h' | h' | h' | h' | h' <;> rw [h']
  · simp
  · rw [show (2 : ZMod 7) = 3 ^ 2 by decide, map_pow, map_pow, h]
  · exact h
  · rw [show (4 : ZMod 7) = 3 ^ 4 by decide, map_pow, map_pow, h]
  · rw [show (5 : ZMod 7) = 3 ^ 5 by decide, map_pow, map_pow, h]
  · rw [show (6 : ZMod 7) = 3 ^ 3 by decide, map_pow, map_pow, h]

theorem apply_three_pow_six (ψ : DirichletCharacter ℂ 7) : ψ 3 ^ 6 = 1 := by
  rw [← map_pow, show (3 : ZMod 7) ^ 6 = 1 by decide, map_one]

/-- **Every character mod 7 is a power of χ₇.** -/
theorem exists_pow (ψ : DirichletCharacter ℂ 7) : ∃ k : Fin 6, ψ = chi7 ^ (k : ℕ) := by
  obtain ⟨i, hi, hω⟩ := ω_prim.eq_pow_of_pow_eq_one (apply_three_pow_six ψ)
  exact ⟨⟨i, hi⟩, eq_of_apply_three (by rw [chi7_pow_three]; exact hω.symm)⟩

theorem pow_injective : Function.Injective (fun k : Fin 6 => chi7 ^ (k : ℕ)) := by
  intro a b hab
  have h3 := congrArg (fun ψ : DirichletCharacter ℂ 7 => ψ 3) hab
  simp only [chi7_pow_three] at h3
  exact Fin.ext (ω_prim.pow_inj a.2 b.2 h3)

theorem pow_bijective : Function.Bijective (fun k : Fin 6 => chi7 ^ (k : ℕ)) :=
  ⟨pow_injective, fun ψ => (exists_pow ψ).imp fun _ h => h.symm⟩

/-- **The nontrivial characters mod 7 are exactly χ₇, …, χ₇⁵.** -/
theorem nontrivial_iff (ψ : DirichletCharacter ℂ 7) :
    ψ ≠ 1 ↔ ∃ j : Fin 5, ψ = chi7 ^ ((j : ℕ) + 1) := by
  constructor
  · intro hψ
    obtain ⟨k, rfl⟩ := exists_pow ψ
    rcases k with ⟨_ | k, hk⟩
    · exact absurd (by simp) hψ
    · exact ⟨⟨k, by omega⟩, rfl⟩
  · rintro ⟨j, rfl⟩ h
    have := @pow_injective ⟨(j : ℕ) + 1, by omega⟩ 0 (by
      show chi7 ^ ((j : ℕ) + 1) = chi7 ^ ((0 : Fin 6) : ℕ); rw [Fin.val_zero, pow_zero]; exact h)
    have h' := congrArg Fin.val this
    change (j : ℕ) + 1 = 0 at h'
    omega

/-- The nontrivial characters mod 7, indexed by Fin 5. -/
noncomputable def nontrivialEquiv : Fin 5 ≃ {ψ : DirichletCharacter ℂ 7 // ψ ≠ 1} :=
  Equiv.ofBijective (fun j => ⟨chi7 ^ ((j : ℕ) + 1), (nontrivial_iff _).mpr ⟨j, rfl⟩⟩)
    ⟨fun a b h => by
      have := @pow_injective ⟨(a : ℕ) + 1, by omega⟩ ⟨(b : ℕ) + 1, by omega⟩
        (congrArg Subtype.val h)
      exact Fin.ext (by simpa [Fin.ext_iff] using this),
     fun ⟨ψ, hψ⟩ => ((nontrivial_iff ψ).mp hψ).imp fun _ h => Subtype.ext h.symm⟩

noncomputable instance : Fintype {ψ : DirichletCharacter ℂ 7 // ψ ≠ 1} :=
  Fintype.ofEquiv _ nontrivialEquiv

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {7} ℚ K]

/-- **ζ_{ℚ(ζ₇)} = ζ · ∏ over all nontrivial Dirichlet characters mod 7.** -/
theorem LSeries_A_eq_zeta_mul_prod_nontrivial {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (IdealCount.A (NumberField.RingOfIntegers K) n : ℂ)) s =
      riemannZeta s * ∏ ψ : {ψ : DirichletCharacter ℂ 7 // ψ ≠ 1}, LSeries (fun n => ψ.1 n) s := by
  rw [LSeries_A_eq_zeta_mul_L5 hs, ← nontrivialEquiv.prod_comp]
  rfl

end Cyclo7

#print axioms Cyclo7.pow_bijective
#print axioms Cyclo7.nontrivial_iff
#print axioms Cyclo7.LSeries_A_eq_zeta_mul_prod_nontrivial
