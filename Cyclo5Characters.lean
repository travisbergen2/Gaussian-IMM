import Cyclo5EulerProduct

/-!
# Cyclo5Characters — χ₅ generates all Dirichlet characters mod 5

* `pow_bijective`: k ↦ χ₅ᵏ (k : Fin 4) is a bijection onto `DirichletCharacter ℂ 5`.
* `nontrivial_iff`: the nontrivial characters mod 5 are exactly χ₅, χ₅², χ₅³.
* `LSeries_A_eq_zeta_mul_prod_nontrivial`: the ℚ(ζ₅) factorization, restated as
  ζ(s) · ∏ over **all** nontrivial characters mod 5.
A character mod 5 is determined by its value at the generator 2, which is a fourth root of unity.
-/

open Complex DirichletCharacter

namespace Cyclo5

instance fact_prime_five' : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

theorem isUnit_two : IsUnit (2 : ZMod 5) := ⟨⟨2, 3, by decide, by decide⟩, rfl⟩

theorem fourth_roots {z : ℂ} (h : z ^ 4 = 1) : z = 1 ∨ z = I ∨ z = -1 ∨ z = -I := by
  have : (z - 1) * (z + 1) * (z - I) * (z + I) = 0 := by
    linear_combination h + (1 - z ^ 2) * I_sq
  rcases mul_eq_zero.mp this with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · left; linear_combination h3
      · right; right; left; linear_combination h3
    · right; left; linear_combination h2
  · right; right; right; linear_combination h1

theorem chi5_pow_two (k : ℕ) : (chi5 ^ k) 2 = I ^ k := by
  rcases k with _ | k
  · rw [pow_zero, pow_zero]; exact MulChar.one_apply isUnit_two
  · rw [MulChar.pow_apply' _ (Nat.succ_ne_zero k), chi5_two]

/-- A character mod 5 is determined by its value at 2. -/
theorem eq_of_apply_two {ψ φ : DirichletCharacter ℂ 5} (h : ψ 2 = φ 2) : ψ = φ := by
  apply MulChar.ext
  intro u
  have hu : (u : ZMod 5) ≠ 0 := u.ne_zero
  rcases cases_unit _ hu with h' | h' | h' | h' <;> rw [h']
  · simp
  · exact h
  · rw [show (3 : ZMod 5) = 2 ^ 3 by decide, map_pow, map_pow, h]
  · rw [show (4 : ZMod 5) = 2 ^ 2 by decide, map_pow, map_pow, h]

theorem apply_two_pow_four (ψ : DirichletCharacter ℂ 5) : ψ 2 ^ 4 = 1 := by
  rw [← map_pow, show (2 : ZMod 5) ^ 4 = 1 by decide, map_one]

/-- **Every character mod 5 is a power of χ₅.** -/
theorem exists_pow (ψ : DirichletCharacter ℂ 5) : ∃ k : Fin 4, ψ = chi5 ^ (k : ℕ) := by
  rcases fourth_roots (apply_two_pow_four ψ) with h | h | h | h
  · exact ⟨0, eq_of_apply_two (by rw [h, chi5_pow_two]; simp)⟩
  · exact ⟨1, eq_of_apply_two (by rw [h, chi5_pow_two]; simp)⟩
  · exact ⟨2, eq_of_apply_two (by rw [h, chi5_pow_two]; simp [I_sq])⟩
  · exact ⟨3, eq_of_apply_two (by rw [h, chi5_pow_two]; simp [pow_succ, I_mul_I])⟩

theorem I_pow_injective {a b : Fin 4} (h : I ^ (a : ℕ) = I ^ (b : ℕ)) : a = b := by
  fin_cases a <;> fin_cases b <;>
    first
    | rfl
    | (exfalso; norm_num [Complex.ext_iff, pow_succ] at h)

theorem pow_injective : Function.Injective (fun k : Fin 4 => chi5 ^ (k : ℕ)) := by
  intro a b hab
  have h2 := congrArg (fun ψ : DirichletCharacter ℂ 5 => ψ 2) hab
  simp only [chi5_pow_two] at h2
  exact I_pow_injective h2

theorem pow_bijective : Function.Bijective (fun k : Fin 4 => chi5 ^ (k : ℕ)) :=
  ⟨pow_injective, fun ψ => (exists_pow ψ).imp fun _ h => h.symm⟩

/-- **The nontrivial characters mod 5 are exactly χ₅, χ₅², χ₅³.** -/
theorem nontrivial_iff (ψ : DirichletCharacter ℂ 5) :
    ψ ≠ 1 ↔ ∃ j : Fin 3, ψ = chi5 ^ ((j : ℕ) + 1) := by
  constructor
  · intro hψ
    obtain ⟨k, rfl⟩ := exists_pow ψ
    fin_cases k
    · exact absurd (by simp) hψ
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · rintro ⟨j, rfl⟩ h
    have := @pow_injective ⟨(j : ℕ) + 1, by omega⟩ 0 (by
      show chi5 ^ ((j : ℕ) + 1) = chi5 ^ ((0 : Fin 4) : ℕ); rw [Fin.val_zero, pow_zero]; exact h)
    have h' := congrArg Fin.val this
    change (j : ℕ) + 1 = 0 at h'
    omega

/-- The nontrivial characters mod 5, indexed by Fin 3. -/
noncomputable def nontrivialEquiv : Fin 3 ≃ {ψ : DirichletCharacter ℂ 5 // ψ ≠ 1} :=
  Equiv.ofBijective (fun j => ⟨chi5 ^ ((j : ℕ) + 1), (nontrivial_iff _).mpr ⟨j, rfl⟩⟩)
    ⟨fun a b h => by
      have := @pow_injective ⟨(a : ℕ) + 1, by omega⟩ ⟨(b : ℕ) + 1, by omega⟩
        (congrArg Subtype.val h)
      exact Fin.ext (by simpa [Fin.ext_iff] using this),
     fun ⟨ψ, hψ⟩ => ((nontrivial_iff ψ).mp hψ).imp fun _ h => Subtype.ext h.symm⟩

noncomputable instance : Fintype {ψ : DirichletCharacter ℂ 5 // ψ ≠ 1} :=
  Fintype.ofEquiv _ nontrivialEquiv

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K]

/-- **ζ_{ℚ(ζ₅)} = ζ · ∏ over all nontrivial Dirichlet characters mod 5.** -/
theorem LSeries_A_eq_zeta_mul_prod_nontrivial {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (IdealCount.A (NumberField.RingOfIntegers K) n : ℂ)) s =
      riemannZeta s * ∏ ψ : {ψ : DirichletCharacter ℂ 5 // ψ ≠ 1}, LSeries (fun n => ψ.1 n) s := by
  rw [LSeries_A_eq_zeta_mul_L3 hs, ← nontrivialEquiv.prod_comp]
  rfl

end Cyclo5

#print axioms Cyclo5.pow_bijective
#print axioms Cyclo5.nontrivial_iff
#print axioms Cyclo5.LSeries_A_eq_zeta_mul_prod_nontrivial
