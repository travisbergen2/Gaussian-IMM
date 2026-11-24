import QuadraticEulerProduct
import EisensteinLocalInstance

/-!
# EisensteinEulerProduct — the thin instance: Σ a₋₃(n) n⁻ˢ = ζ(s) · L(s, χ₋₃)

K is any field with `IsCyclotomicExtension {3} ℚ K` (so K ≅ ℚ(ζ₃) = ℚ(√−3)).
Everything is discharged from Mathlib's cyclotomic results and `EisensteinLocalInstance`:
* `IsGalois ℚ K` (cyclotomic), `finrank ℚ K = φ(3) = 2`;
* `chi3C_matches_splitting`: χ₋₃(p) = c_p for every prime p
  (p ≡ 1: split, c = 1; p ≡ 2: inert, f = ord(2) = 2, c = −1; p = 3: one prime, f = 1, c = 0).
Then the generic `QuadEuler.LSeries_A_eq_zeta_mul_L` gives the identity.
No Gaussian module is imported.
-/

open Ideal NumberField IsCyclotomicExtension.Rat QuadEuler

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]

theorem eis_isGalois : IsGalois ℚ K := IsCyclotomicExtension.isGalois {3} ℚ K

theorem eis_finrank : Module.finrank ℚ K = 2 := by
  rw [IsCyclotomicExtension.Rat.finrank (k := 3) K]; rfl

theorem chi3C_matches_splitting (p : ℕ) (hp : p.Prime) :
    chi3C (p : ZMod 3) = splitChar K p := by
  have : Fact p.Prime := ⟨hp⟩
  unfold splitChar gP fP
  by_cases h3 : p = 3
  · subst h3
    have : IsCyclotomicExtension {(3 : ℕ) ^ 1} ℚ K := by simpa
    rw [ncard_primesOver_of_prime 3 K, inertiaDegIn_eq_of_prime 3 K, chi3C_three]
    norm_num
  · have hp3 : p % 3 ≠ 0 := by
      intro h0
      exact h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h0)).symm
    rcases natCast_zmod3_cases hp3 with ⟨hz, hm⟩ | ⟨hz, hm⟩
    · rw [ncard_split (K := K) hm, chi3C_one_mod_three hm]; simp
    · rw [chi3C_two_mod_three hm, ncard_inert (K := K) hm,
        inertiaDegIn_eq_of_not_dvd p K (not_dvd_three hp3), hz, orderOf_two_zmod3]
      norm_num

/-- **Eisenstein Dedekind factorization**, as a specialization of the generic quadratic
Euler product: Σ a₋₃(n) n⁻ˢ = ζ(s) · L(s, χ₋₃) for Re s > 1. -/
theorem eisenstein_LSeries_eq_zeta_mul_L {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (a3 K n : ℂ)) s = riemannZeta s * LSeries (fun n => chi3C n) s := by
  have := eis_isGalois (K := K)
  exact LSeries_A_eq_zeta_mul_L eis_finrank chi3C chi3C_matches_splitting hs

#print axioms chi3C_matches_splitting
#print axioms eisenstein_LSeries_eq_zeta_mul_L
