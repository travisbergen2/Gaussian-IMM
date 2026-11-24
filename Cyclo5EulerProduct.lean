import AbelianEulerProduct
import Cyclo5Character

/-!
# Cyclo5EulerProduct — ζ_{ℚ(ζ₅)}: Σ A(n) n⁻ˢ = ζ(s) · L(s, χ₅) L(s, χ₅²) L(s, χ₅³)

K: any field with `IsCyclotomicExtension {5} ℚ K` (degree 4, Galois group (ZMod 5)ˣ, cyclic).
Splitting from Mathlib's cyclotomic results:
* p ≠ 5: e = 1, f = ord(p mod 5), g = 4/f;
* p = 5: one prime, f = 1 (totally ramified).
Local check: (1 − x^f)^{4/f} = (1 − x)(1 − c x)(1 − c² x)(1 − c³ x) with c = χ₅(p) ∈ {1, i, −i, −1}.
At p = 5 every χ₅ᵏ vanishes and the factor is (1 − x), which ζ supplies.
-/

open Ideal NumberField IsCyclotomicExtension.Rat GaloisEuler Complex

namespace Cyclo5

theorem orderOf_one' : orderOf (1 : ZMod 5) = 1 := orderOf_one
theorem orderOf_two : orderOf (2 : ZMod 5) = 4 :=
  (orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩
theorem orderOf_three : orderOf (3 : ZMod 5) = 4 :=
  (orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩
theorem orderOf_four : orderOf (4 : ZMod 5) = 2 :=
  (orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩

theorem pow_apply (k : ℕ) (r : ZMod 5) : (chi5 ^ (k + 1)) r = chi5 r ^ (k + 1) :=
  MulChar.pow_apply' _ (Nat.succ_ne_zero k) r

theorem cases_unit (r : ZMod 5) (hr : r ≠ 0) : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by
  revert r; decide

/-- The local identity at a unit residue r. -/
theorem local_identity (r : ZMod 5) (hr : r ≠ 0) (x : ℂ) :
    (1 - x ^ orderOf r) ^ (4 / orderOf r) =
      (1 - x) * ∏ j : Fin 3, (1 - (chi5 ^ ((j : ℕ) + 1)) r * x) := by
  simp only [Fin.prod_univ_three, pow_apply, Fin.val_zero, Fin.val_one, Fin.val_two]
  rcases cases_unit r hr with rfl | rfl | rfl | rfl
  · rw [orderOf_one', chi5_one]; ring
  · rw [orderOf_two, chi5_two]
    norm_num
    linear_combination (x ^ 2 - x ^ 4) * I_sq
  · rw [orderOf_three, chi5_three]
    norm_num
    linear_combination (x ^ 2 - x ^ 4 - x * I - x ^ 2 * I ^ 2 + x ^ 3 * I + x ^ 4 * I ^ 2) * I_sq
  · rw [orderOf_four, chi5_four]; ring

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K]

instance isGalois5 : IsGalois ℚ K := IsCyclotomicExtension.isGalois {5} ℚ K

theorem fundamental5 (p : ℕ) [Fact p.Prime] :
    gK K p * ((span {(p : ℤ)}).ramificationIdxIn (𝓞 K) * fK K p) = 4 := by
  rw [gK, fK, ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn _ (𝓞 K) Gal(K/ℚ),
    IsGaloisGroup.card_eq_finrank Gal(K/ℚ) ℚ K, finrank (k := 5) K]
  rfl

/-- **χ₅, χ₅², χ₅³ match the splitting of every prime in ℚ(ζ₅).** -/
theorem hloc (p : ℕ) (hp : p.Prime) (x : ℂ) :
    (1 - x ^ fK K p) ^ gK K p = (1 - x) * ∏ j : Fin 3, (1 - (chi5 ^ ((j : ℕ) + 1)) (p : ZMod 5) * x) := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases h5 : p = 5
  · subst h5
    have : IsCyclotomicExtension {(5 : ℕ) ^ 1} ℚ K := by simpa
    rw [gK, fK, ncard_primesOver_of_prime 5 K, inertiaDegIn_eq_of_prime 5 K,
      show ((5 : ℕ) : ZMod 5) = 0 from rfl]
    simp [pow_apply, chi5_zero]
  · have hnd : ¬ p ∣ 5 := fun h => h5 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h)
    have hr : (p : ZMod 5) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun h => h5 ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp h).symm
    have hf : fK K p = orderOf (p : ZMod 5) := inertiaDegIn_eq_of_not_dvd p K hnd
    have he : (span {(p : ℤ)}).ramificationIdxIn (𝓞 K) = 1 := ramificationIdxIn_eq_of_not_dvd p K hnd
    have hfun := fundamental5 (K := K) p
    rw [he, one_mul] at hfun
    have hpos : 0 < fK K p := fK_pos p
    have hg : gK K p = 4 / fK K p := by
      rw [← hfun, Nat.mul_div_cancel _ hpos]
    rw [hg, hf]
    exact local_identity _ hr x

/-- **Dedekind factorization for ℚ(ζ₅):** Σ A(n) n⁻ˢ = ζ(s) · L(χ₅) · L(χ₅²) · L(χ₅³), Re s > 1. -/
theorem LSeries_A_eq_zeta_mul_L3 {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (IdealCount.A (𝓞 K) n : ℂ)) s =
      riemannZeta s * ∏ j : Fin 3, LSeries (fun n => (chi5 ^ ((j : ℕ) + 1)) n) s :=
  LSeries_A_eq_zeta_mul_prod (fun j : Fin 3 => chi5 ^ ((j : ℕ) + 1)) hloc hs

end Cyclo5

#print axioms Cyclo5.local_identity
#print axioms Cyclo5.hloc
#print axioms Cyclo5.LSeries_A_eq_zeta_mul_L3
