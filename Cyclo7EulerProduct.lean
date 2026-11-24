import AbelianEulerProduct
import Cyclo7Character

/-!
# Cyclo7EulerProduct — ζ_{ℚ(ζ₇)} = ζ · ∏_{j=1}^{5} L(s, χ₇ʲ)

K: any field with `IsCyclotomicExtension {7} ℚ K` (degree 6, Galois group (ZMod 7)ˣ, cyclic of order 6).
Splitting from Mathlib's cyclotomic results:
* p ≠ 7: e = 1, f = ord(p mod 7) ∈ {1, 2, 3, 6}, g = 6/f;
* p = 7: one prime, f = 1 (totally ramified, e = 6).
Local identity, checked for each unit residue r:
  (1 − x^f)^{6/f} = (1 − x) ∏_{j=1}^{5} (1 − χ₇(r)ʲ x),
using only ω² − ω + 1 = 0 (coefficients computed offline, verified by `linear_combination`).
The general theorem `GaloisEuler.LSeries_A_eq_zeta_mul_prod` is used unchanged.
-/

open Ideal NumberField IsCyclotomicExtension.Rat GaloisEuler Complex

namespace Cyclo7

theorem orderOf_one' : orderOf (1 : ZMod 7) = 1 := orderOf_one
theorem orderOf_two : orderOf (2 : ZMod 7) = 3 :=
  (orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩
theorem orderOf_three : orderOf (3 : ZMod 7) = 6 :=
  (orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩
theorem orderOf_four : orderOf (4 : ZMod 7) = 3 :=
  (orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩
theorem orderOf_five : orderOf (5 : ZMod 7) = 6 :=
  (orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩
theorem orderOf_six : orderOf (6 : ZMod 7) = 2 :=
  (orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩

theorem pow_apply (k : ℕ) (r : ZMod 7) : (chi7 ^ (k + 1)) r = chi7 r ^ (k + 1) :=
  MulChar.pow_apply' _ (Nat.succ_ne_zero k) r

theorem cases_unit (r : ZMod 7) (hr : r ≠ 0) :
    r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 := by
  revert r; decide

/-- The local identity at a unit residue r. -/
theorem local_identity (r : ZMod 7) (hr : r ≠ 0) (x : ℂ) :
    (1 - x ^ orderOf r) ^ (6 / orderOf r) =
      (1 - x) * ∏ j : Fin 5, (1 - (chi7 ^ ((j : ℕ) + 1)) r * x) := by
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.val_zero, Fin.val_succ, pow_apply, mul_one]
  rcases cases_unit r hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [orderOf_one', chi7_one]; ring
  · rw [orderOf_two, chi7_two]
    linear_combination (-ω^28*x^6 + ω^28*x^5 - ω^27*x^6 + ω^27*x^5 + ω^26*x^5 - ω^26*x^4 + ω^25*x^6 - ω^25*x^4 + ω^24*x^6 - ω^24*x^4 - ω^22*x^6 + ω^22*x^5 - ω^22*x^4 + ω^22*x^3 - ω^21*x^6 + ω^21*x^5 - ω^21*x^4 + ω^21*x^3 + ω^20*x^5 - 2*ω^20*x^4 + ω^20*x^3 + ω^19*x^6 - ω^19*x^4 + ω^18*x^6 - 2*ω^18*x^4 + ω^18*x^3 - ω^17*x^4 + ω^17*x^3 - ω^16*x^6 - ω^16*x^4 + 3*ω^16*x^3 - ω^16*x^2 - ω^15*x^6 + 2*ω^15*x^3 - ω^15*x^2 - ω^14*x^4 + 2*ω^14*x^3 - ω^14*x^2 + ω^13*x^6 - ω^13*x^4 + ω^12*x^6 - ω^12*x^4 + ω^12*x^3 - ω^12*x^2 + ω^11*x^3 - ω^11*x^2 - ω^10*x^6 + 3*ω^10*x^3 - 2*ω^10*x^2 - ω^9*x^6 + 2*ω^9*x^3 - ω^9*x^2 + ω^8*x^3 - 2*ω^8*x^2 + ω^8*x + ω^7*x^6 - ω^7*x^3 - ω^7*x^2 + ω^7*x + ω^6*x^6 - ω^6*x^3 - ω^6*x^2 + ω^6*x - ω^4*x^6 + 2*ω^4*x^3 - ω^4*x^2 - ω^3*x^6 + 2*ω^3*x^3 - ω^3*x^2 - ω^2*x^2 + ω^2*x + ω*x^6 - 2*ω*x^3 + ω*x + x^6 - 2*x^3 + x) * ω_rel
  · rw [orderOf_three, chi7_three]
    linear_combination (-ω^13*x^6 + ω^13*x^5 - ω^12*x^6 + 2*ω^12*x^5 - ω^12*x^4 + 2*ω^11*x^5 - 2*ω^11*x^4 + ω^10*x^6 + ω^10*x^5 - 3*ω^10*x^4 + ω^10*x^3 + ω^9*x^6 - 3*ω^9*x^4 + 2*ω^9*x^3 - 3*ω^8*x^4 + 3*ω^8*x^3 - ω^7*x^6 - 2*ω^7*x^4 + 4*ω^7*x^3 - ω^7*x^2 - ω^6*x^6 - ω^6*x^4 + 4*ω^6*x^3 - 2*ω^6*x^2 + 3*ω^5*x^3 - 3*ω^5*x^2 + ω^4*x^6 + 2*ω^4*x^3 - 3*ω^4*x^2 + ω^3*x^6 + ω^3*x^3 - 3*ω^3*x^2 + ω^3*x - 2*ω^2*x^2 + 2*ω^2*x - ω*x^6 - ω*x^2 + 2*ω*x - x^6 + x) * ω_rel
  · rw [orderOf_four, chi7_four]
    linear_combination (-ω^58*x^6 + ω^58*x^5 - ω^57*x^6 + ω^57*x^5 + ω^55*x^6 - ω^55*x^5 + ω^54*x^6 - ω^54*x^4 + ω^53*x^5 - ω^53*x^4 - ω^52*x^6 + ω^52*x^5 - ω^51*x^6 + ω^51*x^4 + ω^49*x^6 - ω^49*x^4 + ω^48*x^6 - ω^48*x^4 - ω^46*x^6 + ω^46*x^5 - ω^46*x^4 + ω^46*x^3 - ω^45*x^6 + ω^45*x^5 - ω^45*x^4 + ω^45*x^3 + ω^43*x^6 - ω^43*x^5 + ω^43*x^4 - ω^43*x^3 + ω^42*x^6 - ω^42*x^4 + ω^41*x^5 - 2*ω^41*x^4 + ω^41*x^3 - ω^40*x^6 + ω^40*x^5 - ω^40*x^4 + ω^40*x^3 - ω^39*x^6 + ω^39*x^4 - ω^38*x^4 + ω^38*x^3 + ω^37*x^6 - 2*ω^37*x^4 + ω^37*x^3 + ω^36*x^6 - ω^36*x^4 + ω^35*x^4 - ω^35*x^3 - ω^34*x^6 + 2*ω^34*x^3 - ω^34*x^2 - ω^33*x^6 - ω^33*x^4 + 3*ω^33*x^3 - ω^33*x^2 - ω^32*x^4 + ω^32*x^3 + ω^31*x^6 - 2*ω^31*x^3 + ω^31*x^2 + ω^30*x^6 - ω^30*x^4 - ω^29*x^4 + 2*ω^29*x^3 - ω^29*x^2 - ω^28*x^6 + 2*ω^28*x^3 - ω^28*x^2 - ω^27*x^6 + ω^27*x^4 + ω^26*x^3 - ω^26*x^2 + ω^25*x^6 - ω^25*x^4 + ω^25*x^3 - ω^25*x^2 + ω^24*x^6 - ω^24*x^4 - ω^23*x^3 + ω^23*x^2 - ω^22*x^6 + 2*ω^22*x^3 - ω^22*x^2 - ω^21*x^6 + 3*ω^21*x^3 - 2*ω^21*x^2 + ω^20*x^3 - ω^20*x^2 + ω^19*x^6 - 2*ω^19*x^3 + ω^19*x^2 + ω^18*x^6 - ω^18*x^3 - ω^18*x^2 + ω^18*x + ω^17*x^3 - 2*ω^17*x^2 + ω^17*x - ω^16*x^6 + 2*ω^16*x^3 - ω^16*x^2 - ω^15*x^6 + ω^15*x^3 + ω^15*x^2 - ω^15*x + ω^13*x^6 - ω^13*x^3 - ω^13*x^2 + ω^13*x + ω^12*x^6 - ω^12*x^3 - ω^12*x^2 + ω^12*x - ω^10*x^6 + 2*ω^10*x^3 - ω^10*x^2 - ω^9*x^6 + 2*ω^9*x^3 - ω^9*x^2 + ω^7*x^6 - 2*ω^7*x^3 + ω^7*x^2 + ω^6*x^6 - 2*ω^6*x^3 + ω^6*x - ω^5*x^2 + ω^5*x - ω^4*x^6 + 2*ω^4*x^3 - ω^4*x^2 - ω^3*x^6 + 2*ω^3*x^3 - ω^3*x + ω*x^6 - 2*ω*x^3 + ω*x + x^6 - 2*x^3 + x) * ω_rel
  · rw [orderOf_five, chi7_five]
    linear_combination (-ω^73*x^6 + ω^73*x^5 - ω^72*x^6 + ω^72*x^5 + ω^70*x^6 - ω^70*x^5 + ω^69*x^6 - ω^69*x^5 + ω^68*x^5 - ω^68*x^4 - ω^67*x^6 + 2*ω^67*x^5 - ω^67*x^4 - ω^66*x^6 + ω^66*x^5 - ω^65*x^5 + ω^65*x^4 + ω^64*x^6 - 2*ω^64*x^5 + ω^64*x^4 + ω^63*x^6 - ω^63*x^4 + 2*ω^62*x^5 - 2*ω^62*x^4 - ω^61*x^6 + 2*ω^61*x^5 - ω^61*x^4 - ω^60*x^6 + ω^60*x^4 - 2*ω^59*x^5 + 2*ω^59*x^4 + ω^58*x^6 - ω^58*x^5 - ω^58*x^4 + ω^58*x^3 + ω^57*x^6 + ω^57*x^5 - 3*ω^57*x^4 + ω^57*x^3 + 2*ω^56*x^5 - 2*ω^56*x^4 - ω^55*x^6 + ω^55*x^5 + ω^55*x^4 - ω^55*x^3 - ω^54*x^6 - ω^54*x^5 + 3*ω^54*x^4 - ω^54*x^3 - ω^53*x^5 + ω^53*x^3 + ω^52*x^6 - 3*ω^52*x^4 + 2*ω^52*x^3 + ω^51*x^6 + ω^51*x^5 - 3*ω^51*x^4 + ω^51*x^3 + ω^50*x^5 - ω^50*x^3 - ω^49*x^6 + 3*ω^49*x^4 - 2*ω^49*x^3 - ω^48*x^6 + ω^48*x^3 - 3*ω^47*x^4 + 3*ω^47*x^3 + ω^46*x^6 - 3*ω^46*x^4 + 2*ω^46*x^3 + ω^45*x^6 - ω^45*x^3 + 3*ω^44*x^4 - 3*ω^44*x^3 - ω^43*x^6 + ω^43*x^4 + ω^43*x^3 - ω^43*x^2 - ω^42*x^6 - 2*ω^42*x^4 + 4*ω^42*x^3 - ω^42*x^2 - 3*ω^41*x^4 + 3*ω^41*x^3 + ω^40*x^6 - ω^40*x^4 - ω^40*x^3 + ω^40*x^2 + ω^39*x^6 + 2*ω^39*x^4 - 4*ω^39*x^3 + ω^39*x^2 + ω^38*x^4 - ω^38*x^2 - ω^37*x^6 - ω^37*x^4 + 4*ω^37*x^3 - 2*ω^37*x^2 - ω^36*x^6 - 2*ω^36*x^4 + 4*ω^36*x^3 - ω^36*x^2 - ω^35*x^4 + ω^35*x^2 + ω^34*x^6 + ω^34*x^4 - 4*ω^34*x^3 + 2*ω^34*x^2 + ω^33*x^6 + ω^33*x^4 - ω^33*x^3 - ω^33*x^2 + 3*ω^32*x^3 - 3*ω^32*x^2 - ω^31*x^6 - ω^31*x^4 + 4*ω^31*x^3 - 2*ω^31*x^2 - ω^30*x^6 - ω^30*x^4 + ω^30*x^3 + ω^30*x^2 - 3*ω^29*x^3 + 3*ω^29*x^2 + ω^28*x^6 - ω^28*x^3 + ω^27*x^6 + 2*ω^27*x^3 - 3*ω^27*x^2 + 3*ω^26*x^3 - 3*ω^26*x^2 - ω^25*x^6 + ω^25*x^3 - ω^24*x^6 - 2*ω^24*x^3 + 3*ω^24*x^2 - ω^23*x^3 + ω^23*x + ω^22*x^6 + ω^22*x^3 - 3*ω^22*x^2 + ω^22*x + ω^21*x^6 + 2*ω^21*x^3 - 3*ω^21*x^2 + ω^20*x^3 - ω^20*x - ω^19*x^6 - ω^19*x^3 + 3*ω^19*x^2 - ω^19*x - ω^18*x^6 - ω^18*x^3 + ω^18*x^2 + ω^18*x - 2*ω^17*x^2 + 2*ω^17*x + ω^16*x^6 + ω^16*x^3 - 3*ω^16*x^2 + ω^16*x + ω^15*x^6 + ω^15*x^3 - ω^15*x^2 - ω^15*x + 2*ω^14*x^2 - 2*ω^14*x - ω^13*x^6 + ω^13*x^2 - ω^12*x^6 - ω^12*x^2 + 2*ω^12*x - 2*ω^11*x^2 + 2*ω^11*x + ω^10*x^6 - ω^10*x^2 + ω^9*x^6 + ω^9*x^2 - 2*ω^9*x + ω^8*x^2 - ω^8*x - ω^7*x^6 + ω^7*x - ω^6*x^6 - ω^6*x^2 + 2*ω^6*x - ω^5*x^2 + ω^5*x + ω^4*x^6 - ω^4*x + ω^3*x^6 - ω^3*x - ω*x^6 + ω*x - x^6 + x) * ω_rel
  · rw [orderOf_six, chi7_six]
    linear_combination (-ω^43*x^6 + ω^43*x^5 - ω^42*x^6 + ω^42*x^5 + ω^40*x^6 - ω^40*x^4 + ω^39*x^6 - ω^39*x^4 - ω^37*x^6 + ω^37*x^5 - ω^36*x^6 + ω^36*x^5 + ω^34*x^6 - 2*ω^34*x^4 + ω^34*x^3 + ω^33*x^6 - 2*ω^33*x^4 + ω^33*x^3 - ω^31*x^6 + ω^31*x^5 - ω^30*x^6 + ω^30*x^5 + ω^28*x^6 - 3*ω^28*x^4 + 2*ω^28*x^3 + ω^27*x^6 - 3*ω^27*x^4 + 2*ω^27*x^3 - ω^25*x^6 + ω^25*x^4 + ω^25*x^3 - ω^25*x^2 - ω^24*x^6 + ω^24*x^4 + ω^24*x^3 - ω^24*x^2 + ω^22*x^6 - 3*ω^22*x^4 + 2*ω^22*x^3 + ω^21*x^6 - 3*ω^21*x^4 + 2*ω^21*x^3 - ω^19*x^6 + 2*ω^19*x^4 + ω^19*x^3 - 2*ω^19*x^2 - ω^18*x^6 + 2*ω^18*x^4 + ω^18*x^3 - 2*ω^18*x^2 + ω^16*x^6 - 3*ω^16*x^4 + 2*ω^16*x^3 + ω^15*x^6 - 3*ω^15*x^4 + 2*ω^15*x^3 - ω^13*x^6 + 3*ω^13*x^4 - 3*ω^13*x^2 + ω^13*x - ω^12*x^6 + 3*ω^12*x^4 - 3*ω^12*x^2 + ω^12*x + ω^10*x^6 - 3*ω^10*x^4 + ω^10*x^3 + ω^10*x^2 + ω^9*x^6 - 3*ω^9*x^4 + ω^9*x^3 + ω^9*x^2 - ω^7*x^6 + 3*ω^7*x^4 - 3*ω^7*x^2 + ω^7*x - ω^6*x^6 + 3*ω^6*x^4 - 3*ω^6*x^2 + ω^6*x + ω^4*x^6 - 3*ω^4*x^4 + 2*ω^4*x^2 + ω^3*x^6 - 3*ω^3*x^4 + 2*ω^3*x^2 - ω*x^6 + 3*ω*x^4 - 3*ω*x^2 + ω*x - x^6 + 3*x^4 - 3*x^2 + x) * ω_rel

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {7} ℚ K]

instance isGalois7 : IsGalois ℚ K := IsCyclotomicExtension.isGalois {7} ℚ K

theorem fundamental7 (p : ℕ) [Fact p.Prime] :
    gK K p * ((span {(p : ℤ)}).ramificationIdxIn (𝓞 K) * fK K p) = 6 := by
  rw [gK, fK, ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn _ (𝓞 K) Gal(K/ℚ),
    IsGaloisGroup.card_eq_finrank Gal(K/ℚ) ℚ K, finrank (k := 7) K]
  rfl

/-- **χ₇, …, χ₇⁵ match the splitting of every prime in ℚ(ζ₇).** -/
theorem hloc (p : ℕ) (hp : p.Prime) (x : ℂ) :
    (1 - x ^ fK K p) ^ gK K p =
      (1 - x) * ∏ j : Fin 5, (1 - (chi7 ^ ((j : ℕ) + 1)) (p : ZMod 7) * x) := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases h7 : p = 7
  · subst h7
    have : IsCyclotomicExtension {(7 : ℕ) ^ 1} ℚ K := by simpa
    rw [gK, fK, ncard_primesOver_of_prime 7 K, inertiaDegIn_eq_of_prime 7 K,
      show ((7 : ℕ) : ZMod 7) = 0 from rfl]
    simp [pow_apply, chi7_zero]
  · have hnd : ¬ p ∣ 7 := fun h => h7 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)
    have hr : (p : ZMod 7) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun h => h7 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h).symm
    have hf : fK K p = orderOf (p : ZMod 7) := inertiaDegIn_eq_of_not_dvd p K hnd
    have he : (span {(p : ℤ)}).ramificationIdxIn (𝓞 K) = 1 := ramificationIdxIn_eq_of_not_dvd p K hnd
    have hfun := fundamental7 (K := K) p
    rw [he, one_mul] at hfun
    have hpos : 0 < fK K p := fK_pos p
    have hg : gK K p = 6 / fK K p := by
      rw [← hfun, Nat.mul_div_cancel _ hpos]
    rw [hg, hf]
    exact local_identity _ hr x

/-- **Dedekind factorization for ℚ(ζ₇):** Σ A(n) n⁻ˢ = ζ(s) · ∏_{j=1}^{5} L(s, χ₇ʲ), Re s > 1. -/
theorem LSeries_A_eq_zeta_mul_L5 {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (IdealCount.A (𝓞 K) n : ℂ)) s =
      riemannZeta s * ∏ j : Fin 5, LSeries (fun n => (chi7 ^ ((j : ℕ) + 1)) n) s :=
  LSeries_A_eq_zeta_mul_prod (fun j : Fin 5 => chi7 ^ ((j : ℕ) + 1)) hloc hs

end Cyclo7

#print axioms Cyclo7.local_identity
#print axioms Cyclo7.hloc
#print axioms Cyclo7.LSeries_A_eq_zeta_mul_L5
