import CyclotomicSubfieldSplitting
import Cyclo7EulerProduct

/-!
# Cyclo7Cubic — the cubic subfield of ℚ(ζ₇): ζ_K = ζ · L(χ²) · L(χ⁴)

K = L^H with L = ℚ(ζ₇), H = {σ : σ(ζ) = ζ^{±1}} (order 2), so [K : ℚ] = 3 (K = ℚ(ζ₇ + ζ₇⁻¹)).
Everything comes from the general subfield theorems:
* p ≠ 7: f_K(p) = order of σ_p H in G/H (`CycloSub.fK_eq_orderOf`) = 1 if p ≡ ±1 (mod 7), else 3;
  g_K(p) · f_K(p) = 3 (`CycloSub.gK_mul_fK`);
* p = 7: totally ramified in L, so g_K = f_K = 1 (`SubfieldDeg.ramified_descends`).
Characters: χ₇² and χ₇⁴, the order-3 characters mod 7 (trivial on ±1).
Local identity (1 − x^f)^g = (1 − x)(1 − χ²(p)x)(1 − χ⁴(p)x) checked for all six unit residues
using ω² − ω + 1 = 0 (coefficients computed offline, verified by `linear_combination`).
-/

open NumberField Ideal IsCyclotomicExtension.Rat GaloisEuler Cyclo7 Complex

namespace Cyclo7Cubic

/-- {±1} in (ZMod 7)ˣ. -/
def Hpm : Subgroup (ZMod 7)ˣ where
  carrier := {u | (u : ZMod 7) = 1 ∨ (u : ZMod 7) = -1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul] at *
    rcases ha with h | h <;> rcases hb with h' | h' <;> simp [h, h']
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, Units.val_inv_eq_inv_val] at *
    rcases ha with h | h <;> simp [h]

theorem card_Hpm : Nat.card Hpm = 2 := by
  show Nat.card {u : (ZMod 7)ˣ // (u : ZMod 7) = 1 ∨ (u : ZMod 7) = -1} = 2
  rw [Nat.card_eq_fintype_card]; decide

theorem index_Hpm : Hpm.index = 3 := by
  have h := Hpm.card_mul_index
  rw [card_Hpm, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] at h
  have : Nat.totient 7 = 6 := by decide
  omega

variable {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {7} ℚ L]

/-- H = automorphisms σ with σ(ζ) = ζ^{±1}. -/
noncomputable def H : Subgroup Gal(L/ℚ) := Hpm.comap (galEquivZMod 7 L).toMonoidHom

instance : (H (L := L)).Normal := CycloSub.normal 7 _

theorem index_H : (H (L := L)).index = 3 := by
  rw [H, Subgroup.index_comap_of_surjective (f := (galEquivZMod 7 L).toMonoidHom) Hpm
    (galEquivZMod 7 L).surjective, index_Hpm]

theorem finrank_K : Module.finrank ℚ (IntermediateField.fixedField (H (L := L))) = 3 := by
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {7} ℚ L
  rw [CycloSub.finrank_K, index_H]

/-- Order of the coset as a decidable function of the residue. -/
def ordH (r : ZMod 7) : ℕ := if r = 1 ∨ r = 6 then 1 else 3

theorem ord_facts : ∀ r : ZMod 7, r ≠ 0 →
    (r ^ ordH r = 1 ∨ r ^ ordH r = -1) ∧
      ∀ m < ordH r, 0 < m → ¬ (r ^ m = 1 ∨ r ^ m = -1) := by
  decide

theorem orderOf_mk (p : ℕ) [Fact p.Prime] (hn : p.Coprime 7) :
    orderOf (QuotientGroup.mk (CycloFrob.sigmaP 7 L p hn) : Gal(L/ℚ) ⧸ H (L := L)) =
      ordH (p : ZMod 7) := by
  have hr : (p : ZMod 7) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => (CycloSub.not_dvd (Fact.out : p.Prime) hn) (by
      exact (Nat.prime_dvd_prime_iff_eq (by norm_num) Fact.out |>.mp h) ▸ dvd_refl 7)
  have key : ∀ k : ℕ, (QuotientGroup.mk (CycloFrob.sigmaP 7 L p hn) : Gal(L/ℚ) ⧸ H (L := L)) ^ k = 1 ↔
      ((p : ZMod 7) ^ k = 1 ∨ (p : ZMod 7) ^ k = -1) := by
    intro k
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    show (galEquivZMod 7 L (CycloFrob.sigmaP 7 L p hn ^ k)) ∈ Hpm ↔ _
    rw [map_pow, CycloFrob.sigmaP, MulEquiv.apply_symm_apply]
    change ((ZMod.unitOfCoprime p hn ^ k : (ZMod 7)ˣ) : ZMod 7) = 1 ∨
      ((ZMod.unitOfCoprime p hn ^ k : (ZMod 7)ˣ) : ZMod 7) = -1 ↔ _
    rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime]
  obtain ⟨h1, h2⟩ := ord_facts _ hr
  rw [orderOf_eq_iff (by unfold ordH; split_ifs <;> norm_num)]
  exact ⟨(key _).mpr h1, fun m hm hm0 h => h2 m hm hm0 ((key m).mp h)⟩

theorem pow_apply2 (j : ℕ) (r : ZMod 7) :
    (chi7 ^ (2 * (j + 1))) r = chi7 r ^ (2 * (j + 1)) :=
  MulChar.pow_apply' _ (by positivity) r

/-- The cubic local identity at a unit residue r. -/
theorem local_identity (r : ZMod 7) (hr : r ≠ 0) (x : ℂ) :
    (1 - x ^ ordH r) ^ (3 / ordH r) =
      (1 - x) * ∏ j : Fin 2, (1 - (chi7 ^ (2 * ((j : ℕ) + 1))) r * x) := by
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.val_zero, Fin.val_succ, pow_apply2,
    mul_one]
  rcases cases_unit r hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show ordH (1 : ZMod 7) = 1 by decide, chi7_one]; ring
  · rw [show ordH (2 : ZMod 7) = 3 by decide, chi7_two, show (3 : ℕ) / 3 = 1 from rfl, pow_one]
    linear_combination (ω^10*x^3 - ω^10*x^2 + ω^9*x^3 - ω^9*x^2 - ω^7*x^3 + ω^7*x^2 - ω^6*x^3 + ω^6*x - ω^5*x^2 + ω^5*x + ω^4*x^3 - ω^4*x^2 + ω^3*x^3 - ω^3*x - ω*x^3 + ω*x - x^3 + x) * ω_rel
  · rw [show ordH (3 : ZMod 7) = 3 by decide, chi7_three, show (3 : ℕ) / 3 = 1 from rfl, pow_one]
    linear_combination (ω^4*x^3 - ω^4*x^2 + ω^3*x^3 - ω^3*x^2 - ω^2*x^2 + ω^2*x - ω*x^3 + ω*x - x^3 + x) * ω_rel
  · rw [show ordH (4 : ZMod 7) = 3 by decide, chi7_four, show (3 : ℕ) / 3 = 1 from rfl, pow_one]
    linear_combination (ω^22*x^3 - ω^22*x^2 + ω^21*x^3 - ω^21*x^2 - ω^19*x^3 + ω^19*x^2 - ω^18*x^3 + ω^18*x^2 + ω^16*x^3 - ω^16*x^2 + ω^15*x^3 - ω^15*x^2 - ω^14*x^2 + ω^14*x - ω^13*x^3 + ω^13*x - ω^12*x^3 + ω^12*x^2 + ω^11*x^2 - ω^11*x + ω^10*x^3 - ω^10*x + ω^9*x^3 - ω^9*x^2 - ω^8*x^2 + ω^8*x - ω^7*x^3 + ω^7*x - ω^6*x^3 + ω^6*x + ω^4*x^3 - ω^4*x + ω^3*x^3 - ω^3*x - ω*x^3 + ω*x - x^3 + x) * ω_rel
  · rw [show ordH (5 : ZMod 7) = 3 by decide, chi7_five, show (3 : ℕ) / 3 = 1 from rfl, pow_one]
    linear_combination (ω^28*x^3 - ω^28*x^2 + ω^27*x^3 - ω^27*x^2 - ω^25*x^3 + ω^25*x^2 - ω^24*x^3 + ω^24*x^2 + ω^22*x^3 - ω^22*x^2 + ω^21*x^3 - ω^21*x^2 - ω^19*x^3 + ω^19*x^2 - ω^18*x^3 + ω^18*x - ω^17*x^2 + ω^17*x + ω^16*x^3 - ω^16*x^2 + ω^15*x^3 - ω^15*x + ω^14*x^2 - ω^14*x - ω^13*x^3 + ω^13*x^2 - ω^12*x^3 + ω^12*x - ω^11*x^2 + ω^11*x + ω^10*x^3 - ω^10*x^2 + ω^9*x^3 - ω^9*x - ω^7*x^3 + ω^7*x - ω^6*x^3 + ω^6*x + ω^4*x^3 - ω^4*x + ω^3*x^3 - ω^3*x - ω*x^3 + ω*x - x^3 + x) * ω_rel
  · rw [show ordH (6 : ZMod 7) = 1 by decide, chi7_six, show (3 : ℕ) / 1 = 3 from rfl, pow_one]
    linear_combination (ω^16*x^3 - ω^16*x^2 + ω^15*x^3 - ω^15*x^2 - ω^13*x^3 + ω^13*x^2 - ω^12*x^3 + ω^12*x^2 + ω^10*x^3 - 2*ω^10*x^2 + ω^10*x + ω^9*x^3 - 2*ω^9*x^2 + ω^9*x - ω^7*x^3 + 2*ω^7*x^2 - ω^7*x - ω^6*x^3 + 2*ω^6*x^2 - ω^6*x + ω^4*x^3 - 3*ω^4*x^2 + 2*ω^4*x + ω^3*x^3 - 3*ω^3*x^2 + 2*ω^3*x - ω*x^3 + 3*ω*x^2 - 2*ω*x - x^3 + 3*x^2 - 2*x) * ω_rel


local notation "K" => IntermediateField.fixedField (H (L := L))

/-- **χ₇², χ₇⁴ match the splitting of every prime in the cubic subfield.** -/
theorem hloc (p : ℕ) (hp : p.Prime) (x : ℂ) :
    (1 - x ^ fK K p) ^ gK K p =
      (1 - x) * ∏ j : Fin 2, (1 - (chi7 ^ (2 * ((j : ℕ) + 1))) (p : ZMod 7) * x) := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {7} ℚ L
  by_cases h7 : p = 7
  · subst h7
    have : IsCyclotomicExtension {(7 : ℕ) ^ 1} ℚ L := by simpa
    obtain ⟨hg, hf⟩ := SubfieldDeg.ramified_descends (H (L := L)) 7
      (ncard_primesOver_of_prime 7 L) (inertiaDegIn_eq_of_prime 7 L)
    rw [gK, fK, hg, hf, show ((7 : ℕ) : ZMod 7) = 0 from rfl]
    simp [pow_apply2, chi7_zero]
  · have hn : p.Coprime 7 := (Nat.coprime_primes hp (by norm_num)).mpr h7
    have hr : (p : ZMod 7) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun h => h7 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h).symm
    have hf : fK K p = ordH (p : ZMod 7) := by
      rw [fK, CycloSub.fK_eq_orderOf 7 L (H (L := L)) p hn, orderOf_mk]
    have hgf := (CycloSub.gK_mul_fK 7 L (H (L := L)) p hn).2
    rw [index_H, ← fK, hf, ← gK] at hgf
    have hpos : 0 < ordH (p : ZMod 7) := by unfold ordH; split_ifs <;> norm_num
    have hg : gK K p = 3 / ordH (p : ZMod 7) := by rw [← hgf, Nat.mul_div_cancel _ hpos]
    rw [hg, hf]
    exact local_identity _ hr x

/-- **Dedekind factorization for the cubic subfield K of ℚ(ζ₇):**
Σ A_K(n) n⁻ˢ = ζ(s) · L(s, χ₇²) · L(s, χ₇⁴) for Re s > 1. -/
theorem LSeries_A_eq_zeta_mul_L2 {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (IdealCount.A (𝓞 K) n : ℂ)) s =
      riemannZeta s * ∏ j : Fin 2, LSeries (fun n => (chi7 ^ (2 * ((j : ℕ) + 1))) n) s := by
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {7} ℚ L
  exact LSeries_A_eq_zeta_mul_prod (fun j : Fin 2 => chi7 ^ (2 * ((j : ℕ) + 1))) hloc hs

end Cyclo7Cubic

#print axioms Cyclo7Cubic.finrank_K
#print axioms Cyclo7Cubic.hloc
#print axioms Cyclo7Cubic.LSeries_A_eq_zeta_mul_L2
