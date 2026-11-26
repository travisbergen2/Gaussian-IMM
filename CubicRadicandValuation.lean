import CubicConjugationConstraint

/-!
# CubicRadicandValuation — prime valuations of the Kummer radicand

**Generic part** (R a domain with finite multiplicities, κ an involutive ring automorphism):
from c³ · κ(a) = d³ · a² (a, c ≠ 0) and π prime,
* `val_constraint`: v_{κπ}(a) ≡ 2 v_π(a) (mod 3), and symmetrically `val_constraint'`;
* `three_dvd_of_fixed`: if κπ ~ π then 3 ∣ v_π(a).

**Eisenstein part** (R = 𝓞 F, F = ℚ(ω), κ = complex conjugation):
* `kappa_coe`, `kappa_kappa`: κ is conjugation on 𝓞 F and an involution;
* `kappa_lambda`: κλ ~ λ for λ = ω − 1 (prime: Mathlib's `zeta_sub_one_prime'`) — the ramified
  prime is conjugation-fixed; `kappa_natCast`: κ fixes rational integers, so any rational prime
  that stays prime in 𝓞 F (inert) is fixed;
* `integral_radicand`: for K ⊆ ℂ cyclic cubic, with the Kummer generator β of
  `CubicConj.conj_constraint`, there are s, A, C, D ∈ 𝓞 F (s, A, C ≠ 0) with
  s³ β³ = A and C³ · κA = D³ · A²;
* `radicand_valuations`: v_{κπ}(A) ≡ 2 v_π(A) (mod 3) for every prime π, 3 ∣ v_λ(A), and
  3 ∣ v_p(A) for every inert rational prime p.
The unit part of A is not constrained here (it is handled separately, via ∛ω = ζ₉).
-/

open IntermediateField Module NumberField CubicKummerRep

namespace CubicVal

section Generic

variable {R : Type*} [CommRing R] [IsDomain R] [WfDvdMonoid R] (κ : R ≃+* R)
  (hκ : ∀ x, κ (κ x) = x)

omit [IsDomain R] [WfDvdMonoid R] in
include hκ in
theorem mult_conj (π a : R) : multiplicity π (κ a) = multiplicity (κ π) a := by
  conv_lhs => rw [← hκ π]
  exact multiplicity_map_eq κ

include hκ in
/-- **v_{κπ}(a) ≡ 2 v_π(a) (mod 3).** -/
theorem val_constraint {π a c d : R} (hπ : Prime π) (ha : a ≠ 0) (hc : c ≠ 0)
    (h : c ^ 3 * κ a = d ^ 3 * a ^ 2) :
    multiplicity (κ π) a % 3 = (2 * multiplicity π a) % 3 := by
  have hκa : κ a ≠ 0 := fun h0 => ha (κ.injective (by rw [h0, map_zero]))
  have hL : c ^ 3 * κ a ≠ 0 := mul_ne_zero (pow_ne_zero _ hc) hκa
  have hR : d ^ 3 * a ^ 2 ≠ 0 := h ▸ hL
  have hm := congrArg (multiplicity π) h
  rw [multiplicity_mul hπ (.of_prime_left hπ hL), multiplicity_mul hπ (.of_prime_left hπ hR),
    multiplicity_pow hπ, multiplicity_pow hπ, multiplicity_pow hπ, mult_conj κ hκ] at hm
  omega

include hκ in
/-- **v_π(a) ≡ 2 v_{κπ}(a) (mod 3).** -/
theorem val_constraint' {π a c d : R} (hπ : Prime π) (ha : a ≠ 0) (hc : c ≠ 0)
    (h : c ^ 3 * κ a = d ^ 3 * a ^ 2) :
    multiplicity π a % 3 = (2 * multiplicity (κ π) a) % 3 := by
  have := val_constraint κ hκ hπ ha hc h
  omega

include hκ in
/-- **Conjugation-fixed primes:** κπ ~ π ⇒ 3 ∣ v_π(a). -/
theorem three_dvd_of_fixed {π a c d : R} (hπ : Prime π) (hfix : Associated (κ π) π)
    (ha : a ≠ 0) (hc : c ≠ 0) (h : c ^ 3 * κ a = d ^ 3 * a ^ 2) :
    3 ∣ multiplicity π a := by
  have := val_constraint κ hκ hπ ha hc h
  rw [← multiplicity_eq_of_associated_left hfix] at this
  omega

end Generic

section Eisenstein

local notation "ω" => CubicAssembly.ω

instance : NumberField F := ⟨⟩

instance : IsCyclotomicExtension {3} ℚ F :=
  CubicAssembly.hω.intermediateField_adjoin_isCyclotomicExtension ℚ

/-- ω as an element of F. -/
noncomputable def ωF : F := ⟨ω, mem_adjoin_simple_self ℚ ω⟩

theorem hωF : IsPrimitiveRoot ωF 3 :=
  CubicAssembly.hω.of_map_of_injective (f := F.val.toMonoidHom) Subtype.val_injective

/-- Complex conjugation on F. -/
noncomputable def conjF : F ≃ₐ[ℚ] F := (Complex.conjAe.restrictScalars ℚ).restrictNormal F

theorem conjF_coe (x : F) : ((conjF x : F) : ℂ) = starRingEnd ℂ (x : ℂ) :=
  (Complex.conjAe.restrictScalars ℚ).restrictNormal_commutes F x

/-- **κ**: complex conjugation on 𝓞 F. -/
noncomputable def κ : 𝓞 F ≃+* 𝓞 F := RingOfIntegers.mapRingEquiv conjF.toRingEquiv

/-- 𝓞 F → ℂ. -/
noncomputable def ι : 𝓞 F →+* ℂ := F.val.toRingHom.comp (algebraMap (𝓞 F) F)

theorem ι_injective : Function.Injective ι :=
  Subtype.val_injective.comp RingOfIntegers.coe_injective

theorem kappa_coe (x : 𝓞 F) : ι (κ x) = starRingEnd ℂ (ι x) := conjF_coe (x : F)

theorem kappa_kappa (x : 𝓞 F) : κ (κ x) = x :=
  ι_injective (by rw [kappa_coe, kappa_coe, Complex.conj_conj])

theorem kappa_natCast (n : ℕ) : κ (n : 𝓞 F) = n := map_natCast κ n

/-- λ = ω − 1 in 𝓞 F. -/
noncomputable def lam : 𝓞 F := hωF.toInteger - 1

theorem lam_prime : Prime lam := hωF.zeta_sub_one_prime'

theorem ι_ω : ι hωF.toInteger = ω := rfl

theorem ω_rel : ω ^ 2 + ω + 1 = 0 := by
  have h3 := CubicConj.ω_cube
  have h1 : ω ≠ 1 := CubicAssembly.hω.ne_one (by norm_num)
  have : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination h3
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h1)

/-- **The ramified prime is conjugation-fixed:** κλ = λ · (ω + 1), with ω + 1 a unit. -/
theorem kappa_lambda : Associated (κ lam) lam := by
  set z := hωF.toInteger
  have hz : ι z = ω := rfl
  have hκz : κ z = z ^ 2 := ι_injective (by
    rw [kappa_coe, map_pow, hz, CubicConj.conj_ω])
  have hu : IsUnit (z + 1) := IsUnit.of_mul_eq_one (-z) (ι_injective (by
    simp only [map_mul, map_add, map_neg, map_one, hz]; linear_combination -ω_rel))
  refine (Associated.symm ⟨hu.unit, ?_⟩)
  apply ι_injective
  simp only [lam, IsUnit.unit_spec, map_mul, map_sub, map_add, map_one, kappa_coe, ι_ω, hz]
  rw [CubicConj.conj_ω]; ring

variable (K : IntermediateField ℚ ℂ) [IsGalois ℚ K] (hK : finrank ℚ K = 3)

include hK in
/-- **Integral radicand:** s³ β³ = A ∈ 𝓞 F with C³ · κA = D³ · A². -/
theorem integral_radicand : ∃ β : ℂ, β ∈ M K ∧ β ^ 3 ∈ F ∧ β ∉ F ∧ M K = ℚ⟮ω, β⟯ ∧
    ∃ s A C D : 𝓞 F, s ≠ 0 ∧ A ≠ 0 ∧ C ≠ 0 ∧ ι s ^ 3 * β ^ 3 = ι A ∧
      C ^ 3 * κ A = D ^ 3 * A ^ 2 := by
  obtain ⟨β, hβM, hβ3, hβF, hM, δ, hδF, hδ0, hconj⟩ := CubicConj.conj_constraint K hK
  refine ⟨β, hβM, hβ3, hβF, hM, ?_⟩
  have hβ0 : β ≠ 0 := by rintro rfl; exact hβF (zero_mem _)
  -- a = x / s and δ = y / t
  obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (𝓞 F))
    (⟨β ^ 3, hβ3⟩ : F)
  obtain ⟨⟨y, t⟩, hyt⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (𝓞 F))
    (⟨δ, hδF⟩ : F)
  have hs := IsLocalization.mk'_spec F x s
  have ht := IsLocalization.mk'_spec F y t
  simp only at hxs hyt
  rw [hxs] at hs; rw [hyt] at ht
  have hsC : β ^ 3 * ι (s : 𝓞 F) = ι x := congrArg Subtype.val hs
  have htC : δ * ι (t : 𝓞 F) = ι y := congrArg Subtype.val ht
  have hs0 : (s : 𝓞 F) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have ht0 : (t : 𝓞 F) ≠ 0 := nonZeroDivisors.coe_ne_zero t
  have hιs : ι (s : 𝓞 F) ≠ 0 := (map_ne_zero_iff _ ι_injective).mpr hs0
  refine ⟨s, s ^ 2 * x, t * s ^ 2, κ s * y, hs0, ?_, mul_ne_zero ht0 (pow_ne_zero _ hs0), ?_, ?_⟩
  · refine mul_ne_zero (pow_ne_zero _ hs0) (fun hx => ?_)
    rw [hx, map_zero] at hsC
    exact mul_ne_zero (pow_ne_zero _ hβ0) hιs hsC
  · rw [map_mul, map_pow, ← hsC]; ring
  · apply ι_injective
    simp only [map_mul, map_pow, kappa_coe, ← hsC, ← htC, map_mul, map_pow]
    rw [map_pow] at hconj
    linear_combination (ι ↑t ^ 3 * ι ↑s ^ 6 * (starRingEnd ℂ) (ι ↑s) ^ 3) * hconj

include hK in
/-- **Valuation constraints for the integral radicand A.** -/
theorem radicand_valuations : ∃ β : ℂ, β ∈ M K ∧ β ^ 3 ∈ F ∧ β ∉ F ∧ M K = ℚ⟮ω, β⟯ ∧
    ∃ s A : 𝓞 F, s ≠ 0 ∧ A ≠ 0 ∧ ι s ^ 3 * β ^ 3 = ι A ∧
      (∀ π : 𝓞 F, Prime π → multiplicity (κ π) A % 3 = (2 * multiplicity π A) % 3) ∧
      3 ∣ multiplicity lam A ∧
      (∀ p : ℕ, Prime (p : 𝓞 F) → 3 ∣ multiplicity (p : 𝓞 F) A) := by
  obtain ⟨β, hβM, hβ3, hβF, hM, s, A, C, D, hs0, hA0, hC0, hsA, hCD⟩ := integral_radicand K hK
  refine ⟨β, hβM, hβ3, hβF, hM, s, A, hs0, hA0, hsA,
    fun π hπ => val_constraint κ kappa_kappa hπ hA0 hC0 hCD,
    three_dvd_of_fixed κ kappa_kappa lam_prime kappa_lambda hA0 hC0 hCD,
    fun p hp => three_dvd_of_fixed κ kappa_kappa hp (by rw [kappa_natCast]) hA0 hC0 hCD⟩

end Eisenstein

end CubicVal

#print axioms CubicVal.val_constraint
#print axioms CubicVal.three_dvd_of_fixed
#print axioms CubicVal.kappa_lambda
#print axioms CubicVal.integral_radicand
#print axioms CubicVal.radicand_valuations
