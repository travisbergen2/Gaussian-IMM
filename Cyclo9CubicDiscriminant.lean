import Cyclo9CubicField

/-!
# Cyclo9CubicDiscriminant — 𝓞_K = ℤ[θ] and disc K = 81 for the cubic subfield of ℚ(ζ₉)

Generic part (namespace `EisCubic`): F a cubic number field, y ∈ F with y³ − 3y² + 3 = 0
(Eisenstein at 3). Then
* `minpoly_y`: minpoly ℚ y = X³ − 3X² + 3, and minpoly ℚ (y − 2) = X³ + 3X² − 1;
* `discr_basis`: the power basis 1, y, y² has discriminant 81, via
  disc = (−1)^{3} N(f′(y)) with f′(y) = 3y(y − 2), N(3) = 27, N(y) = −3, N(y − 2) = 1;
* `isIntegralClosure`: 𝓞_F = ℤ[y]: 81·z = 3⁴·z ∈ ℤ[y] for integral z
  (`Algebra.discr_mul_isIntegral_mem_adjoin`), and the Eisenstein property of minpoly ℤ y at 3
  removes the 3⁴ (`mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt`);
* `discr_eq`: `NumberField.discr F = 81`.
Applied with F = K = ℚ(ζ₉)^H and y = θ + 1 (θ = ζ + ζ⁻¹, θ³ − 3θ + 1 = 0): `Cyclo9Cubic.discr_K`.
-/

open Polynomial IntermediateField NumberField

namespace EisCubic

variable {F : Type*} [Field F] [NumberField F] (hF : Module.finrank ℚ F = 3) {x : F}

include hF in
/-- A non-rational element of a cubic field generates it, and its minpoly is any monic cubic it
satisfies. -/
theorem gen_of_not_rat (hx : x ∉ Set.range (algebraMap ℚ F)) {p : ℚ[X]} (hp : p.Monic)
    (hpdeg : p.natDegree = 3) (hpx : aeval x p = 0) :
    ℚ⟮x⟯ = ⊤ ∧ minpoly ℚ x = p := by
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have hdvd : Module.finrank ℚ ℚ⟮x⟯ ∣ 3 := by
    rw [← hF, ← finrank_top' (F := ℚ) (E := F)]; exact finrank_dvd_of_le_right (K := ℚ) le_top
  have hne : Module.finrank ℚ ℚ⟮x⟯ ≠ 1 := by
    rw [Ne, IntermediateField.finrank_eq_one_iff, adjoin_simple_eq_bot_iff, mem_bot]; exact hx
  have h3 : Module.finrank ℚ ℚ⟮x⟯ = 3 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
    · exact absurd h hne
    · exact h
  have htop : ℚ⟮x⟯ = ⊤ := IntermediateField.eq_of_le_of_finrank_eq le_top (by rw [h3, finrank_top', hF])
  refine ⟨htop, ?_⟩
  have hdeg : (minpoly ℚ x).natDegree = 3 := by rw [← adjoin.finrank hint, h3]
  exact (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hp (minpoly.dvd ℚ _ hpx)
    (by rw [hpdeg, hdeg])).symm

theorem algebra_adjoin_top {x : F} (h : ℚ⟮x⟯ = ⊤) : Algebra.adjoin ℚ {x} = ⊤ := by
  rw [← adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic x), h,
    top_toSubalgebra]

variable {y : F} (hy : y ^ 3 - 3 * y ^ 2 + 3 = 0)

omit [NumberField F] in
include hy in
theorem y_isIntegral : IsIntegral ℤ y := by
  refine ⟨X ^ 3 - C 3 * X ^ 2 + C 3, by monicity!, ?_⟩
  simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_X_pow, eval₂_C]
  simpa using hy

include hy in
theorem y_not_rat : y ∉ Set.range (algebraMap ℚ F) := by
  rintro ⟨q, hq⟩
  have hqi : IsIntegral ℤ q := by
    rw [← isIntegral_algebraMap_iff (B := F), hq]; exact y_isIntegral hy
  obtain ⟨z, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hqi
  rw [← hq] at hy
  have hz : (z : ℚ) ^ 3 - 3 * (z : ℚ) ^ 2 + 3 = 0 := by
    apply (algebraMap ℚ F).injective; simpa using hy
  have hzz : z ^ 3 - 3 * z ^ 2 + 3 = 0 := by exact_mod_cast hz
  have hd : z ∣ 3 := ⟨3 * z - z ^ 2, by linear_combination hzz⟩
  have hn : z.natAbs ∣ 3 := by simpa using Int.natAbs_dvd_natAbs.mpr hd
  rcases (Nat.dvd_prime Nat.prime_three).mp hn with h | h <;>
    rcases Int.natAbs_eq z with h' | h' <;> rw [h'] at hzz <;> rw [h] at hzz <;> norm_num at hzz

include hF hy in
theorem minpoly_y : ℚ⟮y⟯ = ⊤ ∧ minpoly ℚ y = X ^ 3 - 3 * X ^ 2 + 3 := by
  apply gen_of_not_rat hF (y_not_rat hy) (by monicity!) (by compute_degree!)
  simp only [map_add, map_sub, map_pow, aeval_X, map_mul, map_ofNat]; exact hy

include hF hy in
theorem minpoly_y2 : ℚ⟮y - 2⟯ = ⊤ ∧ minpoly ℚ (y - 2) = X ^ 3 + 3 * X ^ 2 - 1 := by
  have hnr : y - 2 ∉ Set.range (algebraMap ℚ F) := by
    rintro ⟨q, hq⟩
    exact y_not_rat hy ⟨q + 2, by rw [map_add, hq, map_ofNat]; ring⟩
  apply gen_of_not_rat hF hnr (by monicity!) (by compute_degree!)
  simp only [map_add, map_sub, map_pow, aeval_X, map_mul, map_ofNat, map_one]
  linear_combination hy

include hF hy in
/-- The power basis 1, y, y². -/
noncomputable def By : PowerBasis ℚ F :=
  PowerBasis.ofAdjoinEqTop' (Algebra.IsIntegral.isIntegral y)
    (algebra_adjoin_top (minpoly_y hF hy).1)

theorem By_gen : (By hF hy).gen = y := PowerBasis.ofAdjoinEqTop'_gen _ _

include hF hy in
theorem norm_y : Algebra.norm ℚ y = -3 := by
  have h := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (By hF hy)
  rw [By_gen, ← PowerBasis.natDegree_minpoly, By_gen, (minpoly_y hF hy).2] at h
  rw [h]
  have hd : (X ^ 3 - 3 * X ^ 2 + 3 : ℚ[X]).natDegree = 3 := by compute_degree!
  rw [hd]; simp [coeff_X_pow]; norm_num

include hF hy in
theorem norm_y2 : Algebra.norm ℚ (y - 2) = 1 := by
  let B2 : PowerBasis ℚ F := PowerBasis.ofAdjoinEqTop' (Algebra.IsIntegral.isIntegral (y - 2))
    (algebra_adjoin_top (minpoly_y2 hF hy).1)
  have hg : B2.gen = y - 2 := PowerBasis.ofAdjoinEqTop'_gen _ _
  have h := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly B2
  rw [hg, ← PowerBasis.natDegree_minpoly, hg, (minpoly_y2 hF hy).2] at h
  rw [h]
  have hd : (X ^ 3 + 3 * X ^ 2 - 1 : ℚ[X]).natDegree = 3 := by compute_degree!
  rw [hd]; simp [coeff_X_pow]; norm_num

include hF hy in
/-- **disc(1, y, y²) = 81.** -/
theorem discr_basis : Algebra.discr ℚ (By hF hy).basis = 81 := by
  rw [Algebra.discr_powerBasis_eq_norm, By_gen, (minpoly_y hF hy).2, hF]
  have hfac : aeval y (derivative (X ^ 3 - 3 * X ^ 2 + 3 : ℚ[X])) =
      algebraMap ℚ F 3 * (y * (y - 2)) := by
    simp only [derivative_add, derivative_sub, derivative_X_pow, derivative_mul,
      derivative_ofNat, derivative_X, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C,
      map_ofNat, map_natCast, zero_mul, zero_add, mul_one, derivative_C]
    simp only [map_zero, add_zero]
    push_cast; ring
  rw [hfac, map_mul, map_mul, Algebra.norm_algebraMap, hF, norm_y hF hy, norm_y2 hF hy]
  norm_num

include hF hy in
theorem minpoly_int : minpoly ℤ y = X ^ 3 - C 3 * X ^ 2 + C 3 := by
  have h := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ (y_isIntegral hy)
  rw [(minpoly_y hF hy).2] at h
  apply Polynomial.map_injective (algebraMap ℤ ℚ) (algebraMap ℤ ℚ).injective_int
  rw [← h]
  simp [map_ofNat]

theorem eisenstein : (X ^ 3 - C 3 * X ^ 2 + C 3 : ℤ[X]).IsEisensteinAt (Ideal.span {(3 : ℤ)}) := by
  have hdeg : (X ^ 3 - C 3 * X ^ 2 + C 3 : ℤ[X]).natDegree = 3 := by compute_degree!
  have hlc : (X ^ 3 - C 3 * X ^ 2 + C 3 : ℤ[X]).leadingCoeff = 1 := by
    rw [leadingCoeff, hdeg]; simp [coeff_X_pow, coeff_C]
  refine ⟨?_, ?_, ?_⟩
  · rw [hlc, Ideal.mem_span_singleton]; decide
  · intro n hn
    rw [hdeg] at hn
    rw [Ideal.mem_span_singleton]
    interval_cases n <;> simp [coeff_X_pow, coeff_C, coeff_X]
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    simp [coeff_X_pow, coeff_C]

include hF hy in
/-- **𝓞_F = ℤ[y].** -/
theorem isIntegralClosure : IsIntegralClosure (Algebra.adjoin ℤ ({y} : Set F)) ℤ F := by
  have hint := y_isIntegral hy
  refine ⟨Subtype.val_injective, @fun x => ⟨fun h => ⟨⟨x, ?_⟩, rfl⟩, ?_⟩⟩
  swap
  · rintro ⟨w, rfl⟩
    exact IsIntegral.algebraMap
      ((le_integralClosure_iff_isIntegral.1 (adjoin_le_integralClosure hint)).isIntegral _)
  have hBint : IsIntegral ℤ (By hF hy).gen := by rw [By_gen]; exact hint
  have H := Algebra.discr_mul_isIntegral_mem_adjoin ℚ hBint h
  rw [discr_basis hF hy] at H
  have h81 : (81 : ℚ) • x = (3 : ℤ) ^ 4 • x := by
    rw [zsmul_eq_mul, Algebra.smul_def]; push_cast; norm_num
  rw [h81] at H
  have hei : (minpoly ℤ (By hF hy).gen).IsEisensteinAt (Ideal.span {(3 : ℤ)}) := by
    rw [By_gen, minpoly_int hF hy]; exact eisenstein
  have := mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt Int.prime_three hBint h H hei
  rwa [By_gen] at this

include hF hy in
/-- **disc F = 81.** -/
theorem discr_eq : NumberField.discr F = 81 := by
  have := isIntegralClosure hF hy
  let pB : PowerBasis ℤ (𝓞 F) := (Algebra.adjoin.powerBasis' (y_isIntegral hy)).map
    (IsIntegralClosure.equiv ℤ (Algebra.adjoin ℤ ({y} : Set F)) F (𝓞 F))
  have hgen : algebraMap (𝓞 F) F pB.gen = y := by
    simp only [pB, PowerBasis.map_gen, Algebra.adjoin.powerBasis'_gen]
    rw [IsIntegralClosure.algebraMap_equiv]
    rfl
  apply (algebraMap ℤ ℚ).injective_int
  rw [← NumberField.discr_eq_discr _ pB.basis,
    ← Algebra.discr_localizationLocalization ℤ (nonZeroDivisors ℤ) F]
  have hdim : pB.dim = (By hF hy).dim := by
    rw [← PowerBasis.finrank, ← PowerBasis.finrank]; exact RingOfIntegers.rank F
  rw [map_ofNat, ← discr_basis hF hy, ← Algebra.discr_reindex _ _ (finCongr hdim)]
  congr 1
  ext i
  simp_rw [Function.comp_apply, Module.Basis.localizationLocalization_apply, PowerBasis.coe_basis,
    map_pow, hgen, By_gen]
  rfl

end EisCubic

namespace Cyclo9Cubic

variable {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {9} ℚ L]

local notation "K" => IntermediateField.fixedField (H (L := L))

/-- y = θ + 1 ∈ K. -/
noncomputable def yK : K := ⟨θ + 1, add_mem theta_mem (one_mem _)⟩

theorem yK_root : (yK : K) ^ 3 - 3 * yK ^ 2 + 3 = 0 := by
  apply (algebraMap K L).injective
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_zero]
  show ((θ : L) + 1) ^ 3 - 3 * (θ + 1) ^ 2 + 3 = 0
  linear_combination theta_root (L := L)

/-- **𝓞_K = ℤ[θ + 1] (= ℤ[θ]).** -/
theorem ringOfIntegers_K :
    IsIntegralClosure (Algebra.adjoin ℤ ({yK} : Set K)) ℤ K :=
  EisCubic.isIntegralClosure finrank_K yK_root

/-- **disc K = 81.** -/
theorem discr_K : NumberField.discr K = 81 :=
  EisCubic.discr_eq finrank_K yK_root

end Cyclo9Cubic

#print axioms EisCubic.discr_basis
#print axioms EisCubic.isIntegralClosure
#print axioms EisCubic.discr_eq
#print axioms Cyclo9Cubic.discr_K
