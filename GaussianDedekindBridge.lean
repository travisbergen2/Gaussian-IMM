import GaussianSynthesis

/-!
# GaussianDedekindBridge

Identifies the frozen ideal-counting series of ℤ[i] (`GaussianSynthesis.LSeries_ideal_count`)
with Mathlib's `NumberField.dedekindZeta` of the concrete field ℚ(i) = `QuadraticAlgebra ℚ (-1) 0`.
Imports the frozen layer; does not modify it.
-/

open QuadraticAlgebra NumberField Ideal

/-! ## Milestone 1: −4 is a fundamental discriminant -/

theorem gaussian_discr : discr (-1 : ℤ) 0 = -4 := by rw [discr_def]; norm_num

theorem gaussian_discr_fundamental : (discr (-1 : ℤ) 0).IsFundamentalDiscr := by
  rw [gaussian_discr, show (-4 : ℤ) = 4 * (-1) by norm_num, Int.isFundamentalDiscr_four_mul]
  exact ⟨by simp, by decide⟩

/-! ## Milestone 2: ℤ[ω] ≃ₐ[ℤ] integral closure of ℤ in ℚ[ω] -/

/-- The concrete field ℚ(i), written with the same (cast) parameters the API uses. -/
abbrev Qi := QuadraticAlgebra ℚ ((-1 : ℤ) : ℚ) ((0 : ℤ) : ℚ)

noncomputable def gaussianIntegralClosureEquiv :
    Zi ≃ₐ[ℤ] integralClosure ℤ Qi :=
  QuadraticAlgebra.Int.algEquivIntegralClosure gaussian_discr_fundamental

/-! ## Milestone 3: ℚ(i) is a number field and 𝓞 ℚ(i) ≃ ℤ[ω] -/

instance : Fact (¬ IsSquare (discr ((-1 : ℤ) : ℚ) ((0 : ℤ) : ℚ))) := by
  refine ⟨fun ⟨r, hr⟩ => ?_⟩
  rw [discr_def] at hr
  push_cast at hr
  nlinarith [sq_nonneg r]

instance : NumberField Qi where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance

/-- 𝓞 ℚ(i) is, by definition, the integral closure — so ℤ[ω] ≃+* 𝓞 ℚ(i). -/
noncomputable def ringOfIntegersEquiv : Zi ≃+* 𝓞 Qi :=
  gaussianIntegralClosureEquiv.toRingEquiv

/-! ## Milestone 4: transfer to `NumberField.dedekindZeta` -/

instance : Infinite Zi := Infinite.of_injective (fun n : ℕ => (n : Zi))
  (fun m n h => by have := congrArg QuadraticAlgebra.re h; simpa using this)

instance : Infinite (𝓞 Qi) := Infinite.of_injective _ ringOfIntegersEquiv.injective

/-- A ring equivalence preserves ideal norms. -/
theorem absNorm_comap (I : Ideal (𝓞 Qi)) :
    absNorm (I.comap ringOfIntegersEquiv) = absNorm I := by
  rw [absNorm_apply, absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  have h : I = (I.comap ringOfIntegersEquiv).map ringOfIntegersEquiv :=
    (map_comap_of_surjective _ ringOfIntegersEquiv.surjective I).symm
  exact Nat.card_congr (quotientEquiv _ I ringOfIntegersEquiv h).toEquiv

/-- The two ideal counts agree for every n. -/
theorem card_ideals_eq (n : ℕ) :
    Nat.card {J : Ideal (𝓞 Qi) // absNorm J = n} = a n := by
  rw [a]
  exact Nat.card_congr ((ringOfIntegersEquiv.idealComapOrderIso).toEquiv.subtypeEquiv
    fun J => by simp [absNorm_comap])

/-- **ζ_{ℚ(i)}(s) = ζ(s) · L(s, χ₄) for Re s > 1**, for Mathlib's own Dedekind zeta. -/
theorem dedekindZeta_Qi {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta Qi s = riemannZeta s * LSeries GaussianLSeries.chi4 s := by
  rw [← GaussianSynthesis.LSeries_ideal_count hs, dedekindZeta]
  congr 1
  funext n
  rw [card_ideals_eq]

#print axioms gaussian_discr_fundamental
#print axioms gaussianIntegralClosureEquiv
#print axioms ringOfIntegersEquiv
#print axioms absNorm_comap
#print axioms card_ideals_eq
#print axioms dedekindZeta_Qi
