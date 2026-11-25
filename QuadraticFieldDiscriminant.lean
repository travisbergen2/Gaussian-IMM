import QuadraticAlgebraTrace

/-!
# QuadraticFieldDiscriminant — ring of integers and discriminant of a quadratic field

K a number field, [K : ℚ] = 2, γ ∈ K ∖ ℚ with γ² = d ∈ ℤ. Write d = e²f with f squarefree and set
D = f if f ≡ 1 (mod 4), D = 4f otherwise (`fundamental_of_squarefree`: D is a fundamental
discriminant, Mathlib's `Int.IsFundamentalDiscr`). With a = D/4, b = D mod 4 (so b² + 4a = D):
* `algEquiv`: K ≅ `QuadraticAlgebra ℚ a b`, ω ↦ θ = (b + √D)/2;
* `ringOfIntegers_equiv`: 𝓞_K ≅ `QuadraticAlgebra ℤ a b` = ℤ[θ] (Mathlib's
  `QuadraticAlgebra.Int.algEquivIntegralClosure`, valid because D is fundamental), i.e.
  𝓞_K = ℤ[√f] if f ≢ 1 and ℤ[(1 + √f)/2] if f ≡ 1 (mod 4);
* `discr_eq`: `NumberField.discr K = D` (the basis 1, θ has discriminant b² + 4a);
* `sqrt_discr`: √D ∈ K ∖ ℚ.
-/

open NumberField QuadraticAlgebra

namespace QuadDiscr

theorem fundamental_of_squarefree {f : ℤ} (hf : Squarefree f) :
    Int.IsFundamentalDiscr (if f % 4 = 1 then f else 4 * f) := by
  rw [Int.isFundamentalDiscr_iff_squarefree]
  have h4 : ¬ (4 : ℤ) ∣ f := by
    intro h
    have := hf 2 (by simpa [show (2 : ℤ) * 2 = 4 by norm_num] using h)
    simp [Int.isUnit_iff] at this
  have h4' : f % 4 ≠ 0 := fun h => h4 (Int.dvd_of_emod_eq_zero h)
  split_ifs with h
  · exact Or.inl ⟨h, hf⟩
  · right
    refine ⟨by simp, by simpa using hf, ?_⟩
    simp only [Int.mul_ediv_cancel_left _ (by norm_num : (4 : ℤ) ≠ 0)]
    omega

variable {K : Type*} [Field K] [NumberField K]

/-- **The quadratic-field structure theorem.** -/
theorem structure_thm (hK : Module.finrank ℚ K = 2) {γ : K} {d : ℤ} (hγ : γ ^ 2 = d)
    (hγQ : γ ∉ Set.range (algebraMap ℚ K)) :
    ∃ D : ℤ, Int.IsFundamentalDiscr D ∧
      Nonempty (QuadraticAlgebra ℚ ((D / 4 : ℤ) : ℚ) ((D % 4 : ℤ) : ℚ) ≃ₐ[ℚ] K) ∧
      Nonempty (QuadraticAlgebra ℤ (D / 4) (D % 4) ≃+* 𝓞 K) ∧
      NumberField.discr K = D ∧
      ∃ s : K, s ^ 2 = D ∧ s ∉ Set.range (algebraMap ℚ K) := by
  -- squarefree part
  have hd : d ≠ 0 := by
    rintro rfl
    have h0 : γ = 0 := by simpa using hγ
    exact hγQ ⟨0, by simp [h0]⟩
  obtain ⟨e, f, hef, hf⟩ := exists_sq_mul_squarefree d
  have he : e ≠ 0 := by rintro rfl; simp at hef; exact hd hef.symm
  have heK : (e : K) ≠ 0 := Int.cast_ne_zero.mpr he
  set s0 : K := γ / e
  have hs0 : s0 ^ 2 = f := by
    rw [div_pow, hγ, ← hef, div_eq_iff (pow_ne_zero 2 heK)]; push_cast; ring
  set D : ℤ := if f % 4 = 1 then f else 4 * f
  set s : K := if f % 4 = 1 then s0 else 2 * s0
  have hs : s ^ 2 = D := by
    simp only [s, D]; split_ifs
    · exact hs0
    · rw [mul_pow, hs0]; push_cast; ring
  have hsQ : s ∉ Set.range (algebraMap ℚ K) := by
    rintro ⟨r, hr⟩
    apply hγQ
    have hg : γ = e * s0 := by simp only [s0]; field_simp
    simp only [s] at hr
    split_ifs at hr
    · exact ⟨e * r, by rw [hg, ← hr]; simp⟩
    · have h2 : s0 = algebraMap ℚ K r / 2 := by rw [hr]; ring
      exact ⟨e * r / 2, by rw [hg, h2]; simp [map_div₀]; ring⟩
  have hfund : Int.IsFundamentalDiscr D := fundamental_of_squarefree hf
  have hab : discr (D / 4) (D % 4) = D := discr_ediv_emod hfund.emod_four_eq_zero_or_one
  set a : ℤ := D / 4
  set b : ℤ := D % 4
  have hab' : (b : K) ^ 2 + 4 * a = D := by
    rw [discr_def] at hab; exact_mod_cast hab
  set θ : K := ((b : K) + s) / 2
  have hθ : θ * θ = ((a : ℚ)) • (1 : K) + ((b : ℚ)) • θ := by
    simp only [θ, Algebra.smul_def, map_intCast, mul_one]
    linear_combination (1 / 4 : K) * hs - (1 / 4 : K) * hab'
  set φ := QuadraticAlgebra.lift (R := ℚ) (a := (a : ℚ)) (b := (b : ℚ)) ⟨θ, hθ⟩
  have hθQ : ∀ r : ℚ, algebraMap ℚ K r ≠ θ := by
    intro r hr
    apply hsQ
    refine ⟨2 * r - b, ?_⟩
    simp only [map_sub, map_mul, map_ofNat, map_intCast, hr, θ]
    ring
  have hinj : Function.Injective φ := by
    rw [lift_injective_iff, LinearIndependent.pair_iff]
    intro u v huv
    by_cases hv : v = 0
    · subst hv; simpa using huv
    · exfalso
      apply hθQ (-u / v)
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at huv
      have hvK : algebraMap ℚ K v ≠ 0 := by simpa using hv
      rw [map_div₀, map_neg, div_eq_iff hvK]
      linear_combination -huv
  have hsurj : Function.Surjective φ := by
    have := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := φ.toLinearMap)
      (by rw [QuadraticAlgebra.finrank_eq_two, hK])).mp hinj
    exact this
  let eK : QuadraticAlgebra ℚ (a : ℚ) (b : ℚ) ≃ₐ[ℚ] K := AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩
  -- rings of integers
  have hfund' : Int.IsFundamentalDiscr (discr a b) := by rw [hab]; exact hfund
  let g : integralClosure ℤ (QuadraticAlgebra ℚ (a : ℚ) (b : ℚ)) ≃+* 𝓞 K :=
    { toFun := fun x => ⟨eK x, x.2.map (eK.toAlgHom.restrictScalars ℤ)⟩
      invFun := fun y => ⟨eK.symm y, y.2.map (eK.symm.toAlgHom.restrictScalars ℤ)⟩
      left_inv := fun x => Subtype.ext (eK.symm_apply_apply _)
      right_inv := fun y => RingOfIntegers.ext (eK.apply_symm_apply _)
      map_mul' := fun x y => RingOfIntegers.ext (map_mul eK _ _)
      map_add' := fun x y => RingOfIntegers.ext (map_add eK _ _) }
  let F : QuadraticAlgebra ℤ a b ≃+* 𝓞 K := (Int.algEquivIntegralClosure hfund').toRingEquiv.trans g
  refine ⟨D, hfund, ⟨eK⟩, ⟨F⟩, ?_, s, hs, hsQ⟩
  -- discriminant
  let B := (basis a b).map F.toIntAlgEquiv.toLinearEquiv
  rw [← NumberField.discr_eq_discr K B]
  have hB : (B : Fin 2 → 𝓞 K) = F.toIntAlgEquiv ∘ (basis a b) := by
    funext i; simp [B]
  rw [hB, ← Algebra.discr_eq_discr_of_algEquiv, QuadTrace.discr_basis, hab]

end QuadDiscr

#print axioms QuadDiscr.fundamental_of_squarefree
#print axioms QuadDiscr.structure_thm
