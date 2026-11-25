import CubicGaussSumIdentity

/-!
# EisensteinJacobiPrime — J(χ, χ) is a primary prime of ℤ[ω] above q

K = ℚ(ω) (`IsCyclotomicExtension {3} ℚ K`), ω a primitive cube root of unity, 𝓞_K = ℤ[ω]
(a PID, Mathlib `three_pid`). F a finite field with q elements, q prime, χ : F → K of order 3.
* `prime_of_norm` (generic number field): an algebraic integer of norm q (q prime) is prime
  (its principal ideal has prime absolute norm);
* `conj_jacobiSum`: σ(J(χ, χ)) = J(χ⁻¹, χ⁻¹), σ the automorphism ω ↦ ω²;
* `norm_jacobiSum`: N_{K/ℚ}(J(χ, χ)) = J · σ(J) = q;
* `J`: J(χ, χ) as an element of 𝓞_K; `J_mul_conj`: q = J · J̄ in 𝓞_K;
* `J_prime`: J is prime in ℤ[ω]; `J_primary`: J ≡ −1 mod (ω − 1)².
-/

open NumberField IsCyclotomicExtension Finset

namespace EisJacobi

/-- An algebraic integer whose norm is a rational prime is a prime element. -/
theorem prime_of_norm {K : Type*} [Field K] [NumberField K] {x : 𝓞 K} {q : ℕ}
    (hq : q.Prime) (hx : Algebra.norm ℚ (x : K) = q) : Prime x := by
  apply Ideal.prime_of_irreducible_absNorm_span
  have h : Algebra.norm ℤ x = q := by exact_mod_cast (Algebra.coe_norm_int x).trans hx
  rw [Ideal.absNorm_span_singleton, h, Int.natAbs_natCast]
  exact hq.prime.irreducible

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
  {F : Type*} [Fintype F] [Field F] {χ : MulChar F K} (hχ : orderOf χ = 3)

local notation "ω" => IsCyclotomicExtension.zeta 3 ℚ K

theorem hω : IsPrimitiveRoot (ω) 3 := zeta_spec 3 ℚ K

/-- σ : ω ↦ ω², the nontrivial automorphism of ℚ(ω). -/
noncomputable def σ : Gal(K/ℚ) := (Rat.galEquivZMod 3 K).symm (-1)

theorem σ_ω : σ (ω) = (ω) ^ 2 := by
  have := Rat.galEquivZMod_apply_of_pow_eq 3 K (σ (K := K)) (hω (K := K)).pow_eq_one
  rw [this, σ, MulEquiv.apply_symm_apply]
  rfl

theorem σ_ne_one : σ (K := K) ≠ 1 := by
  intro h
  have := σ_ω (K := K)
  rw [h, AlgEquiv.one_apply] at this
  have h1 : (ω) ^ 1 = (ω) ^ 2 := by rw [pow_one]; exact this
  have := (hω (K := K)).pow_inj (by norm_num) (by norm_num) h1
  norm_num at this

open Classical in
theorem univ_gal : (univ : Finset Gal(K/ℚ)) = {1, σ} := by
  have hcard : Fintype.card Gal(K/ℚ) = 2 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr (Rat.galEquivZMod 3 K).toEquiv,
      Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    decide
  refine (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_).symm
  rw [Finset.card_univ, hcard, Finset.card_pair (Ne.symm (σ_ne_one (K := K)))]

include hχ in
/-- σ ∘ χ = χ⁻¹. -/
theorem σ_chi (a : F) : σ (χ a) = χ⁻¹ a := by
  rw [MulChar.inv_apply_eq_inv']
  by_cases ha : IsUnit a
  · have h3 : (χ a) ^ 3 = 1 := by
      rw [← MulChar.pow_apply' _ (by norm_num), CubicGauss.pow_three hχ, MulChar.one_apply ha]
    obtain ⟨i, -, hi⟩ := (hω (K := K)).eq_pow_of_pow_eq_one h3
    rw [← hi, map_pow, σ_ω, ← pow_mul]
    exact eq_inv_of_mul_eq_one_left (by
      rw [← pow_add, show 2 * i + i = 3 * i by ring, pow_mul, (hω (K := K)).pow_eq_one, one_pow])
  · rw [MulChar.map_nonunit _ ha, map_zero, inv_zero]

include hχ in
/-- **σ(J(χ, χ)) = J(χ⁻¹, χ⁻¹).** -/
theorem conj_jacobiSum : σ (jacobiSum χ χ) = jacobiSum χ⁻¹ χ⁻¹ := by
  simp only [jacobiSum, map_sum, map_mul, σ_chi hχ]

include hχ in
theorem jacobiSum_mul_conj : jacobiSum χ χ * jacobiSum χ⁻¹ χ⁻¹ = Fintype.card F := by
  have hc : ringChar K ≠ ringChar F := by
    rw [ringChar.eq_zero]; exact (CharP.char_ne_zero_of_finite F (ringChar F)).symm
  exact jacobiSum_mul_jacobiSum_inv hc (CubicGauss.ne_one hχ) (CubicGauss.ne_one hχ)
    (by rw [← pow_two]; exact CubicGauss.sq_ne_one hχ)

include hχ in
/-- **N(J(χ, χ)) = q.** -/
theorem norm_jacobiSum : Algebra.norm ℚ (jacobiSum χ χ) = Fintype.card F := by
  classical
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {3} ℚ K
  apply (algebraMap ℚ K).injective
  rw [Algebra.norm_eq_prod_automorphisms, univ_gal, Finset.prod_pair (σ_ne_one (K := K)).symm,
    AlgEquiv.one_apply, conj_jacobiSum hχ, jacobiSum_mul_conj hχ, map_natCast]

include hχ in
theorem isIntegral_jacobiSum (φ : MulChar F K) (hφ : orderOf φ = 3) :
    jacobiSum φ φ ∈ integralClosure ℤ K :=
  (adjoin_le_integralClosure ((hω (K := K)).isIntegral (by norm_num))
    (CubicGauss.jacobiSum_mem hφ (hω (K := K))))

include hχ in
/-- J(χ, χ) ∈ 𝓞_K = ℤ[ω]. -/
noncomputable def J : 𝓞 K := ⟨jacobiSum χ χ, isIntegral_jacobiSum hχ χ hχ⟩

include hχ in
/-- J̄ = J(χ⁻¹, χ⁻¹) ∈ 𝓞_K. -/
noncomputable def Jbar : 𝓞 K :=
  ⟨jacobiSum χ⁻¹ χ⁻¹, isIntegral_jacobiSum hχ χ⁻¹ (by rw [orderOf_inv, hχ])⟩

/-- **q = J · J̄** in ℤ[ω], with J̄ = σ(J). -/
theorem J_mul_conj : J hχ * Jbar hχ = (Fintype.card F : 𝓞 K) := by
  apply RingOfIntegers.ext
  show algebraMap (𝓞 K) K (J hχ * Jbar hχ) = algebraMap (𝓞 K) K (Fintype.card F : 𝓞 K)
  rw [map_mul, map_natCast]
  exact jacobiSum_mul_conj hχ

/-- **J is prime in ℤ[ω]** when q is prime. -/
theorem J_prime (hq : (Fintype.card F).Prime) : Prime (J hχ) :=
  prime_of_norm hq (norm_jacobiSum hχ)

/-- **J is primary:** J ≡ −1 mod (ω − 1)². -/
theorem J_primary :
    ∃ z : 𝓞 K, J hχ = -1 + z * ((hω (K := K)).toInteger - 1) ^ 2 := by
  obtain ⟨z, hz, hJ⟩ := CubicGauss.jacobiSum_primary hχ (hω (K := K))
  have hzi : z ∈ integralClosure ℤ K :=
    adjoin_le_integralClosure ((hω (K := K)).isIntegral (by norm_num)) hz
  refine ⟨⟨z, hzi⟩, RingOfIntegers.ext ?_⟩
  show algebraMap (𝓞 K) K (J hχ) = algebraMap (𝓞 K) K (-1 + ⟨z, hzi⟩ * ((hω (K := K)).toInteger - 1) ^ 2)
  simp only [map_add, map_neg, map_one, map_mul, map_pow, map_sub]
  exact hJ

end EisJacobi

#print axioms EisJacobi.prime_of_norm
#print axioms EisJacobi.norm_jacobiSum
#print axioms EisJacobi.J_mul_conj
#print axioms EisJacobi.J_prime
#print axioms EisJacobi.J_primary
