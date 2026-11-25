import Mathlib

/-!
# CubicGaussSumIdentity — g(χ)³ = q · J(χ, χ) for a cubic character

Generic (imports only Mathlib). F a finite field with q elements, R an integral domain,
χ : F → R a multiplicative character of order 3, ψ : F → R a primitive additive character.
Conventions (Mathlib's): χ(0) = 0;
  g(χ) = `gaussSum χ ψ` = Σ_{a ∈ F} χ(a) ψ(a),   J(χ, φ) = `jacobiSum χ φ` = Σ_{a ∈ F} χ(a) φ(1 − a).
For F = ZMod p and ψ(a) = ζ_p^a (`AddChar.zmodChar`), g(χ) = Σ χ(a) ζ_p^a.

* `ne_one`, `neg_one` (χ(−1) = 1: odd order), `sq_eq_inv` (χ² = χ⁻¹), `three_dvd_card_sub_one`;
* `gauss_jacobi`: g(χ)² = J(χ, χ) · g(χ²) (Mathlib `jacobiSum_mul_nontrivial`);
* `gauss_product`: g(χ) · g(χ²) = q (Mathlib `gaussSum_mul_gaussSum_pow_orderOf_sub_one`, χ(−1) = 1);
* `gaussSum_cube`: **g(χ)³ = q · J(χ, χ)**, from the two identities above;
* `jacobiSum_mem` / `jacobiSum_primary`: for μ a primitive cube root of unity in R,
  J(χ, χ) ∈ ℤ[μ] and J(χ, χ) = −1 + z(μ − 1)² with z ∈ ℤ[μ] (Mathlib);
* `normSq_jacobiSum` (R = ℂ): |J(χ, χ)|² = q, i.e. N(J(χ, χ)) = q.
-/

open Finset

namespace CubicGauss

variable {F R : Type*} [Fintype F] [Field F] [CommRing R] [IsDomain R]
  {χ : MulChar F R} (hχ : orderOf χ = 3)

include hχ

omit [Fintype F] [IsDomain R] in
theorem ne_one : χ ≠ 1 := by
  rintro rfl; rw [orderOf_one] at hχ; norm_num at hχ

omit [Fintype F] [IsDomain R] in
theorem pow_three : χ ^ 3 = 1 := by rw [← hχ]; exact pow_orderOf_eq_one χ

omit [Fintype F] [IsDomain R] in
/-- χ(−1) = 1 (χ has odd order). -/
theorem neg_one : χ (-1) = 1 :=
  MulChar.val_neg_one_eq_one_of_odd_order (by decide : Odd 3) (pow_three hχ)

omit [Fintype F] [IsDomain R] in
theorem sq_eq_inv : χ ^ 2 = χ⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← pow_succ, pow_three hχ])

omit [Fintype F] [IsDomain R] in
theorem sq_ne_one : χ ^ 2 ≠ 1 := by
  rw [sq_eq_inv hχ, Ne, inv_eq_one]; exact ne_one hχ

omit [IsDomain R] in
/-- 3 ∣ q − 1. -/
theorem three_dvd_card_sub_one : 3 ∣ Fintype.card F - 1 := hχ ▸ χ.orderOf_dvd_card_sub_one

variable {ψ : AddChar F R}

/-- **Gauss–Jacobi:** g(χ)² = J(χ, χ) · g(χ²). -/
theorem gauss_jacobi : gaussSum χ ψ ^ 2 = jacobiSum χ χ * gaussSum (χ ^ 2) ψ := by
  have h := jacobiSum_mul_nontrivial (by rw [← pow_two]; exact sq_ne_one hχ) ψ
  rw [← pow_two] at h
  rw [pow_two, ← h, mul_comm, pow_two]

/-- **Gauss product:** g(χ) · g(χ²) = q. -/
theorem gauss_product (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * gaussSum (χ ^ 2) ψ = Fintype.card F := by
  have h := gaussSum_mul_gaussSum_pow_orderOf_sub_one (ne_one hχ) hψ
  rw [hχ, neg_one hχ, one_mul] at h
  exact h

/-- **The cubic Gauss sum identity: g(χ)³ = q · J(χ, χ).** -/
theorem gaussSum_cube (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ ^ 3 = Fintype.card F * jacobiSum χ χ := by
  rw [pow_succ, gauss_jacobi hχ, mul_assoc, mul_comm (gaussSum (χ ^ 2) ψ), gauss_product hχ hψ,
    mul_comm]

/-- J(χ, χ) ∈ ℤ[μ] for a primitive cube root of unity μ. -/
theorem jacobiSum_mem {μ : R} (hμ : IsPrimitiveRoot μ 3) :
    jacobiSum χ χ ∈ Algebra.adjoin ℤ {μ} :=
  jacobiSum_mem_algebraAdjoin_of_pow_eq_one (pow_three hχ) (pow_three hχ) hμ

/-- **Primary normalization:** J(χ, χ) = −1 + z(μ − 1)², z ∈ ℤ[μ]. -/
theorem jacobiSum_primary {μ : R} (hμ : IsPrimitiveRoot μ 3) :
    ∃ z ∈ Algebra.adjoin ℤ {μ}, jacobiSum χ χ = -1 + z * (μ - 1) ^ 2 :=
  exists_jacobiSum_eq_neg_one_add (by norm_num) (pow_three hχ) (pow_three hχ)
    (three_dvd_card_sub_one hχ) hμ

end CubicGauss

namespace CubicGauss

variable {F : Type*} [Fintype F] [Field F] {χ : MulChar F ℂ} (hχ : orderOf χ = 3)

include hχ

theorem inv_apply_eq_conj (a : F) : χ⁻¹ a = starRingEnd ℂ (χ a) := by
  rw [MulChar.inv_apply_eq_inv']
  by_cases ha : IsUnit a
  · have h3 : (χ a) ^ 3 = 1 := by
      rw [← MulChar.pow_apply' _ (by norm_num), pow_three hχ, MulChar.one_apply ha]
    exact Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one h3 (by norm_num))
  · rw [MulChar.map_nonunit _ ha, inv_zero, map_zero]

/-- **N(J(χ, χ)) = q:** J(χ, χ) · conj J(χ, χ) = q. -/
theorem normSq_jacobiSum : Complex.normSq (jacobiSum χ χ) = Fintype.card F := by
  have hc : ringChar ℂ ≠ ringChar F := by
    rw [ringChar.eq_zero]
    exact (CharP.char_ne_zero_of_finite F (ringChar F)).symm
  have h := jacobiSum_mul_jacobiSum_inv hc (ne_one hχ) (ne_one hχ)
    (by rw [← pow_two]; exact sq_ne_one hχ)
  have hconj : jacobiSum χ⁻¹ χ⁻¹ = starRingEnd ℂ (jacobiSum χ χ) := by
    simp only [jacobiSum, map_sum, map_mul, inv_apply_eq_conj hχ]
  rw [hconj, Complex.mul_conj] at h
  exact_mod_cast h

end CubicGauss

namespace CubicGauss

/-- **Over 𝔽_p:** for p prime, χ of order 3 mod p and ζ a primitive p-th root of unity,
(Σ_a χ(a) ζ^a)³ = p · J(χ, χ). -/
theorem gaussSum_cube_zmod {p : ℕ} [Fact p.Prime] {χ : MulChar (ZMod p) ℂ} (hχ : orderOf χ = 3)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ p) :
    gaussSum χ (AddChar.zmodChar p hζ.pow_eq_one) ^ 3 = p * jacobiSum χ χ := by
  rw [gaussSum_cube hχ (AddChar.zmodChar_primitive_of_primitive_root p hζ), ZMod.card]

/-- Such a χ exists exactly when 3 ∣ p − 1 (i.e. p ≡ 1 mod 3). -/
theorem exists_cubic_char {p : ℕ} [Fact p.Prime] (hp : 3 ∣ p - 1) :
    ∃ χ : MulChar (ZMod p) ℂ, orderOf χ = 3 := by
  have hμ := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  exact MulChar.exists_mulChar_orderOf (ZMod p) (by rwa [ZMod.card]) hμ

end CubicGauss

#print axioms CubicGauss.gaussSum_cube_zmod
#print axioms CubicGauss.exists_cubic_char
#print axioms CubicGauss.gauss_jacobi
#print axioms CubicGauss.gauss_product
#print axioms CubicGauss.gaussSum_cube
#print axioms CubicGauss.jacobiSum_primary
#print axioms CubicGauss.normSq_jacobiSum
