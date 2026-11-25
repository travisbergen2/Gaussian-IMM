import CyclotomicSqrt
import CyclotomicSubfieldSplitting

/-!
# QuadraticKroneckerWeber — every quadratic field is a subfield of a cyclotomic field

K a number field with [K : ℚ] = 2.
* `exists_quadratic_relation`: K = ℚ(α) with α² + bα + c = 0, b, c ∈ ℚ;
* `exists_embedding`: with D = b² − 4c and m = num(D)·den(D) ∈ ℤ, there is a ℚ-algebra embedding
  K → ℚ(ζ_N) with N = 8|m| (N = 8 if m = 0): α ↦ (√m / den(D) − b)/2, √m from `CycloSqrt`
  (Gauss sums, ζ₈ + ζ₈⁻¹, ζ₄);
* `quadratic_kronecker_weber`: there are N ≠ 0 and H ≤ Gal(ℚ(ζ_N)/ℚ) of index 2 with
  K ≃ₐ[ℚ] ℚ(ζ_N)^H.
This is the degree-2 case of Kronecker–Weber only. It does not identify H as ker χ_D.
-/

open Polynomial IntermediateField

namespace QuadKW

variable (K : Type*) [Field K] [NumberField K]

/-- For a primitive element α of a quadratic field: minpoly α = X² + bX + c, evaluated anywhere. -/
theorem aeval_minpoly {α : K} (hdeg : (minpoly ℚ α).natDegree = 2) {F : Type*} [Field F]
    [Algebra ℚ F] (x : F) :
    aeval x (minpoly ℚ α) =
      x ^ 2 + algebraMap ℚ F ((minpoly ℚ α).coeff 1) * x +
        algebraMap ℚ F ((minpoly ℚ α).coeff 0) := by
  have hmon : (minpoly ℚ α).coeff 2 = 1 := by
    rw [← hdeg]; exact minpoly.monic (Algebra.IsIntegral.isIntegral α)
  conv_lhs => rw [(minpoly ℚ α).as_sum_range_C_mul_X_pow, hdeg]
  simp [Finset.sum_range_succ, hmon]
  ring

variable {K}

theorem exists_primitive (hK : Module.finrank ℚ K = 2) :
    ∃ α : K, ℚ⟮α⟯ = ⊤ ∧ (minpoly ℚ α).natDegree = 2 := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ K
  refine ⟨α, hα, ?_⟩
  rw [← adjoin.finrank (Algebra.IsIntegral.isIntegral α), hα, finrank_top', hK]

/-- **K embeds in every ℚ(ζ_N)**, for a suitable N ≠ 0 (N = 8|m| or 8). -/
theorem exists_embedding (hK : Module.finrank ℚ K = 2) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ (L : Type*) [Field L] [CharZero L] [IsCyclotomicExtension {N} ℚ L],
      Nonempty (K →ₐ[ℚ] L) := by
  obtain ⟨α, hα, hdeg⟩ := exists_primitive hK
  set b := (minpoly ℚ α).coeff 1
  set c := (minpoly ℚ α).coeff 0
  set D : ℚ := b ^ 2 - 4 * c
  set m : ℤ := D.num * D.den
  set N : ℕ := if m = 0 then 8 else 8 * m.natAbs
  have hN0 : N ≠ 0 := by simp only [N]; split_ifs with h <;> simp [h]
  have h8 : 8 ∣ N := by simp only [N]; split_ifs <;> simp
  have hmN : m = 0 ∨ m.natAbs ∣ N := by
    by_cases h : m = 0
    · exact Or.inl h
    · right; simp only [N, if_neg h]; exact Dvd.intro_left 8 rfl
  refine ⟨N, hN0, fun L _ _ _ => ?_⟩
  have : NeZero N := ⟨hN0⟩
  obtain ⟨y, hy⟩ := CycloSqrt.exists_sq_int (IsCyclotomicExtension.zeta_spec N ℚ L) h8 hmN
  have hden : (D.den : L) ≠ 0 := Nat.cast_ne_zero.mpr D.den_nz
  set z : L := y / D.den
  have hz : z ^ 2 = algebraMap ℚ L D := by
    rw [div_pow, hy, div_eq_iff (pow_ne_zero 2 hden), eq_ratCast, Rat.cast_def]
    simp only [m, Int.cast_mul, Int.cast_natCast]
    field_simp
  set y' : L := (z - algebraMap ℚ L b) / 2
  have hroot : aeval y' (minpoly ℚ α) = 0 := by
    rw [aeval_minpoly K hdeg]
    have : algebraMap ℚ L D = (algebraMap ℚ L b) ^ 2 - 4 * algebraMap ℚ L c := by
      simp only [D, map_sub, map_pow, map_mul, map_ofNat]
    simp only [y']
    linear_combination (1 / 4 : L) * (hz.trans this)
  have hint : IsIntegral ℚ α := Algebra.IsIntegral.isIntegral α
  have hmem : y' ∈ (minpoly ℚ α).aroots L :=
    (mem_aroots).mpr ⟨minpoly.ne_zero hint, hroot⟩
  let φ0 : ℚ⟮α⟯ →ₐ[ℚ] L := (algHomAdjoinIntegralEquiv ℚ hint).symm ⟨y', hmem⟩
  exact ⟨φ0.comp ((equivOfEq hα.symm).toAlgHom.comp topEquiv.symm.toAlgHom)⟩

/-- **Quadratic Kronecker–Weber:** for a suitable N ≠ 0 and every L = ℚ(ζ_N), K ≅ L^H for some
H ≤ Gal(L/ℚ) of index 2. -/
theorem quadratic_kronecker_weber (hK : Module.finrank ℚ K = 2) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ (L : Type*) [Field L] [CharZero L] [IsCyclotomicExtension {N} ℚ L],
      ∃ H : Subgroup Gal(L/ℚ), H.index = 2 ∧ Nonempty (K ≃ₐ[ℚ] fixedField H) := by
  obtain ⟨N, hN0, hemb⟩ := exists_embedding hK
  refine ⟨N, hN0, fun L _ _ _ => ?_⟩
  have : NeZero N := ⟨hN0⟩
  obtain ⟨φ⟩ := hemb L
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {N} ℚ L
  have : FiniteDimensional ℚ L := IsCyclotomicExtension.finiteDimensional {N} ℚ L
  set E : IntermediateField ℚ L := IntermediateField.map φ ⊤
  have hE : fixedField E.fixingSubgroup = E := IsGalois.fixedField_fixingSubgroup E
  let e : K ≃ₐ[ℚ] fixedField E.fixingSubgroup :=
    (topEquiv.symm.trans ((⊤ : IntermediateField ℚ K).equivMap φ)).trans (equivOfEq hE.symm)
  refine ⟨E.fixingSubgroup, ?_, ⟨e⟩⟩
  rw [← CycloSub.finrank_K (L := L) E.fixingSubgroup, ← e.toLinearEquiv.finrank_eq, hK]

/-- The hypotheses are met by Mathlib's `CyclotomicField N ℚ` (with the canonical ℚ-algebra
structure, which equals the `CyclotomicField` one since ℚ-algebra structures are unique). -/
theorem cyclotomicField_isCyclotomic (N : ℕ) [NeZero N] :
    @IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) _ _ DivisionRing.toRatAlgebra := by
  convert CyclotomicField.isCyclotomicExtension N ℚ
  exact Subsingleton.elim (α := Algebra ℚ (CyclotomicField N ℚ)) _ _

/-- **Concrete form:** K ≅ (CyclotomicField N ℚ)^H, [Gal : H] = 2. -/
theorem quadratic_kronecker_weber_cyclotomicField (hK : Module.finrank ℚ K = 2) :
    ∃ N : ℕ, ∃ _ : NeZero N, ∃ H : Subgroup ((CyclotomicField N ℚ) ≃ₐ[ℚ] (CyclotomicField N ℚ)),
      H.index = 2 ∧ Nonempty (K ≃ₐ[ℚ] fixedField H) := by
  obtain ⟨N, hN0, h⟩ := quadratic_kronecker_weber hK
  have : NeZero N := ⟨hN0⟩
  have := cyclotomicField_isCyclotomic N
  exact ⟨N, ⟨hN0⟩, h (CyclotomicField N ℚ)⟩

end QuadKW

#print axioms QuadKW.exists_embedding
#print axioms QuadKW.quadratic_kronecker_weber
#print axioms QuadKW.quadratic_kronecker_weber_cyclotomicField
