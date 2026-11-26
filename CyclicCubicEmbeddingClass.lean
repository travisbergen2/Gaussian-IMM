import Mathlib

/-!
# CyclicCubicEmbeddingClass — abstract Galois number fields vs. their images in ℂ

E an abstract number field, Galois over ℚ (e.g. cyclic cubic). An *embedding* is a ℚ-algebra map
φ : E →ₐ[ℚ] ℂ; its image `φ.fieldRange` is a subfield of ℂ. (An automorphism of the image moves
elements inside the image; it does not change the image.)
* `exists_embedding`: E has an embedding into ℂ;
* `fieldRange_eq`: **all embeddings of E have the same image** (E normal: the image of one
  embedding is a normal subfield of ℂ, which every other embedding maps onto,
  `AlgHom.fieldRange_of_normal`);
* `isGalois_range`, `finrank_range`: the image is Galois with [image : ℚ] = [E : ℚ];
* `subfield_eq_range`: a subfield K ⊆ ℂ isomorphic to E is that image;
* `iso_iff_range_eq`: two such fields are ℚ-isomorphic iff their images in ℂ are equal.
So ℚ-isomorphism classes of Galois number fields correspond bijectively to their images, the
Galois subfields of ℂ; in particular for cyclic cubic fields.
-/

open IntermediateField Module

namespace GaloisEmbedding

/-- Precomposing with an isomorphism does not change the image. -/
theorem fieldRange_comp_equiv {A A' : Type*} [Field A] [Algebra ℚ A] [Field A'] [Algebra ℚ A']
    (ψ : A' →ₐ[ℚ] ℂ) (σ : A ≃ₐ[ℚ] A') : (ψ.comp σ.toAlgHom).fieldRange = ψ.fieldRange := by
  ext x
  simp only [AlgHom.mem_fieldRange, AlgHom.comp_apply]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨σ y, rfl⟩
  · rintro ⟨z, rfl⟩; exact ⟨σ.symm z, by simp⟩

variable (E : Type*) [Field E] [NumberField E] [IsGalois ℚ E]

theorem exists_embedding : Nonempty (E →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩

/-- **All embeddings of a Galois number field into ℂ have the same image.** -/
theorem fieldRange_eq (φ₁ φ₂ : E →ₐ[ℚ] ℂ) : φ₁.fieldRange = φ₂.fieldRange := by
  obtain ⟨e⟩ : Nonempty (E ≃ₐ[ℚ] φ₁.fieldRange) := ⟨AlgEquiv.ofInjectiveField φ₁⟩
  have : Normal ℚ φ₁.fieldRange := Normal.of_algEquiv e
  have h := AlgHom.fieldRange_of_normal (E := φ₁.fieldRange) (φ₂.comp e.symm.toAlgHom)
  exact h.symm.trans (fieldRange_comp_equiv φ₂ e.symm)

theorem isGalois_range (φ : E →ₐ[ℚ] ℂ) : IsGalois ℚ φ.fieldRange :=
  IsGalois.of_algEquiv (AlgEquiv.ofInjectiveField φ)

theorem finrank_range (φ : E →ₐ[ℚ] ℂ) : finrank ℚ φ.fieldRange = finrank ℚ E :=
  (AlgEquiv.ofInjectiveField φ).toLinearEquiv.finrank_eq.symm

/-- A subfield of ℂ isomorphic to E is the image of E. -/
theorem subfield_eq_range (K : IntermediateField ℚ ℂ) (σ : E ≃ₐ[ℚ] K) (φ : E →ₐ[ℚ] ℂ) :
    K = φ.fieldRange := by
  rw [← fieldRange_eq E (K.val.comp σ.toAlgHom) φ, fieldRange_comp_equiv K.val σ,
    fieldRange_val]

/-- **ℚ-isomorphism ⟺ equal images in ℂ.** -/
theorem iso_iff_range_eq (E' : Type*) [Field E'] [NumberField E'] [IsGalois ℚ E']
    (φ : E →ₐ[ℚ] ℂ) (φ' : E' →ₐ[ℚ] ℂ) : Nonempty (E ≃ₐ[ℚ] E') ↔ φ.fieldRange = φ'.fieldRange := by
  constructor
  · rintro ⟨σ⟩
    rw [fieldRange_eq E φ (φ'.comp σ.toAlgHom), fieldRange_comp_equiv φ' σ]
  · intro h
    exact ⟨(AlgEquiv.ofInjectiveField φ).trans
      ((IntermediateField.equivOfEq h).trans (AlgEquiv.ofInjectiveField φ').symm)⟩

end GaloisEmbedding

#print axioms GaloisEmbedding.fieldRange_eq
#print axioms GaloisEmbedding.iso_iff_range_eq
