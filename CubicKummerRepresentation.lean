import CubicCharacterAssembly

/-!
# CubicKummerRepresentation — a cyclic cubic K ⊆ ℂ becomes a Kummer extension over ℚ(ω)

Setting: K an intermediate field of ℂ/ℚ, Galois of degree 3; F = ℚ(ω), ω = e^{2πi/3};
M = K ⊔ F = K(ω).
* `finrank_F`: [F : ℚ] = 2; `finrank_M`: [M : ℚ] = 6 (3 ∣ [M:ℚ], 2 ∣ [M:ℚ], [M:ℚ] ≤ 6);
* `gal_comm`: Gal(M/ℚ) is commutative (it embeds in Gal(K/ℚ) × Gal(F/ℚ));
* `kummer`: there is β ∈ M with β³ ∈ F, β ∉ F and M = ℚ(ω, β) — from Mathlib's Kummer
  theorem `isCyclic_tfae` applied to the cyclic cubic extension M/F.
-/

open IntermediateField Module

namespace CubicKummerRep

local notation "ω" => CubicAssembly.ω

/-- F = ℚ(ω). -/
noncomputable abbrev F : IntermediateField ℚ ℂ := ℚ⟮ω⟯

theorem hint : IsIntegral ℚ ω := (CubicAssembly.hω.isIntegral (by norm_num)).tower_top

instance : FiniteDimensional ℚ F := adjoin.finiteDimensional hint

theorem finrank_F : finrank ℚ F = 2 := by
  rw [adjoin.finrank hint, ← Polynomial.cyclotomic_eq_minpoly_rat CubicAssembly.hω
    (by norm_num), Polynomial.natDegree_cyclotomic]
  decide

instance isGalois_F : IsGalois ℚ F := by
  have : IsCyclotomicExtension {3} ℚ F :=
    CubicAssembly.hω.intermediateField_adjoin_isCyclotomicExtension ℚ
  exact IsCyclotomicExtension.isGalois {3} ℚ F

variable (K : IntermediateField ℚ ℂ) [IsGalois ℚ K] (hK : finrank ℚ K = 3)

/-- M = K ⊔ F = K(ω). -/
noncomputable abbrev M : IntermediateField ℚ ℂ := K ⊔ F

omit [IsGalois ℚ K] in
include hK in
theorem finiteDimensional_K : FiniteDimensional ℚ K :=
  Module.finite_of_finrank_pos (by rw [hK]; norm_num)

include hK in
/-- **[M : ℚ] = 6.** -/
theorem finrank_M : finrank ℚ (M K) = 6 := by
  have := finiteDimensional_K K hK
  have h1 := finrank_dvd_of_le_right (le_sup_left : K ≤ M K)
  have h2 := finrank_dvd_of_le_right (le_sup_right : F ≤ M K)
  have h3 := finrank_sup_le K F
  rw [hK] at h1 h3; rw [finrank_F] at h2 h3
  have : FiniteDimensional ℚ (M K) := IntermediateField.finiteDimensional_sup K F
  have hpos : 0 < finrank ℚ (M K) := finrank_pos
  have h6 : 6 ∣ finrank ℚ (M K) := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h2
  obtain ⟨k, hk⟩ := h6
  rw [hk] at h3 hpos ⊢
  have : k = 1 := by omega
  rw [this]

include hK in
/-- **Gal(M/ℚ) is commutative.** -/
theorem gal_comm (σ τ : Gal(M K/ℚ)) : σ * τ = τ * σ := by
  have := finiteDimensional_K K hK
  have hKc : IsCyclic Gal(K/ℚ) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    apply isCyclic_of_prime_card (p := 3)
    rw [IsGalois.card_aut_eq_finrank, hK]
  have hFc : IsCyclic Gal(F/ℚ) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    apply isCyclic_of_prime_card (p := 2)
    rw [IsGalois.card_aut_eq_finrank, finrank_F]
  apply restrictNormalHomSupProd_injective K F
  rw [map_mul, map_mul]
  ext1
  · exact (IsCyclic.commGroup (α := Gal(K/ℚ))).mul_comm _ _
  · exact (IsCyclic.commGroup (α := Gal(F/ℚ))).mul_comm _ _

include hK in
/-- **Kummer representation:** M = ℚ(ω, β) with β³ ∈ F, β ∉ F. -/
theorem kummer : ∃ β : ℂ, β ∈ M K ∧ β ^ 3 ∈ F ∧ β ∉ F ∧ M K = ℚ⟮ω, β⟯ := by
  have := finiteDimensional_K K hK
  have : FiniteDimensional ℚ (M K) := IntermediateField.finiteDimensional_sup K F
  -- work inside Ω = M
  set K' : IntermediateField ℚ (M K) := restrict (le_sup_left : K ≤ M K)
  set F' : IntermediateField ℚ (M K) := restrict (le_sup_right : F ≤ M K)
  have eK : K ≃ₐ[ℚ] K' := AlgEquiv.ofInjectiveField (inclusion (le_sup_left : K ≤ M K))
  have eF : F ≃ₐ[ℚ] F' := AlgEquiv.ofInjectiveField (inclusion (le_sup_right : F ≤ M K))
  have : IsGalois ℚ K' := IsGalois.of_algEquiv eK
  have : FiniteDimensional ℚ K' := LinearEquiv.finiteDimensional eK.toLinearEquiv
  have hsup : K' ⊔ F' = ⊤ :=
    lift_injective _ (by simp [K', F', lift_sup, lift_restrict, lift_top])
  have : IsGalois F' (M K) := IsGalois.sup_right K' F' hsup
  have hF' : finrank ℚ F' = 2 := by rw [← eF.toLinearEquiv.finrank_eq, finrank_F]
  have hdeg : finrank F' (M K) = 3 := by
    have h := Module.finrank_mul_finrank ℚ F' (M K)
    rw [hF', finrank_M K hK] at h
    omega
  have : FiniteDimensional F' (M K) := Module.finite_of_finrank_pos (by rw [hdeg]; norm_num)
  -- a primitive cube root of unity in F'
  have hωF : ω ∈ F := mem_adjoin_simple_self ℚ ω
  set ωM : M K := ⟨ω, le_sup_right (a := K) hωF⟩
  have hωF' : ωM ∈ F' := (mem_restrict _ ωM).mpr hωF
  have hprim : (primitiveRoots (finrank F' (M K)) F').Nonempty := by
    refine ⟨⟨ωM, hωF'⟩, ?_⟩
    rw [hdeg, mem_primitiveRoots (by norm_num)]
    have : IsPrimitiveRoot (((⟨ωM, hωF'⟩ : F') : M K) : ℂ) 3 := CubicAssembly.hω
    exact (this.of_map_of_injective (f := (M K).val.toMonoidHom.comp F'.val.toMonoidHom)
      (Subtype.val_injective.comp Subtype.val_injective))
  have hcyc : IsGalois F' (M K) ∧ IsCyclic Gal(M K/F') := by
    refine ⟨inferInstance, ?_⟩
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    apply isCyclic_of_prime_card (p := 3)
    rw [IsGalois.card_aut_eq_finrank, hdeg]
  obtain ⟨α, ⟨a, ha⟩, hα⟩ := ((isCyclic_tfae F' (M K) hprim).out 1 3).mp hcyc
  rw [hdeg] at ha
  set β : ℂ := (α : ℂ)
  have hβ3 : β ^ 3 ∈ F := by
    have : ((a : M K) : ℂ) ∈ F := (mem_restrict _ (a : M K)).mp a.2
    rw [show β ^ 3 = ((α ^ 3 : M K) : ℂ) by rfl, ← ha]
    exact this
  have hM : M K = ℚ⟮ω, β⟯ := by
    have h1 : lift (restrictScalars ℚ F'⟮α⟯) = M K := by rw [hα, restrictScalars_top, lift_top]
    rw [restrictScalars_adjoin, lift_adjoin] at h1
    rw [← h1]
    apply le_antisymm
    · rw [adjoin_le_iff]
      rintro _ ⟨x, hx, rfl⟩
      rcases hx with hx | hx
      · have : (x : ℂ) ∈ F := (mem_restrict _ x).mp hx
        exact adjoin.mono ℚ {ω} {ω, β} (by simp) (by simpa [F] using this)
      · rw [Set.mem_singleton_iff] at hx; subst hx
        exact subset_adjoin ℚ _ (by simp [β])
    · rw [adjoin_le_iff]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact subset_adjoin ℚ _ ⟨ωM, Or.inl hωF', rfl⟩
      · exact subset_adjoin ℚ _ ⟨α, Or.inr rfl, rfl⟩
  refine ⟨β, α.2, hβ3, fun hβF => ?_, hM⟩
  have hle : M K ≤ F := by
    rw [hM, adjoin_le_iff]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hωF
    · exact hβF
  have := finrank_le_of_le_right hle
  rw [finrank_M K hK, finrank_F] at this
  omega

end CubicKummerRep

#print axioms CubicKummerRep.finrank_M
#print axioms CubicKummerRep.gal_comm
#print axioms CubicKummerRep.kummer
