import CyclicCubicIntrinsicPair
import CyclicCubicEmbeddingClass

/-!
# CyclicCubicCharacterBijection — cyclic cubic fields ⟷ primitive cubic characters modulo Ψ ~ Ψ̄

For a primitive cubic Dirichlet character Ψ at its **exact conductor** f (Ψ³ = 1, Ψ ≠ 1, Ψ
primitive), `KΨ Ψ` ⊆ ℂ is the fixed field of ker Ψ inside ℚ(ζ_f) ⊆ ℂ (`CubicFixedField.K`,
lifted to ℂ). No inflated representative is used to define the field.
* `isGalois_KΨ`, `finrank_KΨ`, `zeta_KΨ`: KΨ is cyclic cubic with ζ = ζ · L(Ψ) · L(Ψ̄);
* `mem_perpNontriv`: Ψ is nontrivial and trivial on Gal(ℚ(ζ_f)/KΨ);
* `KΨ_eq_of_mem`: if K ⊆ ℚ(ζ_f) is cyclic cubic and Ψ is trivial on Gal(ℚ(ζ_f)/K), then KΨ = K;
* **field → pair → field** (`field_to_char_to_field`): every cyclic cubic K ⊆ ℂ is KΨ for the
  intrinsic pair of K;
* **pair → field → pair** (`fiber`): KΨ' = KΨ ⟺ f' = f and Ψ' = Ψ or Ψ' = Ψ̄ (pointwise) — the
  fibres of Ψ ↦ KΨ are exactly the conjugate pairs; `KΨ_sq`: KΨ̄ = KΨ;
* `classification`: the map Ψ ↦ KΨ from primitive cubic characters onto cyclic cubic subfields
  of ℂ is surjective with fibres {Ψ, Ψ̄}; f = 9^a · q₁ ⋯ q_r;
* `abstract_classification`: for abstract cyclic cubic fields E, E' (any embeddings into ℂ),
  E ≃ₐ[ℚ] E' ⟺ their characters have the same conductor and agree up to conjugation.
-/

open IntermediateField Module NumberField DirichletCharacter CubicKW IsCyclotomicExtension.Rat
  CubicRecovery CubicIntrinsic

namespace CubicBijection

section Char

variable {f : ℕ} [NeZero f] (Ψ : DirichletCharacter ℂ f)

/-- **K_Ψ ⊆ ℂ**: the fixed field of ker Ψ in ℚ(ζ_f), f the level of Ψ. -/
noncomputable def KΨ : IntermediateField ℚ ℂ := lift (CubicFixedField.K (Cyc f) Ψ)

theorem KΨ_le : KΨ Ψ ≤ Cyc f := lift_le _

theorem restrict_KΨ : restrict (KΨ_le Ψ) = CubicFixedField.K (Cyc f) Ψ := by
  ext x
  rw [mem_restrict]
  exact mem_lift x

noncomputable def KΨ_equiv : CubicFixedField.K (Cyc f) Ψ ≃ₐ[ℚ] KΨ Ψ := liftAlgEquiv _

instance isGalois_KΨ : IsGalois ℚ (KΨ Ψ) := IsGalois.of_algEquiv (KΨ_equiv Ψ)

theorem finrank_KΨ (h3 : Ψ ^ 3 = 1) (hne : Ψ ≠ 1) : finrank ℚ (KΨ Ψ) = 3 := by
  rw [← (KΨ_equiv Ψ).toLinearEquiv.finrank_eq, CubicFixedField.finrank_K h3 hne]

instance : FiniteDimensional ℚ (KΨ Ψ) :=
  LinearEquiv.finiteDimensional (KΨ_equiv Ψ).toLinearEquiv

/-- **ζ_{KΨ} = ζ · L(Ψ) · L(Ψ²).** -/
theorem zeta_KΨ (h3 : Ψ ^ 3 = 1) (hne : Ψ ≠ 1) (hp : Ψ.IsPrimitive) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (IdealCount.A (𝓞 (KΨ Ψ)) n : ℂ)) s =
      riemannZeta s * LSeries (fun n => Ψ n) s * LSeries (fun n => (Ψ ^ 2) n) s := by
  rw [← IdealCountIso.LSeries_eq_of_equiv (KΨ_equiv Ψ).toRingEquiv,
    CubicFixedField.zeta_K h3 hne hp hs]

/-- σ ∈ Gal(ℚ(ζ_f)/ℚ) lies in ker Ψ iff Ψ(σ) = 1. -/
theorem mem_HΨ (σ : Gal(Cyc f/ℚ)) :
    σ ∈ CubicFixedField.H (Cyc f) Ψ ↔ Ψ (galEquivZMod f (Cyc f) σ) = 1 := by
  rw [CubicFixedField.H, MonoidHom.mem_ker, CubicFixedField.psiGal, MonoidHom.comp_apply,
    Units.ext_iff, Units.val_one]
  rfl

/-- **Ψ is nontrivial and trivial on Gal(ℚ(ζ_f)/KΨ).** -/
theorem mem_perpNontriv (hne : Ψ ≠ 1) :
    Ψ ∈ CycloSubEuler.perpNontriv f (Cyc f) (H (KΨ Ψ) (KΨ_le Ψ)) := by
  refine Finset.mem_erase.mpr ⟨hne, ?_⟩
  rw [mem_perp_iff_fix]
  intro σ hσ
  have hσH : σ ∈ H (KΨ Ψ) (KΨ_le Ψ) := (mem_H _ _).mpr hσ
  have : H (KΨ Ψ) (KΨ_le Ψ) = CubicFixedField.H (Cyc f) Ψ := by
    show (restrict (KΨ_le Ψ)).fixingSubgroup = _
    rw [restrict_KΨ, CubicFixedField.K, IntermediateField.fixingSubgroup_fixedField]
  rw [this, mem_HΨ] at hσH
  exact hσH

/-- If K ⊆ ℚ(ζ_f) is cyclic cubic and Ψ is trivial on Gal(ℚ(ζ_f)/K), then KΨ = K. -/
theorem KΨ_eq_of_mem (h3 : Ψ ^ 3 = 1) (hne : Ψ ≠ 1) (K : IntermediateField ℚ ℂ) [IsGalois ℚ K]
    (hK : finrank ℚ K = 3) (hKf : K ≤ Cyc f)
    (hmem : Ψ ∈ CycloSubEuler.perp f (Cyc f) (H K hKf)) : KΨ Ψ = K := by
  have hle : CubicFixedField.K (Cyc f) Ψ ≤ Kp K hKf := by
    rw [CubicFixedField.K, IsGalois.fixedField_le_iff_fixingSubgroup_le]
    intro σ hσ
    rw [mem_HΨ]
    exact (mem_perp_iff_fix K hKf Ψ).mp hmem σ ((mem_H K hKf).mp hσ)
  have hfr : finrank ℚ (CubicFixedField.K (Cyc f) Ψ) = finrank ℚ (Kp K hKf) := by
    rw [CubicFixedField.finrank_K h3 hne, ← (eK K hKf).toLinearEquiv.finrank_eq, hK]
  have heq := IntermediateField.eq_of_le_of_finrank_eq hle hfr
  rw [KΨ, heq, lift_restrict]

/-- **KΨ̄ = KΨ** (ker Ψ² = ker Ψ). -/
theorem KΨ_sq (h3 : Ψ ^ 3 = 1) : KΨ (Ψ ^ 2) = KΨ Ψ := by
  have : CubicFixedField.H (Cyc f) (Ψ ^ 2) = CubicFixedField.H (Cyc f) Ψ := by
    ext σ
    rw [mem_HΨ, mem_HΨ]
    set u := galEquivZMod f (Cyc f) σ
    have hu3 : (Ψ u) ^ 3 = 1 := by
      rw [← MulChar.pow_apply' _ (by norm_num), h3, MulChar.one_apply u.isUnit]
    rw [MulChar.pow_apply' _ (by norm_num)]
    constructor
    · intro h
      have := hu3
      rw [pow_succ, h, one_mul] at this
      exact this
    · intro h; rw [h, one_pow]
  rw [KΨ, KΨ, CubicFixedField.K, CubicFixedField.K, this]

end Char

theorem pointwise_combine {f₀ : ℕ} {Ψ₀ : DirichletCharacter ℂ f₀} (h3 : Ψ₀ ^ 3 = 1)
    {α β : ℕ → ℂ} (hα : (∀ n, α n = Ψ₀ n) ∨ (∀ n, α n = (Ψ₀ ^ 2) n))
    (hβ : (∀ n, β n = Ψ₀ n) ∨ (∀ n, β n = (Ψ₀ ^ 2) n)) :
    (∀ n, β n = α n) ∨ (∀ n, β n = α n ^ 2) := by
  have hsq : ∀ n : ℕ, (Ψ₀ ^ 2) n = (Ψ₀ n) ^ 2 := fun n => MulChar.pow_apply' _ (by norm_num) _
  have h4 : ∀ n : ℕ, (Ψ₀ n) ^ 4 = Ψ₀ n := fun n => by
    rw [← MulChar.pow_apply' _ (by norm_num), show Ψ₀ ^ 4 = Ψ₀ ^ 3 * Ψ₀ by rw [pow_succ], h3,
      one_mul]
  rcases hα with hα | hα <;> rcases hβ with hβ | hβ
  · exact Or.inl fun n => by rw [hα, hβ]
  · exact Or.inr fun n => by rw [hα, hβ, hsq]
  · exact Or.inr fun n => by rw [hα, hβ, hsq, ← pow_mul, h4]
  · exact Or.inl fun n => by rw [hα, hβ]

theorem H_congr {M : ℕ} [NeZero M] {K₁ K₂ : IntermediateField ℚ ℂ} (h : K₁ = K₂)
    (h₁ : K₁ ≤ Cyc M) (h₂ : K₂ ≤ Cyc M) : H K₁ h₁ = H K₂ h₂ := by subst h; rfl

/-- **Field → pair → field.** Every cyclic cubic K ⊆ ℂ is KΨ for a primitive cubic Ψ at its
exact conductor (the intrinsic pair of K). -/
theorem field_to_char_to_field (K : IntermediateField ℚ ℂ) [IsGalois ℚ K] (hK : finrank ℚ K = 3)
    [FiniteDimensional ℚ K] :
    ∃ f : ℕ, ∃ _ : NeZero f, ∃ Ψ : DirichletCharacter ℂ f,
      Ψ ^ 3 = 1 ∧ Ψ ≠ 1 ∧ Ψ.IsPrimitive ∧ KΨ Ψ = K := by
  obtain ⟨f, hfz, Ψ, h3, hne, hp, -, -, hcond, -, -, hpres, -⟩ := intrinsic_pair K hK
  have hKf : K ≤ Cyc f := (hcond f (NeZero.ne f)).mpr dvd_rfl
  obtain ⟨hff, hmem⟩ := hpres f hKf
  have hself : changeLevel hff Ψ = Ψ := changeLevel_self Ψ
  rw [hself] at hmem
  exact ⟨f, hfz, Ψ, h3, hne, hp, KΨ_eq_of_mem Ψ h3 hne K hK hKf (Finset.mem_of_mem_erase hmem)⟩

/-- **Pair → field → pair.** KΨ' = KΨ ⟺ the levels agree and Ψ' ∈ {Ψ, Ψ̄}. -/
theorem fiber {f f' : ℕ} [NeZero f] [NeZero f'] (Ψ : DirichletCharacter ℂ f)
    (Ψ' : DirichletCharacter ℂ f') (h3 : Ψ ^ 3 = 1) (hne : Ψ ≠ 1) (hp : Ψ.IsPrimitive)
    (h3' : Ψ' ^ 3 = 1) (hne' : Ψ' ≠ 1) (hp' : Ψ'.IsPrimitive) :
    KΨ Ψ' = KΨ Ψ ↔ f' = f ∧ ((∀ n : ℕ, Ψ' n = Ψ n) ∨ (∀ n : ℕ, Ψ' n = (Ψ ^ 2) n)) := by
  constructor
  · intro hKK
    obtain ⟨f₀, _, Ψ₀, h30, -, -, -, -, -, -, -, -, huniq⟩ :=
      intrinsic_pair (KΨ Ψ) (finrank_KΨ Ψ h3 hne)
    have hΨmem : changeLevel (dvd_refl f) Ψ ∈
        CycloSubEuler.perpNontriv f (Cyc f) (H (KΨ Ψ) (KΨ_le Ψ)) := by
      rw [changeLevel_self]; exact mem_perpNontriv Ψ hne
    obtain ⟨hf0, hΨ0⟩ := huniq f (KΨ_le Ψ) f Ψ (dvd_refl f) hp hΨmem
    have hle' : KΨ Ψ ≤ Cyc f' := hKK ▸ KΨ_le Ψ'
    have hΨ'mem : changeLevel (dvd_refl f') Ψ' ∈
        CycloSubEuler.perpNontriv f' (Cyc f') (H (KΨ Ψ) hle') := by
      rw [changeLevel_self, ← H_congr hKK (KΨ_le Ψ') hle']; exact mem_perpNontriv Ψ' hne'
    obtain ⟨hf0', hΨ0'⟩ := huniq f' hle' f' Ψ' (dvd_refl f') hp' hΨ'mem
    refine ⟨hf0'.trans hf0.symm, ?_⟩
    rcases pointwise_combine h30 (α := fun n => Ψ n) (β := fun n => Ψ' n) hΨ0 hΨ0' with h | h
    · exact Or.inl h
    · exact Or.inr fun n => by rw [h n, MulChar.pow_apply' _ (by norm_num)]
  · rintro ⟨rfl, h | h⟩
    · have : Ψ' = Ψ := MulChar.ext' fun a => by rw [← ZMod.natCast_zmod_val a]; exact h a.val
      rw [this]
    · have : Ψ' = Ψ ^ 2 := MulChar.ext' fun a => by rw [← ZMod.natCast_zmod_val a]; exact h a.val
      rw [this, KΨ_sq Ψ h3]

/-- **Classification of cyclic cubic subfields of ℂ.** Ψ ↦ KΨ maps primitive cubic characters
(at their exact conductors) onto the cyclic cubic subfields of ℂ, with fibres exactly the
conjugate pairs {Ψ, Ψ̄}; the conductors are f = 9^a · q₁ ⋯ q_r, and ζ_{KΨ} = ζ · L(Ψ) · L(Ψ̄). -/
theorem classification :
    (∀ (K : IntermediateField ℚ ℂ) [IsGalois ℚ K] [FiniteDimensional ℚ K], finrank ℚ K = 3 →
      ∃ f : ℕ, ∃ _ : NeZero f, ∃ Ψ : DirichletCharacter ℂ f,
        Ψ ^ 3 = 1 ∧ Ψ ≠ 1 ∧ Ψ.IsPrimitive ∧ KΨ Ψ = K) ∧
    (∀ (f : ℕ) [NeZero f] (Ψ : DirichletCharacter ℂ f), Ψ ^ 3 = 1 → Ψ ≠ 1 → Ψ.IsPrimitive →
      IsGalois ℚ (KΨ Ψ) ∧ finrank ℚ (KΨ Ψ) = 3 ∧
      (∃ a : Bool, ∃ qs : List ℕ, qs.Nodup ∧ (∀ q ∈ qs, q.Prime) ∧ (∀ q ∈ qs, 3 ∣ q - 1) ∧
        (a = true ∨ qs ≠ []) ∧ f = (if a then 9 else 1) * qs.prod) ∧
      (∀ s : ℂ, 1 < s.re → LSeries (fun n => (IdealCount.A (𝓞 (KΨ Ψ)) n : ℂ)) s =
        riemannZeta s * LSeries (fun n => Ψ n) s * LSeries (fun n => (Ψ ^ 2) n) s) ∧
      (∀ a, (Ψ ^ 2) a = starRingEnd ℂ (Ψ a))) ∧
    (∀ (f f' : ℕ) [NeZero f] [NeZero f'] (Ψ : DirichletCharacter ℂ f)
      (Ψ' : DirichletCharacter ℂ f'), Ψ ^ 3 = 1 → Ψ ≠ 1 → Ψ.IsPrimitive →
      Ψ' ^ 3 = 1 → Ψ' ≠ 1 → Ψ'.IsPrimitive →
      (KΨ Ψ' = KΨ Ψ ↔ f' = f ∧ ((∀ n : ℕ, Ψ' n = Ψ n) ∨ (∀ n : ℕ, Ψ' n = (Ψ ^ 2) n)))) :=
  ⟨fun K _ _ hK => field_to_char_to_field K hK,
   fun f _ Ψ h3 hne hp => ⟨inferInstance, finrank_KΨ Ψ h3 hne,
     CubicClass.classification h3 hne hp, fun s hs => zeta_KΨ Ψ h3 hne hp hs,
     CubicFixedField.sq_eq_conj h3⟩,
   fun f f' _ _ Ψ Ψ' h3 hne hp h3' hne' hp' => fiber Ψ Ψ' h3 hne hp h3' hne' hp'⟩

/-- **Abstract cyclic cubic fields.** For E, E' Galois of degree 3 with any embeddings φ, φ' into
ℂ, whose images are KΨ and KΨ': E ≃ₐ[ℚ] E' ⟺ f' = f and Ψ' ∈ {Ψ, Ψ̄}. Every such E has such a Ψ. -/
theorem abstract_classification (E : Type*) [Field E] [NumberField E] [IsGalois ℚ E]
    (hE : finrank ℚ E = 3) (φ : E →ₐ[ℚ] ℂ) :
    (∃ f : ℕ, ∃ _ : NeZero f, ∃ Ψ : DirichletCharacter ℂ f,
      Ψ ^ 3 = 1 ∧ Ψ ≠ 1 ∧ Ψ.IsPrimitive ∧ KΨ Ψ = φ.fieldRange) ∧
    (∀ (E' : Type*) [Field E'] [NumberField E'] [IsGalois ℚ E'] (φ' : E' →ₐ[ℚ] ℂ)
      (f f' : ℕ) [NeZero f] [NeZero f'] (Ψ : DirichletCharacter ℂ f) (Ψ' : DirichletCharacter ℂ f'),
      Ψ ^ 3 = 1 → Ψ ≠ 1 → Ψ.IsPrimitive → Ψ' ^ 3 = 1 → Ψ' ≠ 1 → Ψ'.IsPrimitive →
      KΨ Ψ = φ.fieldRange → KΨ Ψ' = φ'.fieldRange →
      (Nonempty (E ≃ₐ[ℚ] E') ↔ f' = f ∧ ((∀ n : ℕ, Ψ' n = Ψ n) ∨ (∀ n : ℕ, Ψ' n = (Ψ ^ 2) n)))) := by
  refine ⟨?_, ?_⟩
  · have := GaloisEmbedding.isGalois_range E φ
    have hK : finrank ℚ φ.fieldRange = 3 := by rw [GaloisEmbedding.finrank_range, hE]
    have : FiniteDimensional ℚ φ.fieldRange := Module.finite_of_finrank_pos (by rw [hK]; norm_num)
    exact field_to_char_to_field φ.fieldRange hK
  · intro E' _ _ _ φ' f f' _ _ Ψ Ψ' h3 hne hp h3' hne' hp' hΨ hΨ'
    rw [GaloisEmbedding.iso_iff_range_eq E E' φ φ', ← hΨ, ← hΨ', eq_comm]
    exact fiber Ψ Ψ' h3 hne hp h3' hne' hp'

end CubicBijection

#print axioms CubicBijection.KΨ_eq_of_mem
#print axioms CubicBijection.fiber
#print axioms CubicBijection.classification
#print axioms CubicBijection.abstract_classification
