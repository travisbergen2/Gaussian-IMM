import CubicKroneckerWeber
import CubicCharacterFixedField
import CubicConductorClassification
import CyclotomicCharacterCorrespondence
import DedekindZetaIsomorphism

/-!
# CyclicCubicCharacterRecovery — from a cyclic cubic field to its primitive cubic character pair

K ⊆ ℂ Galois of degree 3. `CubicKW.cubic_kronecker_weber` gives K ⊆ ℚ(ζ_N) ⊆ ℂ. With
K' = K viewed inside L = ℚ(ζ_N) and H = Gal(L/K') (`H`), H^⊥ (Dirichlet characters mod N
trivial on Gal(L/K)) has 3 elements:
* `perp_eq`: H^⊥ = {1, ψ, ψ²} for any nontrivial ψ ∈ H^⊥, and ψ³ = 1;
* Ψ = ψ* (primitive character, level f = conductor ψ): Ψ³ = 1, Ψ ≠ 1, Ψ primitive; (ψ²)* = Ψ²
  pointwise; Ψ² = Ψ̄;
* `le_cyc_iff` (via Mathlib's `intermediateFieldEquivSubgroupChar` and
  `mem_intermediateFieldEquivSubgroupChar_iff_conductor_dvd`): for m ∣ N,
  K ⊆ ℚ(ζ_m) ⟺ every χ ∈ H^⊥ has conductor ∣ m. Hence K ⊆ ℚ(ζ_f), and f ∣ m whenever
  K ⊆ ℚ(ζ_m) with m ∣ N (f is the least such level);
* `character_recovery`: f = 9^a · q₁ ⋯ q_r (a ∈ {0,1}, qᵢ ≡ 1 mod 3), ζ_K = ζ · L(Ψ) · L(Ψ̄),
  and **uniqueness**: a primitive Φ of level f' ∣ N whose lift to level N is nontrivial and
  trivial on Gal(ℚ(ζ_N)/K) has f' = f and Φ = Ψ or Φ = Ψ̄ (pointwise) — the pair {Ψ, Ψ̄} is
  determined by K.
Everything takes place in the one ambient field ℂ. Independence of the pair from the choice of
N (comparing two levels) is not treated here.
-/

open IntermediateField Module NumberField DirichletCharacter CubicKW IsCyclotomicExtension.Rat

namespace CubicRecovery

instance (N : ℕ) [NeZero N] : IsCyclotomicExtension {N} ℚ (Cyc N) := isCyclotomic N

instance (N : ℕ) [NeZero N] : NumberField (Cyc N) := IsCyclotomicExtension.numberField {N} ℚ _

instance (N : ℕ) [NeZero N] : IsGalois ℚ (Cyc N) := IsCyclotomicExtension.isGalois {N} ℚ _

variable (K : IntermediateField ℚ ℂ) [IsGalois ℚ K] (hK : finrank ℚ K = 3)
  {N : ℕ} [NeZero N] (hKN : K ≤ Cyc N)

/-- K inside ℚ(ζ_N). -/
noncomputable abbrev Kp : IntermediateField ℚ (Cyc N) := restrict hKN

/-- H = Gal(ℚ(ζ_N)/K). -/
noncomputable abbrev H : Subgroup Gal(Cyc N/ℚ) := (Kp K hKN).fixingSubgroup

instance : (H K hKN).Normal := CycloSub.normal N _

noncomputable def eK : K ≃ₐ[ℚ] Kp K hKN := AlgEquiv.ofInjectiveField (inclusion hKN)

theorem fixedField_H : fixedField (H K hKN) = Kp K hKN := IsGalois.fixedField_fixingSubgroup _

include hK in
theorem index_H : (H K hKN).index = 3 := by
  rw [← CycloSub.finrank_K, fixedField_H, ← (eK K hKN).toLinearEquiv.finrank_eq, hK]

theorem mem_H {σ : Gal(Cyc N/ℚ)} : σ ∈ H K hKN ↔ ∀ x : Cyc N, (x : ℂ) ∈ K → σ x = x := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  exact ⟨fun h x hx => h x ((mem_restrict _ x).mpr hx), fun h x hx => h x ((mem_restrict _ x).mp hx)⟩

/-- χ ∈ H^⊥ ⟺ χ is trivial on Gal(ℚ(ζ_N)/K). -/
theorem mem_perp_iff_fix (χ : DirichletCharacter ℂ N) :
    χ ∈ CycloSubEuler.perp N (Cyc N) (H K hKN) ↔
      ∀ σ : Gal(Cyc N/ℚ), (∀ x : Cyc N, (x : ℂ) ∈ K → σ x = x) →
        χ (galEquivZMod N (Cyc N) σ) = 1 := by
  rw [CycloSubEuler.mem_perp_iff]
  constructor
  · intro h σ hσ
    exact h _ ⟨σ, (mem_H K hKN).mpr hσ, rfl⟩
  · rintro h _ ⟨σ, hσ, rfl⟩
    exact h σ ((mem_H K hKN).mp hσ)

include hK in
theorem card_perp : (CycloSubEuler.perp N (Cyc N) (H K hKN)).card = 3 := by
  rw [(CycloCharCorr.card_perp N (Cyc N) (H K hKN)).1, index_H K hK hKN]

include hK in
/-- Every χ ∈ H^⊥ satisfies χ³ = 1. -/
theorem cube_eq_one {χ : DirichletCharacter ℂ N} (hχ : χ ∈ CycloSubEuler.perp N (Cyc N) (H K hKN)) :
    χ ^ 3 = 1 := by
  rw [CycloSubEuler.mem_perp_iff] at hχ
  apply MulChar.ext
  intro u
  have hu : u ^ 3 ∈ CycloSubEuler.H' N (Cyc N) (H K hKN) := by
    have := (CycloSubEuler.H' N (Cyc N) (H K hKN)).pow_index_mem u
    rwa [CycloSubEuler.index_H', index_H K hK hKN] at this
  rw [MulChar.pow_apply' _ (by norm_num), ← map_pow, ← Units.val_pow_eq_pow_val, hχ _ hu,
    MulChar.one_apply u.isUnit]

theorem sq_mem {χ : DirichletCharacter ℂ N} (hχ : χ ∈ CycloSubEuler.perp N (Cyc N) (H K hKN)) :
    χ ^ 2 ∈ CycloSubEuler.perp N (Cyc N) (H K hKN) := by
  rw [CycloSubEuler.mem_perp_iff] at hχ ⊢
  intro u hu
  rw [MulChar.pow_apply' _ (by norm_num), hχ u hu, one_pow]

include hK in
/-- **H^⊥ ∖ {1} = {ψ, ψ²}.** -/
theorem perpNontriv_eq {ψ : DirichletCharacter ℂ N}
    (hψ : ψ ∈ CycloSubEuler.perpNontriv N (Cyc N) (H K hKN)) :
    CycloSubEuler.perpNontriv N (Cyc N) (H K hKN) = {ψ, ψ ^ 2} := by
  classical
  obtain ⟨hne, hp⟩ := Finset.mem_erase.mp hψ
  have h3 := cube_eq_one K hK hKN hp
  have hsq1 : ψ ^ 2 ≠ 1 := CubicFixedField.sq_ne_one h3 hne
  have hsqψ : ψ ^ 2 ≠ ψ := CubicFixedField.sq_ne_self hne
  have hcard : (CycloSubEuler.perpNontriv N (Cyc N) (H K hKN)).card = 2 := by
    rw [CycloSubEuler.perpNontriv, Finset.card_erase_of_mem (CycloSubEuler.one_mem_perp _ _ _),
      card_perp K hK hKN]
  have hsub : ({ψ, ψ ^ 2} : Finset _) ⊆ CycloSubEuler.perpNontriv N (Cyc N) (H K hKN) := by
    intro φ hφ
    rw [Finset.mem_insert, Finset.mem_singleton] at hφ
    rcases hφ with rfl | rfl
    · exact hψ
    · exact Finset.mem_erase.mpr ⟨hsq1, sq_mem K hKN hp⟩
  exact (Finset.eq_of_subset_of_card_le hsub
    (by rw [hcard, Finset.card_pair (Ne.symm hsqψ)])).symm

/-- **Containment criterion** (m ∣ N): K ⊆ ℚ(ζ_m) ⟺ every χ ∈ H^⊥ has conductor ∣ m. -/
theorem le_cyc_iff (m : ℕ) [NeZero m] (hm : m ∣ N) :
    K ≤ Cyc m ↔ ∀ χ ∈ CycloSubEuler.perp N (Cyc N) (H K hKN), χ.conductor ∣ m := by
  have hmN : Cyc m ≤ Cyc N := by
    obtain ⟨k, hk⟩ := hm
    have hk0 : k ≠ 0 := by rintro rfl; exact NeZero.ne N (by rw [hk, mul_zero])
    rw [hk]; exact Cyc_le_mul m k (NeZero.ne m) hk0
  set Fm : IntermediateField ℚ (Cyc N) := restrict hmN
  have : IsCyclotomicExtension {m} ℚ Fm :=
    IsCyclotomicExtension.equiv {m} ℚ (Cyc m) (AlgEquiv.ofInjectiveField (inclusion hmN))
  have : IsAbelianGalois ℚ (Cyc N) := IsCyclotomicExtension.isAbelianGalois {N} ℚ _
  have h1 : K ≤ Cyc m ↔ Kp K hKN ≤ Fm := by
    constructor
    · intro h x hx
      exact (mem_restrict _ x).mpr (h ((mem_restrict _ x).mp hx))
    · intro h y hy
      have := h ((mem_restrict _ ⟨y, hKN hy⟩).mpr hy)
      exact (mem_restrict _ _).mp this
  rw [h1, ← (IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar N (Cyc N) ℂ).le_iff_le]
  constructor
  · intro h χ hχ
    have hX : χ ∈ IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar N (Cyc N) ℂ
        (Kp K hKN) := by
      rw [IsCyclotomicExtension.Rat.mem_intermediateFieldEquivSubgroupChar_iff]
      intro σ hσ
      exact (mem_perp_iff_fix K hKN χ).mp hχ σ ((mem_H K hKN).mp hσ)
    have := h hX
    rwa [IsCyclotomicExtension.Rat.mem_intermediateFieldEquivSubgroupChar_iff_conductor_dvd
      N (Cyc N) ℂ Fm hm] at this
  · intro h χ hχ
    rw [IsCyclotomicExtension.Rat.mem_intermediateFieldEquivSubgroupChar_iff_conductor_dvd
      N (Cyc N) ℂ Fm hm]
    apply h
    rw [mem_perp_iff_fix]
    intro σ hσ
    rw [IsCyclotomicExtension.Rat.mem_intermediateFieldEquivSubgroupChar_iff] at hχ
    exact hχ σ ((mem_H K hKN).mpr hσ)

include hK in
theorem card_perpNontriv : (CycloSubEuler.perpNontriv N (Cyc N) (H K hKN)).card = 2 := by
  classical
  rw [CycloSubEuler.perpNontriv, Finset.card_erase_of_mem (CycloSubEuler.one_mem_perp _ _ _),
    card_perp K hK hKN]

/-- The primitive character of a lift of a primitive character is the character itself. -/
theorem prim_changeLevel_apply {a b : ℕ} [NeZero a] [NeZero b] (h : a ∣ b)
    (χ : DirichletCharacter ℂ a) (hχ : χ.IsPrimitive) (n : ℕ) :
    (changeLevel h χ).primitiveCharacter n = χ n := by
  have := primitiveCharacter_changeLevel_apply h χ (n : ℤ)
  simp only [Int.cast_natCast] at this
  rw [this]; exact CubicFixedField.primitive_apply hχ n

instance (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] : NumberField K := ⟨⟩

include hK in
/-- **Character recovery.** For a cyclic cubic K ⊆ ℂ there are N with K ⊆ ℚ(ζ_N) and a primitive
cubic Ψ of conductor f ∣ N such that: Ψ² = Ψ̄ is primitive of conductor f; K ⊆ ℚ(ζ_f) and f
divides every m ∣ N with K ⊆ ℚ(ζ_m); f = 9^a · q₁ ⋯ q_r; ζ_K = ζ · L(Ψ) · L(Ψ²); and any
primitive Φ of level f' ∣ N whose lift is nontrivial and trivial on Gal(ℚ(ζ_N)/K) has f' = f
and Φ = Ψ or Φ = Ψ² pointwise. -/
theorem character_recovery [FiniteDimensional ℚ K] :
    ∃ N : ℕ, ∃ _ : NeZero N, ∃ _ : K ≤ Cyc N,
    ∃ f : ℕ, ∃ _ : NeZero f, ∃ Ψ : DirichletCharacter ℂ f,
      Ψ ^ 3 = 1 ∧ Ψ ≠ 1 ∧ Ψ.IsPrimitive ∧ f ∣ N ∧
      (∀ a, (Ψ ^ 2) a = starRingEnd ℂ (Ψ a)) ∧ (Ψ ^ 2).conductor = f ∧
      K ≤ Cyc f ∧ (∀ m : ℕ, m ≠ 0 → m ∣ N → K ≤ Cyc m → f ∣ m) ∧
      (∃ a : Bool, ∃ qs : List ℕ, qs.Nodup ∧ (∀ q ∈ qs, q.Prime) ∧ (∀ q ∈ qs, 3 ∣ q - 1) ∧
        (a = true ∨ qs ≠ []) ∧ f = (if a then 9 else 1) * qs.prod) ∧
      (∀ s : ℂ, 1 < s.re → LSeries (fun n => (IdealCount.A (𝓞 K) n : ℂ)) s =
        riemannZeta s * LSeries (fun n => Ψ n) s * LSeries (fun n => (Ψ ^ 2) n) s) ∧
      (∀ (f' : ℕ) [NeZero f'] (Φ : DirichletCharacter ℂ f') (h : f' ∣ N), Φ.IsPrimitive →
        changeLevel h Φ ≠ 1 →
        (∀ σ : Gal(Cyc N/ℚ), (∀ x : Cyc N, (x : ℂ) ∈ K → σ x = x) →
          changeLevel h Φ (galEquivZMod N (Cyc N) σ) = 1) →
        f' = f ∧ ((∀ n : ℕ, Φ n = Ψ n) ∨ (∀ n : ℕ, Φ n = (Ψ ^ 2) n))) := by
  classical
  obtain ⟨N, hN, hKN, -⟩ := cubic_kronecker_weber K hK
  have hNz : NeZero N := ⟨hN.ne'⟩
  obtain ⟨ψ, hψ⟩ : (CycloSubEuler.perpNontriv N (Cyc N) (H K hKN)).Nonempty := by
    rw [← Finset.card_pos, card_perpNontriv K hK hKN]; norm_num
  obtain ⟨hne, hp⟩ := Finset.mem_erase.mp hψ
  have h3 := cube_eq_one K hK hKN hp
  have hfN : ψ.conductor ∣ N := conductor_dvd_level ψ
  set f := ψ.conductor with hfdef
  have : NeZero f := ⟨fun h => NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ hfN))⟩
  set Ψ := ψ.primitiveCharacter with hΨdef
  have hlift : changeLevel hfN Ψ = ψ := changeLevel_primitiveCharacter ψ
  have hΨ3 : Ψ ^ 3 = 1 := changeLevel_injective hfN (by rw [map_pow, hlift, h3, map_one])
  have hΨ1 : Ψ ≠ 1 := fun h => hne (by rw [← hlift, h, map_one])
  have hΨp : Ψ.IsPrimitive := primitiveCharacter_isPrimitive ψ
  have hΨ2c : (Ψ ^ 2).conductor = f := CubicFixedField.conductor_sq hΨ3 hΨp
  have hψ2 : ψ ^ 2 = changeLevel hfN (Ψ ^ 2) := by rw [map_pow, hlift]
  have hψ2c : (ψ ^ 2).conductor = f := by rw [hψ2, conductor_changeLevel, hΨ2c]
  have hsqval : ∀ n : ℕ, (ψ ^ 2).primitiveCharacter n = (Ψ ^ 2) n := fun n => by
    rw [hψ2]; exact prim_changeLevel_apply hfN (Ψ ^ 2) hΨ2c n
  have hperp : ∀ χ ∈ CycloSubEuler.perp N (Cyc N) (H K hKN), χ = 1 ∨ χ = ψ ∨ χ = ψ ^ 2 := by
    intro χ hχ
    by_cases h1 : χ = 1
    · exact Or.inl h1
    · have : χ ∈ CycloSubEuler.perpNontriv N (Cyc N) (H K hKN) := Finset.mem_erase.mpr ⟨h1, hχ⟩
      rw [perpNontriv_eq K hK hKN hψ, Finset.mem_insert, Finset.mem_singleton] at this
      exact Or.inr this
  refine ⟨N, hNz, hKN, f, inferInstance, Ψ, hΨ3, hΨ1, hΨp, hfN, CubicFixedField.sq_eq_conj hΨ3,
    hΨ2c, ?_, ?_, CubicClass.classification hΨ3 hΨ1 hΨp, ?_, ?_⟩
  · -- K ⊆ ℚ(ζ_f)
    rw [le_cyc_iff K hKN f hfN]
    intro χ hχ
    rcases hperp χ hχ with rfl | rfl | rfl
    · rw [conductor_one]; exact one_dvd _
    · exact dvd_rfl
    · rw [hψ2c]
  · -- minimality
    intro m hm0 hmN hKm
    have : NeZero m := ⟨hm0⟩
    exact (le_cyc_iff K hKN m hmN).mp hKm ψ hp
  · -- ζ_K = ζ L(Ψ) L(Ψ²)
    intro s hs
    have e : K ≃+* fixedField (H K hKN) :=
      ((eK K hKN).trans (IntermediateField.equivOfEq (fixedField_H K hKN).symm)).toRingEquiv
    rw [IdealCountIso.LSeries_eq_of_equiv e,
      CompositeEuler.LSeries_eq_zeta_mul_prod_primitive N (Cyc N) (H K hKN) hs,
      Finset.prod_coe_sort (CycloSubEuler.perpNontriv N (Cyc N) (H K hKN))
        (fun φ => LSeries (fun m => φ.primitiveCharacter m) s), perpNontriv_eq K hK hKN hψ,
      Finset.prod_pair (Ne.symm (CubicFixedField.sq_ne_self hne)), mul_assoc]
    have : (fun m : ℕ => (ψ ^ 2).primitiveCharacter m) = fun m : ℕ => (Ψ ^ 2) m := funext hsqval
    rw [this]
  · -- uniqueness of the pair
    intro f' _ Φ h hΦp hΦ1 hΦfix
    have hmem : changeLevel h Φ ∈ CycloSubEuler.perpNontriv N (Cyc N) (H K hKN) :=
      Finset.mem_erase.mpr ⟨hΦ1, (mem_perp_iff_fix K hKN _).mpr hΦfix⟩
    rw [perpNontriv_eq K hK hKN hψ, Finset.mem_insert, Finset.mem_singleton] at hmem
    have hval : ∀ n : ℕ, Φ n = (changeLevel h Φ).primitiveCharacter n := fun n =>
      (prim_changeLevel_apply h Φ hΦp n).symm
    have hcond : f' = (changeLevel h Φ).conductor := by rw [conductor_changeLevel]; exact hΦp.symm
    rcases hmem with hc | hc
    · refine ⟨by rw [hcond, hc], Or.inl fun n => ?_⟩
      rw [hval, hc]
    · refine ⟨by rw [hcond, hc, hψ2c], Or.inr fun n => ?_⟩
      rw [hval, hc, hsqval]

end CubicRecovery

#print axioms CubicRecovery.perpNontriv_eq
#print axioms CubicRecovery.le_cyc_iff
#print axioms CubicRecovery.character_recovery
