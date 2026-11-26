import CyclicCubicCharacterRecovery

/-!
# CyclicCubicIntrinsicPair — the conductor and the pair {Ψ, Ψ̄} do not depend on the level N

K ⊆ ℂ Galois of degree 3. For a level M with K ⊆ ℚ(ζ_M), H_M^⊥ is the set of Dirichlet
characters mod M trivial on Gal(ℚ(ζ_M)/K) (`CubicRecovery`).
* `res_galEquiv`, `res_coe` (via Mathlib's `galEquivZMod_restrictNormal_apply`): for N ∣ P,
  restriction Gal(ℚ(ζ_P)/ℚ) → Gal(ℚ(ζ_N)/ℚ) corresponds to (ℤ/P)ˣ → (ℤ/N)ˣ, and σ fixes K iff
  its restriction does (K ⊆ ℚ(ζ_N));
* `compat`: χ ∈ H_N^⊥ ⟺ (χ inflated to level P) ∈ H_P^⊥ — the three objects (the character at its
  level, its inflation, and the Galois character) are kept separate;
* `intrinsic_pair`: there is a primitive cubic Ψ of conductor f, with Ψ² = Ψ̄, such that
  - **K ⊆ ℚ(ζ_m) ⟺ f ∣ m for every m ≥ 1** (the intrinsic conductor, divisibility not size);
  - f = 9^a · q₁ ⋯ q_r and ζ_K = ζ · L(Ψ) · L(Ψ̄);
  - at **every** level M with K ⊆ ℚ(ζ_M), the inflation of Ψ to M is nontrivial and trivial on
    Gal(ℚ(ζ_M)/K);
  - at **every** such M, a primitive Φ of level f' ∣ M whose inflation is nontrivial and trivial
    on Gal(ℚ(ζ_M)/K) has f' = f and Φ = Ψ or Φ = Ψ̄ (pointwise).
  So the unordered pair {Ψ, Ψ̄} is determined by K alone (any two levels are compared through
  their product).
-/

open IntermediateField Module NumberField DirichletCharacter CubicKW IsCyclotomicExtension.Rat
  CubicRecovery

namespace CubicIntrinsic

theorem cyc_le {N P : ℕ} [NeZero P] (h : N ∣ P) : Cyc N ≤ Cyc P := by
  obtain ⟨k, rfl⟩ := h
  by_cases hN : N = 0
  · subst hN; simp at *
  exact Cyc_le_mul N k hN (fun hk => NeZero.ne (N * k) (by rw [hk, mul_zero]))

/-- Inflation on units: (χ ↑ P)(u) = χ(u mod N). -/
theorem changeLevel_unit {N P : ℕ} (h : N ∣ P) (χ : DirichletCharacter ℂ N) (u : (ZMod P)ˣ) :
    changeLevel h χ u = χ (ZMod.unitsMap h u) := by
  rw [changeLevel_eq_cast_of_dvd, ZMod.unitsMap_val]

variable (K : IntermediateField ℚ ℂ) [IsGalois ℚ K] (hK : finrank ℚ K = 3)

/-- **Compatibility of H^⊥ with inflation** (N ∣ P, K ⊆ ℚ(ζ_N)). -/
theorem compat {N P : ℕ} [NeZero N] [NeZero P] (hKN : K ≤ Cyc N) (hNP : N ∣ P)
    (χ : DirichletCharacter ℂ N) :
    χ ∈ CycloSubEuler.perp N (Cyc N) (H K hKN) ↔
      changeLevel hNP χ ∈ CycloSubEuler.perp P (Cyc P) (H K (hKN.trans (cyc_le hNP))) := by
  letI : Algebra (Cyc N) (Cyc P) := (inclusion (cyc_le hNP)).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ (Cyc N) (Cyc P) := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hres : ∀ σ : Gal(Cyc P/ℚ), galEquivZMod N (Cyc N) (σ.restrictNormal (Cyc N)) =
      ZMod.unitsMap hNP (galEquivZMod P (Cyc P) σ) := fun σ =>
    galEquivZMod_restrictNormal_apply P (Cyc P) (Cyc N) hNP σ
  have hcom : ∀ (σ : Gal(Cyc P/ℚ)) (x : Cyc N),
      algebraMap (Cyc N) (Cyc P) (σ.restrictNormal (Cyc N) x) = σ (algebraMap (Cyc N) (Cyc P) x) :=
    fun σ x => σ.restrictNormal_commutes (Cyc N) x
  have halg : ∀ x : Cyc N, ((algebraMap (Cyc N) (Cyc P) x : Cyc P) : ℂ) = (x : ℂ) := fun x => by
    rw [RingHom.algebraMap_toAlgebra]; exact coe_inclusion _ x
  have hinj : Function.Injective (algebraMap (Cyc N) (Cyc P)) := (algebraMap (Cyc N) (Cyc P)).injective
  have hfix : ∀ σ : Gal(Cyc P/ℚ), (∀ y : Cyc P, (y : ℂ) ∈ K → σ y = y) ↔
      (∀ x : Cyc N, (x : ℂ) ∈ K → σ.restrictNormal (Cyc N) x = x) := by
    intro σ
    constructor
    · intro h x hx
      apply hinj
      rw [hcom, h _ (by rwa [halg])]
    · intro h y hy
      obtain ⟨x, hx⟩ : ∃ x : Cyc N, algebraMap (Cyc N) (Cyc P) x = y :=
        ⟨⟨y, hKN hy⟩, Subtype.ext (halg _)⟩
      have hxK : (x : ℂ) ∈ K := by rw [← halg, hx]; exact hy
      rw [← hx, ← hcom, h x hxK]
  rw [mem_perp_iff_fix, mem_perp_iff_fix]
  constructor
  · intro h σ hσ
    rw [changeLevel_unit, ← hres]
    exact h _ ((hfix σ).mp hσ)
  · intro h τ hτ
    have hlift := τ.restrict_liftNormal (Cyc P)
    have := h (τ.liftNormal (Cyc P)) ((hfix _).mpr (by rw [hlift]; exact hτ))
    rwa [changeLevel_unit, ← hres, hlift] at this

omit [IsGalois ℚ K] in
/-- A cubic ψ and ψ² have the same conductor. -/
theorem sq_conductor {N : ℕ} [NeZero N] {ψ : DirichletCharacter ℂ N} (h3 : ψ ^ 3 = 1) :
    (ψ ^ 2).conductor = ψ.conductor := by
  have hfN : ψ.conductor ∣ N := conductor_dvd_level ψ
  have : NeZero ψ.conductor := ⟨fun h => NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ hfN))⟩
  have hlift : changeLevel hfN ψ.primitiveCharacter = ψ := changeLevel_primitiveCharacter ψ
  have hΨ3 : ψ.primitiveCharacter ^ 3 = 1 :=
    changeLevel_injective hfN (by rw [map_pow, hlift, h3, map_one])
  have hψ2 : ψ ^ 2 = changeLevel hfN (ψ.primitiveCharacter ^ 2) := by rw [map_pow, hlift]
  rw [hψ2, conductor_changeLevel,
    CubicFixedField.conductor_sq hΨ3 (primitiveCharacter_isPrimitive ψ)]

include hK in
/-- **The conductor and the pair {Ψ, Ψ̄} are intrinsic to K.** -/
theorem intrinsic_pair [FiniteDimensional ℚ K] :
    ∃ f : ℕ, ∃ _ : NeZero f, ∃ Ψ : DirichletCharacter ℂ f,
      Ψ ^ 3 = 1 ∧ Ψ ≠ 1 ∧ Ψ.IsPrimitive ∧
      (∀ a, (Ψ ^ 2) a = starRingEnd ℂ (Ψ a)) ∧ (Ψ ^ 2).conductor = f ∧
      (∀ m : ℕ, m ≠ 0 → (K ≤ Cyc m ↔ f ∣ m)) ∧
      (∃ a : Bool, ∃ qs : List ℕ, qs.Nodup ∧ (∀ q ∈ qs, q.Prime) ∧ (∀ q ∈ qs, 3 ∣ q - 1) ∧
        (a = true ∨ qs ≠ []) ∧ f = (if a then 9 else 1) * qs.prod) ∧
      (∀ s : ℂ, 1 < s.re → LSeries (fun n => (IdealCount.A (𝓞 K) n : ℂ)) s =
        riemannZeta s * LSeries (fun n => Ψ n) s * LSeries (fun n => (Ψ ^ 2) n) s) ∧
      (∀ (M : ℕ) [NeZero M] (hKM : K ≤ Cyc M), ∃ hfM : f ∣ M,
        changeLevel hfM Ψ ∈ CycloSubEuler.perpNontriv M (Cyc M) (H K hKM)) ∧
      (∀ (M : ℕ) [NeZero M] (hKM : K ≤ Cyc M) (f' : ℕ) [NeZero f']
        (Φ : DirichletCharacter ℂ f') (h : f' ∣ M), Φ.IsPrimitive →
        changeLevel h Φ ∈ CycloSubEuler.perpNontriv M (Cyc M) (H K hKM) →
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
  have hfz : NeZero f := ⟨fun h => NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ hfN))⟩
  set Ψ := ψ.primitiveCharacter with hΨdef
  have hlift : changeLevel hfN Ψ = ψ := changeLevel_primitiveCharacter ψ
  have hΨ3 : Ψ ^ 3 = 1 := changeLevel_injective hfN (by rw [map_pow, hlift, h3, map_one])
  have hΨ1 : Ψ ≠ 1 := fun h => hne (by rw [← hlift, h, map_one])
  have hΨp : Ψ.IsPrimitive := primitiveCharacter_isPrimitive ψ
  have hΨ2c : (Ψ ^ 2).conductor = f := CubicFixedField.conductor_sq hΨ3 hΨp
  have hψ2 : ψ ^ 2 = changeLevel hfN (Ψ ^ 2) := by rw [map_pow, hlift]
  have hsqval : ∀ n : ℕ, (ψ ^ 2).primitiveCharacter n = (Ψ ^ 2) n := fun n => by
    rw [hψ2]; exact prim_changeLevel_apply hfN (Ψ ^ 2) hΨ2c n
  -- at P = N·M, H_P^⊥ ∖ {1} = {ψ↑, ψ↑²}
  have hcommon : ∀ (M : ℕ) [NeZero M], ∃ (P : ℕ) (_ : NeZero P) (hNP : N ∣ P) (hMP : M ∣ P),
      CycloSubEuler.perpNontriv P (Cyc P) (H K (hKN.trans (cyc_le hNP))) =
        {changeLevel hNP ψ, changeLevel hNP ψ ^ 2} := by
    intro M _
    have hPz : NeZero (N * M) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne M)⟩
    refine ⟨N * M, hPz, dvd_mul_right N M, dvd_mul_left M N, ?_⟩
    apply perpNontriv_eq K hK
    refine Finset.mem_erase.mpr ⟨fun h => hne ?_, (compat K hKN _ ψ).mp hp⟩
    exact changeLevel_injective (dvd_mul_right N M) (by rw [h, map_one])
  have hcondψ : ∀ {P : ℕ} [NeZero P] (hNP : N ∣ P), (changeLevel hNP ψ).conductor = f ∧
      (changeLevel hNP ψ ^ 2).conductor = f := fun hNP =>
    ⟨conductor_changeLevel _ _, by rw [← map_pow, conductor_changeLevel, sq_conductor h3]⟩
  have hprimψ : ∀ {P : ℕ} [NeZero P] (hNP : N ∣ P) (n : ℕ),
      (changeLevel hNP ψ).primitiveCharacter n = Ψ n ∧
      (changeLevel hNP ψ ^ 2).primitiveCharacter n = (Ψ ^ 2) n := fun hNP n => by
    have h1 := primitiveCharacter_changeLevel_apply hNP ψ (n : ℤ)
    have h2 := primitiveCharacter_changeLevel_apply hNP (ψ ^ 2) (n : ℤ)
    simp only [Int.cast_natCast] at h1 h2
    rw [← map_pow]
    exact ⟨h1, h2.trans (hsqval n)⟩
  have hmemψ : ∀ {P : ℕ} [NeZero P] (hNP : N ∣ P) (S : Finset (DirichletCharacter ℂ P)),
      (S.erase 1 = {changeLevel hNP ψ, changeLevel hNP ψ ^ 2}) → changeLevel hNP ψ ∈ S :=
    fun hNP S hS => Finset.mem_of_mem_erase (by rw [hS]; simp)
  -- the intrinsic conductor
  have hcond : ∀ m : ℕ, m ≠ 0 → (K ≤ Cyc m ↔ f ∣ m) := by
    intro m hm0
    have : NeZero m := ⟨hm0⟩
    obtain ⟨P, hPz, hNP, hmP, hpn⟩ := hcommon m
    rw [le_cyc_iff K (hKN.trans (cyc_le hNP)) m hmP]
    constructor
    · intro h
      have := h _ (hmemψ hNP _ hpn)
      rwa [(hcondψ hNP).1] at this
    · intro hfm χ hχ
      by_cases h1 : χ = 1
      · rw [h1, conductor_one]; exact one_dvd _
      · have : χ ∈ CycloSubEuler.perpNontriv P (Cyc P) (H K (hKN.trans (cyc_le hNP))) :=
          Finset.mem_erase.mpr ⟨h1, hχ⟩
        rw [hpn, Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with rfl | rfl
        · rw [(hcondψ hNP).1]; exact hfm
        · rw [(hcondψ hNP).2]; exact hfm
  refine ⟨f, hfz, Ψ, hΨ3, hΨ1, hΨp, CubicFixedField.sq_eq_conj hΨ3, hΨ2c, hcond,
    CubicClass.classification hΨ3 hΨ1 hΨp, ?_, ?_, ?_⟩
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
  · -- Ψ appears at every level M containing K
    intro M _ hKM
    have hfM : f ∣ M := (hcond M (NeZero.ne M)).mp hKM
    refine ⟨hfM, Finset.mem_erase.mpr
      ⟨fun h => hΨ1 (changeLevel_injective hfM (by rw [h, map_one])), ?_⟩⟩
    obtain ⟨P, hPz, hNP, hMP, hpn⟩ := hcommon M
    rw [compat K hKM hMP, ← changeLevel_trans]
    have : changeLevel (hfM.trans hMP) Ψ = changeLevel hNP ψ := by
      rw [← hlift, ← changeLevel_trans]
    rw [this]
    exact hmemψ hNP _ hpn
  · -- uniqueness at every level M containing K
    intro M _ hKM f' _ Φ h hΦp hΦ
    obtain ⟨P, hPz, hNP, hMP, hpn⟩ := hcommon M
    obtain ⟨hΦ1, hΦperp⟩ := Finset.mem_erase.mp hΦ
    have hmemP : changeLevel (h.trans hMP) Φ ∈
        CycloSubEuler.perpNontriv P (Cyc P) (H K (hKN.trans (cyc_le hNP))) := by
      refine Finset.mem_erase.mpr ⟨fun h1 => hΦ1 ?_, ?_⟩
      · exact changeLevel_injective hMP (by rw [← changeLevel_trans, h1, map_one])
      · rw [changeLevel_trans Φ h hMP]; exact (compat K hKM hMP _).mp hΦperp
    rw [hpn, Finset.mem_insert, Finset.mem_singleton] at hmemP
    have hval : ∀ n : ℕ, Φ n = (changeLevel (h.trans hMP) Φ).primitiveCharacter n := fun n =>
      (prim_changeLevel_apply (h.trans hMP) Φ hΦp n).symm
    have hcond' : f' = (changeLevel (h.trans hMP) Φ).conductor := by
      rw [conductor_changeLevel]; exact hΦp.symm
    rcases hmemP with hc | hc
    · refine ⟨by rw [hcond', hc, (hcondψ hNP).1], Or.inl fun n => ?_⟩
      rw [hval, hc, (hprimψ hNP n).1]
    · refine ⟨by rw [hcond', hc, (hcondψ hNP).2], Or.inr fun n => ?_⟩
      rw [hval, hc, (hprimψ hNP n).2]

end CubicIntrinsic

#print axioms CubicIntrinsic.compat
#print axioms CubicIntrinsic.intrinsic_pair
