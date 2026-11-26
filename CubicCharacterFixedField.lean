import CubicCharacterAssembly
import CompositeCyclotomicEulerProduct
import CyclotomicCharacterCorrespondence

/-!
# CubicCharacterFixedField — primitive cubic character ⇒ cyclic cubic field

Direction proved here: **primitive cubic character ⟹ cyclic cubic field**. The converse
(every cyclic cubic field arises this way) is not proved here.

Setting: f ≥ 1, L = ℚ(ζ_f), Ψ a Dirichlet character mod f with Ψ³ = 1, Ψ ≠ 1, Ψ primitive.
The field is cut out by the global character directly (no compositum of local fields):
* `psiGal` = Ψ ∘ galEquivZMod; `H` = ker; `index_H`: [G : H] = 3 (image = μ₃);
* `K` = L^H: `finrank_K` = 3, Galois, `isCyclic_K`;
* `H'_eq`: the image of H in (ZMod f)ˣ is ker Ψ;
* `perpNontriv_eq`: H^⊥ = {1, Ψ, Ψ²} (via the quotient-character count |H^⊥| = [G : H]);
* `sq_eq_conj`: Ψ² = Ψ̄; `conductor_sq`: Ψ² is primitive of conductor f as well;
* `zeta_K`: ζ_K(s) = ζ(s) · L(s, Ψ) · L(s, Ψ̄), Re s > 1 (Ψ at level f, not a primitive lift);
* `exists_cyclic_cubic`: for f = 9^a · q₁ ⋯ q_r (distinct primes qᵢ ≡ 1 mod 3), a cyclic
  cubic K ⊆ ℚ(ζ_f) with ζ_K = ζ · L(Ψ) · L(Ψ̄), Ψ primitive cubic of conductor f.
-/

open NumberField IntermediateField IsCyclotomicExtension IsCyclotomicExtension.Rat
  DirichletCharacter

namespace CubicFixedField

section Generic

variable {f : ℕ} {Ψ : DirichletCharacter ℂ f}

/-- Ψ³ = 1, Ψ ≠ 1 ⇒ the image of Ψ on units is μ₃ (order 3). -/
theorem card_range_toUnitHom (h3 : Ψ ^ 3 = 1) (hne : Ψ ≠ 1) :
    Nat.card Ψ.toUnitHom.range = 3 := by
  have hle3 : Ψ.toUnitHom.range ≤ rootsOfUnity 3 ℂ := by
    rintro x ⟨u, rfl⟩
    rw [mem_rootsOfUnity]; apply Units.ext
    rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, Units.val_one,
      ← MulChar.pow_apply' _ (by norm_num), h3, MulChar.one_apply u.isUnit]
  have hdvd := Subgroup.card_dvd_of_le hle3
  rw [Complex.card_rootsOfUnity] at hdvd
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exfalso; apply hne
    rw [Subgroup.card_eq_one, MonoidHom.range_eq_bot_iff] at h
    apply MulChar.ext; intro u
    rw [← MulChar.coe_toUnitHom, h, MonoidHom.one_apply, Units.val_one, MulChar.one_apply u.isUnit]
  · exact h

theorem sq_ne_one (h3 : Ψ ^ 3 = 1) (hne : Ψ ≠ 1) : Ψ ^ 2 ≠ 1 := by
  intro h; apply hne
  rw [show Ψ = Ψ ^ 3 * (Ψ ^ 2)⁻¹ by group, h3, h, inv_one, mul_one]

theorem sq_ne_self (hne : Ψ ≠ 1) : Ψ ^ 2 ≠ Ψ := by
  intro h; apply hne; rw [pow_two, mul_eq_left] at h; exact h

/-- **Ψ² = Ψ̄.** -/
theorem sq_eq_conj (h3 : Ψ ^ 3 = 1) (a : ZMod f) : (Ψ ^ 2) a = starRingEnd ℂ (Ψ a) := by
  by_cases ha : IsUnit a
  · have h3' : (Ψ a) ^ 3 = 1 := by
      rw [← MulChar.pow_apply' _ (by norm_num), h3, MulChar.one_apply ha]
    have hnorm := Complex.norm_eq_one_of_pow_eq_one h3' (by norm_num)
    rw [MulChar.pow_apply' _ (by norm_num), ← Complex.inv_eq_conj hnorm]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h3'])
  · rw [MulChar.map_nonunit _ ha, MulChar.map_nonunit _ ha, map_zero]

/-- **Ψ² = Ψ̄ is primitive of conductor f too.** -/
theorem conductor_sq [NeZero f] (h3 : Ψ ^ 3 = 1) (hp : Ψ.IsPrimitive) : (Ψ ^ 2).conductor = f := by
  apply Nat.dvd_antisymm (conductor_dvd_level _)
  have hd : (Ψ ^ 2).conductor ∣ f := conductor_dvd_level _
  have hf : Ψ.FactorsThrough (Ψ ^ 2).conductor := by
    rw [factorsThrough_iff_ker_unitsMap hd]
    have hf2 := factorsThrough_conductor (Ψ ^ 2)
    rw [factorsThrough_iff_ker_unitsMap hd] at hf2
    intro u hu
    have h2 := hf2 hu
    rw [MonoidHom.mem_ker] at h2 ⊢
    have h2' : (Ψ ^ 2) u = 1 := by
      have := congrArg Units.val h2
      rwa [MulChar.coe_toUnitHom, Units.val_one] at this
    apply Units.ext
    rw [MulChar.coe_toUnitHom, Units.val_one]
    have : Ψ = (Ψ ^ 2) ^ 2 := by rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, h3, one_mul]
    rw [this, MulChar.pow_apply_coe, h2', one_pow]
  have := (mem_conductorSet_iff_conductor_dvd Ψ hd).mp hf
  rwa [hp] at this

/-- For ψ of conductor = level, ψ* = ψ on ℕ. -/
theorem primitive_apply [NeZero f] {ψ : DirichletCharacter ℂ f} (hc : ψ.conductor = f) (m : ℕ) :
    ψ.primitiveCharacter m = ψ m := by
  by_cases hm : m.Coprime f
  · have := primitiveCharacter_apply_of_isCoprime ψ (a := m)
      (Nat.isCoprime_iff_coprime.mpr hm)
    simpa using this
  · rw [MulChar.map_nonunit _ (by rw [ZMod.isUnit_iff_coprime, hc]; exact hm),
      MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])]

end Generic

variable {f : ℕ} [NeZero f] {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {f} ℚ L]
  {Ψ : DirichletCharacter ℂ f}

/-- Ψ ∘ galEquivZMod : Gal(L/ℚ) →* ℂˣ. -/
noncomputable def psiGal (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {f} ℚ L]
    (Ψ : DirichletCharacter ℂ f) : Gal(L/ℚ) →* ℂˣ :=
  Ψ.toUnitHom.comp (galEquivZMod f L).toMonoidHom

/-- H = ker Ψ, pulled back to Gal(L/ℚ). -/
noncomputable def H (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {f} ℚ L]
    (Ψ : DirichletCharacter ℂ f) : Subgroup Gal(L/ℚ) := (psiGal L Ψ).ker

instance : (H L Ψ).Normal := CycloSub.normal f _

/-- **The cyclic cubic field K = L^{ker Ψ}.** -/
noncomputable abbrev K (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {f} ℚ L]
    (Ψ : DirichletCharacter ℂ f) : IntermediateField ℚ L := fixedField (H L Ψ)

theorem range_psiGal : (psiGal L Ψ).range = Ψ.toUnitHom.range := by
  ext x
  constructor
  · rintro ⟨σ, rfl⟩; exact ⟨_, rfl⟩
  · rintro ⟨u, rfl⟩
    obtain ⟨σ, rfl⟩ := (galEquivZMod f L).surjective u
    exact ⟨σ, rfl⟩

/-- **[G : H] = 3.** -/
theorem index_H (h3 : Ψ ^ 3 = 1) (hne : Ψ ≠ 1) : (H L Ψ).index = 3 := by
  rw [H, Subgroup.index_ker, range_psiGal, card_range_toUnitHom h3 hne]

theorem finrank_K (h3 : Ψ ^ 3 = 1) (hne : Ψ ≠ 1) : Module.finrank ℚ (K L Ψ) = 3 := by
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {f} ℚ L
  rw [CycloSub.finrank_K, index_H h3 hne]

instance isGalois_K : IsGalois ℚ (K L Ψ) := by
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {f} ℚ L
  exact IsGalois.of_fixedField_normal_subgroup (H L Ψ)

/-- **K/ℚ is cyclic of degree 3.** -/
theorem isCyclic_K (h3 : Ψ ^ 3 = 1) (hne : Ψ ≠ 1) : IsCyclic Gal(K L Ψ/ℚ) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply isCyclic_of_prime_card (p := 3)
  rw [IsGalois.card_aut_eq_finrank, finrank_K h3 hne]

/-- The image of H in (ZMod f)ˣ is ker Ψ. -/
theorem H'_eq : CycloSubEuler.H' f L (H L Ψ) = Ψ.toUnitHom.ker := by
  have : H L Ψ = Ψ.toUnitHom.ker.comap (galEquivZMod f L).toMonoidHom := rfl
  rw [CycloSubEuler.H', this]
  exact Subgroup.map_comap_eq_self_of_surjective (galEquivZMod f L).surjective _

theorem mem_perp {ψ : DirichletCharacter ℂ f} :
    ψ ∈ CycloSubEuler.perp f L (H L Ψ) ↔ ∀ u ∈ Ψ.toUnitHom.ker, ψ u = 1 := by
  rw [CycloSubEuler.mem_perp_iff, H'_eq]

theorem pow_mem_perp (k : ℕ) : Ψ ^ k ∈ CycloSubEuler.perp f L (H L Ψ) := by
  rw [mem_perp]
  intro u hu
  rw [MonoidHom.mem_ker] at hu
  have hu' : Ψ u = 1 := by
    have := congrArg Units.val hu
    rwa [MulChar.coe_toUnitHom, Units.val_one] at this
  rw [MulChar.pow_apply_coe, hu', one_pow]

/-- **H^⊥ = {1, Ψ, Ψ²}**, i.e. H^⊥ ∖ {1} = {Ψ, Ψ²}. -/
theorem perpNontriv_eq (h3 : Ψ ^ 3 = 1) (hne : Ψ ≠ 1) :
    CycloSubEuler.perpNontriv f L (H L Ψ) = {Ψ, Ψ ^ 2} := by
  classical
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {f} ℚ L
  have hcard : (CycloSubEuler.perpNontriv f L (H L Ψ)).card = 2 := by
    rw [CycloSubEuler.perpNontriv, Finset.card_erase_of_mem (CycloSubEuler.one_mem_perp _ L _),
      (CycloCharCorr.card_perp f L (H L Ψ)).1, index_H h3 hne]
  have hsub : ({Ψ, Ψ ^ 2} : Finset _) ⊆ CycloSubEuler.perpNontriv f L (H L Ψ) := by
    intro φ hφ
    rw [Finset.mem_insert, Finset.mem_singleton] at hφ
    rcases hφ with rfl | rfl
    · exact Finset.mem_erase.mpr ⟨hne, by simpa using pow_mem_perp (L := L) (Ψ := φ) 1⟩
    · exact Finset.mem_erase.mpr ⟨sq_ne_one h3 hne, pow_mem_perp 2⟩
  exact (Finset.eq_of_subset_of_card_le hsub
    (by rw [hcard, Finset.card_pair (Ne.symm (sq_ne_self hne))])).symm

/-- **ζ_K(s) = ζ(s) · L(s, Ψ) · L(s, Ψ²)**, Re s > 1, with Ψ² = Ψ̄. -/
theorem zeta_K (h3 : Ψ ^ 3 = 1) (hne : Ψ ≠ 1) (hp : Ψ.IsPrimitive) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun m => (IdealCount.A (𝓞 (K L Ψ)) m : ℂ)) s =
      riemannZeta s * LSeries (fun m => Ψ m) s * LSeries (fun m => (Ψ ^ 2) m) s := by
  classical
  rw [CompositeEuler.LSeries_eq_zeta_mul_prod_primitive f L (H L Ψ) hs,
    Finset.prod_coe_sort (CycloSubEuler.perpNontriv f L (H L Ψ))
      (fun φ => LSeries (fun m => φ.primitiveCharacter m) s), perpNontriv_eq h3 hne,
    Finset.prod_pair (Ne.symm (sq_ne_self hne)), mul_assoc]
  simp only [primitive_apply hp, primitive_apply (conductor_sq h3 hp)]

/-- **Cyclic cubic fields of conductor 9^a · q₁ ⋯ q_r.** For distinct primes qᵢ ≡ 1 (mod 3),
a ∈ {0,1}, not both trivial, and any L = ℚ(ζ_f): some primitive cubic Ψ of conductor f cuts out a
cyclic cubic K ⊆ L with ζ_K = ζ · L(Ψ) · L(Ψ̄). -/
theorem exists_cyclic_cubic (qs : List ℕ) (hnd : qs.Nodup) (hprime : ∀ q ∈ qs, q.Prime)
    (hmod : ∀ q ∈ qs, 3 ∣ q - 1) (a : Bool) (hne : a = true ∨ qs ≠ [])
    {f : ℕ} [NeZero f] (hf : f = (if a then 9 else 1) * qs.prod)
    (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {f} ℚ L] :
    ∃ Ψ : DirichletCharacter ℂ f, Ψ ^ 3 = 1 ∧ Ψ ≠ 1 ∧ Ψ.conductor = f ∧
      Module.finrank ℚ (K L Ψ) = 3 ∧ IsCyclic Gal(K L Ψ/ℚ) ∧
      (∀ x, (Ψ ^ 2) x = starRingEnd ℂ (Ψ x)) ∧
      ∀ s : ℂ, 1 < s.re → LSeries (fun m => (IdealCount.A (𝓞 (K L Ψ)) m : ℂ)) s =
        riemannZeta s * LSeries (fun m => Ψ m) s * LSeries (fun m => (Ψ ^ 2) m) s := by
  subst hf
  obtain ⟨-, Ψ, h3, h1, hp⟩ := CubicAssembly.hasPrimCubic_conductor qs hnd hprime hmod a hne
  exact ⟨Ψ, h3, h1, hp, finrank_K h3 h1, isCyclic_K h3 h1, sq_eq_conj h3,
    fun s hs => zeta_K h3 h1 hp hs⟩

end CubicFixedField

#print axioms CubicFixedField.index_H
#print axioms CubicFixedField.isCyclic_K
#print axioms CubicFixedField.perpNontriv_eq
#print axioms CubicFixedField.conductor_sq
#print axioms CubicFixedField.zeta_K
#print axioms CubicFixedField.exists_cyclic_cubic
