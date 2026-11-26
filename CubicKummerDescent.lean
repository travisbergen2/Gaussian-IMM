import CubicKummerCyclotomicContainment
import CyclotomicSubfieldSplitting

/-!
# CubicKummerDescent — the cyclic cubic field K_q inside E = ℚ(ω, g(χ)) ⊆ ℚ(ζ_{3q})

Setting of `CubicKummer`: q prime, 3 ∣ q − 1, L = ℚ(ζ_{3q}), χ of order 3 mod q,
g = g(χ), E = ℚ(ω, g). Instead of computing Gal(E/ℚ) ≅ C₆ abstractly, the cubic field is
defined by the character:
* `Hq` = {σ_a ∈ Gal(L/ℚ) : χ(a mod q) = 1} = ker(χ ∘ (mod q) ∘ galEquivZMod);
* `index_Hq`: [G : Hq] = |im χ| = 3; `Kq` = L^{Hq}: `finrank_Kq` = 3, `isGalois_Kq`,
  `isCyclic_Kq` (Gal(K_q/ℚ) of prime order 3);
* `finrank_E`: [E : ℚ] = 6 (= 2 · 3);
* `fixing_E_le`: σ fixing E has a ≡ 1 (mod 3) and χ(a) = 1, so fix(E) ≤ Hq and
  `Kq_le_E`: K_q ⊆ E;
* `E_eq_sup`: E = K_q · ℚ(ω) (degrees 3 and 2 both divide [K_q ℚ(ω) : ℚ] ≤ 6).
So the cubic Kummer field descends to the cyclic cubic field cut out by ker χ.
-/

open Polynomial IntermediateField IsCyclotomicExtension CubicKummer

namespace CubicDescent

variable {q : ℕ} [hq : Fact q.Prime] (hq3 : 3 ∣ q - 1)
  {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {3 * q} ℚ L]
  {χ : MulChar (ZMod q) L} (hχ : orderOf χ = 3)

local notation "K₀" => ℚ⟮(ω (q := q) (L := L))⟯

theorem q_dvd : q ∣ 3 * q := dvd_mul_left q 3

/-- χ ∘ (mod q) ∘ galEquivZMod : Gal(L/ℚ) →* Lˣ. -/
noncomputable def chiGal (χ : MulChar (ZMod q) L) : Gal(L/ℚ) →* Lˣ :=
  (χ.toUnitHom.comp (ZMod.unitsMap (q_dvd (q := q)))).comp
    (Rat.galEquivZMod (3 * q) L).toMonoidHom

/-- Hq = ker χ, pulled back to Gal(L/ℚ). -/
noncomputable def Hq (χ : MulChar (ZMod q) L) : Subgroup Gal(L/ℚ) := (chiGal χ).ker

instance : (Hq χ).Normal := CycloSub.normal (3 * q) _

theorem range_chiGal : (chiGal χ).range = χ.toUnitHom.range := by
  ext x
  constructor
  · rintro ⟨σ, rfl⟩; exact ⟨_, rfl⟩
  · rintro ⟨u, rfl⟩
    obtain ⟨v, rfl⟩ := ZMod.unitsMap_surjective (q_dvd (q := q)) u
    obtain ⟨σ, rfl⟩ := (Rat.galEquivZMod (3 * q) L).surjective v
    exact ⟨σ, rfl⟩

include hq3 hχ in
theorem card_range : Nat.card (chiGal χ).range = 3 := by
  rw [range_chiGal]
  have hle : χ.toUnitHom.range ≤ rootsOfUnity 3 L := by
    rintro x ⟨u, rfl⟩
    rw [mem_rootsOfUnity]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, Units.val_one,
      ← MulChar.pow_apply' _ (by norm_num), CubicGauss.pow_three hχ, MulChar.one_apply u.isUnit]
  have hdvd := Subgroup.card_dvd_of_le hle
  have hc : Nat.card (rootsOfUnity 3 L) = 3 := by
    first
    | exact (hω (q := q) (L := L)).card_rootsOfUnity
    | (rw [Nat.card_eq_fintype_card]; exact (hω (q := q) (L := L)).card_rootsOfUnity)
  rw [hc] at hdvd
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exfalso
    apply CubicGauss.ne_one hχ
    rw [Subgroup.card_eq_one, MonoidHom.range_eq_bot_iff] at h
    apply MulChar.ext
    intro u
    rw [← MulChar.coe_toUnitHom, h, MonoidHom.one_apply, Units.val_one,
      MulChar.one_apply u.isUnit]
  · exact h

include hq3 hχ in
theorem index_Hq : (Hq χ).index = 3 := by
  rw [Hq, Subgroup.index_ker, card_range hq3 hχ]

/-- **The cyclic cubic field K_q = L^{ker χ}.** -/
noncomputable abbrev Kq (χ : MulChar (ZMod q) L) : IntermediateField ℚ L := fixedField (Hq χ)

include hq3 hχ in
theorem finrank_Kq : Module.finrank ℚ (Kq χ) = 3 := by
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {3 * q} ℚ L
  rw [CycloSub.finrank_K, index_Hq hq3 hχ]

instance isGalois_Kq : IsGalois ℚ (Kq χ) := by
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {3 * q} ℚ L
  exact IsGalois.of_fixedField_normal_subgroup (Hq χ)

include hq3 hχ in
/-- **K_q/ℚ is cyclic** (Galois of prime degree 3). -/
theorem isCyclic_Kq : IsCyclic Gal(Kq χ/ℚ) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply isCyclic_of_prime_card (p := 3)
  rw [IsGalois.card_aut_eq_finrank, finrank_Kq hq3 hχ]

theorem finrank_K₀ : Module.finrank ℚ K₀ = 2 := by
  have hint : IsIntegral ℚ (ω (q := q) (L := L)) :=
    (hω (q := q) (L := L)).isIntegral (by norm_num) |>.tower_top
  rw [adjoin.finrank hint, ← Polynomial.cyclotomic_eq_minpoly_rat (hω (q := q) (L := L))
    (by norm_num), Polynomial.natDegree_cyclotomic]
  decide

/-- E = ℚ(ω, g). -/
noncomputable abbrev E (χ : MulChar (ZMod q) L) : IntermediateField ℚ L :=
  ℚ⟮(ω (q := q) (L := L)), gaussSum χ (ψ (q := q) (L := L))⟯

include hq3 hχ in
/-- **[E : ℚ] = 6.** -/
theorem finrank_E : Module.finrank ℚ (E χ) = 6 := by
  rw [E, ← adjoin_simple_adjoin_simple]
  show Module.finrank ℚ (K₀⟮gaussSum χ (ψ (q := q) (L := L))⟯) = 6
  have : Module.Free K₀ (K₀⟮gaussSum χ (ψ (q := q) (L := L))⟯) := Module.Free.of_divisionRing _ _
  rw [← Module.finrank_mul_finrank ℚ K₀, finrank_K₀, finrank_kummer hq3 hχ]

theorem ω_mem_E : (ω (q := q) (L := L)) ∈ E χ := subset_adjoin _ _ (by simp)
theorem g_mem_E : gaussSum χ (ψ (q := q) (L := L)) ∈ E χ := subset_adjoin _ _ (by simp)

include hq3 hχ in
/-- **fix(E) ≤ Hq:** σ fixing ω and g has a ≡ 1 (mod 3) and χ(a) = 1. -/
theorem fixing_E_le : (E χ).fixingSubgroup ≤ Hq χ := by
  intro σ hσ
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
  set u := Rat.galEquivZMod (3 * q) L σ
  set a := (u : ZMod (3 * q)).val
  have hlt : a < 3 * q := ZMod.val_lt _
  have hua : ((a : ℕ) : ZMod (3 * q)) = u := ZMod.natCast_zmod_val _
  have ha : a.Coprime (3 * q) := by
    rw [← ZMod.isUnit_iff_coprime, hua]; exact u.isUnit
  have hστ : σ = tau a ha := by
    rw [tau]; apply (Rat.galEquivZMod (3 * q) L).injective
    rw [MulEquiv.apply_symm_apply]; apply Units.ext; rw [ZMod.coe_unitOfCoprime, hua]
  -- a ≡ 1 mod 3
  have hω1 := hσ _ ω_mem_E
  rw [hστ, ω, map_pow, tau_ζ ha hlt, ← pow_mul, Nat.mul_comm a q, pow_mul] at hω1
  have h1 : a % 3 = 1 := by
    have hωa : (ω (q := q) (L := L)) ^ a = ω := hω1
    rw [CubicKummer.pow_mod_q (q := 3) (hω (q := q) (L := L)).pow_eq_one] at hωa
    have := (hω (q := q) (L := L)).pow_inj (Nat.mod_lt _ (by norm_num)) (by norm_num)
      (hωa.trans (pow_one _).symm)
    exact this
  -- χ(a) = 1
  have hg := hσ _ g_mem_E
  rw [hστ, tau_gauss hχ ha hlt h1] at hg
  have hau : IsUnit (a : ZMod q) :=
    (ZMod.isUnit_iff_coprime a q).mpr (Nat.Coprime.coprime_dvd_right (dvd_mul_left q 3) ha)
  have hm := gaussSum_mulShift χ ψ hau.unit
  rw [IsUnit.unit_spec, hg] at hm
  have hχa : χ (a : ZMod q) = 1 :=
    mul_right_cancel₀ (gauss_ne_zero hχ) (hm.trans (one_mul _).symm)
  -- σ ∈ Hq
  show chiGal χ σ = 1
  apply Units.ext
  rw [chiGal, MonoidHom.comp_apply, MonoidHom.comp_apply, MulChar.coe_toUnitHom, ZMod.unitsMap_val,
    Units.val_one]
  show χ (((Rat.galEquivZMod (3 * q) L σ : (ZMod (3 * q))ˣ) : ZMod (3 * q)).cast) = 1
  rw [← hua, ZMod.cast_natCast (dvd_mul_left q 3)]
  exact hχa

include hq3 hχ in
/-- **K_q ⊆ E.** -/
theorem Kq_le_E : Kq χ ≤ E χ := by
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {3 * q} ℚ L
  calc Kq χ ≤ fixedField (E χ).fixingSubgroup := fixedField_antitone (fixing_E_le hq3 hχ)
    _ = E χ := IsGalois.fixedField_fixingSubgroup _

include hq3 hχ in
/-- **E = K_q · ℚ(ω).** -/
theorem E_eq_sup : Kq χ ⊔ K₀ = E χ := by
  have hle : Kq χ ⊔ K₀ ≤ E χ :=
    sup_le (Kq_le_E hq3 hχ) ((adjoin_simple_le_iff).mpr ω_mem_E)
  apply eq_of_le_of_finrank_eq hle
  rw [finrank_E hq3 hχ]
  have h3 : 3 ∣ Module.finrank ℚ (Kq χ ⊔ K₀ : IntermediateField ℚ L) := by
    rw [← finrank_Kq hq3 hχ]; exact finrank_dvd_of_le_right le_sup_left
  have h2 : 2 ∣ Module.finrank ℚ (Kq χ ⊔ K₀ : IntermediateField ℚ L) := by
    rw [← finrank_K₀ (q := q) (L := L)]; exact finrank_dvd_of_le_right le_sup_right
  have h6 : Module.finrank ℚ (Kq χ ⊔ K₀ : IntermediateField ℚ L) ∣ 6 := by
    rw [← finrank_E hq3 hχ]; exact finrank_dvd_of_le_right hle
  have hpos := Nat.pos_of_dvd_of_pos h6 (by norm_num)
  have hle6 := Nat.le_of_dvd (by norm_num) h6
  obtain ⟨k, hk⟩ := h3
  obtain ⟨m, hm⟩ := h2
  omega

end CubicDescent

#print axioms CubicDescent.index_Hq
#print axioms CubicDescent.finrank_Kq
#print axioms CubicDescent.isCyclic_Kq
#print axioms CubicDescent.finrank_E
#print axioms CubicDescent.Kq_le_E
#print axioms CubicDescent.E_eq_sup