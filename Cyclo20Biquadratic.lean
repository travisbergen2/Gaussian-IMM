import CompositeCyclotomicEulerProduct

/-!
# Cyclo20Biquadratic — ℚ(i, √5) inside ℚ(ζ₂₀), conductor 20

L = ℚ(ζ₂₀), H = {σ : σ(ζ) = ζ^a, a ∈ {1, 9}} (`H`, `mem_H_iff`), K = L^H, [K : ℚ] = 4 (`index_H`).
* `fixedField_eq`: K = ℚ(i, s), i = ζ⁵ (`ii_sq`: i² = −1), s = η + η⁴ − η² − η³, η = ζ⁴
  (`s_sq`: s² = 5).
* `data_two`: at 2 (n = 2²·5): f = 2, g = 1, e = 2. `euler_two`: ∏_{H^⊥} (1 − χ*(2)x) = 1 − x².
* `data_five`: at 5 (n = 5·4): f = 1, g = 2, e = 2. `euler_five`: ∏_{H^⊥} (1 − χ*(5)x) = (1 − x)².
* `perp_eq`: H^⊥ = {1, χ₋₄, χ₅, χ₋₂₀}, with χ₋₄ from Mathlib's `ZMod.χ₄` (level 4), χ₅ from
  `quadraticChar (ZMod 5)` (level 5), both lifted by `changeLevel`, and χ₋₂₀ = χ₋₄χ₅; `distinct`.
* `LSeries_K_explicit`: Σ A_K(m) m⁻ˢ = ζ(s) L(s, χ₋₄*) L(s, χ₅*) L(s, χ₋₂₀*) for Re s > 1,
  an instance of `CompositeEuler.LSeries_eq_zeta_mul_prod_primitive`.

Not proved here: that the primitive characters χ* have conductors exactly 4, 5, 20.
-/

open GaloisEuler NumberField IsCyclotomicExtension IsCyclotomicExtension.Rat IntermediateField

namespace Cyclo20

/-- {1, 9} ≤ (ZMod 20)ˣ. -/
def Hsub : Subgroup (ZMod 20)ˣ where
  carrier := {u | (u : ZMod 20) = 1 ∨ (u : ZMod 20) = 9}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul] at *
    rcases ha with h | h <;> rcases hb with h' | h' <;> rw [h, h'] <;> decide
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rcases ha with h | h
    · left; rw [← Units.val_one, ← Units.ext_iff] at h ⊢; rw [h, inv_one]
    · right
      have h81 : (a : ZMod 20) * 9 = 1 := by rw [h]; decide
      have : (a⁻¹ : (ZMod 20)ˣ) = a := by
        rw [inv_eq_iff_mul_eq_one]; apply Units.ext; rw [Units.val_mul, Units.val_one, h]; decide
      rw [this, h]

instance : DecidablePred (· ∈ Hsub) := fun u =>
  inferInstanceAs (Decidable ((u : ZMod 20) = 1 ∨ (u : ZMod 20) = 9))

theorem units_cases : ∀ x : (ZMod 20)ˣ, (x : ZMod 20) = 1 ∨ (x : ZMod 20) = 3 ∨
    (x : ZMod 20) = 7 ∨ (x : ZMod 20) = 9 ∨ (x : ZMod 20) = 11 ∨ (x : ZMod 20) = 13 ∨
    (x : ZMod 20) = 17 ∨ (x : ZMod 20) = 19 := by
  decide

variable {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {20} ℚ L]

local notation "ζ" => IsCyclotomicExtension.zeta 20 ℚ L

theorem hζ : IsPrimitiveRoot (ζ) 20 := zeta_spec 20 ℚ L

/-- i = ζ⁵. -/
noncomputable def ii : L := ζ ^ 5
/-- η = ζ⁴, a primitive 5th root of unity. -/
noncomputable def η : L := ζ ^ 4
/-- s = η + η⁴ − η² − η³ (s² = 5). -/
noncomputable def s : L := η + η ^ 4 - η ^ 2 - η ^ 3

theorem hη : IsPrimitiveRoot (η : L) 5 := (hζ (L := L)).pow (by norm_num) (by norm_num : 20 = 4 * 5)

theorem s_sq : (s : L) ^ 2 = 5 := by
  have h5 : (η : L) ^ 5 = 1 := (hη (L := L)).pow_eq_one
  have hsum := (hη (L := L)).geom_sum_eq_zero (by norm_num : 1 < 5)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one] at hsum
  rw [s]
  linear_combination ((η : L) ^ 3 - 2 * (η : L) ^ 2 - η + 4) * h5 - hsum

theorem s_ne_zero : (s : L) ≠ 0 := by
  intro h
  have := s_sq (L := L)
  rw [h] at this
  norm_num at this

theorem ζ_pow_mod (k : ℕ) : (ζ : L) ^ k = ζ ^ (k % 20) := by
  conv_lhs => rw [← Nat.mod_add_div k 20, pow_add, pow_mul, (hζ (L := L)).pow_eq_one, one_pow,
    mul_one]

/-- How σ acts, given σ(ζ) = ζ^c. -/
theorem act {σ : Gal(L/ℚ)} {c : ℕ} (hc : σ ζ = ζ ^ c) :
    σ (ii : L) = ζ ^ (5 * c) ∧
      σ (s : L) = ζ ^ (4 * c) + ζ ^ (16 * c) - ζ ^ (8 * c) - ζ ^ (12 * c) := by
  refine ⟨?_, ?_⟩
  · rw [ii, map_pow, hc, ← pow_mul, mul_comm]
  · rw [s, η]
    simp only [← pow_mul, map_sub, map_add, map_pow, hc]
    ring_nf

theorem s_val : (s : L) = ζ ^ 4 + ζ ^ 16 - ζ ^ 8 - ζ ^ 12 := by
  rw [s, η]; ring

/-- H = automorphisms σ with σ(ζ) = ζ^a, a ∈ {1, 9}. -/
noncomputable def H : Subgroup Gal(L/ℚ) := Hsub.comap (galEquivZMod 20 L).toMonoidHom

/-- **σ ∈ H ↔ σ fixes i and s.** -/
theorem mem_H_iff (σ : Gal(L/ℚ)) : σ ∈ H ↔ (σ (ii : L) = ii ∧ σ (s : L) = s) := by
  have hσ : σ ζ = ζ ^ ((galEquivZMod 20 L σ : (ZMod 20)ˣ) : ZMod 20).val :=
    galEquivZMod_apply_of_pow_eq 20 L σ (hζ (L := L)).pow_eq_one
  show ((galEquivZMod 20 L σ : (ZMod 20)ˣ) : ZMod 20) = 1 ∨
    ((galEquivZMod 20 L σ : (ZMod 20)ˣ) : ZMod 20) = 9 ↔ _
  rcases units_cases (galEquivZMod 20 L σ) with h | h | h | h | h | h | h | h
  · have hc : σ ζ = ζ ^ 1 := by rw [hσ, h]; rfl
    obtain ⟨h1, h2⟩ := act hc
    rw [ζ_pow_mod] at h1
    rw [ζ_pow_mod (4 * 1), ζ_pow_mod (16 * 1), ζ_pow_mod (8 * 1), ζ_pow_mod (12 * 1)] at h2
    norm_num at h1 h2
    rw [h]
    refine ⟨fun _ => ⟨by rw [h1, ii], by rw [h2, s_val]; try ring⟩, fun _ => by decide⟩
  · have hc : σ ζ = ζ ^ 3 := by rw [hσ, h]; rfl
    obtain ⟨h1, h2⟩ := act hc
    rw [ζ_pow_mod] at h1
    rw [ζ_pow_mod (4 * 3), ζ_pow_mod (16 * 3), ζ_pow_mod (8 * 3), ζ_pow_mod (12 * 3)] at h2
    norm_num at h1 h2
    rw [h]
    refine ⟨fun hc => absurd hc (by decide), fun ⟨hi, _⟩ => absurd ?_ (by norm_num : (15 : ℕ) ≠ 5)⟩
    rw [h1, ii] at hi
    exact (hζ (L := L)).pow_inj (by norm_num) (by norm_num) hi
  · have hc : σ ζ = ζ ^ 7 := by rw [hσ, h]; rfl
    obtain ⟨h1, h2⟩ := act hc
    rw [ζ_pow_mod] at h1
    rw [ζ_pow_mod (4 * 7), ζ_pow_mod (16 * 7), ζ_pow_mod (8 * 7), ζ_pow_mod (12 * 7)] at h2
    norm_num at h1 h2
    rw [h]
    refine ⟨fun hc => absurd hc (by decide), fun ⟨hi, _⟩ => absurd ?_ (by norm_num : (15 : ℕ) ≠ 5)⟩
    rw [h1, ii] at hi
    exact (hζ (L := L)).pow_inj (by norm_num) (by norm_num) hi
  · have hc : σ ζ = ζ ^ 9 := by rw [hσ, h]; rfl
    obtain ⟨h1, h2⟩ := act hc
    rw [ζ_pow_mod] at h1
    rw [ζ_pow_mod (4 * 9), ζ_pow_mod (16 * 9), ζ_pow_mod (8 * 9), ζ_pow_mod (12 * 9)] at h2
    norm_num at h1 h2
    rw [h]
    refine ⟨fun _ => ⟨by rw [h1, ii], by rw [h2, s_val]; try ring⟩, fun _ => by decide⟩
  · have hc : σ ζ = ζ ^ 11 := by rw [hσ, h]; rfl
    obtain ⟨h1, h2⟩ := act hc
    rw [ζ_pow_mod] at h1
    rw [ζ_pow_mod (4 * 11), ζ_pow_mod (16 * 11), ζ_pow_mod (8 * 11), ζ_pow_mod (12 * 11)] at h2
    norm_num at h1 h2
    rw [h]
    refine ⟨fun hc => absurd hc (by decide), fun ⟨hi, _⟩ => absurd ?_ (by norm_num : (15 : ℕ) ≠ 5)⟩
    rw [h1, ii] at hi
    exact (hζ (L := L)).pow_inj (by norm_num) (by norm_num) hi
  · have hc : σ ζ = ζ ^ 13 := by rw [hσ, h]; rfl
    obtain ⟨h1, h2⟩ := act hc
    rw [ζ_pow_mod] at h1
    rw [ζ_pow_mod (4 * 13), ζ_pow_mod (16 * 13), ζ_pow_mod (8 * 13), ζ_pow_mod (12 * 13)] at h2
    norm_num at h1 h2
    rw [h]
    refine ⟨fun hc => absurd hc (by decide), fun ⟨_, hs⟩ => absurd ?_ (s_ne_zero (L := L))⟩
    have : σ (s : L) = -s := by rw [h2, s_val]; ring
    rw [hs] at this
    linear_combination this / 2
  · have hc : σ ζ = ζ ^ 17 := by rw [hσ, h]; rfl
    obtain ⟨h1, h2⟩ := act hc
    rw [ζ_pow_mod] at h1
    rw [ζ_pow_mod (4 * 17), ζ_pow_mod (16 * 17), ζ_pow_mod (8 * 17), ζ_pow_mod (12 * 17)] at h2
    norm_num at h1 h2
    rw [h]
    refine ⟨fun hc => absurd hc (by decide), fun ⟨_, hs⟩ => absurd ?_ (s_ne_zero (L := L))⟩
    have : σ (s : L) = -s := by rw [h2, s_val]; ring
    rw [hs] at this
    linear_combination this / 2
  · have hc : σ ζ = ζ ^ 19 := by rw [hσ, h]; rfl
    obtain ⟨h1, h2⟩ := act hc
    rw [ζ_pow_mod] at h1
    rw [ζ_pow_mod (4 * 19), ζ_pow_mod (16 * 19), ζ_pow_mod (8 * 19), ζ_pow_mod (12 * 19)] at h2
    norm_num at h1 h2
    rw [h]
    refine ⟨fun hc => absurd hc (by decide), fun ⟨hi, _⟩ => absurd ?_ (by norm_num : (15 : ℕ) ≠ 5)⟩
    rw [h1, ii] at hi
    exact (hζ (L := L)).pow_inj (by norm_num) (by norm_num) hi

/-- **The fixed field of H is ℚ(i, √5)** (s = √5 up to sign: s² = 5). -/
theorem fixedField_eq : fixedField (H (L := L)) = adjoin ℚ {(ii : L), s} := by
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {20} ℚ L
  apply le_antisymm
  · rw [← IsGalois.fixedField_fixingSubgroup (adjoin ℚ {(ii : L), s})]
    intro x hx
    rw [mem_fixedField_iff] at hx ⊢
    intro σ hσ
    apply hx σ
    rw [mem_H_iff]
    exact ⟨hσ ⟨ii, subset_adjoin _ _ (by simp)⟩, hσ ⟨s, subset_adjoin _ _ (by simp)⟩⟩
  · rw [adjoin_le_iff]
    rintro x (rfl | rfl) <;> rw [SetLike.mem_coe, mem_fixedField_iff] <;> intro σ hσ
    · exact ((mem_H_iff σ).mp hσ).1
    · exact ((mem_H_iff σ).mp hσ).2

theorem ii_sq : (ii : L) ^ 2 = -1 := by
  have h := (hζ (L := L)).pow (by norm_num) (by norm_num : 20 = 5 * 4)
  have h2 := h.pow (by norm_num) (by norm_num : 4 = 2 * 2)
  rw [ii]
  exact IsPrimitiveRoot.eq_neg_one_of_two_right h2

instance : (H (L := L)).Normal := CycloSub.normal 20 _

theorem H'_eq : CycloSubEuler.H' 20 L (H (L := L)) = Hsub :=
  Subgroup.map_comap_eq_self_of_surjective (galEquivZMod 20 L).surjective _

theorem card_Hsub : Nat.card Hsub = 2 := by
  rw [Nat.card_eq_fintype_card]; decide

theorem index_H : (H (L := L)).index = 4 := by
  rw [H, Subgroup.index_comap_of_surjective (f := (galEquivZMod 20 L).toMonoidHom) _
    (galEquivZMod 20 L).surjective]
  have h := Hsub.card_mul_index
  rw [card_Hsub, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] at h
  have : Nat.totient 20 = 8 := by decide
  omega

/-! ### p = 2: n = 2²·5 -/

theorem hn2 : (20 : ℕ) = 2 ^ (1 + 1) * 5 := by norm_num
theorem hm2 : ¬ (2 : ℕ) ∣ 5 := by decide

/-- H'' at 2 is {1, 4} ⊂ (ZMod 5)ˣ. -/
theorem mem_H''2 (y : (ZMod 5)ˣ) :
    y ∈ CompositeLocal.H'' (p := 2) (H (L := L)) hn2 ↔ ((y : ZMod 5) = 1 ∨ (y : ZMod 5) = 4) := by
  rw [CompositeLocal.H'', H'_eq, Subgroup.mem_map]
  revert y
  decide

local notation "K" => IntermediateField.fixedField (H (L := L))

theorem card_H''2 : Nat.card (CompositeLocal.H'' (p := 2) (H (L := L)) hn2) = 2 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (mem_H''2 (L := L))), Nat.card_eq_fintype_card]
  decide

theorem orderOf_u2 :
    orderOf (QuotientGroup.mk (CompositeLocal.u (p := 2) hm2) :
      (ZMod 5)ˣ ⧸ CompositeLocal.H'' (p := 2) (H (L := L)) hn2) = 2 := by
  apply orderOf_eq_prime
  · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_H''2]; right; decide
  · rw [Ne, QuotientGroup.eq_one_iff, mem_H''2]; decide

/-- **At p = 2: f = 2, g = 1, e = 2.** -/
theorem data_two :
    fK K 2 = 2 ∧ gK K 2 = 1 ∧ (Ideal.span {((2 : ℕ) : ℤ)}).ramificationIdxIn (𝓞 K) = 2 := by
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {20} ℚ L
  obtain ⟨hf, hg⟩ := CompositeLocal.fK_gK_ramified (H (L := L)) hn2 hm2
  rw [orderOf_u2] at hf hg
  have hi := (CompositeLocal.H'' (p := 2) (H (L := L)) hn2).card_mul_index
  rw [card_H''2, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] at hi
  have h4 : Nat.totient 5 = 4 := by decide
  have hidx : (CompositeLocal.H'' (p := 2) (H (L := L)) hn2).index = 2 := by omega
  rw [hidx] at hg
  have hgef := SubfieldDeg.gK_eK_fK (H (L := L)) 2
  rw [index_H] at hgef
  refine ⟨hf, hg, ?_⟩
  rw [gK] at hg; rw [fK] at hf
  rw [hf, hg] at hgef
  omega

/-! ### p = 5: n = 5·4 -/

theorem hn5 : (20 : ℕ) = 5 ^ (0 + 1) * 4 := by norm_num
theorem hm5 : ¬ (5 : ℕ) ∣ 4 := by decide

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- H'' at 5 is trivial. -/
theorem mem_H''5 (y : (ZMod 4)ˣ) :
    y ∈ CompositeLocal.H'' (p := 5) (H (L := L)) hn5 ↔ (y : ZMod 4) = 1 := by
  rw [CompositeLocal.H'', H'_eq, Subgroup.mem_map]
  revert y
  decide

theorem card_H''5 : Nat.card (CompositeLocal.H'' (p := 5) (H (L := L)) hn5) = 1 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (mem_H''5 (L := L))), Nat.card_eq_fintype_card]
  decide

theorem orderOf_u5 :
    orderOf (QuotientGroup.mk (CompositeLocal.u (p := 5) hm5) :
      (ZMod 4)ˣ ⧸ CompositeLocal.H'' (p := 5) (H (L := L)) hn5) = 1 := by
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff, mem_H''5]; decide

/-- **At p = 5: f = 1, g = 2, e = 2.** -/
theorem data_five :
    fK K 5 = 1 ∧ gK K 5 = 2 ∧ (Ideal.span {((5 : ℕ) : ℤ)}).ramificationIdxIn (𝓞 K) = 2 := by
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {20} ℚ L
  obtain ⟨hf, hg⟩ := CompositeLocal.fK_gK_ramified (H (L := L)) hn5 hm5
  rw [orderOf_u5] at hf hg
  have hi := (CompositeLocal.H'' (p := 5) (H (L := L)) hn5).card_mul_index
  rw [card_H''5, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] at hi
  have h4 : Nat.totient 4 = 2 := by decide
  have hidx : (CompositeLocal.H'' (p := 5) (H (L := L)) hn5).index = 2 := by omega
  rw [hidx] at hg
  have hgef := SubfieldDeg.gK_eK_fK (H (L := L)) 5
  rw [index_H] at hgef
  refine ⟨hf, hg, ?_⟩
  rw [gK] at hg; rw [fK] at hf
  rw [hf, hg] at hgef
  omega

/-! ### Local Euler factors and the global factorization -/

/-- **Euler factor at 2:** ∏_{χ ∈ H^⊥} (1 − χ*(2) x) = 1 − x². -/
theorem euler_two (x : ℂ) :
    ∏ χ ∈ CycloSubEuler.perp 20 L (H (L := L)), (1 - CompositeLocal.pv χ ((2 : ℕ) : ℤ) * x) =
      1 - x ^ 2 := by
  rw [← CompositeLocal.local_ramified (H (L := L)) hn2 hm2, (data_two (L := L)).1,
    (data_two (L := L)).2.1, pow_one]

/-- **Euler factor at 5:** ∏_{χ ∈ H^⊥} (1 − χ*(5) x) = (1 − x)². -/
theorem euler_five (x : ℂ) :
    ∏ χ ∈ CycloSubEuler.perp 20 L (H (L := L)), (1 - CompositeLocal.pv χ ((5 : ℕ) : ℤ) * x) =
      (1 - x) ^ 2 := by
  rw [← CompositeLocal.local_ramified (H (L := L)) hn5 hm5, (data_five (L := L)).1,
    (data_five (L := L)).2.1, pow_one]

/-- **Global factorization for ℚ(i, √5)**, Re s > 1. -/
theorem LSeries_K {z : ℂ} (hz : 1 < z.re) :
    LSeries (fun m => (IdealCount.A (𝓞 K) m : ℂ)) z =
      riemannZeta z * ∏ χ : CycloSubEuler.perpNontriv 20 L (H (L := L)),
        LSeries (fun m => χ.1.primitiveCharacter m) z :=
  CompositeEuler.LSeries_eq_zeta_mul_prod_primitive 20 L (H (L := L)) hz

/-! ### H^⊥ = {1, χ₋₄, χ₅, χ₋₂₀} -/

/-- χ₋₄, the character of ℚ(i) (conductor 4), from Mathlib's `ZMod.χ₄`. -/
noncomputable def c4 : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)
/-- χ₅ = (·/5), the character of ℚ(√5) (conductor 5), from Mathlib's `quadraticChar`. -/
noncomputable def c5 : DirichletCharacter ℂ 5 :=
  (quadraticChar (ZMod 5)).ringHomComp (Int.castRingHom ℂ)

/-- The three quadratic characters, lifted to level 20. -/
noncomputable def chiM4 : DirichletCharacter ℂ 20 := DirichletCharacter.changeLevel (by norm_num) c4
noncomputable def chi5 : DirichletCharacter ℂ 20 := DirichletCharacter.changeLevel (by norm_num) c5
noncomputable def chiM20 : DirichletCharacter ℂ 20 := chiM4 * chi5

theorem q5_sq (a : ZMod 5) (h0 : a ≠ 0) (h : IsSquare a) : c5 a = 1 := by
  simp only [c5, MulChar.ringHomComp_apply, quadraticChar_apply, quadraticCharFun, if_neg h0,
    if_pos h]; simp

theorem q5_nsq (a : ZMod 5) (h0 : a ≠ 0) (h : ¬ IsSquare a) : c5 a = -1 := by
  simp only [c5, MulChar.ringHomComp_apply, quadraticChar_apply, quadraticCharFun, if_neg h0,
    if_neg h]; simp

theorem lvl4 (c : ℕ) (hc : c.Coprime 20) : chiM4 (c : ZMod 20) = c4 ((c : ZMod 20).cast) := by
  rw [← ZMod.coe_unitOfCoprime c hc, chiM4, DirichletCharacter.changeLevel_eq_cast_of_dvd]

theorem lvl5 (c : ℕ) (hc : c.Coprime 20) : chi5 (c : ZMod 20) = c5 ((c : ZMod 20).cast) := by
  rw [← ZMod.coe_unitOfCoprime c hc, chi5, DirichletCharacter.changeLevel_eq_cast_of_dvd]

theorem chiM4_3 : chiM4 ((3 : ℕ) : ZMod 20) = -1 := by
  rw [lvl4 3 (by norm_num), show ((3 : ℕ) : ZMod 20).cast = (3 : ZMod 4) by decide]; simp [c4] <;> decide
theorem chiM4_11 : chiM4 ((11 : ℕ) : ZMod 20) = -1 := by
  rw [lvl4 11 (by norm_num), show ((11 : ℕ) : ZMod 20).cast = (3 : ZMod 4) by decide]; simp [c4] <;> decide
theorem chiM4_9 : chiM4 ((9 : ℕ) : ZMod 20) = 1 := by
  rw [lvl4 9 (by norm_num), show ((9 : ℕ) : ZMod 20).cast = (1 : ZMod 4) by decide]; simp
theorem chi5_3 : chi5 ((3 : ℕ) : ZMod 20) = -1 := by
  rw [lvl5 3 (by norm_num), show ((3 : ℕ) : ZMod 20).cast = (3 : ZMod 5) by decide]
  exact q5_nsq _ (by decide) (by rintro ⟨r, hr⟩; revert r; decide)
theorem chi5_11 : chi5 ((11 : ℕ) : ZMod 20) = 1 := by
  rw [lvl5 11 (by norm_num), show ((11 : ℕ) : ZMod 20).cast = (1 : ZMod 5) by decide]; simp
theorem chi5_9 : chi5 ((9 : ℕ) : ZMod 20) = 1 := by
  rw [lvl5 9 (by norm_num), show ((9 : ℕ) : ZMod 20).cast = (4 : ZMod 5) by decide]
  exact q5_sq _ (by decide) ⟨2, by decide⟩

/-- (ZMod 20)ˣ = ⟨3⟩ × ⟨11⟩: a character with χ(9) = 1 is determined by χ(3), χ(11). -/
theorem eq_of_vals {χ ψ : DirichletCharacter ℂ 20} (hχ : χ (9 : ZMod 20) = 1)
    (hψ : ψ (9 : ZMod 20) = 1) (h3 : χ (3 : ZMod 20) = ψ 3) (h11 : χ (11 : ZMod 20) = ψ 11) :
    χ = ψ := by
  apply MulChar.ext
  intro a
  rcases units_cases a with h | h | h | h | h | h | h | h <;> rw [h]
  · simp
  · exact h3
  · rw [show (7 : ZMod 20) = 3 * 9 by decide, map_mul, map_mul, h3, hχ, hψ]
  · rw [hχ, hψ]
  · exact h11
  · rw [show (13 : ZMod 20) = 3 * 11 by decide, map_mul, map_mul, h3, h11]
  · rw [show (17 : ZMod 20) = 3 * 9 * 11 by decide, map_mul, map_mul, map_mul, map_mul, h3, h11,
      hχ, hψ]
  · rw [show (19 : ZMod 20) = 9 * 11 by decide, map_mul, map_mul, h11, hχ, hψ]

theorem mem_perp_iff9 (χ : DirichletCharacter ℂ 20) :
    χ ∈ CycloSubEuler.perp 20 L (H (L := L)) ↔ χ (9 : ZMod 20) = 1 := by
  rw [CycloSubEuler.mem_perp_iff, H'_eq]
  constructor
  · intro h
    have := h (ZMod.unitOfCoprime 9 (by norm_num)) (Or.inr (by simp))
    simpa using this
  · intro h u hu
    rcases hu with hu | hu
    · rw [hu, map_one]
    · rw [hu, h]

theorem sq_one {χ : DirichletCharacter ℂ 20} {c : ZMod 20} (h : χ (c * c) = 1) :
    χ c = 1 ∨ χ c = -1 := by
  rw [map_mul] at h; exact mul_self_eq_one_iff.mp h

/-- **H^⊥ = {1, χ₋₄, χ₅, χ₋₂₀}.** -/
theorem perp_eq : CycloSubEuler.perp 20 L (H (L := L)) = {1, chiM4, chi5, chiM20} := by
  have v43 : chiM4 (3 : ZMod 20) = -1 := by simpa using chiM4_3
  have v411 : chiM4 (11 : ZMod 20) = -1 := by simpa using chiM4_11
  have v49 : chiM4 (9 : ZMod 20) = 1 := by simpa using chiM4_9
  have v53 : chi5 (3 : ZMod 20) = -1 := by simpa using chi5_3
  have v511 : chi5 (11 : ZMod 20) = 1 := by simpa using chi5_11
  have v59 : chi5 (9 : ZMod 20) = 1 := by simpa using chi5_9
  have one3 : (1 : DirichletCharacter ℂ 20) (3 : ZMod 20) = 1 := MulChar.one_apply (by decide)
  have one9 : (1 : DirichletCharacter ℂ 20) (9 : ZMod 20) = 1 := MulChar.one_apply (by decide)
  have one11 : (1 : DirichletCharacter ℂ 20) (11 : ZMod 20) = 1 := MulChar.one_apply (by decide)
  ext χ
  simp only [Finset.mem_insert, Finset.mem_singleton, mem_perp_iff9]
  constructor
  · intro h9
    have h3 := sq_one (χ := χ) (c := 3) (by rw [show (3 : ZMod 20) * 3 = 9 by decide]; exact h9)
    have h11 := sq_one (χ := χ) (c := 11) (by rw [show (11 : ZMod 20) * 11 = 1 by decide]; simp)
    rcases h3 with h3 | h3 <;> rcases h11 with h11 | h11
    · left; exact eq_of_vals h9 one9 (by rw [h3, one3]) (by rw [h11, one11])
    · right; right; right
      exact eq_of_vals h9 (by simp [chiM20, v49, v59])
        (by simp [chiM20, h3, v43, v53]) (by simp [chiM20, h11, v411, v511])
    · right; right; left; exact eq_of_vals h9 v59 (by rw [h3, v53]) (by rw [h11, v511])
    · right; left; exact eq_of_vals h9 v49 (by rw [h3, v43]) (by rw [h11, v411])
  · rintro (rfl | rfl | rfl | rfl)
    · exact one9
    · exact v49
    · exact v59
    · simp [chiM20, v49, v59]

/-- The four characters are distinct (values at 3 and 11). -/
theorem distinct :
    (1 : DirichletCharacter ℂ 20) ≠ chiM4 ∧ (1 : DirichletCharacter ℂ 20) ≠ chi5 ∧
      (1 : DirichletCharacter ℂ 20) ≠ chiM20 ∧ chiM4 ≠ chi5 ∧ chiM4 ≠ chiM20 ∧ chi5 ≠ chiM20 := by
  have v43 : chiM4 (3 : ZMod 20) = -1 := by simpa using chiM4_3
  have v411 : chiM4 (11 : ZMod 20) = -1 := by simpa using chiM4_11
  have v53 : chi5 (3 : ZMod 20) = -1 := by simpa using chi5_3
  have v511 : chi5 (11 : ZMod 20) = 1 := by simpa using chi5_11
  have one3 : (1 : DirichletCharacter ℂ 20) (3 : ZMod 20) = 1 :=
    MulChar.one_apply (by decide)
  have one11 : (1 : DirichletCharacter ℂ 20) (11 : ZMod 20) = 1 :=
    MulChar.one_apply (by decide)
  have m3 : chiM20 (3 : ZMod 20) = 1 := by simp [chiM20, v43, v53]
  have m11 : chiM20 (11 : ZMod 20) = -1 := by simp [chiM20, v411, v511]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h
  · have := congrArg (· (3 : ZMod 20)) h; simp only [one3, v43] at this; norm_num at this
  · have := congrArg (· (3 : ZMod 20)) h; simp only [one3, v53] at this; norm_num at this
  · have := congrArg (· (11 : ZMod 20)) h; simp only [one11, m11] at this; norm_num at this
  · have := congrArg (· (11 : ZMod 20)) h; simp only [v411, v511] at this; norm_num at this
  · have := congrArg (· (3 : ZMod 20)) h; simp only [v43, m3] at this; norm_num at this
  · have := congrArg (· (3 : ZMod 20)) h; simp only [v53, m3] at this; norm_num at this

theorem perpNontriv_eq :
    CycloSubEuler.perpNontriv 20 L (H (L := L)) = {chiM4, chi5, chiM20} := by
  classical
  obtain ⟨d1, d2, d3, -, -, -⟩ := distinct
  rw [CycloSubEuler.perpNontriv, perp_eq]
  ext χ
  simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hne, h | h | h | h⟩
    · exact absurd h hne
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h) <;> subst h
    · exact ⟨d1.symm, Or.inr (Or.inl rfl)⟩
    · exact ⟨d2.symm, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨d3.symm, Or.inr (Or.inr (Or.inr rfl))⟩

/-- **Global factorization, explicit:** for Re s > 1,
Σ A_K(m) m⁻ˢ = ζ(s) · L(s, χ₋₄*) · L(s, χ₅*) · L(s, χ₋₂₀*), K = ℚ(i, √5). -/
theorem LSeries_K_explicit {z : ℂ} (hz : 1 < z.re) :
    LSeries (fun m => (IdealCount.A (𝓞 K) m : ℂ)) z =
      riemannZeta z * (LSeries (fun m => chiM4.primitiveCharacter m) z *
        (LSeries (fun m => chi5.primitiveCharacter m) z *
          LSeries (fun m => chiM20.primitiveCharacter m) z)) := by
  classical
  obtain ⟨-, -, -, d4, d5, d6⟩ := distinct
  rw [LSeries_K hz, Finset.prod_coe_sort (CycloSubEuler.perpNontriv 20 L (H (L := L)))
    (fun χ => LSeries (fun m => χ.primitiveCharacter m) z), perpNontriv_eq,
    Finset.prod_insert (by simp [d4, d5]), Finset.prod_insert (by simp [d6]),
    Finset.prod_singleton]

end Cyclo20

#print axioms Cyclo20.fixedField_eq
#print axioms Cyclo20.data_two
#print axioms Cyclo20.data_five
#print axioms Cyclo20.euler_two
#print axioms Cyclo20.euler_five
#print axioms Cyclo20.perp_eq
#print axioms Cyclo20.LSeries_K_explicit
