import CharacterDescent
import SubfieldInertia
import CyclotomicDecomposition
import CyclotomicSubfieldEulerProduct
import QuotientOrder

/-!
# CompositeLocalFactor — the local factor of K = ℚ(ζₙ)^H at a ramified prime p ∣ n

n = p^{k+1} m, p ∤ m, r : (ZMod n)ˣ → (ZMod m)ˣ, H' = image of H in (ZMod n)ˣ, H'' = r(H'),
u = p mod m. Then
* `fK_gK_ramified`: f_K(p) = order of u in (ZMod m)ˣ/H'' and g_K(p) = [(ZMod m)ˣ : H''] / f_K(p)
  (from `SubfieldInertia` + `CyclotomicDecomposition` + counting through r);
* `local_ramified`: (1 − x^{f_K})^{g_K} = ∏_{χ ∈ H^⊥} (1 − χ*(p) x), χ* the primitive character:
  characters of H^⊥ factoring through m descend to level m (value at p = ψ(p)); the others have
  p ∣ conductor, so χ*(p) = 0.
-/

open NumberField Ideal MulAction IsCyclotomicExtension.Rat GaloisEuler Finset DirichletCharacter
open scoped Pointwise

namespace CompositeLocal

variable {n m p k : ℕ} [NeZero n] {L : Type*} [Field L] [NumberField L]
  [IsCyclotomicExtension {n} ℚ L] [hp : Fact (Nat.Prime p)]
  (H : Subgroup Gal(L/ℚ)) [H.Normal] (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m)

local notation "K" => IntermediateField.fixedField H

/-- r(H'), the image of H in (ZMod m)ˣ. -/
noncomputable abbrev H'' (hn : n = p ^ (k + 1) * m) : Subgroup (ZMod m)ˣ :=
  (CycloSubEuler.H' n L H).map (CycloDecomp.red hn)

/-- p as a unit mod m. -/
noncomputable abbrev u (hm : ¬ p ∣ m) : (ZMod m)ˣ :=
  ZMod.unitOfCoprime p ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm)

include hn hm in
/-- **f_K(p) and g_K(p) at a ramified prime, from the reduction map.** -/
theorem fK_gK_ramified :
    fK K p = orderOf (QuotientGroup.mk (u hm) : (ZMod m)ˣ ⧸ H'' H hn) ∧
      gK K p = (H'' H hn).index / orderOf (QuotientGroup.mk (u hm) : (ZMod m)ˣ ⧸ H'' H hn) := by
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {n} ℚ L
  have : NeZero m := ⟨(CycloDecomp.m_pos hn).ne'⟩
  have hspan : (span {(p : ℤ)}).IsMaximal := CycloSub.span_isMaximal hp.out
  obtain ⟨⟨P, _, _⟩⟩ := (span {(p : ℤ)}).nonempty_primesOver (S := 𝓞 L)
  have : P.IsMaximal := IsMaximal.of_liesOver_isMaximal P (span {(p : ℤ)})
  set e := galEquivZMod n L
  set r := CycloDecomp.red hn
  set H' := CycloSubEuler.H' n L H
  set Z := Subgroup.zpowers (u hm)
  have hI : (P.inertia Gal(L/ℚ)).map e.toMonoidHom = r.ker := CycloDecomp.inertia_map P hn hm
  have hD : (stabilizer Gal(L/ℚ) P).map e.toMonoidHom = Z.comap r :=
    CycloDecomp.stabilizer_map P hn hm
  have tr : ∀ X : Subgroup Gal(L/ℚ), Nat.card X = Nat.card (X.map e.toMonoidHom) := fun X =>
    (Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective).symm
  have trinf : ∀ X : Subgroup Gal(L/ℚ),
      (X ⊓ H).map e.toMonoidHom = X.map e.toMonoidHom ⊓ H' := fun X =>
    Subgroup.map_inf_eq _ _ _ e.injective
  have heK := SubfieldDeg.eK_mul_card H p P
  have hfK := SubfieldDeg.fK_mul_card H p P
  have hg := SubfieldDeg.gK_eK_fK H p
  rw [tr (P.inertia Gal(L/ℚ) ⊓ H), trinf, hI, tr (P.inertia Gal(L/ℚ)), hI] at heK
  rw [tr (stabilizer Gal(L/ℚ) P ⊓ H), trinf, hD, tr (stabilizer Gal(L/ℚ) P), hD,
    tr (P.inertia Gal(L/ℚ) ⊓ H), trinf, hI, tr (P.inertia Gal(L/ℚ)), hI] at hfK
  have hsurj : Function.Surjective r := ZMod.unitsMap_surjective (CycloDecomp.m_dvd hn)
  -- counting through r
  have hDc : Nat.card (Z.comap r) = Nat.card r.ker * Nat.card Z := by
    rw [CharDescent.card_eq_card_inf_ker_mul_card_map r (Z.comap r),
      inf_eq_right.mpr (MonoidHom.ker_le_comap r Z), Subgroup.map_comap_eq_self_of_surjective hsurj]
  have hDHc : Nat.card (Z.comap r ⊓ H' : Subgroup _) =
      Nat.card (r.ker ⊓ H' : Subgroup _) * Nat.card (Z ⊓ H'' H hn : Subgroup _) := by
    have e1 : (Z.comap r ⊓ H') ⊓ r.ker = r.ker ⊓ H' := by
      rw [inf_comm, ← inf_assoc, inf_eq_left.mpr (MonoidHom.ker_le_comap r Z)]
    have e2 : (Z.comap r ⊓ H').map r = Z ⊓ H'' H hn := by
      apply le_antisymm
      · rintro _ ⟨x, ⟨hx1, hx2⟩, rfl⟩; exact ⟨hx1, ⟨x, hx2, rfl⟩⟩
      · rintro _ ⟨hz, ⟨x, hx, rfl⟩⟩; exact ⟨x, ⟨hz, hx⟩, rfl⟩
    rw [CharDescent.card_eq_card_inf_ker_mul_card_map r (Z.comap r ⊓ H'), e1, e2]
  have hq0 := QuotientOrder.orderOf_mk_mul_card_inf (H'' H hn) (u hm)
  have hq : orderOf (QuotientGroup.mk (u hm) : (ZMod m)ˣ ⧸ H'' H hn) *
      Nat.card (Z ⊓ H'' H hn : Subgroup _) = Nat.card Z := by
    rw [Nat.card_zpowers]; exact hq0
  set ord := orderOf (QuotientGroup.mk (u hm) : (ZMod m)ˣ ⧸ H'' H hn)
  set c := Nat.card (Z ⊓ H'' H hn : Subgroup _)
  set A := Nat.card (r.ker ⊓ H' : Subgroup _)
  set B := Nat.card r.ker
  rw [hDHc, hDc, ← hq] at hfK
  have hApos : 0 < A := Nat.card_pos
  have hBpos : 0 < B := Nat.card_pos
  have hcpos : 0 < c := Nat.card_pos
  have hf : fK K p = ord := by
    refine Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (Nat.mul_pos hApos hcpos) hBpos) ?_
    calc fK K p * (A * c * B) = (span {(p : ℤ)}).inertiaDegIn (𝓞 K) * (A * c) * B := by
          rw [fK]; ring
      _ = B * (ord * c) * A := hfK
      _ = ord * (A * c * B) := by ring
  refine ⟨hf, ?_⟩
  -- the prime count
  have hH'c := CharDescent.card_eq_card_inf_ker_mul_card_map r H'
  have hidxA := H'.card_mul_index
  have hidxB := (H'' H hn).card_mul_index
  have hA : Nat.card (ZMod n)ˣ = B * Nat.card (ZMod m)ˣ := by
    rw [CycloDecomp.card_units hn hm]; congr 1; exact (CycloDecomp.card_ker_red hn hm).symm
  rw [hA, ← hidxB, hH'c, inf_comm] at hidxA
  have heK' : (span {(p : ℤ)}).ramificationIdxIn (𝓞 K) * A = B := by
    exact heK
  have hidx : H'.index = (span {(p : ℤ)}).ramificationIdxIn (𝓞 K) * (H'' H hn).index := by
    have hHpos : 0 < Nat.card (H'' H hn) := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hApos hHpos) ?_
    calc H'.index * (A * Nat.card (H'' H hn)) = A * Nat.card (H'' H hn) * H'.index := by ring
      _ = B * (Nat.card (H'' H hn) * (H'' H hn).index) := hidxA
      _ = _ := by rw [← heK']; ring
  rw [← CycloSubEuler.index_H' n L H, hidx] at hg
  have hePos : 0 < (span {(p : ℤ)}).ramificationIdxIn (𝓞 K) := by
    rcases Nat.eq_zero_or_pos ((span {(p : ℤ)}).ramificationIdxIn (𝓞 K)) with h | h
    · rw [h, zero_mul] at heK'; omega
    · exact h
  have hgf : gK K p * ord = (H'' H hn).index := by
    refine Nat.eq_of_mul_eq_mul_left hePos ?_
    rw [← hf, gK, fK]
    calc _ = ((span {(p : ℤ)}).primesOver (𝓞 K)).ncard *
          ((span {(p : ℤ)}).ramificationIdxIn (𝓞 K) * (span {(p : ℤ)}).inertiaDegIn (𝓞 K)) := by ring
      _ = _ := hg
  have hopos : 0 < ord := orderOf_pos (QuotientGroup.mk (u hm) : (ZMod m)ˣ ⧸ H'' H hn)
  rw [← hgf, Nat.mul_div_cancel _ hopos]

/-- The primitive character of χ, evaluated at the integer a. -/
noncomputable def pv {N : ℕ} (χ : DirichletCharacter ℂ N) (a : ℤ) : ℂ :=
  χ.primitiveCharacter (a : ZMod χ.conductor)

include hn in
theorem changeLevel_apply_unit (ψ : DirichletCharacter ℂ m) (w : (ZMod n)ˣ) :
    changeLevel (CycloDecomp.m_dvd hn) ψ (w : ZMod n) = ψ (CycloDecomp.red hn w : ZMod m) := by
  rw [changeLevel_eq_cast_of_dvd, ZMod.unitsMap_val]

include hn hm in
/-- A character of level n not factoring through m has p ∣ conductor, so χ*(p) = 0. -/
theorem pv_eq_zero (χ : DirichletCharacter ℂ n) (h : ¬ χ.FactorsThrough m) : pv χ (p : ℤ) = 0 := by
  rw [pv, apply_eq_zero_iff]
  intro hcop
  apply h
  have hcop' : Nat.Coprime (p ^ (k + 1)) χ.conductor :=
    Nat.Coprime.pow_left _ (Nat.isCoprime_iff_coprime.mp hcop)
  have hdvd : χ.conductor ∣ m := by
    obtain ⟨c, hc⟩ := χ.conductor_dvd_level
    exact hcop'.symm.dvd_of_dvd_mul_left ⟨c, by rw [← hn]; exact hc⟩
  exact (χ.mem_conductorSet_iff_conductor_dvd (CycloDecomp.m_dvd hn)).mpr hdvd

include hn hm in
/-- For ψ of level m: (changeLevel ψ)*(p) = ψ(p mod m). -/
theorem pv_changeLevel (ψ : DirichletCharacter ℂ m) :
    pv (changeLevel (CycloDecomp.m_dvd hn) ψ) (p : ℤ) = ψ ((u hm : (ZMod m)ˣ) : ZMod m) := by
  have : NeZero m := ⟨(CycloDecomp.m_pos hn).ne'⟩
  rw [pv, primitiveCharacter_changeLevel_apply, primitiveCharacter_apply_of_isCoprime,
    ZMod.coe_unitOfCoprime, Int.cast_natCast]
  exact Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm)

include hn hm in
/-- **Local identity at a ramified prime:** (1 − x^{f_K})^{g_K} = ∏_{χ ∈ H^⊥} (1 − χ*(p) x). -/
theorem local_ramified (x : ℂ) :
    (1 - x ^ fK K p) ^ gK K p = ∏ χ ∈ CycloSubEuler.perp n L H, (1 - pv χ (p : ℤ) * x) := by
  classical
  have : NeZero m := ⟨(CycloDecomp.m_pos hn).ne'⟩
  set Φ : DirichletCharacter ℂ m → DirichletCharacter ℂ n :=
    fun ψ => changeLevel (R := ℂ) (CycloDecomp.m_dvd hn) ψ
  have hΦinj : Function.Injective Φ := changeLevel_injective (CycloDecomp.m_dvd hn)
  rw [← prod_filter_mul_prod_filter_not (CycloSubEuler.perp n L H) (fun χ => χ.FactorsThrough m)]
  have hrest : ∏ χ ∈ (CycloSubEuler.perp n L H).filter (fun χ => ¬ χ.FactorsThrough m),
      (1 - pv χ (p : ℤ) * x) = 1 :=
    prod_eq_one fun χ hχ => by rw [pv_eq_zero hn hm χ (mem_filter.mp hχ).2, zero_mul, sub_zero]
  have himg : (CycloSubEuler.perp n L H).filter (fun χ => χ.FactorsThrough m) =
      (CharDescent.perpN m (H'' H hn)).image Φ := by
    ext χ
    simp only [mem_filter, CycloSubEuler.mem_perp_iff, mem_image, CharDescent.mem_perpN]
    constructor
    · rintro ⟨hperp, hft⟩
      refine ⟨hft.χ₀, ?_, hft.eq_changeLevel.symm⟩
      rintro _ ⟨w, hw, rfl⟩
      rw [← changeLevel_apply_unit hn, ← hft.eq_changeLevel]
      exact hperp w hw
    · rintro ⟨ψ, hψ, rfl⟩
      refine ⟨fun w hw => ?_, changeLevel_factorsThrough _ _⟩
      rw [changeLevel_apply_unit hn]
      exact hψ _ ⟨w, hw, rfl⟩
  rw [hrest, mul_one, himg, prod_image fun a _ b _ h => hΦinj h]
  simp only [Φ, pv_changeLevel hn hm]
  rw [CharDescent.prod_perpN, (fK_gK_ramified H hn hm).1, (fK_gK_ramified H hn hm).2]

end CompositeLocal

#print axioms CompositeLocal.fK_gK_ramified
#print axioms CompositeLocal.local_ramified
