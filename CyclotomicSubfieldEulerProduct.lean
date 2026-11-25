import CharacterProduct
import CyclotomicSubfieldSplitting
import AbelianEulerProduct

/-!
# CyclotomicSubfieldEulerProduct — ζ_K = ζ · ∏_{χ ∈ H^⊥, χ ≠ 1} L(χ) for every K = ℚ(ζₙ)^H

Automatic character selection. For H ≤ Gal(ℚ(ζₙ)/ℚ), let H' ≤ (ZMod n)ˣ be its image and
H^⊥ = {Dirichlet characters χ mod n with χ = 1 on H'}. Then for p ∤ n

    (1 − x^{f_K(p)})^{g_K(p)} = ∏_{χ ∈ H^⊥} (1 − χ(p) x)

(`CharProd.prod_one_sub_perp` + `CycloSub.fK_eq_orderOf` + `CycloSub.gK_mul_fK`).
For p ∣ n we assume p has one prime of residue degree 1 in ℚ(ζₙ) (`hram`); this holds for
every prime-power n (`LSeries_eq_prod_perp_primePow`). Then every nontrivial χ vanishes at p and
the local factor is (1 − x).
-/

open NumberField Ideal IsCyclotomicExtension.Rat GaloisEuler Finset

namespace CycloSubEuler

variable (n : ℕ) [NeZero n] (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {n} ℚ L]
  (H : Subgroup Gal(L/ℚ))

/-- The image of H in (ZMod n)ˣ. -/
noncomputable def H' : Subgroup (ZMod n)ˣ := H.map (galEquivZMod n L).toMonoidHom

noncomputable instance : Fintype (DirichletCharacter ℂ n) := Fintype.ofFinite _

open Classical in
/-- H^⊥: Dirichlet characters mod n trivial on H'. -/
noncomputable def perp : Finset (DirichletCharacter ℂ n) :=
  univ.filter fun χ => ∀ u ∈ H' n L H, χ u = 1

open Classical in
/-- The nontrivial characters in H^⊥. -/
noncomputable def perpNontriv : Finset (DirichletCharacter ℂ n) := (perp n L H).erase 1

theorem one_mem_perp : (1 : DirichletCharacter ℂ n) ∈ perp n L H := by
  classical
  simp [perp, MulChar.one_apply_coe]

theorem index_H' : (H' n L H).index = H.index :=
  Subgroup.index_map_equiv H (galEquivZMod n L)

local notation "K" => IntermediateField.fixedField H

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (hn : p.Coprime n)

theorem mem_perp_iff (χ : DirichletCharacter ℂ n) :
    χ ∈ perp n L H ↔ ∀ u ∈ H' n L H, χ u = 1 := by
  classical
  simp [perp]

/-- Dirichlet characters trivial on H' ≃ unit characters trivial on H'. -/
noncomputable def perpUnitEquiv :
    {χ : DirichletCharacter ℂ n // ∀ u ∈ H' n L H, χ u = 1} ≃
      {φ : (ZMod n)ˣ →* ℂˣ // ∀ h ∈ H' n L H, φ h = 1} :=
  MulChar.equivToUnitHom.subtypeEquiv fun χ => by
    refine forall₂_congr fun u _ => ?_
    rw [Units.ext_iff, MulChar.coe_equivToUnitHom, Units.val_one]

include hn in
/-- **∏_{χ ∈ H^⊥} (1 − χ(p) x) = (1 − x^f)^{[G:H]/f}** with f = order of the image of p in
(ZMod n)ˣ/H'. -/
theorem prod_perp_eq (x : ℂ) :
    ∏ χ ∈ perp n L H, (1 - χ (p : ZMod n) * x) =
      (1 - x ^ orderOf (QuotientGroup.mk (ZMod.unitOfCoprime p hn) : (ZMod n)ˣ ⧸ H' n L H)) ^
        (H.index / orderOf (QuotientGroup.mk (ZMod.unitOfCoprime p hn) : (ZMod n)ˣ ⧸ H' n L H)) := by
  classical
  have := CharProd.finite_dual (A := (ZMod n)ˣ)
  have : Fintype {φ : (ZMod n)ˣ →* ℂˣ // ∀ h ∈ H' n L H, φ h = 1} := Fintype.ofFinite _
  rw [prod_subtype (perp n L H) (mem_perp_iff n L H),
    Fintype.prod_equiv (perpUnitEquiv n L H) _
      (fun φ => 1 - ((φ.1 (ZMod.unitOfCoprime p hn) : ℂˣ) : ℂ) * x) (fun χ => by
        simp [perpUnitEquiv, MulChar.coe_equivToUnitHom, ZMod.coe_unitOfCoprime]),
    CharProd.prod_one_sub_perp, index_H']

variable [H.Normal]

include hn in
theorem orderOf_eq_fK :
    orderOf (QuotientGroup.mk (ZMod.unitOfCoprime p hn) : (ZMod n)ˣ ⧸ H' n L H) = fK K p := by
  have he : H.map (galEquivZMod n L : Gal(L/ℚ) →* (ZMod n)ˣ) = H' n L H := rfl
  have hC : QuotientGroup.congr H (H' n L H) (galEquivZMod n L) he
      (QuotientGroup.mk (CycloFrob.sigmaP n L p hn)) =
      QuotientGroup.mk (ZMod.unitOfCoprime p hn) := by
    rw [QuotientGroup.congr_mk, CycloFrob.sigmaP, MulEquiv.apply_symm_apply]
  rw [fK, CycloSub.fK_eq_orderOf n L H p hn, ← hC, MulEquiv.orderOf_eq]

include hn in
/-- **Local identity at p ∤ n:** (1 − x^{f_K})^{g_K} = ∏_{χ ∈ H^⊥} (1 − χ(p) x). -/
theorem local_unramified (x : ℂ) :
    (1 - x ^ fK K p) ^ gK K p = ∏ χ ∈ perp n L H, (1 - χ (p : ZMod n) * x) := by
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {n} ℚ L
  have hgf := (CycloSub.gK_mul_fK n L H p hn).2
  rw [← gK, ← fK] at hgf
  have hpos : 0 < fK K p := by exact fK_pos p
  have hg : gK K p = H.index / fK K p := by rw [← hgf, Nat.mul_div_cancel _ hpos]
  rw [prod_perp_eq n L H p hn, orderOf_eq_fK n L H p hn, hg]

/-- Separate the trivial character: ∏_{H^⊥} = (1 − 1(p) x) · ∏_{H^⊥ \ 1}. -/
theorem prod_perp_split (F : DirichletCharacter ℂ n → ℂ) :
    ∏ χ ∈ perp n L H, F χ = F 1 * ∏ χ : perpNontriv n L H, F χ := by
  classical
  rw [← mul_prod_erase _ _ (one_mem_perp n L H), prod_coe_sort]
  rfl

omit hp in
/-- **Local matching at every prime**, assuming each p ∣ n has one prime of degree 1 in ℚ(ζₙ). -/
theorem hloc_general
    (hram : ∀ q : ℕ, q.Prime → q ∣ n →
      ((span {(q : ℤ)}).primesOver (𝓞 L)).ncard = 1 ∧ (span {(q : ℤ)}).inertiaDegIn (𝓞 L) = 1)
    (p : ℕ) (hp : p.Prime) (x : ℂ) :
    (1 - x ^ fK K p) ^ gK K p =
      (1 - x) * ∏ χ : perpNontriv n L H, (1 - χ.1 (p : ZMod n) * x) := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {n} ℚ L
  by_cases hcop : p.Coprime n
  · rw [local_unramified n L H p hcop, prod_perp_split n L H (fun χ => 1 - χ (p : ZMod n) * x)]
    have hu : IsUnit (p : ZMod n) := (ZMod.isUnit_iff_coprime p n).mpr hcop
    rw [MulChar.one_apply hu, one_mul]
  · have hdvd : p ∣ n := (Nat.Prime.dvd_iff_not_coprime hp).mpr hcop
    obtain ⟨hg, hf⟩ := SubfieldDeg.ramified_descends H p (hram p hp hdvd).1 (hram p hp hdvd).2
    have hnu : ¬ IsUnit (p : ZMod n) := fun h => hcop ((ZMod.isUnit_iff_coprime p n).mp h)
    rw [gK, fK, hg, hf, pow_one, pow_one]
    simp [MulChar.map_nonunit _ hnu]

omit hp in
/-- **Dedekind factorization of every subfield K = ℚ(ζₙ)^H**, characters chosen automatically:
Σ A_K(m) m⁻ˢ = ζ(s) · ∏_{χ ∈ H^⊥, χ ≠ 1} L(s, χ), Re s > 1
(assuming each p ∣ n has one prime of degree 1 in ℚ(ζₙ)). -/
theorem LSeries_eq_zeta_mul_prod_perp
    (hram : ∀ q : ℕ, q.Prime → q ∣ n →
      ((span {(q : ℤ)}).primesOver (𝓞 L)).ncard = 1 ∧ (span {(q : ℤ)}).inertiaDegIn (𝓞 L) = 1)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun m => (IdealCount.A (𝓞 K) m : ℂ)) s =
      riemannZeta s * ∏ χ : perpNontriv n L H, LSeries (fun m => χ.1 m) s := by
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {n} ℚ L
  exact LSeries_A_eq_zeta_mul_prod (fun χ : perpNontriv n L H => χ.1) (hloc_general n L H hram) hs

end CycloSubEuler

namespace CycloSubEuler

/-- **Prime-power conductor: no hypothesis.** For L = ℚ(ζ_{ℓ^{k+1}}) and any subgroup H,
ζ_{L^H} = ζ · ∏_{χ ∈ H^⊥, χ ≠ 1} L(χ) for Re s > 1. -/
theorem LSeries_eq_prod_perp_primePow (ℓ k : ℕ) [hℓ : Fact ℓ.Prime] {L : Type*} [Field L]
    [NumberField L] [IsCyclotomicExtension {ℓ ^ (k + 1)} ℚ L] (H : Subgroup Gal(L/ℚ))
    {s : ℂ} (hs : 1 < s.re) :
    haveI : NeZero (ℓ ^ (k + 1)) := ⟨pow_ne_zero _ hℓ.out.ne_zero⟩
    LSeries (fun m => (IdealCount.A (𝓞 (IntermediateField.fixedField H)) m : ℂ)) s =
      riemannZeta s * ∏ χ : perpNontriv (ℓ ^ (k + 1)) L H, LSeries (fun m => χ.1 m) s := by
  have : NeZero (ℓ ^ (k + 1)) := ⟨pow_ne_zero _ hℓ.out.ne_zero⟩
  have : H.Normal := CycloSub.normal (ℓ ^ (k + 1)) H
  refine LSeries_eq_zeta_mul_prod_perp (ℓ ^ (k + 1)) L H (fun q hq hdvd => ?_) hs
  obtain rfl : q = ℓ := (Nat.prime_dvd_prime_iff_eq hq hℓ.out).mp (hq.dvd_of_dvd_pow hdvd)
  exact ⟨ncard_primesOver_of_prime_pow q k L, inertiaDegIn_eq_of_prime_pow q k L⟩

end CycloSubEuler

#print axioms CycloSubEuler.local_unramified
#print axioms CycloSubEuler.LSeries_eq_zeta_mul_prod_perp
#print axioms CycloSubEuler.LSeries_eq_prod_perp_primePow
