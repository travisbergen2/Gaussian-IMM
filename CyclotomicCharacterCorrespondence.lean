import QuotientCharacterEquiv
import CyclotomicSubfieldEulerProduct

/-!
# CyclotomicCharacterCorrespondence — characters of Gal(K/ℚ) are exactly H^⊥

L = ℚ(ζₙ), G = Gal(L/ℚ) ≅ (ZMod n)ˣ, H ≤ G, K = L^H, H' = image of H in (ZMod n)ˣ.
Specializing `QuotChar.equiv` (characters of a quotient = annihilator):
* `galCharEquiv : (Gal(K/ℚ) →* ℂˣ) ≃* H'^⊥`, through Gal(K/ℚ) ≅ G ⧸ H ≅ (ZMod n)ˣ ⧸ H'
  (`IsGalois.normalAutEquivQuotient`, `QuotientGroup.congr`);
* `perpEquivGal : {χ // χ ∈ perp n L H} ≃ (Gal(K/ℚ) →* ℂˣ)`, from Dirichlet characters mod n
  (`MulChar.equivToUnitHom`), with
  `perpEquivGal_apply`: (perpEquivGal χ)(σ|_K) = χ(a_σ), σ(ζ) = ζ^{a_σ};
* `card_perp`: |H^⊥| = [G : H] = [K : ℚ].
So the Dirichlet characters in `CompositeEuler.LSeries_eq_zeta_mul_prod_primitive` are exactly the
characters of Gal(K/ℚ), each once.
-/

open IsCyclotomicExtension.Rat

namespace CycloCharCorr

variable (n : ℕ) [NeZero n] (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {n} ℚ L]
  [IsGalois ℚ L] (H : Subgroup Gal(L/ℚ)) [H.Normal]

local notation "K" => IntermediateField.fixedField H
local notation "H'" => CycloSubEuler.H' n L H

/-- G ⧸ H ≅ (ZMod n)ˣ ⧸ H'. -/
noncomputable def quotEquiv : Gal(L/ℚ) ⧸ H ≃* (ZMod n)ˣ ⧸ H' :=
  QuotientGroup.congr H (H') (galEquivZMod n L) rfl

/-- Gal(K/ℚ) ≅ (ZMod n)ˣ ⧸ H'. -/
noncomputable def galKEquiv : Gal(K/ℚ) ≃* (ZMod n)ˣ ⧸ H' :=
  (IsGalois.normalAutEquivQuotient H).symm.trans (quotEquiv n L H)

theorem galKEquiv_restrict (σ : Gal(L/ℚ)) :
    galKEquiv n L H (AlgEquiv.restrictNormalHom K σ) = QuotientGroup.mk (galEquivZMod n L σ) := by
  rw [galKEquiv, MulEquiv.trans_apply, ← IsGalois.normalAutEquivQuotient_apply,
    MulEquiv.symm_apply_apply]
  rfl

/-- **Characters of Gal(K/ℚ) ≃* H'^⊥ ⊆ characters of (ZMod n)ˣ.** -/
noncomputable def galCharEquiv : (Gal(K/ℚ) →* ℂˣ) ≃* QuotChar.annihilator (M := ℂˣ) (H') :=
  (MulEquiv.monoidHomCongrLeft (galKEquiv n L H)).trans (QuotChar.equiv (H'))

/-- Dirichlet characters in `perp` ≃ H'^⊥ (unit-valued homomorphisms). -/
noncomputable def perpEquivAnn :
    {χ // χ ∈ CycloSubEuler.perp n L H} ≃ QuotChar.annihilator (M := ℂˣ) (H') :=
  MulChar.equivToUnitHom.subtypeEquiv fun χ => by
    rw [CycloSubEuler.mem_perp_iff, QuotChar.mem_annihilator]
    refine forall₂_congr fun u _ => ?_
    rw [Units.ext_iff, MulChar.coe_equivToUnitHom, Units.val_one]

/-- **H^⊥ (Dirichlet characters mod n trivial on H') ≃ characters of Gal(K/ℚ).** -/
noncomputable def perpEquivGal :
    {χ // χ ∈ CycloSubEuler.perp n L H} ≃ (Gal(K/ℚ) →* ℂˣ) :=
  (perpEquivAnn n L H).trans (galCharEquiv n L H).symm.toEquiv

/-- **The correspondence is the expected one:** (perpEquivGal χ)(σ|_K) = χ(a_σ). -/
theorem perpEquivGal_apply (χ : {χ // χ ∈ CycloSubEuler.perp n L H}) (σ : Gal(L/ℚ)) :
    ((perpEquivGal n L H χ (AlgEquiv.restrictNormalHom K σ) : ℂˣ) : ℂ) =
      χ.1 (galEquivZMod n L σ) := by
  have key : (galCharEquiv n L H).symm (perpEquivAnn n L H χ) (AlgEquiv.restrictNormalHom K σ) =
      (perpEquivAnn n L H χ).1 (galEquivZMod n L σ) := by
    show (QuotChar.equiv (H')).symm (perpEquivAnn n L H χ)
      (galKEquiv n L H (AlgEquiv.restrictNormalHom K σ)) = _
    rw [galKEquiv_restrict, QuotChar.equiv_symm_apply_mk]
  rw [perpEquivGal, Equiv.trans_apply, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, key]
  exact MulChar.coe_equivToUnitHom _ _

/-- **|H^⊥| = [G : H] = [K : ℚ].** -/
theorem card_perp :
    (CycloSubEuler.perp n L H).card = H.index ∧
      (CycloSubEuler.perp n L H).card = Module.finrank ℚ K := by
  have h1 : (CycloSubEuler.perp n L H).card = H.index := by
    rw [← CycloSubEuler.index_H' n L H, ← QuotChar.card_annihilator (H'),
      ← Nat.card_congr (perpEquivAnn n L H), Nat.card_eq_fintype_card, Fintype.card_coe]
  refine ⟨h1, ?_⟩
  have : IsGalois ℚ K := IsGalois.of_fixedField_normal_subgroup H
  rw [h1, Subgroup.index, ← IsGalois.card_aut_eq_finrank]
  exact Nat.card_congr (IsGalois.normalAutEquivQuotient H).toEquiv

end CycloCharCorr

#print axioms CycloCharCorr.galCharEquiv
#print axioms CycloCharCorr.perpEquivGal_apply
#print axioms CycloCharCorr.card_perp
