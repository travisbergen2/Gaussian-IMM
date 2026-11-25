import Mathlib

/-!
# QuotientCharacterEquiv — characters of A ⧸ H are the characters of A trivial on H

A a commutative group, H ≤ A, M a commutative group (later M = ℂˣ). No number fields, no
Dirichlet characters.
* `annihilator H` = H^⊥ = {χ : A →* M | χ(h) = 1 for all h ∈ H}, a subgroup of A →* M;
* `pullback ψ = ψ ∘ (A → A ⧸ H)` lies in H^⊥ (`pullback_mem`);
* `descend χ`: the character gH ↦ χ(g) of A ⧸ H, well defined for χ ∈ H^⊥ (`descend_mk`);
* `pullback_descend`, `descend_pullback`: the two constructions are inverse;
* `equiv : (A ⧸ H →* M) ≃* H^⊥` (a group isomorphism, χ ↦ pointwise products preserved);
* `card_annihilator`: for A finite and M = ℂˣ, |H^⊥| = [A : H].
-/

namespace QuotChar

variable {A M : Type*} [CommGroup A] [CommGroup M] (H : Subgroup A)

/-- H^⊥: characters trivial on H. -/
def annihilator : Subgroup (A →* M) where
  carrier := {χ | ∀ h ∈ H, χ h = 1}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun ha hb h hh => by simp [ha h hh, hb h hh]
  inv_mem' := fun ha h hh => by simp [ha h hh]

theorem mem_annihilator (χ : A →* M) : χ ∈ annihilator H ↔ ∀ h ∈ H, χ h = 1 := Iff.rfl

theorem le_ker_of_mem {χ : A →* M} (hχ : χ ∈ annihilator H) : H ≤ χ.ker := fun h hh =>
  (MonoidHom.mem_ker).mpr (hχ h hh)

/-- **Pullback** along the quotient map, ψ ↦ (g ↦ ψ(gH)), as a group homomorphism. -/
def pullback : (A ⧸ H →* M) →* (A →* M) where
  toFun ψ := ψ.comp (QuotientGroup.mk' H)
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem pullback_apply (ψ : A ⧸ H →* M) (g : A) :
    pullback H ψ g = ψ (QuotientGroup.mk g) := rfl

/-- **The pullback is trivial on H.** -/
theorem pullback_mem (ψ : A ⧸ H →* M) : pullback H ψ ∈ annihilator H := fun h hh => by
  rw [pullback_apply, (QuotientGroup.eq_one_iff h).mpr hh, map_one]

/-- **Descent**: χ ∈ H^⊥ gives the character gH ↦ χ(g) of A ⧸ H. -/
def descend (χ : annihilator (M := M) H) : A ⧸ H →* M :=
  QuotientGroup.lift H χ.1 (le_ker_of_mem H χ.2)

@[simp] theorem descend_mk (χ : annihilator (M := M) H) (g : A) :
    descend H χ (QuotientGroup.mk g) = χ.1 g :=
  QuotientGroup.lift_mk H _ g

/-- **Well-definedness, explicitly:** gH = g'H ⇒ χ(g) = χ(g'). -/
theorem well_defined (χ : annihilator (M := M) H) {g g' : A}
    (h : (QuotientGroup.mk g : A ⧸ H) = QuotientGroup.mk g') : χ.1 g = χ.1 g' := by
  rw [← descend_mk H χ g, h, descend_mk]

theorem pullback_descend (χ : annihilator (M := M) H) : pullback H (descend H χ) = χ.1 :=
  MonoidHom.ext fun g => by simp

theorem descend_pullback (ψ : A ⧸ H →* M) : descend H ⟨pullback H ψ, pullback_mem H ψ⟩ = ψ :=
  MonoidHom.ext fun x => by
    induction x using QuotientGroup.induction_on with
    | H g => simp

/-- **Characters of A ⧸ H ≃* H^⊥.** -/
def equiv : (A ⧸ H →* M) ≃* annihilator (M := M) H where
  toFun ψ := ⟨pullback H ψ, pullback_mem H ψ⟩
  invFun := descend H
  left_inv := descend_pullback H
  right_inv χ := Subtype.ext (pullback_descend H χ)
  map_mul' _ _ := rfl

@[simp] theorem equiv_apply (ψ : A ⧸ H →* M) (g : A) :
    (equiv H ψ).1 g = ψ (QuotientGroup.mk g) := rfl

@[simp] theorem equiv_symm_apply_mk (χ : annihilator (M := M) H) (g : A) :
    (equiv H).symm χ (QuotientGroup.mk g) = χ.1 g :=
  descend_mk H χ g

/-- **|H^⊥| = [A : H]** for finite A, characters valued in ℂˣ. -/
theorem card_annihilator [Finite A] : Nat.card (annihilator (M := ℂˣ) H) = H.index := by
  rw [← Nat.card_congr (equiv (M := ℂˣ) H).toEquiv,
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (A ⧸ H) ℂ, Subgroup.index]

end QuotChar

#print axioms QuotChar.equiv
#print axioms QuotChar.well_defined
#print axioms QuotChar.card_annihilator
