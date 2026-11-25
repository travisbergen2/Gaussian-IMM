import CharacterProduct

/-!
# CharacterDescent — characters through a reduction map, and level-free character products

Generic (no number fields):
* `card_eq_card_inf_ker_mul_card_map`: for r : A →* B and S ≤ A, #S = #(S ⊓ ker r) · #(r(S)).
* `perpN N S`: Dirichlet characters of level N trivial on S ≤ (ZMod N)ˣ;
  `prod_perpN`: ∏_{χ ∈ perpN N S} (1 − χ(u) x) = (1 − x^f)^{[(ZMod N)ˣ : S]/f}, f = order of uS.
* `descend`: χ of level n factors through m ∣ n iff χ = changeLevel ψ for a ψ of level m;
  ψ is trivial on r(S) iff changeLevel ψ is trivial on S (r = reduction).
-/

open Finset DirichletCharacter

namespace CharDescent

/-- #S = #(S ⊓ ker r) · #r(S). -/
theorem card_eq_card_inf_ker_mul_card_map {A B : Type*} [Group A] [Group B] (r : A →* B)
    (S : Subgroup A) :
    Nat.card S = Nat.card (S ⊓ r.ker : Subgroup A) * Nat.card (S.map r) := by
  let r' : S →* B := r.comp S.subtype
  have hrange : r'.range = S.map r := by rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card r'.ker = Nat.card (S ⊓ r.ker : Subgroup A) := by
    have : r'.ker = (r.ker).subgroupOf S := by ext x; simp [r', Subgroup.mem_subgroupOf]
    rw [this, ← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup r'.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange r').toEquiv, hrange, hker, mul_comm]

variable (N : ℕ) [NeZero N]

noncomputable instance : Fintype (DirichletCharacter ℂ N) := Fintype.ofFinite _

open Classical in
/-- Dirichlet characters of level N trivial on S. -/
noncomputable def perpN (S : Subgroup (ZMod N)ˣ) : Finset (DirichletCharacter ℂ N) :=
  univ.filter fun χ => ∀ u ∈ S, χ u = 1

theorem mem_perpN (S : Subgroup (ZMod N)ˣ) (χ : DirichletCharacter ℂ N) :
    χ ∈ perpN N S ↔ ∀ u ∈ S, χ u = 1 := by
  classical
  simp [perpN]

/-- **Level-free character product.** -/
theorem prod_perpN (S : Subgroup (ZMod N)ˣ) (u : (ZMod N)ˣ) (x : ℂ) :
    ∏ χ ∈ perpN N S, (1 - χ u * x) =
      (1 - x ^ orderOf (QuotientGroup.mk u : (ZMod N)ˣ ⧸ S)) ^
        (S.index / orderOf (QuotientGroup.mk u : (ZMod N)ˣ ⧸ S)) := by
  classical
  have := CharProd.finite_dual (A := (ZMod N)ˣ)
  have : Fintype {φ : (ZMod N)ˣ →* ℂˣ // ∀ h ∈ S, φ h = 1} := Fintype.ofFinite _
  let e : {χ : DirichletCharacter ℂ N // ∀ v ∈ S, χ v = 1} ≃
      {φ : (ZMod N)ˣ →* ℂˣ // ∀ h ∈ S, φ h = 1} :=
    MulChar.equivToUnitHom.subtypeEquiv fun χ => by
      refine forall₂_congr fun v _ => ?_
      rw [Units.ext_iff, MulChar.coe_equivToUnitHom, Units.val_one]
  rw [prod_subtype (perpN N S) (mem_perpN N S),
    Fintype.prod_equiv e _ (fun φ => 1 - ((φ.1 u : ℂˣ) : ℂ) * x) (fun χ => by
      simp [e, MulChar.coe_equivToUnitHom]),
    CharProd.prod_one_sub_perp]

end CharDescent

#print axioms CharDescent.card_eq_card_inf_ker_mul_card_map
#print axioms CharDescent.prod_perpN
