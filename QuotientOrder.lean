import Mathlib

/-!
# QuotientOrder — order of a coset in G/H

Pure group theory, no number fields. For a finite group G, a normal subgroup H and g ∈ G:

    orderOf (gH) · #(⟨g⟩ ∩ H) = orderOf g.

Used to compute residue degrees in fixed fields: the Frobenius coset σ_p H has order
|D| / |D ∩ H| where D = ⟨σ_p⟩ is the decomposition group.
-/

namespace QuotientOrder

variable {G : Type*} [Group G] (H : Subgroup G) [H.Normal] (g : G)

/-- **orderOf (gH) · #(⟨g⟩ ⊓ H) = orderOf g.** -/
theorem orderOf_mk_mul_card_inf :
    orderOf (QuotientGroup.mk g : G ⧸ H) * Nat.card (Subgroup.zpowers g ⊓ H : Subgroup G) =
      orderOf g := by
  set Z := Subgroup.zpowers g
  let φ : Z →* G ⧸ H := (QuotientGroup.mk' H).comp Z.subtype
  have hrange : φ.range = Subgroup.zpowers (QuotientGroup.mk g : G ⧸ H) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, MonoidHom.map_zpowers]; rfl
  have hker : φ.ker = H.subgroupOf Z := by
    ext x
    simp [φ, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
  have hcard : Nat.card Z = Nat.card φ.ker * Nat.card φ.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, mul_comm]
  have hinf : Nat.card (H.subgroupOf Z) = Nat.card (Z ⊓ H : Subgroup G) := by
    rw [← Subgroup.inf_subgroupOf_left H Z]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← Nat.card_zpowers, ← Nat.card_zpowers, hcard, hker, hrange, hinf, mul_comm]

end QuotientOrder

#print axioms QuotientOrder.orderOf_mk_mul_card_inf
