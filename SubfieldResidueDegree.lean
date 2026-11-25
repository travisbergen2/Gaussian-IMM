import Mathlib

/-!
# SubfieldResidueDegree — residue degree in a fixed field of a Galois number field

Generic: L/ℚ Galois, H ⊴ Gal(L/ℚ), K = L^H, p a prime unramified in L, P a prime of 𝓞 L above p,
D = stabilizer of P (decomposition group). Then

    f_K(p) · #(D ⊓ H) = #D.

Route: tower laws for f and e (K/ℚ, L/K, L/ℚ), |stabilizer| = e·f for L/K (group Gal(L/K)) and
for L/ℚ, and Gal(L/K) ≅ H compatibly with the action on ideals of 𝓞 L.
No cyclotomic input, no project imports.
-/

open NumberField Ideal MulAction
open scoped Pointwise

namespace SubfieldDeg

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L] (H : Subgroup Gal(L/ℚ)) [H.Normal]

local notation "K" => IntermediateField.fixedField H

/-- Gal(L/K) ≅ H for K = L^H. -/
noncomputable def galEquivH : H ≃* Gal(L/K) :=
  (MulEquiv.subgroupCongr (IntermediateField.fixingSubgroup_fixedField H).symm).trans
    (IntermediateField.fixingSubgroupEquiv K)

theorem galEquivH_apply (τ : H) (x : L) : galEquivH H τ x = (τ : Gal(L/ℚ)) x := rfl

theorem smul_ideal (τ : H) (P : Ideal (𝓞 L)) :
    (galEquivH H τ) • P = (τ : Gal(L/ℚ)) • P := rfl

/-- The decomposition group of P in L/K is D ⊓ H. -/
theorem card_stabilizer_rel (P : Ideal (𝓞 L)) :
    Nat.card (stabilizer Gal(L/K) P) = Nat.card (stabilizer Gal(L/ℚ) P ⊓ H : Subgroup Gal(L/ℚ)) := by
  refine Nat.card_congr ?_
  refine ((galEquivH H).symm.toEquiv.subtypeEquiv (p := fun σ => σ ∈ stabilizer Gal(L/K) P)
    (q := fun τ : H => (τ : Gal(L/ℚ)) ∈ stabilizer Gal(L/ℚ) P) fun σ => ?_).trans ?_
  · simp only [mem_stabilizer_iff, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
    rw [← smul_ideal, MulEquiv.apply_symm_apply]
  · exact (Equiv.subtypeSubtypeEquivSubtypeInter (fun g => g ∈ H)
      (fun g => g ∈ stabilizer Gal(L/ℚ) P)).trans
      (Equiv.subtypeEquivRight fun g => by simp [and_comm])

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (P : Ideal (𝓞 L)) [P.IsMaximal]
  [P.LiesOver (span {(p : ℤ)})]

/-- **Residue degree in the fixed field** (p unramified in L): f_K(p) · #(D ⊓ H) = #D. -/
theorem inertiaDegIn_mul_card_inf
    (hram : (span {(p : ℤ)}).ramificationIdxIn (𝓞 L) = 1) :
    (span {(p : ℤ)}).inertiaDegIn (𝓞 K) * Nat.card (stabilizer Gal(L/ℚ) P ⊓ H : Subgroup Gal(L/ℚ)) =
      Nat.card (stabilizer Gal(L/ℚ) P) := by
  set Q : Ideal (𝓞 K) := P.under (𝓞 K)
  have : Q.IsMaximal := IsMaximal.under (𝓞 K) P
  have : Q.LiesOver (span {(p : ℤ)}) := LiesOver.tower_bot P Q (span {(p : ℤ)})
  have : Nonempty (Q.primesOver (𝓞 L)) := ⟨⟨P, inferInstance, inferInstance⟩⟩
  have hspan : (span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp.out).irreducible
  have hf := inertiaDegIn_mul_inertiaDegIn (p := span {(p : ℤ)}) (P := Q) (C := 𝓞 L)
    (G := Gal(K/ℚ)) (GAC := Gal(L/ℚ)) (GBC := Gal(L/K))
  have he := ramificationIdxIn_mul_ramificationIdxIn (p := span {(p : ℤ)}) (P := Q) (C := 𝓞 L)
    (G := Gal(K/ℚ)) (GAC := Gal(L/ℚ)) (GBC := Gal(L/K))
  rw [hram] at he
  have heQ : Q.ramificationIdxIn (𝓞 L) = 1 := Nat.eq_one_of_mul_eq_one_left he
  have hDK := card_stabilizer_eq (G := Gal(L/K)) Q P
  have hDL := card_stabilizer_eq (G := Gal(L/ℚ)) (span {(p : ℤ)}) P
  rw [heQ, one_mul] at hDK
  rw [hram, one_mul] at hDL
  rw [← card_stabilizer_rel, hDK, hf, hDL]

end SubfieldDeg

#print axioms SubfieldDeg.inertiaDegIn_mul_card_inf
