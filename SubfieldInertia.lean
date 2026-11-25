import SubfieldResidueDegree

/-!
# SubfieldInertia — e, f, g of any prime in a fixed field K = L^H (ramified primes allowed)

Generic: L/ℚ Galois, H ⊴ Gal(L/ℚ), K = L^H, p prime, P a prime of 𝓞 L above p,
D = decomposition group (stabilizer of P), I = inertia group of P. Then

* `card_inertia_rel`: the inertia group of P in L/K is I ⊓ H (via Gal(L/K) ≅ H);
* `eK_mul_card`: e_K(p) · #(I ⊓ H) = #I;
* `fK_mul_card`: f_K(p) · #(D ⊓ H) · #I = #D · #(I ⊓ H);
* `gK_eK_fK`: g_K(p) · e_K(p) · f_K(p) = [K : ℚ].

From |I| = e and |D| = e·f (Mathlib, for both L/ℚ and L/K) and the tower laws for e and f.
This extends `SubfieldDeg.inertiaDegIn_mul_card_inf` (the case I = 1) to ramified primes.
No cyclotomic input.
-/

open NumberField Ideal MulAction
open scoped Pointwise

namespace SubfieldDeg

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L] (H : Subgroup Gal(L/ℚ)) [H.Normal]

local notation "K" => IntermediateField.fixedField H

/-- The inertia group of P in L/K is I ⊓ H. -/
theorem card_inertia_rel (P : Ideal (𝓞 L)) :
    Nat.card (P.inertia Gal(L/K)) = Nat.card (P.inertia Gal(L/ℚ) ⊓ H : Subgroup Gal(L/ℚ)) := by
  refine Nat.card_congr ?_
  refine ((galEquivH H).symm.toEquiv.subtypeEquiv (p := fun σ => σ ∈ P.inertia Gal(L/K))
    (q := fun τ : H => (τ : Gal(L/ℚ)) ∈ P.inertia Gal(L/ℚ)) fun σ => ?_).trans ?_
  · simp only [Ideal.mem_inertia, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
    conv_lhs => rw [← MulEquiv.apply_symm_apply (galEquivH H) σ]
    rfl
  · exact (Equiv.subtypeSubtypeEquivSubtypeInter (fun g => g ∈ H)
      (fun g => g ∈ P.inertia Gal(L/ℚ))).trans
      (Equiv.subtypeEquivRight fun g => by simp [and_comm])

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (P : Ideal (𝓞 L)) [P.IsMaximal]
  [P.LiesOver (span {(p : ℤ)})]

/-- Shared setup: the prime Q of K below P and the tower identities. -/
theorem tower_data :
    let Q : Ideal (𝓞 K) := P.under (𝓞 K)
    (span {(p : ℤ)}).ramificationIdxIn (𝓞 K) * Q.ramificationIdxIn (𝓞 L) =
        (span {(p : ℤ)}).ramificationIdxIn (𝓞 L) ∧
      (span {(p : ℤ)}).inertiaDegIn (𝓞 K) * Q.inertiaDegIn (𝓞 L) =
        (span {(p : ℤ)}).inertiaDegIn (𝓞 L) ∧
      Nat.card (P.inertia Gal(L/K)) = Q.ramificationIdxIn (𝓞 L) ∧
      Nat.card (stabilizer Gal(L/K) P) = Q.ramificationIdxIn (𝓞 L) * Q.inertiaDegIn (𝓞 L) := by
  intro Q
  have : Q.IsMaximal := IsMaximal.under (𝓞 K) P
  have : Q.LiesOver (span {(p : ℤ)}) := LiesOver.tower_bot P Q (span {(p : ℤ)})
  have : Nonempty (Q.primesOver (𝓞 L)) := ⟨⟨P, inferInstance, inferInstance⟩⟩
  have hspan : (span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp.out).irreducible
  exact ⟨ramificationIdxIn_mul_ramificationIdxIn (p := span {(p : ℤ)}) (P := Q) (C := 𝓞 L)
      (G := Gal(K/ℚ)) (GAC := Gal(L/ℚ)) (GBC := Gal(L/K)),
    inertiaDegIn_mul_inertiaDegIn (p := span {(p : ℤ)}) (P := Q) (C := 𝓞 L)
      (G := Gal(K/ℚ)) (GAC := Gal(L/ℚ)) (GBC := Gal(L/K)),
    card_inertia_eq_ramificationIdxIn (G := Gal(L/K)) Q P,
    card_stabilizer_eq (G := Gal(L/K)) Q P⟩

/-- **Ramification index in the fixed field:** e_K(p) · #(I ⊓ H) = #I. -/
theorem eK_mul_card :
    (span {(p : ℤ)}).ramificationIdxIn (𝓞 K) *
        Nat.card (P.inertia Gal(L/ℚ) ⊓ H : Subgroup Gal(L/ℚ)) =
      Nat.card (P.inertia Gal(L/ℚ)) := by
  obtain ⟨he, -, hI, -⟩ := tower_data H p P
  have hspan : (span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp.out).irreducible
  rw [← card_inertia_rel, hI, he, card_inertia_eq_ramificationIdxIn (G := Gal(L/ℚ))
    (span {(p : ℤ)}) P]

/-- **Residue degree in the fixed field:** f_K(p) · #(D ⊓ H) · #I = #D · #(I ⊓ H). -/
theorem fK_mul_card :
    (span {(p : ℤ)}).inertiaDegIn (𝓞 K) *
        Nat.card (stabilizer Gal(L/ℚ) P ⊓ H : Subgroup Gal(L/ℚ)) *
        Nat.card (P.inertia Gal(L/ℚ)) =
      Nat.card (stabilizer Gal(L/ℚ) P) *
        Nat.card (P.inertia Gal(L/ℚ) ⊓ H : Subgroup Gal(L/ℚ)) := by
  obtain ⟨he, hf, hI, hD⟩ := tower_data H p P
  have hspan : (span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp.out).irreducible
  rw [← card_stabilizer_rel, ← card_inertia_rel, hD, hI,
    card_inertia_eq_ramificationIdxIn (G := Gal(L/ℚ)) (span {(p : ℤ)}) P,
    card_stabilizer_eq (G := Gal(L/ℚ)) (span {(p : ℤ)}) P, ← he, ← hf]
  ring

omit [P.IsMaximal] [P.LiesOver (span {(p : ℤ)})] in
/-- **Fundamental identity in K:** g_K(p) · e_K(p) · f_K(p) = [G : H] = [K : ℚ]. -/
theorem gK_eK_fK :
    ((span {(p : ℤ)}).primesOver (𝓞 K)).ncard *
        ((span {(p : ℤ)}).ramificationIdxIn (𝓞 K) * (span {(p : ℤ)}).inertiaDegIn (𝓞 K)) =
      H.index := by
  have hspan : (span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp.out).irreducible
  rw [ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn _ (𝓞 K) Gal(K/ℚ),
    IsGaloisGroup.card_eq_finrank Gal(K/ℚ) ℚ K]
  have h1 := Module.finrank_mul_finrank ℚ K L
  rw [IntermediateField.finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank ℚ L,
    ← H.card_mul_index] at h1
  exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := H)) (by rw [h1, mul_comm])

end SubfieldDeg

#print axioms SubfieldDeg.eK_mul_card
#print axioms SubfieldDeg.fK_mul_card
#print axioms SubfieldDeg.gK_eK_fK
