import CyclotomicFrobenius
import SubfieldResidueDegree
import SubfieldRamified
import QuotientOrder

/-!
# CyclotomicSubfieldSplitting — splitting of p ∤ n in any subfield K = L^H of L = ℚ(ζₙ)

* `galois_comm`, `normal`: Gal(ℚ(ζₙ)/ℚ) is commutative, so every H is normal (K/ℚ Galois).
* `fK_eq_orderOf`: f_K(p) = order of the Frobenius coset σ_p H in G/H.
* `gK_mul_fK`: e_K(p) = 1 and g_K(p) · f_K(p) = [G : H].
Combines `CycloFrob` (D = ⟨σ_p⟩), `SubfieldDeg` (f_K · #(D ⊓ H) = #D) and `QuotientOrder`.
-/

open NumberField Ideal MulAction IsCyclotomicExtension.Rat

namespace CycloSub

theorem galois_comm (n : ℕ) [NeZero n] {L : Type*} [Field L] [CharZero L]
    [IsCyclotomicExtension {n} ℚ L] (a b : Gal(L/ℚ)) : a * b = b * a :=
  (IsCyclotomicExtension.autEquivPow L (Polynomial.cyclotomic.irreducible_rat (NeZero.pos n))).injective
    (by rw [map_mul, map_mul, mul_comm])

theorem normal (n : ℕ) [NeZero n] {L : Type*} [Field L] [CharZero L]
    [IsCyclotomicExtension {n} ℚ L] (H : Subgroup Gal(L/ℚ)) : H.Normal :=
  ⟨fun a ha g => by rw [galois_comm n g a, mul_inv_cancel_right]; exact ha⟩

theorem finrank_K {L : Type*} [Field L] [CharZero L] [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (H : Subgroup Gal(L/ℚ)) : Module.finrank ℚ (IntermediateField.fixedField H) = H.index := by
  have h1 := Module.finrank_mul_finrank ℚ (IntermediateField.fixedField H) L
  rw [IntermediateField.finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank ℚ L,
    ← H.card_mul_index] at h1
  exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := H)) (by rw [h1, mul_comm])

theorem not_dvd {n p : ℕ} (hp : p.Prime) (hn : p.Coprime n) : ¬ p ∣ n :=
  fun h => hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hn h)

theorem span_isMaximal {p : ℕ} (hp : p.Prime) : (span {(p : ℤ)}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible

variable (n : ℕ) [NeZero n] (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {n} ℚ L]
  (H : Subgroup Gal(L/ℚ)) [H.Normal] (p : ℕ) [hp : Fact (Nat.Prime p)] (hn : p.Coprime n)

local notation "K" => IntermediateField.fixedField H

/-- **f_K(p) = order of σ_p H in G/H.** -/
theorem fK_eq_orderOf :
    (span {(p : ℤ)}).inertiaDegIn (𝓞 K) =
      orderOf (QuotientGroup.mk (CycloFrob.sigmaP n L p hn) : Gal(L/ℚ) ⧸ H) := by
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {n} ℚ L
  have := span_isMaximal hp.out
  obtain ⟨⟨P, _, _⟩⟩ := (span {(p : ℤ)}).nonempty_primesOver (S := 𝓞 L)
  have : P.IsMaximal := IsMaximal.of_liesOver_isMaximal P (span {(p : ℤ)})
  have hram : (span {(p : ℤ)}).ramificationIdxIn (𝓞 L) = 1 :=
    ramificationIdxIn_eq_of_not_dvd p L (not_dvd hp.out hn)
  have h1 := SubfieldDeg.inertiaDegIn_mul_card_inf H p P hram
  have h2 := QuotientOrder.orderOf_mk_mul_card_inf H (CycloFrob.sigmaP n L p hn)
  rw [CycloFrob.stabilizer_eq_zpowers p P hn, Nat.card_zpowers] at h1
  have hpos : 0 < Nat.card (Subgroup.zpowers (CycloFrob.sigmaP n L p hn) ⊓ H : Subgroup _) :=
    Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

include n hn in
/-- **e_K(p) = 1 and g_K(p) · f_K(p) = [G : H].** -/
theorem gK_mul_fK :
    (span {(p : ℤ)}).ramificationIdxIn (𝓞 K) = 1 ∧
      ((span {(p : ℤ)}).primesOver (𝓞 K)).ncard * (span {(p : ℤ)}).inertiaDegIn (𝓞 K) = H.index := by
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {n} ℚ L
  have := span_isMaximal hp.out
  obtain ⟨⟨P, _, _⟩⟩ := (span {(p : ℤ)}).nonempty_primesOver (S := 𝓞 L)
  have : P.IsMaximal := IsMaximal.of_liesOver_isMaximal P (span {(p : ℤ)})
  set Q : Ideal (𝓞 K) := P.under (𝓞 K)
  have : Q.IsMaximal := IsMaximal.under (𝓞 K) P
  have : Q.LiesOver (span {(p : ℤ)}) := LiesOver.tower_bot P Q (span {(p : ℤ)})
  have : Nonempty (Q.primesOver (𝓞 L)) := ⟨⟨P, inferInstance, inferInstance⟩⟩
  have he := ramificationIdxIn_mul_ramificationIdxIn (p := span {(p : ℤ)}) (P := Q) (C := 𝓞 L)
    (G := Gal(K/ℚ)) (GAC := Gal(L/ℚ)) (GBC := Gal(L/K))
  rw [ramificationIdxIn_eq_of_not_dvd p L (not_dvd hp.out hn)] at he
  have heK := Nat.eq_one_of_mul_eq_one_right he
  refine ⟨heK, ?_⟩
  have hfun := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (span {(p : ℤ)}) (𝓞 K) Gal(K/ℚ)
  rw [heK, one_mul, IsGaloisGroup.card_eq_finrank Gal(K/ℚ) ℚ K, finrank_K] at hfun
  exact hfun

end CycloSub

#print axioms CycloSub.fK_eq_orderOf
#print axioms CycloSub.gK_mul_fK
