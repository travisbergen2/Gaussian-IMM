import Mathlib

/-!
# SubfieldRamified — a prime with one prime and residue degree 1 above it in L keeps both in K

Generic: L/ℚ Galois, H ⊴ Gal(L/ℚ), K = L^H. If p has a single prime above it in L, of residue
degree 1 (e.g. p totally ramified in L), then the same holds in K: g_K(p) = 1, f_K(p) = 1.
Tower laws only. No project imports.
-/

open NumberField Ideal

namespace SubfieldDeg

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L] (H : Subgroup Gal(L/ℚ)) [H.Normal]

local notation "K" => IntermediateField.fixedField H

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

theorem ramified_descends
    (hg : ((span {(p : ℤ)}).primesOver (𝓞 L)).ncard = 1)
    (hf : (span {(p : ℤ)}).inertiaDegIn (𝓞 L) = 1) :
    ((span {(p : ℤ)}).primesOver (𝓞 K)).ncard = 1 ∧ (span {(p : ℤ)}).inertiaDegIn (𝓞 K) = 1 := by
  have hspan : (span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp.out).irreducible
  obtain ⟨⟨P, _, _⟩⟩ := (span {(p : ℤ)}).nonempty_primesOver (S := 𝓞 L)
  have : P.IsMaximal := IsMaximal.of_liesOver_isMaximal P (span {(p : ℤ)})
  set Q : Ideal (𝓞 K) := P.under (𝓞 K)
  have : Q.IsMaximal := IsMaximal.under (𝓞 K) P
  have : Q.LiesOver (span {(p : ℤ)}) := LiesOver.tower_bot P Q (span {(p : ℤ)})
  have : Nonempty (Q.primesOver (𝓞 L)) := ⟨⟨P, inferInstance, inferInstance⟩⟩
  have htf := inertiaDegIn_mul_inertiaDegIn (p := span {(p : ℤ)}) (P := Q) (C := 𝓞 L)
    (G := Gal(K/ℚ)) (GAC := Gal(L/ℚ)) (GBC := Gal(L/K))
  have htg := ncard_primesOver_mul_ncard_primesOver (p := span {(p : ℤ)}) (P := Q) (C := 𝓞 L)
    (G := Gal(K/ℚ)) (GAC := Gal(L/ℚ))
  rw [hf] at htf
  rw [hg] at htg
  exact ⟨Nat.eq_one_of_mul_eq_one_right htg, Nat.eq_one_of_mul_eq_one_right htf⟩

end SubfieldDeg

#print axioms SubfieldDeg.ramified_descends
