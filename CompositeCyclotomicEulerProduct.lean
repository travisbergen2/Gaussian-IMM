import CompositeLocalFactor
import AbelianEulerProductLevels

/-!
# CompositeCyclotomicEulerProduct — ζ_K = ζ · ∏_{χ ∈ H^⊥, χ ≠ 1} L(χ*) for EVERY n and H

K = ℚ(ζₙ)^H, H^⊥ = Dirichlet characters mod n trivial on the image of H, χ* = primitive
character of χ (level = conductor). No hypothesis on n: at p ∤ n the local identity is
`CycloSubEuler.local_unramified`, at p ∣ n it is `CompositeLocal.local_ramified`, and both are
read through χ*(p). The global assembly uses the varying-level Euler product.
-/

open NumberField Ideal GaloisEuler Finset DirichletCharacter CompositeLocal

namespace CompositeEuler

variable (n : ℕ) [NeZero n] (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {n} ℚ L]
  (H : Subgroup Gal(L/ℚ)) [H.Normal]

local notation "K" => IntermediateField.fixedField H

theorem pv_of_coprime {p : ℕ} (hcop : p.Coprime n) (χ : DirichletCharacter ℂ n) :
    pv χ (p : ℤ) = χ (p : ZMod n) := by
  rw [pv, primitiveCharacter_apply_of_isCoprime, Int.cast_natCast]
  exact Nat.isCoprime_iff_coprime.mpr hcop

theorem pv_one (p : ℕ) [Fact p.Prime] : pv (1 : DirichletCharacter ℂ n) (p : ℤ) = 1 := by
  by_cases hcop : p.Coprime n
  · rw [pv_of_coprime n hcop, MulChar.one_apply ((ZMod.isUnit_iff_coprime p n).mpr hcop)]
  · have hp : p.Prime := Fact.out
    have hdvd : p ∣ n := (Nat.Prime.dvd_iff_not_coprime hp).mpr hcop
    set k := n.factorization p - 1
    set m := n / p ^ n.factorization p
    have hfac : 0 < n.factorization p := hp.factorization_pos_of_dvd (NeZero.ne n) hdvd
    have hn : n = p ^ (k + 1) * m := by
      rw [show k + 1 = n.factorization p by omega, Nat.ordProj_mul_ordCompl_eq_self]
    have hm : ¬ p ∣ m := Nat.not_dvd_ordCompl hp (NeZero.ne n)
    have : NeZero m := ⟨(CycloDecomp.m_pos hn).ne'⟩
    rw [← changeLevel_one (R := ℂ) (CycloDecomp.m_dvd hn), pv_changeLevel hn hm,
      MulChar.one_apply (Units.isUnit _)]

/-- **Local matching at every prime, through primitive characters.** -/
theorem hloc_composite (p : ℕ) (hp : p.Prime) (x : ℂ) :
    (1 - x ^ fK K p) ^ gK K p =
      (1 - x) * ∏ χ : CycloSubEuler.perpNontriv n L H,
        (1 - χ.1.primitiveCharacter (p : ZMod χ.1.conductor) * x) := by
  have : Fact p.Prime := ⟨hp⟩
  have hpv : ∀ χ : DirichletCharacter ℂ n,
      χ.primitiveCharacter (p : ZMod χ.conductor) = pv χ (p : ℤ) := fun χ => by
    rw [pv, Int.cast_natCast]
  simp only [hpv]
  have hsplit := CycloSubEuler.prod_perp_split n L H (fun χ => 1 - pv χ (p : ℤ) * x)
  simp only [pv_one n p, one_mul] at hsplit
  rw [← hsplit]
  by_cases hcop : p.Coprime n
  · rw [CycloSubEuler.local_unramified n L H p hcop]
    exact prod_congr rfl fun χ _ => by rw [pv_of_coprime n hcop]
  · have hdvd : p ∣ n := (Nat.Prime.dvd_iff_not_coprime hp).mpr hcop
    set k := n.factorization p - 1
    set m := n / p ^ n.factorization p
    have hfac : 0 < n.factorization p := hp.factorization_pos_of_dvd (NeZero.ne n) hdvd
    have hn : n = p ^ (k + 1) * m := by
      rw [show k + 1 = n.factorization p by omega, Nat.ordProj_mul_ordCompl_eq_self]
    have hm : ¬ p ∣ m := Nat.not_dvd_ordCompl hp (NeZero.ne n)
    exact local_ramified H hn hm x

/-- **Dedekind factorization of every subfield of every cyclotomic field:**
Σ A_K(m) m⁻ˢ = ζ(s) · ∏_{χ ∈ H^⊥, χ ≠ 1} L(s, χ*) for Re s > 1, χ* the primitive character. -/
theorem LSeries_eq_zeta_mul_prod_primitive {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun m => (IdealCount.A (𝓞 K) m : ℂ)) s =
      riemannZeta s * ∏ χ : CycloSubEuler.perpNontriv n L H,
        LSeries (fun m => χ.1.primitiveCharacter m) s := by
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {n} ℚ L
  exact LSeries_A_eq_zeta_mul_prod_levels
    (fun χ : CycloSubEuler.perpNontriv n L H => χ.1.primitiveCharacter)
    (hloc_composite n L H) hs

end CompositeEuler

#print axioms CompositeEuler.hloc_composite
#print axioms CompositeEuler.LSeries_eq_zeta_mul_prod_primitive
