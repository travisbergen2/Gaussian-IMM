import QuadraticFieldDiscriminant
import QuadraticCharacterIdentification

/-!
# QuadraticKroneckerCharacter — ζ_K = ζ · L(χ*) with χ*(q) = (D_K/q)

K a quadratic number field, D_K = `NumberField.discr K`.
* `discr_isFundamental`: D_K is a fundamental discriminant, 𝓞_K ≅ `QuadraticAlgebra ℤ (D_K/4)
  (D_K mod 4)` and √D_K ∈ K ∖ ℚ (from `QuadDiscr.structure_thm`);
* `zeta_eq_discr_character`: for Re s > 1, ζ_K(s) = ζ(s) L(s, χ*) where χ is a nontrivial
  quadratic Dirichlet character mod some N and χ*(q) = (D_K/q) for every prime q ∤ N, q ≠ 2,
  q ∤ D_K (apply `QuadCharId.quadratic_zeta_legendre` with d = D_K, γ = √D_K).
Not proved here: conductor(χ) = |D_K|, nor χ* equal to the Kronecker symbol at the finitely many
excluded primes.
-/

open NumberField

namespace QuadKronecker

variable {K : Type*} [Field K] [NumberField K]

theorem discr_isFundamental (hK : Module.finrank ℚ K = 2) :
    Int.IsFundamentalDiscr (discr K) ∧
      Nonempty (QuadraticAlgebra ℤ (discr K / 4) (discr K % 4) ≃+* 𝓞 K) ∧
      ∃ s : K, s ^ 2 = discr K ∧ s ∉ Set.range (algebraMap ℚ K) := by
  obtain ⟨d, γ, hγ, hγQ⟩ := QuadCharId.exists_sqrt hK
  obtain ⟨D, hD, -, hO, hdisc, hs⟩ := QuadDiscr.structure_thm hK hγ hγQ
  rw [hdisc]
  exact ⟨hD, hO, hs⟩

/-- **ζ_K = ζ · L(χ*) with χ*(q) = (D_K/q).** -/
theorem zeta_eq_discr_character (hK : Module.finrank ℚ K = 2) :
    ∃ N : ℕ, ∃ _ : NeZero N, ∃ χ : DirichletCharacter ℂ N, χ ≠ 1 ∧ χ ^ 2 = 1 ∧
      (∀ s : ℂ, 1 < s.re →
        LSeries (fun m => (IdealCount.A (𝓞 K) m : ℂ)) s =
          riemannZeta s * LSeries (fun m => χ.primitiveCharacter m) s) ∧
      ∀ (q : ℕ) [Fact q.Prime], q.Coprime N → q ≠ 2 → ¬ (q : ℤ) ∣ discr K →
        CompositeLocal.pv χ (q : ℤ) = legendreSym q (discr K) := by
  obtain ⟨N, hN, χ, hne, hsq, hz, hleg⟩ := QuadCharId.quadratic_zeta_legendre hK
  obtain ⟨-, -, s, hs, hsQ⟩ := discr_isFundamental hK
  exact ⟨N, hN, χ, hne, hsq, hz, fun q _ hqN hq2 hqD => hleg (discr K) s hs hsQ q hqN hq2 hqD⟩

end QuadKronecker

#print axioms QuadKronecker.discr_isFundamental
#print axioms QuadKronecker.zeta_eq_discr_character
