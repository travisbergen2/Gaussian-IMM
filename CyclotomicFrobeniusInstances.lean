import CyclotomicFrobenius
import Cyclo5Galois
import Cyclo7Galois

/-!
# CyclotomicFrobeniusInstances — closing the Frobenius gap for ℚ(ζ₅) and ℚ(ζ₇)

The automorphisms σ_p used in `Cyclo5Galois` / `Cyclo7Galois` are definitionally the generic
`CycloFrob.sigmaP`, hence arithmetic Frobenius elements in Mathlib's sense. Consequently, for every
prime P above p ∤ n and every Dirichlet character ψ, the corresponding Galois character takes the
value ψ(p) at a Frobenius element at P, and that element generates the decomposition group of P.
-/

open NumberField Ideal MulAction
open scoped Pointwise

namespace Cyclo5

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K]
  (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K)) [P.IsMaximal]
  [P.LiesOver (Ideal.span {(p : ℤ)})] (hp : p.Coprime 5)

theorem sigma_eq_sigmaP : sigma K p hp = CycloFrob.sigmaP 5 K p hp := rfl

/-- **σ_p is the arithmetic Frobenius at P** (ℚ(ζ₅)). -/
theorem sigma_isArithFrobAt : IsArithFrobAt ℤ (sigma K p hp) P :=
  CycloFrob.sigmaP_isArithFrobAt p P hp

/-- **ψ(p) = Galois character of ψ at the Frobenius at P**, which generates the decomposition group. -/
theorem galChar_frobenius (ψ : DirichletCharacter ℂ 5) :
    IsArithFrobAt ℤ (sigma K p hp) P ∧
      stabilizer Gal(K/ℚ) P = Subgroup.zpowers (sigma K p hp) ∧
      (galCharEquiv K ψ (sigma K p hp) : ℂ) = ψ p :=
  ⟨sigma_isArithFrobAt p P hp, CycloFrob.stabilizer_eq_zpowers p P hp, galChar_sigma_p K ψ p hp⟩

end Cyclo5

namespace Cyclo7

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {7} ℚ K]
  (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K)) [P.IsMaximal]
  [P.LiesOver (Ideal.span {(p : ℤ)})] (hp : p.Coprime 7)

theorem sigma_eq_sigmaP : sigma K p hp = CycloFrob.sigmaP 7 K p hp := rfl

/-- **σ_p is the arithmetic Frobenius at P** (ℚ(ζ₇)). -/
theorem sigma_isArithFrobAt : IsArithFrobAt ℤ (sigma K p hp) P :=
  CycloFrob.sigmaP_isArithFrobAt p P hp

theorem galChar_frobenius (ψ : DirichletCharacter ℂ 7) :
    IsArithFrobAt ℤ (sigma K p hp) P ∧
      stabilizer Gal(K/ℚ) P = Subgroup.zpowers (sigma K p hp) ∧
      (galCharEquiv K ψ (sigma K p hp) : ℂ) = ψ p :=
  ⟨sigma_isArithFrobAt p P hp, CycloFrob.stabilizer_eq_zpowers p P hp, galChar_sigma_p K ψ p hp⟩

end Cyclo7

#print axioms Cyclo5.galChar_frobenius
#print axioms Cyclo7.galChar_frobenius
