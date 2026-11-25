import KroneckerPrimitive
import QuadraticKroneckerCharacter

/-!
# QuadraticKroneckerIdentification — ζ_K = ζ · L(χ_{D_K}) for every quadratic field

* `primitive_eq_of_changeLevel` (generic): two primitive characters that agree after lifting to a
  common level M have the same level and agree everywhere (conductors are preserved by
  `changeLevel`; `changeLevel` is injective).
* `chi_eq_kronecker`: for a quadratic field K with D = D_K, the character χ of
  `QuadKronecker.zeta_eq_discr_character` has conductor |D| and χ*(a) = χ_D(a) for all a ∈ ℤ.
  Proof: lift χ* and χ_D to M = N·|D|; each unit class mod M contains a prime q > 2N|D|
  (Dirichlet's theorem, `Nat.forall_exists_prime_gt_and_eq_mod`), where both equal (D/q).
* `dedekindZeta_quadratic`: Σ A_K(m) m⁻ˢ = ζ(s) · L(s, χ_{D_K}) for Re s > 1.
-/

open NumberField DirichletCharacter

namespace QuadKronId

/-- Primitive characters agreeing at a common level are equal (with equal levels). -/
theorem primitive_eq_of_changeLevel {m₁ m₂ M : ℕ} [NeZero M] (ψ₁ : DirichletCharacter ℂ m₁)
    (ψ₂ : DirichletCharacter ℂ m₂) (h₁ : m₁ ∣ M) (h₂ : m₂ ∣ M) (hp₁ : ψ₁.IsPrimitive)
    (hp₂ : ψ₂.IsPrimitive) (heq : changeLevel h₁ ψ₁ = changeLevel h₂ ψ₂) :
    m₁ = m₂ ∧ ∀ a : ℤ, ψ₁ (a : ZMod m₁) = ψ₂ (a : ZMod m₂) := by
  have hm : m₁ = m₂ := by
    have := congrArg conductor heq
    rw [conductor_changeLevel, conductor_changeLevel] at this
    rw [← hp₁, ← hp₂]; exact this
  subst hm
  refine ⟨rfl, fun a => ?_⟩
  rw [changeLevel_injective h₁ heq]

variable {K : Type*} [Field K] [NumberField K]

/-- **χ* = χ_{D_K}** (as functions on ℤ), and conductor χ = |D_K|. -/
theorem chi_eq_kronecker (hK : Module.finrank ℚ K = 2) :
    ∃ N : ℕ, ∃ _ : NeZero N, ∃ χ : DirichletCharacter ℂ N, χ ≠ 1 ∧ χ ^ 2 = 1 ∧
      (∀ s : ℂ, 1 < s.re →
        LSeries (fun m => (IdealCount.A (𝓞 K) m : ℂ)) s =
          riemannZeta s * LSeries (fun m => χ.primitiveCharacter m) s) ∧
      conductor χ = (discr K).natAbs ∧
      ∀ a : ℤ, χ.primitiveCharacter (a : ZMod (conductor χ)) =
        Kronecker.kronecker (discr K) (QuadKronecker.discr_isFundamental hK).1.ne_zero
          (a : ZMod (discr K).natAbs) := by
  have hD := (QuadKronecker.discr_isFundamental hK).1
  obtain ⟨N, hN, χ, hne, hsq, hz, hleg⟩ := QuadKronecker.zeta_eq_discr_character hK
  set D := discr K
  set n := D.natAbs
  have hn0 : n ≠ 0 := Int.natAbs_ne_zero.mpr hD.ne_zero
  have hN0 : N ≠ 0 := NeZero.ne N
  have : NeZero (N * n) := ⟨mul_ne_zero hN0 hn0⟩
  have h₁ : conductor χ ∣ N * n := (conductor_dvd_level χ).trans (dvd_mul_right N n)
  have h₂ : n ∣ N * n := dvd_mul_left n N
  have heq : changeLevel h₁ χ.primitiveCharacter =
      changeLevel h₂ (Kronecker.kronecker D hD.ne_zero) := by
    apply MulChar.ext
    intro u
    obtain ⟨q, hqb, hq, hqu⟩ :=
      Nat.forall_exists_prime_gt_and_eq_mod (Units.isUnit u) (2 * (N * n))
    have : Fact q.Prime := ⟨hq⟩
    have hqM : q.Coprime (N * n) :=
      (Nat.Prime.coprime_iff_not_dvd hq).mpr fun h =>
        absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne _)) h) (by omega)
    have hqN : q.Coprime N := Nat.Coprime.coprime_dvd_right (dvd_mul_right N n) hqM
    have hqn : q.Coprime n := Nat.Coprime.coprime_dvd_right (dvd_mul_left n N) hqM
    have hq2 : q ≠ 2 := by
      have : 1 ≤ N * n := Nat.pos_of_ne_zero (NeZero.ne _)
      omega
    have hqD : ¬ (q : ℤ) ∣ D := fun h =>
      (Nat.Prime.coprime_iff_not_dvd hq).mp hqn (Int.ofNat_dvd_left.mp h)
    rw [← hqu, Kronecker.cast_lift _ _ hqM, Kronecker.cast_lift _ _ hqM,
      Kronecker.kronecker_prime hD q hq2 hqD]
    have := hleg q hqN hq2 hqD
    simpa [CompositeLocal.pv] using this
  obtain ⟨hc, hall⟩ := primitive_eq_of_changeLevel _ _ h₁ h₂
    (primitiveCharacter_isPrimitive χ) (KroneckerPrim.isPrimitive_kronecker hD) heq
  exact ⟨N, hN, χ, hne, hsq, hz, hc, hall⟩

/-- **The classical factorization:** ζ_K(s) = ζ(s) · L(s, χ_{D_K}) for Re s > 1. -/
theorem dedekindZeta_quadratic (hK : Module.finrank ℚ K = 2) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun m => (IdealCount.A (𝓞 K) m : ℂ)) s =
      riemannZeta s * LSeries (fun m => Kronecker.kronecker (discr K)
        (QuadKronecker.discr_isFundamental hK).1.ne_zero (m : ZMod (discr K).natAbs)) s := by
  obtain ⟨N, hN, χ, -, -, hz, -, hall⟩ := chi_eq_kronecker hK
  rw [hz s hs]
  congr 2
  funext m
  have := hall m
  simpa using this

end QuadKronId

#print axioms QuadKronId.primitive_eq_of_changeLevel
#print axioms QuadKronId.chi_eq_kronecker
#print axioms QuadKronId.dedekindZeta_quadratic
