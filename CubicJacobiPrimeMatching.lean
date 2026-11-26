import CubicRadicandValuation
import EisensteinJacobiPrime

/-!
# CubicJacobiPrimeMatching — every non-conjugation-fixed prime of ℤ[ω] is a Jacobi-sum prime

R = 𝓞 F, F = ℚ(ω) ⊆ ℂ, κ = complex conjugation (`CubicVal`).
* `conjF_eq_σ`: complex conjugation on F is the automorphism σ : ω ↦ ω² of `EisJacobi`;
* `norm_eq`: N(x) = x · κx in R (Gal(F/ℚ) = {1, κ}); `norm_nonneg'`: N(x) = |x|² ≥ 0;
* `split_of_not_fixed`: if π is prime and κπ ≁ π, then π · κπ = q for a rational prime q with
  3 ∣ q − 1. Steps: π divides some rational prime p; N(π) ∣ p², N(π) ≠ 1 (π not a unit);
  N(π) = p² would make π ~ p, which is κ-fixed; so N(π) = p. Then R/(π) is a field with p
  elements in which ω ≢ 1 (else π ~ λ = ω − 1, κ-fixed), so ω has order 3 and 3 ∣ p − 1;
* `kappa_J`: κ(J) = J̄ for J = J(χ, χ), J̄ = J(χ⁻¹, χ⁻¹) (`EisJacobi`);
* `assoc_jacobi`: a prime π ∣ q is associated to J or to J̄ (q = J · J̄, J and J̄ prime);
* `prime_cases`: every prime π is either κ-fixed (κπ ~ π) or π · κπ = q, q ≡ 1 (mod 3), and
  π ~ J_q or π ~ J̄_q for a cubic character χ mod q;
* `radicand_prime_cases`: for the integral Kummer radicand A of a cyclic cubic K, every prime π
  has 3 ∣ v_π(A), or is a Jacobi-sum prime (as above) with v_{κπ}(A) ≡ 2 v_π(A) (mod 3).
The orientation of each split pair in A and the unit factor are not determined here.
-/

open IntermediateField Module NumberField CubicKummerRep CubicVal

namespace CubicMatch

local notation "ω" => CubicAssembly.ω

/-- **Complex conjugation on F = ℚ(ω) is σ : ω ↦ ω².** -/
theorem conjF_eq_σ : conjF = EisJacobi.σ (K := F) := by
  classical
  have h := Finset.mem_univ conjF
  rw [EisJacobi.univ_gal] at h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h
  · exfalso
    have := conjF_coe ωF
    rw [h, AlgEquiv.one_apply] at this
    change ω = starRingEnd ℂ ω at this
    rw [CubicConj.conj_ω] at this
    have h1 : ω ^ 1 = ω ^ 2 := by rw [pow_one]; exact this
    have := CubicAssembly.hω.pow_inj (by norm_num) (by norm_num) h1
    norm_num at this
  · exact h

theorem ι_norm (x : 𝓞 F) : ((Algebra.norm ℤ x : ℤ) : ℂ) = ι x * starRingEnd ℂ (ι x) := by
  classical
  have h1 : algebraMap ℚ F (Algebra.norm ℚ (x : F)) = (x : F) * conjF (x : F) := by
    rw [Algebra.norm_eq_prod_automorphisms, EisJacobi.univ_gal,
      Finset.prod_pair (EisJacobi.σ_ne_one (K := F)).symm, AlgEquiv.one_apply, conjF_eq_σ]
  have h2 := congrArg F.val h1
  rw [AlgHom.commutes, map_mul, ← Algebra.coe_norm_int, eq_ratCast, Rat.cast_intCast] at h2
  rw [h2]
  exact congrArg (ι x * ·) (conjF_coe (x : F))

/-- **N(x) = x · κx.** -/
theorem norm_eq (x : 𝓞 F) : ((Algebra.norm ℤ x : ℤ) : 𝓞 F) = x * κ x :=
  ι_injective (by rw [map_intCast, map_mul, kappa_coe, ι_norm])

theorem norm_nonneg' (x : 𝓞 F) : 0 ≤ Algebra.norm ℤ x := by
  have h := ι_norm x
  rw [Complex.mul_conj] at h
  have : ((Algebra.norm ℤ x : ℤ) : ℝ) = Complex.normSq (ι x) := by exact_mod_cast h
  exact_mod_cast (this ▸ Complex.normSq_nonneg (ι x) : (0 : ℝ) ≤ (Algebra.norm ℤ x : ℝ))

theorem absNorm_eq (x : 𝓞 F) :
    Ideal.absNorm (Ideal.span ({x} : Set (𝓞 F))) = (Algebra.norm ℤ x).natAbs :=
  Ideal.absNorm_span_singleton x

/-- A prime dividing a positive integer divides one of its prime factors. -/
theorem exists_prime_dvd {π : 𝓞 F} (hπ : Prime π) :
    ∀ m : ℕ, m ≠ 0 → π ∣ (m : 𝓞 F) → ∃ p : ℕ, p.Prime ∧ π ∣ (p : 𝓞 F) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm hdvd
    by_cases h1 : m = 1
    · subst h1; rw [Nat.cast_one] at hdvd; exact absurd (isUnit_of_dvd_one hdvd) hπ.2.1
    · obtain ⟨p, hp, k, rfl⟩ := Nat.exists_prime_and_dvd h1
      rw [Nat.cast_mul] at hdvd
      rcases hπ.dvd_or_dvd hdvd with h | h
      · exact ⟨p, hp, h⟩
      · have hk : k ≠ 0 := by rintro rfl; exact hm (mul_zero p)
        exact ih k (by have := hp.two_le; nlinarith [Nat.pos_of_ne_zero hk]) hk h

theorem fixed_of_assoc {π y : 𝓞 F} (h : Associated π y) (hy : Associated (κ y) y) :
    Associated (κ π) π :=
  ((h.map κ).trans hy).trans h.symm

theorem z_cube : hωF.toInteger ^ 3 = 1 :=
  ι_injective (by rw [map_pow, ι_ω, map_one]; exact CubicConj.ω_cube)

/-- **Non-fixed primes split over a prime q ≡ 1 (mod 3):** π · κπ = q. -/
theorem split_of_not_fixed {π : 𝓞 F} (hπ : Prime π) (hnf : ¬ Associated (κ π) π) :
    ∃ q : ℕ, q.Prime ∧ 3 ∣ q - 1 ∧ π * κ π = (q : 𝓞 F) := by
  have hπ0 := hπ.ne_zero
  set n := Algebra.norm ℤ π with hn
  have hnπ : ((n : ℤ) : 𝓞 F) = π * κ π := norm_eq π
  have hn0 : 0 ≤ n := norm_nonneg' π
  have hnat : ((n.natAbs : ℕ) : 𝓞 F) = π * κ π := by
    rw [← hnπ, ← Int.cast_natCast, Int.natAbs_of_nonneg hn0]
  have hnot1 : n.natAbs ≠ 1 := by
    intro h
    apply hπ.2.1
    rw [← Ideal.span_singleton_eq_top, ← Ideal.absNorm_eq_one_iff, absNorm_eq, ← hn, h]
  have hnne0 : n.natAbs ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero] at hnat
    exact mul_ne_zero hπ0 (fun h' => hπ0 (κ.injective (by rw [h', map_zero]))) hnat.symm
  -- π divides a rational prime p
  obtain ⟨p, hp, ρ, hρ⟩ := exists_prime_dvd hπ n.natAbs hnne0 ⟨κ π, hnat⟩
  -- N(π) ∣ p²
  have hrank : finrank ℤ (𝓞 F) = 2 := by rw [RingOfIntegers.rank, finrank_F]
  have hNp : Algebra.norm ℤ (p : 𝓞 F) = (p : ℤ) ^ 2 := by
    rw [← map_natCast (algebraMap ℤ (𝓞 F)), Algebra.norm_algebraMap, hrank]
  have hmul : (p : ℤ) ^ 2 = n * Algebra.norm ℤ ρ := by rw [← hNp, hρ, map_mul]
  have hmulN : p ^ 2 = n.natAbs * (Algebra.norm ℤ ρ).natAbs := by
    have := congrArg Int.natAbs hmul
    rwa [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at this
  obtain ⟨i, hi, hni⟩ := (Nat.dvd_prime_pow hp).mp ⟨_, hmulN⟩
  have hnp : n.natAbs = p := by
    interval_cases i
    · exact absurd hni hnot1
    · simpa using hni
    · exfalso
      have hb : (Algebra.norm ℤ ρ).natAbs = 1 := by
        rw [hni] at hmulN
        exact (Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) (by rw [mul_one]; exact hmulN.symm))
      have hρu : IsUnit ρ := by
        rw [← Ideal.span_singleton_eq_top, ← Ideal.absNorm_eq_one_iff, absNorm_eq, hb]
      apply hnf
      have hass : Associated π (p : 𝓞 F) := by
        rw [hρ]; exact associated_mul_unit_right π ρ hρu
      exact fixed_of_assoc hass (by rw [kappa_natCast])
  refine ⟨p, hp, ?_, by rw [← hnat, hnp]⟩
  -- 3 ∣ p − 1: ω has order 3 in the residue field R/(π) of size p
  set P : Ideal (𝓞 F) := Ideal.span {π}
  have hP : P.IsPrime := (Ideal.span_singleton_prime hπ0).mpr hπ
  have hPne : P ≠ ⊥ := by rw [Ne, Ideal.span_singleton_eq_bot]; exact hπ0
  have : P.IsMaximal := hP.isMaximal hPne
  letI : Field (𝓞 F ⧸ P) := Ideal.Quotient.field P
  have : Infinite (𝓞 F) := Infinite.of_injective (fun m : ℕ => (m : 𝓞 F)) (fun a b h => by
    have := congrArg ι h; simp only [map_natCast] at this; exact_mod_cast this)
  have hcard : Nat.card (𝓞 F ⧸ P) = p := by
    rw [← Ideal.absNorm_eq_natCard, absNorm_eq, ← hn, hnp]
  have : Finite (𝓞 F ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  set w : 𝓞 F ⧸ P := Ideal.Quotient.mk P hωF.toInteger
  have hw3 : w ^ 3 = 1 := by rw [← map_pow, z_cube, map_one]
  have hw1 : w ≠ 1 := by
    intro h
    have : hωF.toInteger - 1 ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one]; exact sub_eq_zero.mpr h
    rw [Ideal.mem_span_singleton] at this
    exact hnf (fixed_of_assoc (hπ.associated_of_dvd lam_prime this) kappa_lambda)
  have hw0 : w ≠ 0 := by rintro h; rw [h, zero_pow (by norm_num)] at hw3; exact zero_ne_one hw3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf (Units.mk0 w hw0) = 3 := by
    rw [← orderOf_units, Units.val_mk0]; exact orderOf_eq_prime hw3 hw1
  have := orderOf_dvd_natCard (Units.mk0 w hw0)
  rwa [hord, Nat.card_units, hcard] at this

/-- **κ(J) = J̄.** -/
theorem kappa_J {q : ℕ} [Fact q.Prime] {χ : MulChar (ZMod q) F} (hχ : orderOf χ = 3) :
    κ (EisJacobi.J hχ) = EisJacobi.Jbar hχ := by
  apply RingOfIntegers.ext
  change conjF (jacobiSum χ χ) = jacobiSum χ⁻¹ χ⁻¹
  rw [conjF_eq_σ]; exact EisJacobi.conj_jacobiSum hχ

theorem Jbar_prime {q : ℕ} [hq : Fact q.Prime] {χ : MulChar (ZMod q) F} (hχ : orderOf χ = 3) :
    Prime (EisJacobi.Jbar hχ) := by
  have hχ' : orderOf χ⁻¹ = 3 := by rw [orderOf_inv, hχ]
  exact EisJacobi.J_prime hχ' (by rw [ZMod.card]; exact hq.out)

/-- **Prime matching:** a prime π ∣ q is associated to J or to J̄. -/
theorem assoc_jacobi {q : ℕ} [hq : Fact q.Prime] {χ : MulChar (ZMod q) F} (hχ : orderOf χ = 3)
    {π : 𝓞 F} (hπ : Prime π) (hdvd : π ∣ (q : 𝓞 F)) :
    Associated π (EisJacobi.J hχ) ∨ Associated π (EisJacobi.Jbar hχ) := by
  have hJ := EisJacobi.J_prime hχ (by rw [ZMod.card]; exact hq.out)
  have hprod := EisJacobi.J_mul_conj hχ
  rw [ZMod.card] at hprod
  rw [← hprod] at hdvd
  rcases hπ.dvd_or_dvd hdvd with h | h
  · exact Or.inl (hπ.associated_of_dvd hJ h)
  · exact Or.inr (hπ.associated_of_dvd (Jbar_prime hχ) h)

theorem exists_chi (q : ℕ) [Fact q.Prime] (hq3 : 3 ∣ q - 1) :
    ∃ χ : MulChar (ZMod q) F, orderOf χ = 3 :=
  MulChar.exists_mulChar_orderOf (ZMod q) (by rwa [ZMod.card]) hωF

/-- **Every prime of ℤ[ω] is κ-fixed or a Jacobi-sum prime above some q ≡ 1 (mod 3).** -/
theorem prime_cases {π : 𝓞 F} (hπ : Prime π) :
    Associated (κ π) π ∨ ∃ q : ℕ, ∃ _ : Fact q.Prime, 3 ∣ q - 1 ∧ π * κ π = (q : 𝓞 F) ∧
      ∃ χ : MulChar (ZMod q) F, ∃ hχ : orderOf χ = 3,
        κ (EisJacobi.J hχ) = EisJacobi.Jbar hχ ∧
        (Associated π (EisJacobi.J hχ) ∨ Associated π (EisJacobi.Jbar hχ)) := by
  by_cases hf : Associated (κ π) π
  · exact Or.inl hf
  right
  obtain ⟨q, hq, hq3, hqπ⟩ := split_of_not_fixed hπ hf
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨χ, hχ⟩ := exists_chi q hq3
  exact ⟨q, this, hq3, hqπ, χ, hχ, kappa_J hχ, assoc_jacobi hχ hπ ⟨κ π, hqπ.symm⟩⟩

variable (K : IntermediateField ℚ ℂ) [IsGalois ℚ K] (hK : finrank ℚ K = 3)

include hK in
/-- **Prime cases for the integral Kummer radicand A.** -/
theorem radicand_prime_cases : ∃ β : ℂ, β ∈ M K ∧ β ^ 3 ∈ F ∧ β ∉ F ∧ M K = ℚ⟮ω, β⟯ ∧
    ∃ s A : 𝓞 F, s ≠ 0 ∧ A ≠ 0 ∧ ι s ^ 3 * β ^ 3 = ι A ∧
      ∀ π : 𝓞 F, Prime π → 3 ∣ multiplicity π A ∨
        (multiplicity (κ π) A % 3 = (2 * multiplicity π A) % 3 ∧
          ∃ q : ℕ, ∃ _ : Fact q.Prime, 3 ∣ q - 1 ∧ π * κ π = (q : 𝓞 F) ∧
            ∃ χ : MulChar (ZMod q) F, ∃ hχ : orderOf χ = 3,
              κ (EisJacobi.J hχ) = EisJacobi.Jbar hχ ∧
              (Associated π (EisJacobi.J hχ) ∨ Associated π (EisJacobi.Jbar hχ))) := by
  obtain ⟨β, hβM, hβ3, hβF, hM, s, A, C, D, hs0, hA0, hC0, hsA, hCD⟩ := integral_radicand K hK
  refine ⟨β, hβM, hβ3, hβF, hM, s, A, hs0, hA0, hsA, fun π hπ => ?_⟩
  rcases prime_cases hπ with hf | hsplit
  · exact Or.inl (three_dvd_of_fixed κ kappa_kappa hπ hf hA0 hC0 hCD)
  · exact Or.inr ⟨val_constraint κ kappa_kappa hπ hA0 hC0 hCD, hsplit⟩

end CubicMatch

#print axioms CubicMatch.conjF_eq_σ
#print axioms CubicMatch.norm_eq
#print axioms CubicMatch.split_of_not_fixed
#print axioms CubicMatch.kappa_J
#print axioms CubicMatch.assoc_jacobi
#print axioms CubicMatch.prime_cases
#print axioms CubicMatch.radicand_prime_cases
