import QuadraticLocalIdealCount

/-!
# WeightedLocalIdealCount — the local count when residue degrees differ (non-Galois allowed)

If the primes above p are P₁,…,P_g with N(Pᵢ) = p^{fᵢ}, then
  #{I : N(I) = pᵏ} = #{a ∈ ℕ^g : f₁a₁ + ⋯ + f_g a_g = k},
a weighted partition count. With all fᵢ = f this is `LocalCount.card_ideals_norm_prime_pow`.
Reuses the construction `LocalCount.build`; no Galois hypothesis.
-/

open Ideal UniqueFactorizationMonoid LocalCount

namespace WeightedCount

variable {S : Type*} [CommRing S] [IsDedekindDomain S] [Ring.HasFiniteQuotients S]
variable {g : ℕ} {P : Fin g → Ideal S}

theorem absNorm_build_weighted {p : ℕ} {f : Fin g → ℕ} (hnorm : ∀ i, absNorm (P i) = p ^ f i)
    (a : Fin g → ℕ) : absNorm (build P a) = p ^ (∑ i, f i * a i) := by
  rw [build, map_prod]
  simp only [map_pow, hnorm, ← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]

/-- **Weighted local count:** primes above p of possibly different residue degrees f i. -/
theorem card_ideals_norm_prime_pow_weighted {p : ℕ} {f : Fin g → ℕ} (hp : 1 < p)
    (hP : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (habove : ∀ Q : Ideal S, Prime Q → Q ∣ span {(p : S)} → ∃ i, Q = P i)
    (hnorm : ∀ i, absNorm (P i) = p ^ f i) (k : ℕ) :
    Nat.card {I : Ideal S // absNorm I = p ^ k} =
      Nat.card {a : Fin g → ℕ // ∑ i, f i * a i = k} := by
  classical
  symm
  refine Nat.card_eq_of_bijective (fun a => ⟨build P a.1, ?_⟩) ⟨?_, ?_⟩
  · rw [absNorm_build_weighted hnorm, a.2]
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ h
    have h' : build P a = build P b := congrArg Subtype.val h
    apply Subtype.ext; funext j
    show a j = b j
    rw [← count_nf_build hP hinj a j, ← count_nf_build hP hinj b j, h']
  · rintro ⟨I, hI⟩
    have hI0 : I ≠ 0 := by
      intro h; rw [h] at hI
      have : absNorm (0 : Ideal S) = 0 := absNorm_bot
      rw [this] at hI; exact (pow_ne_zero k (by omega : p ≠ 0)) hI.symm
    -- every normalized factor of I lies over p
    have hdvd : I ∣ span {(p : S)} ^ k := by
      rw [Ideal.dvd_iff_le, span_singleton_pow, span_le, Set.singleton_subset_iff, ← Nat.cast_pow,
        ← hI]
      exact absNorm_mem I
    have hmem : ∀ Q ∈ normalizedFactors I, ∃ i, Q = P i := fun Q hQ =>
      habove Q (prime_of_normalized_factor Q hQ)
        ((prime_of_normalized_factor Q hQ).dvd_of_dvd_pow
          ((dvd_of_mem_normalizedFactors hQ).trans hdvd))
    let a : Fin g → ℕ := fun i => (normalizedFactors I).count (P i)
    have hnf : normalizedFactors I = normalizedFactors (build P a) := by
      ext Q
      rw [nf_build hP, Multiset.count_sum']
      by_cases hQ : ∃ i, Q = P i
      · obtain ⟨j, rfl⟩ := hQ
        rw [Finset.sum_eq_single j]
        · simp [a]
        · intro i _ hij; exact count_other hinj hij _
        · simp
      · push Not at hQ
        rw [Multiset.count_eq_zero_of_notMem (fun h => by
          obtain ⟨i, hi⟩ := hmem Q h; exact hQ i hi)]
        symm; apply Finset.sum_eq_zero; intro i _
        simp [Multiset.count_singleton, (hQ i)]
    have hbuild : build P a = I := by
      have h1 := prod_normalizedFactors hI0
      have h2 := prod_normalizedFactors
        (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero (a i) (hP i).ne_zero :
          build P a ≠ 0)
      rw [hnf] at h1
      exact (associated_iff_eq.mp h2).symm.trans (associated_iff_eq.mp h1)
    refine ⟨⟨a, ?_⟩, Subtype.ext hbuild⟩
    have := absNorm_build_weighted hnorm a
    rw [hbuild, hI] at this
    exact (Nat.pow_right_injective hp this).symm

end WeightedCount

#print axioms WeightedCount.card_ideals_norm_prime_pow_weighted
