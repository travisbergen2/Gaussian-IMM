import Mathlib

/-!
# QuadraticLocalIdealCount — local ideal counts from the splitting data (f, g)

Generic: no Gaussian or Eisenstein integers, no characters, no L-functions.

Setting: `S` a Dedekind domain with finite quotients (so `Ideal.absNorm` is defined and
multiplicative); `p > 1` a natural number; `P : Fin g → Ideal S` the distinct prime ideals
lying over p (every prime ideal containing p is one of them), each of norm `p ^ f`.

* `card_ideals_norm_prime_pow`: the ideals of norm pᵏ are in bijection with exponent allocations
    {a : Fin g → ℕ | f · Σ aᵢ = k},  via a ↦ ∏ Pᵢ^{aᵢ}.
  (The ramification index e never appears: it only constrains which (f, g) occur.)
* The three quadratic patterns:
    split    (f, g) = (1, 2):  k + 1
    inert    (f, g) = (2, 1):  1 if k even, 0 if k odd
    ramified (f, g) = (1, 1):  1
-/

open Ideal UniqueFactorizationMonoid

namespace LocalCount

variable {S : Type*} [CommRing S] [IsDedekindDomain S] [Ring.HasFiniteQuotients S]
variable {g : ℕ} (P : Fin g → Ideal S)

/-- The ideal with exponent allocation `a`. -/
def build (a : Fin g → ℕ) : Ideal S := ∏ i, P i ^ a i

variable {P}

theorem nf_prod (hP : ∀ i, Prime (P i)) (a : Fin g → ℕ) (s : Finset (Fin g)) :
    normalizedFactors (∏ i ∈ s, P i ^ a i) = ∑ i ∈ s, a i • ({P i} : Multiset (Ideal S)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty]; exact normalizedFactors_one
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj,
      normalizedFactors_mul (pow_ne_zero _ (hP j).ne_zero)
        (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hP i).ne_zero),
      normalizedFactors_pow, normalizedFactors_irreducible (hP j).irreducible, normalize_eq, ih]

theorem nf_build (hP : ∀ i, Prime (P i)) (a : Fin g → ℕ) :
    normalizedFactors (build P a) = ∑ i, a i • ({P i} : Multiset (Ideal S)) :=
  nf_prod hP a Finset.univ

theorem count_other (hinj : Function.Injective P) {i j : Fin g} (hij : i ≠ j) (n : ℕ) :
    (n • ({P i} : Multiset (Ideal S))).count (P j) = 0 := by
  rw [Multiset.count_nsmul, Multiset.count_singleton, if_neg (fun h => hij (hinj h).symm), mul_zero]

theorem count_nf_build (hP : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (a : Fin g → ℕ) (j : Fin g) :
    (normalizedFactors (build P a)).count (P j) = a j := by
  classical
  rw [nf_build hP, Multiset.count_sum', Finset.sum_eq_single j]
  · simp
  · intro i _ hij; exact count_other hinj hij _
  · simp

theorem absNorm_build {p f : ℕ} (hnorm : ∀ i, absNorm (P i) = p ^ f) (a : Fin g → ℕ) :
    absNorm (build P a) = p ^ (f * ∑ i, a i) := by
  rw [build, map_prod]
  simp only [map_pow, hnorm, ← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum, Finset.mul_sum]

/-- **The generic local count.** -/
theorem card_ideals_norm_prime_pow {p f : ℕ} (hp : 1 < p)
    (hP : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (habove : ∀ Q : Ideal S, Prime Q → Q ∣ span {(p : S)} → ∃ i, Q = P i)
    (hnorm : ∀ i, absNorm (P i) = p ^ f) (k : ℕ) :
    Nat.card {I : Ideal S // absNorm I = p ^ k} =
      Nat.card {a : Fin g → ℕ // f * ∑ i, a i = k} := by
  classical
  symm
  refine Nat.card_eq_of_bijective (fun a => ⟨build P a.1, ?_⟩) ⟨?_, ?_⟩
  · rw [absNorm_build hnorm, a.2]
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
    have := absNorm_build hnorm a
    rw [hbuild, hI] at this
    exact (Nat.pow_right_injective hp this).symm

/-! ## The three quadratic patterns (pure counting) -/

theorem card_split (k : ℕ) : Nat.card {a : Fin 2 → ℕ // 1 * ∑ i, a i = k} = k + 1 := by
  rw [← Nat.card_fin (k + 1)]
  symm
  refine Nat.card_eq_of_bijective (fun j => ⟨![j, k - j], ?_⟩) ⟨?_, ?_⟩
  · simp [Fin.sum_univ_two]; omega
  · intro j j' h
    have := congrArg (fun a => a.1 0) h
    simp at this; exact Fin.ext this
  · rintro ⟨a, ha⟩
    simp [Fin.sum_univ_two] at ha
    refine ⟨⟨a 0, by omega⟩, Subtype.ext ?_⟩
    funext i; fin_cases i <;> simp; omega

theorem card_inert (k : ℕ) :
    Nat.card {a : Fin 1 → ℕ // 2 * ∑ i, a i = k} = if Even k then 1 else 0 := by
  split_ifs with hk
  · obtain ⟨j, rfl⟩ := hk
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => Subtype.ext (funext fun i => ?_)⟩, ⟨⟨![j], by simp; ring⟩⟩⟩
    have hx := x.2; have hy := y.2
    simp at hx hy; fin_cases i; simp; omega
  · rw [Nat.card_eq_zero]; left
    refine ⟨fun x => hk ⟨x.1 0, ?_⟩⟩
    have := x.2; simp at this; omega

theorem card_ramified (k : ℕ) : Nat.card {a : Fin 1 → ℕ // 1 * ∑ i, a i = k} = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun x y => Subtype.ext (funext fun i => ?_)⟩, ⟨⟨![k], by simp⟩⟩⟩
  have hx := x.2; have hy := y.2
  simp at hx hy; fin_cases i; simp; omega

end LocalCount

#print axioms LocalCount.card_ideals_norm_prime_pow
#print axioms LocalCount.card_split
#print axioms LocalCount.card_inert
#print axioms LocalCount.card_ramified
