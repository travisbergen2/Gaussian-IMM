import Mathlib

/-!
# DedekindIdealCountMultiplicative — the global ideal count is multiplicative

Generic: any Dedekind domain `S` with finite quotients that is a free, finite ℤ-module
(e.g. any ring of integers). No quadratic assumption, no class number, no generators,
no characters, no splitting data.

* `A S n` = number of ideals of `S` of norm n.
* `A_mul_of_coprime`: A(mn) = A(m)·A(n) for coprime m, n > 0, via the bijection (I, J) ↦ IJ,
  inverted by `factor_recover`: I = IJ ⊔ (m) when N(I) = m, N(J) = n, gcd(m, n) = 1.
* `A_mul`: the same for all coprime m, n (with A(0) = A(1) = 1).

Lifted from the Gaussian `a_mul_of_coprime`; the only field-specific step there
(N((m)) = m²) is replaced by N((m)) = m^[S:ℤ] (`absNorm_span_natCast`).
-/

open Ideal

namespace IdealCount

variable (S : Type*) [CommRing S] [IsDedekindDomain S] [Ring.HasFiniteQuotients S]
  [Module.Free ℤ S] [Module.Finite ℤ S]

/-- The number of ideals of norm n. -/
noncomputable def A (n : ℕ) : ℕ := Nat.card {I : Ideal S // absNorm I = n}

variable {S}

theorem A_one : A S 1 = 1 := by
  rw [A, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun I J => Subtype.ext ?_⟩, ⟨⟨⊤, absNorm_top⟩⟩⟩
  rw [absNorm_eq_one_iff.mp I.2, absNorm_eq_one_iff.mp J.2]

theorem A_zero : A S 0 = 1 := by
  rw [A, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun I J => Subtype.ext ?_⟩, ⟨⟨⊥, absNorm_bot⟩⟩⟩
  rw [absNorm_eq_zero_iff.mp I.2, absNorm_eq_zero_iff.mp J.2]

/-- N((m)) = m^d, d = rank of S over ℤ. -/
theorem absNorm_span_natCast (m : ℕ) :
    absNorm (span {((m : ℕ) : S)}) = m ^ Module.finrank ℤ S := by
  rw [absNorm_span_singleton, show ((m : ℕ) : S) = algebraMap ℤ S (m : ℤ) by simp,
    Algebra.norm_algebraMap]
  simp [Int.natAbs_pow]

/-- An ideal of norm n contains n. -/
theorem span_le_of_absNorm {J : Ideal S} {n : ℕ} (h : absNorm J = n) :
    span ({((n : ℕ) : S)} : Set S) ≤ J := by
  rw [← h, span_le, Set.singleton_subset_iff]; exact absNorm_mem J

/-- Coprime integers generate comaximal ideals. -/
theorem span_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    span ({((m : ℕ) : S)} : Set S) ⊔ span {((n : ℕ) : S)} = ⊤ := by
  rw [eq_top_iff_one, Submodule.mem_sup]
  have hb := Nat.gcd_eq_gcd_ab m n
  rw [h] at hb
  refine ⟨(m.gcdA n : S) * m, mul_mem_left _ _ (mem_span_singleton_self _),
    (m.gcdB n : S) * n, mul_mem_left _ _ (mem_span_singleton_self _), ?_⟩
  have := congrArg (Int.cast : ℤ → S) hb
  push_cast at this
  rw [this]; ring

/-- **Recovery:** N(I) = m, N(J) = n, gcd(m, n) = 1 ⟹ I = IJ ⊔ (m). -/
theorem factor_recover {I J : Ideal S} {m n : ℕ} (hmn : Nat.Coprime m n)
    (hI : absNorm I = m) (hJ : absNorm J = n) :
    I * J ⊔ span {((m : ℕ) : S)} = I := by
  apply le_antisymm
  · exact sup_le mul_le_left (span_le_of_absNorm hI)
  · have hJM : J ⊔ span {((m : ℕ) : S)} = ⊤ := by
      apply eq_top_iff.mpr
      rw [← span_coprime hmn]
      exact sup_le le_sup_right (le_trans (span_le_of_absNorm hJ) le_sup_left)
    calc I = I * (J ⊔ span {((m : ℕ) : S)}) := by rw [hJM, mul_top]
      _ = I * J ⊔ I * span {((m : ℕ) : S)} := mul_sup _ _ _
      _ ≤ I * J ⊔ span {((m : ℕ) : S)} := sup_le_sup_left mul_le_right _

/-- An ideal of norm n divides (n). -/
theorem dvd_span_absNorm (I : Ideal S) : I ∣ span {((absNorm I : ℕ) : S)} := by
  rw [Ideal.dvd_iff_le, span_le, Set.singleton_subset_iff]; exact absNorm_mem I

/-- **Multiplicativity:** A(mn) = A(m)·A(n) for coprime m, n > 0. -/
theorem A_mul_of_coprime {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) :
    A S (m * n) = A S m * A S n := by
  let f : {I : Ideal S // absNorm I = m} × {J : Ideal S // absNorm J = n} →
      {K : Ideal S // absNorm K = m * n} :=
    fun x => ⟨x.1.1 * x.2.1, by rw [map_mul, x.1.2, x.2.2]⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨I, hI⟩, ⟨J, hJ⟩⟩ ⟨⟨I', hI'⟩, ⟨J', hJ'⟩⟩ h
      have h' : I * J = I' * J' := congrArg Subtype.val h
      have e1 : I = I' := by
        rw [← factor_recover hmn hI hJ, ← factor_recover hmn hI' hJ', h']
      have e2 : J = J' := by
        rw [← factor_recover hmn.symm hJ hI, ← factor_recover hmn.symm hJ' hI', mul_comm J,
          mul_comm J', h']
      subst e1; subst e2; rfl
    · rintro ⟨K, hK⟩
      have hdvd : K ∣ span {((m : ℕ) : S)} * span {((n : ℕ) : S)} := by
        have := dvd_span_absNorm K
        rwa [hK, Nat.cast_mul, ← span_singleton_mul_span_singleton] at this
      obtain ⟨I, J, hI, hJ, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hdvd
      set d := Module.finrank ℤ S
      have hNI : absNorm I ∣ m ^ d := by
        have := map_dvd absNorm hI; rwa [absNorm_span_natCast] at this
      have hNJ : absNorm J ∣ n ^ d := by
        have := map_dvd absNorm hJ; rwa [absNorm_span_natCast] at this
      have hprod : absNorm I * absNorm J = m * n := by rw [← map_mul, hK]
      have d1 : absNorm I ∣ m :=
        (Nat.Coprime.coprime_dvd_left hNI (Nat.Coprime.pow_left d hmn)).dvd_of_dvd_mul_right
          (hprod ▸ dvd_mul_right _ _)
      have d2 : absNorm J ∣ n :=
        (Nat.Coprime.coprime_dvd_left hNJ (Nat.Coprime.pow_left d hmn.symm)).dvd_of_dvd_mul_left
          (hprod ▸ dvd_mul_left _ _)
      have l1 := Nat.le_of_dvd hm d1
      have l2 := Nat.le_of_dvd hn d2
      have eI : absNorm I = m := by nlinarith
      have eJ : absNorm J = n := by nlinarith
      exact ⟨(⟨I, eI⟩, ⟨J, eJ⟩), rfl⟩
  rw [A, ← Nat.card_eq_of_bijective f hf, Nat.card_prod, A, A]

/-- Multiplicativity for all coprime pairs (A(0) = A(1) = 1 handles the edge cases). -/
theorem A_mul {m n : ℕ} (h : Nat.Coprime m n) : A S (m * n) = A S m * A S n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.coprime_zero_left] at h; subst h; simp [A_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.coprime_zero_right] at h; subst h; simp [A_one]
  exact A_mul_of_coprime hm hn h

end IdealCount

#print axioms IdealCount.A_mul_of_coprime
#print axioms IdealCount.A_mul
#print axioms IdealCount.absNorm_span_natCast
