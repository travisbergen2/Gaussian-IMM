import QuadraticLocalIdealCount

/-!
# LocalCountBinomial — closed form of the local ideal count for arbitrary (g, f)

Degree-free. If p has g primes above it, all of residue degree f > 0, then

  #{I : N(I) = pᵏ} = C(k/f + g − 1, g − 1) if f ∣ k, and 0 otherwise.

The allocation count {a : Fin g → ℕ // f·Σa = k} is reduced to stars and bars
(`Sym.equivNatSumOfFintype`, `Sym.card_sym_eq_choose`). Ramification indices do not enter.
-/

open Ideal

namespace LocalCount

/-- Stars and bars: #{a : Fin g → ℕ // Σ a = m} = C(m + g − 1, g − 1). -/
theorem card_sum_eq (g m : ℕ) (hg : 0 < g) :
    Nat.card {a : Fin g → ℕ // ∑ i, a i = m} = (m + g - 1).choose (g - 1) := by
  rw [← Nat.card_congr (Sym.equivNatSumOfFintype (Fin g) m), Nat.card_eq_fintype_card,
    Sym.card_sym_eq_choose, Fintype.card_fin]
  rw [show g + m - 1 = m + g - 1 by omega, show g - 1 = (m + g - 1) - m by omega,
    Nat.choose_symm (by omega)]

/-- **Allocation count, closed form.** -/
theorem card_alloc (g f k : ℕ) (hg : 0 < g) (hf : 0 < f) :
    Nat.card {a : Fin g → ℕ // f * ∑ i, a i = k} =
      if f ∣ k then (k / f + g - 1).choose (g - 1) else 0 := by
  split_ifs with hdvd
  · obtain ⟨m, rfl⟩ := hdvd
    rw [Nat.mul_div_cancel_left m hf, ← card_sum_eq g m hg]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun a => by
      constructor
      · exact fun h => Nat.eq_of_mul_eq_mul_left hf h
      · exact fun h => by rw [h])
  · rw [Nat.card_eq_zero]
    left
    exact ⟨fun ⟨a, ha⟩ => hdvd ⟨_, ha.symm⟩⟩

variable {S : Type*} [CommRing S] [IsDedekindDomain S] [Ring.HasFiniteQuotients S]

/-- **Local ideal count, closed form**, under the hypotheses of `card_ideals_norm_prime_pow`. -/
theorem card_ideals_norm_prime_pow_closed {g : ℕ} (hg : 0 < g) {P : Fin g → Ideal S} {p f : ℕ}
    (hp : 1 < p) (hf : 0 < f) (hP : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (habove : ∀ Q : Ideal S, Prime Q → Q ∣ span {(p : S)} → ∃ i, Q = P i)
    (hnorm : ∀ i, absNorm (P i) = p ^ f) (k : ℕ) :
    Nat.card {I : Ideal S // absNorm I = p ^ k} =
      if f ∣ k then (k / f + g - 1).choose (g - 1) else 0 := by
  rw [card_ideals_norm_prime_pow hp hP hinj habove hnorm k, card_alloc g f k hg hf]

end LocalCount

#print axioms LocalCount.card_alloc
#print axioms LocalCount.card_ideals_norm_prime_pow_closed
