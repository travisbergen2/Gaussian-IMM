import Mathlib

/-!
# CyclotomicSqrt — square roots of integers from roots of unity

L a field of characteristic 0 containing a primitive N-th root of unity ζ, 8 ∣ N.
* `sq_neg_one`: i = ζ^{N/4} has i² = −1;
* `sq_two`: ζ₈ + ζ₈⁷ (ζ₈ = ζ^{N/8}) squares to 2;
* `sq_odd_prime`: for an odd prime p ∣ N, the quadratic Gauss sum g = Σ (a/p) ψ(a) (ψ built from
  ζ^{N/p}) has g² = (−1/p)·p (Mathlib `gaussSum_sq`), so p or −p is a square in L, hence p is;
* `exists_sq_int`: every integer m with |m| ∣ N (or m = 0) is a square in L.
So √m ∈ ℚ(ζ_{8|m|}) for every integer m ≠ 0.
-/

namespace CycloSqrt

variable {L : Type*} [Field L] [CharZero L] {N : ℕ} [NeZero N] {ζ : L} (hζ : IsPrimitiveRoot ζ N) (h8 : 8 ∣ N)

include hζ h8

omit hζ h8 in
theorem N_pos : 0 < N := NeZero.pos N

omit [CharZero L] in
/-- i = ζ^{N/4}, i² = −1. -/
theorem sq_neg_one : (ζ ^ (N / 4)) ^ 2 = -1 := by
  have h4 : 4 ∣ N := (by norm_num : 4 ∣ 8).trans h8
  have hi := hζ.pow N_pos (Nat.div_mul_cancel h4).symm
  exact IsPrimitiveRoot.eq_neg_one_of_two_right (hi.pow (by norm_num) (by norm_num : 4 = 2 * 2))

omit [CharZero L] in
/-- (ζ₈ + ζ₈⁷)² = 2. -/
theorem sq_two : (ζ ^ (N / 8) + (ζ ^ (N / 8)) ^ 7) ^ 2 = 2 := by
  have h := hζ.pow N_pos (Nat.div_mul_cancel h8).symm
  set z := ζ ^ (N / 8)
  have h4 : z ^ 4 = -1 :=
    IsPrimitiveRoot.eq_neg_one_of_two_right (by
      simpa [← pow_mul] using h.pow (by norm_num) (by norm_num : 8 = 4 * 2))
  linear_combination (z ^ 10 - z ^ 6 + 2 * z ^ 4 + z ^ 2 - 2) * h4

omit h8 in
/-- **Quadratic Gauss sum:** for an odd prime p ∣ N, p or −p has a square root in L. -/
theorem sq_odd_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpN : p ∣ N) :
    ∃ y : L, y ^ 2 = p ∨ y ^ 2 = -p := by
  have : Fact p.Prime := ⟨hp⟩
  have hζp := hζ.pow N_pos (Nat.div_mul_cancel hpN).symm
  let ψ := AddChar.zmodChar p hζp.pow_eq_one
  have hψ : ψ.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root p hζp
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  let χ : MulChar (ZMod p) L := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom L)
  have hq : χ.IsQuadratic := (quadraticChar_isQuadratic (ZMod p)).comp _
  have hne : χ ≠ 1 := by
    obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hchar
    have ha0 : a ≠ 0 := fun h => ha (h ▸ IsSquare.zero)
    intro h
    have h1 := congrArg (· (a : ZMod p)) h
    simp only [χ, MulChar.ringHomComp_apply, quadraticChar_neg_one_iff_not_isSquare.mpr ha,
      MulChar.one_apply (Ne.isUnit ha0)] at h1
    norm_num at h1
  have hg := gaussSum_sq hne hq hψ
  rw [ZMod.card] at hg
  refine ⟨gaussSum χ ψ, ?_⟩
  rcases quadraticChar_dichotomy (F := ZMod p) (neg_ne_zero.mpr one_ne_zero) with h | h
  · left; rw [hg]; simp [χ, MulChar.ringHomComp_apply, h]
  · right; rw [hg]; simp [χ, MulChar.ringHomComp_apply, h]

/-- Every prime p ∣ N is a square in L. -/
theorem sq_prime {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) : ∃ y : L, y ^ 2 = p := by
  by_cases hp2 : p = 2
  · subst hp2; exact ⟨_, by rw [sq_two hζ h8]; norm_num⟩
  · obtain ⟨y, hy | hy⟩ := sq_odd_prime hζ hp hp2 hpN
    · exact ⟨y, hy⟩
    · refine ⟨y * ζ ^ (N / 4), ?_⟩
      rw [mul_pow, sq_neg_one hζ h8, hy]; ring

/-- Every k ∣ N is a square in L. -/
theorem sq_nat {k : ℕ} (hk : k ∣ N) : ∃ y : L, y ^ 2 = k := by
  induction k using induction_on_primes with
  | zero => exact absurd (Nat.eq_zero_of_zero_dvd hk) N_pos.ne'
  | one => exact ⟨1, by simp⟩
  | prime_mul p a hp ih =>
    obtain ⟨y, hy⟩ := sq_prime hζ h8 hp ((Dvd.intro a rfl).trans hk)
    obtain ⟨z, hz⟩ := ih ((Dvd.intro_left p rfl).trans hk)
    exact ⟨y * z, by rw [mul_pow, hy, hz]; push_cast; ring⟩

/-- **Every integer m with m = 0 or |m| ∣ N is a square in L.** -/
theorem exists_sq_int {m : ℤ} (hm : m = 0 ∨ m.natAbs ∣ N) : ∃ y : L, y ^ 2 = m := by
  rcases hm with rfl | hm
  · exact ⟨0, by simp⟩
  obtain ⟨y, hy⟩ := sq_nat hζ h8 hm
  rcases Int.natAbs_eq m with h | h
  · have hc : (m : L) = (m.natAbs : L) := by
      rw [← Int.cast_natCast]; exact congrArg (Int.cast) h
    exact ⟨y, by rw [hy, hc]⟩
  · have hc : (m : L) = -(m.natAbs : L) := by
      have := congrArg (Int.cast (R := L)) h
      rw [Int.cast_neg, Int.cast_natCast] at this; exact this
    refine ⟨y * ζ ^ (N / 4), ?_⟩
    rw [mul_pow, sq_neg_one hζ h8, hy, hc]; ring

end CycloSqrt

#print axioms CycloSqrt.sq_odd_prime
#print axioms CycloSqrt.exists_sq_int
