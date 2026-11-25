import KroneckerCharacter
import ConductorCongruence

/-!
# KroneckerPrimitive — χ_D is primitive: conductor χ_D = |D|

Generic (no number fields, no zeta functions). D a fundamental discriminant, n = |D| = 2^e·o with
o = `oddPart D` odd and e ∈ {0, 2, 3} (`structure_fd`). For every prime p ∣ n there is a ∈ ℕ,
coprime to n, with a ≡ 1 (mod n/p) and χ_D(a) = −1 (`witness`):
* p odd: a ≡ 1 (mod n/p), a ≡ nonresidue (mod p) (CRT; p² ∤ D);
* p = 2, e = 2: a ≡ 1 (mod o), a ≡ 3 (mod 4), χ₄(3) = −1;
* p = 2, e = 3: a ≡ 1 (mod o), a ≡ 5 (mod 8), χ₈(5) = χ₈′(5) = −1.
So χ_D factors through no n/p (`CondCong.not_factorsThrough`), and every proper divisor of n
divides some n/p: `conductor_kronecker : conductor χ_D = |D|`.
-/

open ZMod DirichletCharacter Kronecker

namespace KroneckerPrim

variable {D : ℤ}

/-- n = 2^e · oddPart D with o odd and e ∈ {0,2,3}, matching the definitions of twoChar. -/
theorem structure_fd (hD : Int.IsFundamentalDiscr D) :
    Odd (oddPart D) ∧
      ((¬ 4 ∣ D.natAbs ∧ D.natAbs = oddPart D) ∨
       (4 ∣ D.natAbs ∧ ¬ 8 ∣ D.natAbs ∧ D.natAbs = 4 * oddPart D) ∨
       (8 ∣ D.natAbs ∧ D.natAbs = 8 * oddPart D)) := by
  have h4i : ∀ k : ℕ, (k ∣ D.natAbs ↔ (k : ℤ) ∣ D) := fun k => Int.ofNat_dvd_left.symm
  rcases Int.isFundamentalDiscr_iff_squarefree.mp hD with ⟨h1, -⟩ | ⟨h0, -, h23⟩
  · have n4 : ¬ 4 ∣ D.natAbs := by rw [h4i]; push_cast; omega
    have n8 : ¬ 8 ∣ D.natAbs := by rw [h4i]; push_cast; omega
    simp only [oddPart, if_neg n4, if_neg n8]
    refine ⟨Int.natAbs_odd.mpr (Int.odd_iff.mpr (by omega)), Or.inl ⟨n4, trivial⟩⟩
  rcases h23 with h2 | h3
  · have y8 : 8 ∣ D.natAbs := by rw [h4i]; push_cast; omega
    simp only [oddPart, if_pos y8]
    refine ⟨?_, Or.inr (Or.inr ⟨y8, (Nat.mul_div_cancel' y8).symm⟩)⟩
    have := Int.natAbs_ediv_of_dvd (by omega : (8 : ℤ) ∣ D)
    simp only [show (8 : ℤ).natAbs = 8 from rfl] at this
    rw [← this]
    exact Int.natAbs_odd.mpr (Int.odd_iff.mpr (by omega))
  · have y4 : 4 ∣ D.natAbs := by rw [h4i]; push_cast; omega
    have n8 : ¬ 8 ∣ D.natAbs := by rw [h4i]; push_cast; omega
    simp only [oddPart, if_neg n8, if_pos y4]
    refine ⟨?_, Or.inr (Or.inl ⟨y4, n8, (Nat.mul_div_cancel' y4).symm⟩)⟩
    have := Int.natAbs_ediv_of_dvd (by omega : (4 : ℤ) ∣ D)
    simp only [show (4 : ℤ).natAbs = 4 from rfl] at this
    rw [← this]
    exact Int.natAbs_odd.mpr (Int.odd_iff.mpr (by omega))

/-- Odd primes divide D at most once. -/
theorem odd_prime_sq (hD : Int.IsFundamentalDiscr D) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ^ 2 ∣ D.natAbs := by
  intro h
  exact hD.2.2 p hp (hp.odd_of_ne_two hp2) (by exact_mod_cast Int.ofNat_dvd_left.mpr h)

theorem jacobi_one_of_modEq {a o : ℕ} (h : a ≡ 1 [MOD o]) : jacobiSym a o = 1 := by
  rw [jacobiSym.mod_left' (a₂ := 1), jacobiSym.one_left]
  have := congrArg (fun x : ℕ => (x : ℤ)) h
  simpa [Nat.ModEq, Int.natCast_mod] using this

theorem coprime_of_modEq_one {a m : ℕ} (h : a ≡ 1 [MOD m]) : a.Coprime m := by
  have := Nat.ModEq.gcd_eq h
  rw [Nat.gcd_one_left] at this
  exact this

/-- CRT with modulus 1 at m and residue b at a power of two. -/
theorem crt_two {o t b : ℕ} (ho : Odd o) (ht : t = 4 ∨ t = 8) :
    ∃ k : ℕ, k ≡ 1 [MOD o] ∧ k % t = b % t := by
  have h2 : o.Coprime 2 := (Nat.coprime_comm.mp
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by have := Nat.odd_iff.mp ho; omega)))
  have hco : o.Coprime t := by
    rcases ht with rfl | rfl
    · simpa using h2.pow_right 2
    · simpa using h2.pow_right 3
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hco 1 b
  exact ⟨k, hk1, hk2⟩

/-- **Witness at p = 2.** -/
theorem witness_two (hD : Int.IsFundamentalDiscr D) (h2 : 2 ∣ D.natAbs) :
    ∃ a : ℕ, a.Coprime D.natAbs ∧ a ≡ 1 [MOD D.natAbs / 2] ∧
      twoVal D a * jacobiSym a (oddPart D) = -1 := by
  obtain ⟨ho, hcase⟩ := structure_fd hD
  have ho2 : oddPart D % 2 = 1 := Nat.odd_iff.mp ho
  have hco2 : (oddPart D).Coprime 2 := Nat.coprime_two_right.mpr ho
  rcases hcase with ⟨-, hn⟩ | ⟨y4, n8, hn⟩ | ⟨y8, hn⟩
  · exfalso; rw [hn] at h2; omega
  · obtain ⟨k, hk1, hk4⟩ := crt_two (b := 3) ho (Or.inl rfl)
    have hk2 : k ≡ 1 [MOD 2] := by unfold Nat.ModEq; omega
    refine ⟨k, ?_, ?_, ?_⟩
    · rw [hn]
      exact Nat.Coprime.mul_right (by simpa using (show k.Coprime 2 from
        coprime_of_modEq_one hk2).pow_right 2) (coprime_of_modEq_one hk1)
    · rw [hn, show 4 * oddPart D / 2 = 2 * oddPart D by omega]
      exact (Nat.modEq_and_modEq_iff_modEq_mul hco2.symm).mp ⟨hk2, hk1⟩
    · simp only [twoVal, if_neg n8, if_pos y4, jacobi_one_of_modEq hk1, mul_one]
      exact χ₄_nat_three_mod_four (by omega)
  · obtain ⟨k, hk1, hk8⟩ := crt_two (b := 5) ho (Or.inr rfl)
    have hk4 : k ≡ 1 [MOD 4] := by unfold Nat.ModEq; omega
    have hk2 : k ≡ 1 [MOD 2] := by unfold Nat.ModEq; omega
    refine ⟨k, ?_, ?_, ?_⟩
    · rw [hn]
      exact Nat.Coprime.mul_right (by simpa using (show k.Coprime 2 from
        coprime_of_modEq_one hk2).pow_right 3) (coprime_of_modEq_one hk1)
    · rw [hn, show 8 * oddPart D / 2 = 4 * oddPart D by omega]
      exact (Nat.modEq_and_modEq_iff_modEq_mul (by simpa using hco2.symm.pow_left 2)).mp ⟨hk4, hk1⟩
    · simp only [twoVal, if_pos y8, jacobi_one_of_modEq hk1, mul_one]
      split_ifs
      · rw [χ₈_nat_eq_if_mod_eight]; split_ifs <;> omega
      · rw [χ₈'_nat_eq_if_mod_eight]; split_ifs <;> omega

/-- **Witness at an odd prime p ∣ D.** -/
theorem witness_odd (hD : Int.IsFundamentalDiscr D) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ D.natAbs) :
    ∃ a : ℕ, a.Coprime D.natAbs ∧ a ≡ 1 [MOD D.natAbs / p] ∧
      twoVal D a * jacobiSym a (oddPart D) = -1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ho, hcase⟩ := structure_fd hD
  set n := D.natAbs
  set o := oddPart D
  have hpo : p ∣ o := by
    have hcop : p.Coprime 8 := by
      have : p.Coprime 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
      simpa using this.pow_right 3
    rcases hcase with ⟨-, hn⟩ | ⟨-, -, hn⟩ | ⟨-, hn⟩
    · rwa [← hn]
    · rw [hn] at hpn
      exact (hcop.coprime_dvd_right (by norm_num : 4 ∣ 8)).dvd_of_dvd_mul_left hpn
    · rw [hn] at hpn; exact hcop.dvd_of_dvd_mul_left hpn
  obtain ⟨o', ho'⟩ := hpo
  have hnp : n = p * (n / p) := (Nat.mul_div_cancel' hpn).symm
  have hpq : ¬ p ∣ n / p := by
    intro h
    apply odd_prime_sq hD hp hp2
    have := Nat.mul_dvd_mul_left p h
    rw [← hnp, ← pow_two] at this
    exact this
  have hcopp : (n / p).Coprime p :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpq)
  -- a nonresidue mod p
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  obtain ⟨x, hx⟩ := FiniteField.exists_nonsquare hchar
  have hx0 : x ≠ 0 := fun h => hx (h ▸ IsSquare.zero)
  obtain ⟨k, hk1, hkr⟩ := Nat.chineseRemainder hcopp 1 x.val
  have hkx : (k : ZMod p) = x := by
    rw [← ZMod.natCast_zmod_val x, ZMod.natCast_eq_natCast_iff]; exact hkr
  have hkp : k.Coprime p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    apply hx0
    rw [← hkx]
    exact (ZMod.natCast_eq_zero_iff k p).mpr h
  refine ⟨k, ?_, hk1, ?_⟩
  · rw [hnp]; exact Nat.Coprime.mul_right hkp (coprime_of_modEq_one hk1)
  · have ht : ∀ t : ℕ, t = 4 ∨ t = 8 → t ∣ n → k % t = 1 := by
      intro t ht htn
      have hpt : p.Coprime t := by
        have : p.Coprime 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
        rcases ht with rfl | rfl
        · simpa using this.pow_right 2
        · simpa using this.pow_right 3
      have htnp : t ∣ n / p := by
        rw [hnp] at htn; exact hpt.symm.dvd_of_dvd_mul_left htn
      have := hk1.of_dvd htnp
      unfold Nat.ModEq at this
      rw [this, Nat.one_mod_eq_one.mpr (by rcases ht with rfl | rfl <;> norm_num)]
    have htwo : twoVal D k = 1 := by
      unfold twoVal
      split_ifs with h8 hr h4
      · have := ht 8 (Or.inr rfl) h8; rw [χ₈_nat_eq_if_mod_eight]; split_ifs <;> omega
      · have := ht 8 (Or.inr rfl) h8; rw [χ₈'_nat_eq_if_mod_eight]; split_ifs <;> omega
      · exact χ₄_nat_one_mod_four (ht 4 (Or.inl rfl) h4)
      · rfl
    have ho0 : o' ≠ 0 := by rintro rfl; simp at ho'; rw [ho'] at ho; exact absurd ho (by simp)
    have : NeZero o' := ⟨ho0⟩
    have ho'np : o' ∣ n / p := by
      apply Nat.dvd_div_of_mul_dvd
      rw [← ho']; exact oddPart_dvd D
    have hJ1 : jacobiSym k o' = 1 := jacobi_one_of_modEq (hk1.of_dvd ho'np)
    have hJp : jacobiSym k p = -1 := by
      rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff]
      rwa [Int.cast_natCast, hkx]
    rw [htwo, one_mul, ho', jacobiSym.mul_right, hJ1, hJp, mul_one]

/-- **χ_D is primitive: conductor χ_D = |D|.** -/
theorem conductor_kronecker (hD : Int.IsFundamentalDiscr D) :
    conductor (kronecker D hD.ne_zero) = D.natAbs := by
  have hn0 : D.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD.ne_zero
  have : NeZero D.natAbs := ⟨hn0⟩
  obtain ⟨k, hk⟩ := conductor_dvd_level (kronecker D hD.ne_zero)
  by_contra hne
  generalize hc : conductor (kronecker D hD.ne_zero) = c at hk hne
  have hk1 : k ≠ 1 := by rintro rfl; exact hne (by rw [hk, mul_one])
  have hk0 : k ≠ 0 := by rintro rfl; exact hn0 (by rw [hk, mul_zero])
  have hp : k.minFac.Prime := Nat.minFac_prime hk1
  have hpk : k.minFac ∣ k := Nat.minFac_dvd k
  have hpn : k.minFac ∣ D.natAbs := by rw [hk]; exact Dvd.dvd.mul_left hpk _
  have hcL : c ∣ D.natAbs / k.minFac := by
    rw [hk, Nat.mul_div_assoc _ hpk]; exact Dvd.intro _ rfl
  have hf := CondCong.factorsThrough_of_conductor_dvd (kronecker D hD.ne_zero) (hc ▸ hcL)
    (Nat.div_dvd_of_dvd hpn)
  obtain ⟨a, ha, haL, hval⟩ : ∃ a : ℕ, a.Coprime D.natAbs ∧ a ≡ 1 [MOD D.natAbs / k.minFac] ∧
      twoVal D a * jacobiSym a (oddPart D) = -1 := by
    by_cases hp2 : k.minFac = 2
    · rw [hp2] at hpn ⊢; exact witness_two hD hpn
    · exact witness_odd hD hp hp2 hpn
  apply CondCong.not_factorsThrough _ ha (Nat.coprime_one_left _) haL _ hf
  rw [kronecker_apply hD.ne_zero ha, hval, Nat.cast_one, map_one]
  norm_num

/-- χ_D is a primitive Dirichlet character. -/
theorem isPrimitive_kronecker (hD : Int.IsFundamentalDiscr D) :
    (kronecker D hD.ne_zero).IsPrimitive :=
  conductor_kronecker hD

end KroneckerPrim

#print axioms KroneckerPrim.witness_two
#print axioms KroneckerPrim.witness_odd
#print axioms KroneckerPrim.conductor_kronecker
