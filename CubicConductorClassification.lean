import CubicCharacterAssembly

/-!
# CubicConductorClassification — conductors of primitive cubic characters

Pure character theory (no number fields). For Ψ primitive mod N with Ψ³ = 1, Ψ ≠ 1:
* `ker_pow`: on ker((ℤ/N)ˣ → (ℤ/d)ˣ), u^c = 1 where c · φ(d) = φ(N);
* `dvd_of_ker_trivial`: if Ψ is trivial on that kernel (d ∣ N), then N ∣ d — primitivity;
* `not_sq_dvd`: p² ∤ N for primes p ≠ 3 (kernel of order p, coprime to 3);
* `three_dvd_sub_one`: p ∥ N ⇒ 3 ∣ p − 1 (kernel ≅ (ℤ/p)ˣ of order p − 1); so p ≠ 2, 3 there,
  and 3 ∣ N ⇒ 9 ∣ N;
* `not_27_dvd`: 27 ∤ N (if N = 27M, every u ≡ 1 mod 9M is a cube: (1 + 3Mt)³ ≡ 1 + 9Mt);
* `classification`: N = 9^a · q₁ ⋯ q_r, a ∈ {0,1}, distinct primes qᵢ ≡ 1 (mod 3), not both
  trivial;
* `hasPrimCubic_iff`: with `CubicAssembly.hasPrimCubic_conductor`, a primitive cubic character
  of conductor N exists **iff** N has that form.
-/

open DirichletCharacter

namespace CubicClass

variable {N : ℕ} [NeZero N] {Ψ : DirichletCharacter ℂ N}

/-- On ker((ℤ/N)ˣ → (ℤ/d)ˣ), u^c = 1 for c = φ(N)/φ(d). -/
theorem ker_pow {d : ℕ} (hd : d ∣ N) :
    ∃ c, c * d.totient = N.totient ∧ ∀ u ∈ (ZMod.unitsMap hd).ker, u ^ c = 1 := by
  have : NeZero d := ⟨fun h => NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ hd))⟩
  refine ⟨Nat.card (ZMod.unitsMap hd).ker, ?_, fun u hu => ?_⟩
  · have h := (ZMod.unitsMap hd).ker.card_mul_index
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (ZMod.unitsMap_surjective hd),
      Subgroup.card_top] at h
    simpa only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] using h
  · have := pow_card_eq_one' (x := (⟨u, hu⟩ : (ZMod.unitsMap hd).ker))
    exact congrArg Subtype.val this

/-- **Primitivity:** Ψ trivial on ker((ℤ/N)ˣ → (ℤ/d)ˣ) ⇒ N ∣ d. -/
theorem dvd_of_ker_trivial (hp : Ψ.IsPrimitive) {d : ℕ} (hd : d ∣ N)
    (h : ∀ u ∈ (ZMod.unitsMap hd).ker, Ψ u = 1) : N ∣ d := by
  have hf : Ψ.FactorsThrough d := by
    rw [factorsThrough_iff_ker_unitsMap hd]
    intro u hu
    rw [MonoidHom.mem_ker]; apply Units.ext
    rw [MulChar.coe_toUnitHom, Units.val_one]; exact h u hu
  have := (mem_conductorSet_iff_conductor_dvd Ψ hd).mp hf
  rwa [hp] at this

/-- Ψ³ = 1 and u^c = 1 on the kernel, c coprime to 3 ⇒ N ∣ d. -/
theorem dvd_of_coprime (h3 : Ψ ^ 3 = 1) (hp : Ψ.IsPrimitive) {d : ℕ} (hd : d ∣ N) {c : ℕ}
    (hc : c.Coprime 3) (hpow : ∀ u ∈ (ZMod.unitsMap hd).ker, u ^ c = 1) : N ∣ d := by
  apply dvd_of_ker_trivial hp hd
  intro u hu
  have h1 : (Ψ u) ^ c = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hpow u hu, Units.val_one, map_one]
  have h2 : (Ψ u) ^ 3 = 1 := by
    rw [← MulChar.pow_apply' _ (by norm_num), h3, MulChar.one_apply u.isUnit]
  have := pow_gcd_eq_one.mpr ⟨h1, h2⟩
  rwa [hc, pow_one] at this

theorem lt_of_mul {p d : ℕ} (hp : p.Prime) (hN : N = p * d) : ¬ N ∣ d := by
  intro h
  have hd0 : d ≠ 0 := by rintro rfl; exact NeZero.ne N (by rw [hN, mul_zero])
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) h
  rw [hN] at this
  have := hp.two_le
  nlinarith [Nat.pos_of_ne_zero hd0]

/-- **p² ∤ N for primes p ≠ 3.** -/
theorem not_sq_dvd (h3 : Ψ ^ 3 = 1) (hp : Ψ.IsPrimitive) {p : ℕ} (hpp : p.Prime) (hp3 : p ≠ 3) :
    ¬ p ^ 2 ∣ N := by
  rintro ⟨k, hk⟩
  have hN : N = p * (p * k) := by rw [hk]; ring
  have hd : p * k ∣ N := ⟨p, by rw [hN]; ring⟩
  obtain ⟨c, hc, hpow⟩ := ker_pow (N := N) hd
  have htot : N.totient = p * (p * k).totient := by
    rw [hN]
    first
    | exact Nat.totient_mul_of_dvd (dvd_mul_right p k)
    | exact Nat.totient_mul_of_prime_of_dvd hpp (dvd_mul_right p k)
  have hpos : 0 < (p * k).totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (fun h => by
    apply NeZero.ne N; rw [hN, h, mul_zero]))
  have hcp : c = p := by
    rw [htot] at hc; exact Nat.eq_of_mul_eq_mul_right hpos hc
  subst hcp
  exact lt_of_mul hpp hN (dvd_of_coprime h3 hp hd
    ((Nat.coprime_primes hpp Nat.prime_three).mpr hp3) hpow)

/-- **p ∥ N ⇒ 3 ∣ p − 1.** -/
theorem three_dvd_sub_one (h3 : Ψ ^ 3 = 1) (hp : Ψ.IsPrimitive) {p : ℕ} (hpp : p.Prime)
    (hpN : p ∣ N) (hsq : ¬ p ^ 2 ∣ N) : 3 ∣ p - 1 := by
  obtain ⟨d, hN⟩ := hpN
  have hpd : ¬ p ∣ d := by
    rintro ⟨k, rfl⟩; exact hsq ⟨k, by rw [hN]; ring⟩
  have hd : d ∣ N := ⟨p, by rw [hN]; ring⟩
  obtain ⟨c, hc, hpow⟩ := ker_pow (N := N) hd
  have htot : N.totient = (p - 1) * d.totient := by
    rw [hN]; exact Nat.totient_mul_of_prime_of_not_dvd hpp hpd
  have hpos : 0 < d.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (fun h => by
    apply NeZero.ne N; rw [hN, h, mul_zero]))
  have hcp : c = p - 1 := by
    rw [htot] at hc; exact Nat.eq_of_mul_eq_mul_right hpos hc
  subst hcp
  by_contra h
  exact lt_of_mul hpp hN (dvd_of_coprime h3 hp hd
    (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h)) hpow)

/-- **27 ∤ N:** for N = 27M every u ≡ 1 (mod 9M) is a cube, so Ψ is trivial there. -/
theorem not_27_dvd (h3 : Ψ ^ 3 = 1) (hp : Ψ.IsPrimitive) : ¬ 27 ∣ N := by
  rintro ⟨M, hM⟩
  have hM0 : 0 < M := Nat.pos_of_ne_zero (fun h => NeZero.ne N (by rw [hM, h, mul_zero]))
  have hd : 9 * M ∣ N := ⟨3, by rw [hM]; ring⟩
  have key := dvd_of_ker_trivial hp hd (fun u hu => by
    rw [MonoidHom.mem_ker] at hu
    have hu' := congrArg Units.val hu
    rw [ZMod.unitsMap_val, Units.val_one, ZMod.cast_eq_val] at hu'
    set x := (u : ZMod N).val with hx
    have hmod : x % (9 * M) = 1 := by
      have := (ZMod.natCast_eq_natCast_iff' x 1 (9 * M)).mp (by rw [hu', Nat.cast_one])
      rw [this]; exact Nat.mod_eq_of_lt (by omega)
    set t := x / (9 * M)
    have hxt : x = 9 * M * t + 1 := by rw [← hmod]; exact (Nat.div_add_mod x (9 * M)).symm
    set y := 1 + 3 * M * t
    have hy : y ^ 3 = x + N * (M * t ^ 2 + M ^ 2 * t ^ 3) := by rw [hxt, hM]; ring
    have hyu : ((y : ZMod N)) ^ 3 = (u : ZMod N) := by
      rw [← Nat.cast_pow, hy, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero,
        hx, ZMod.natCast_zmod_val]
    have hyunit : IsUnit (y : ZMod N) :=
      (isUnit_pow_iff (by norm_num : (3 : ℕ) ≠ 0)).mp (hyu ▸ u.isUnit)
    rw [← hyu, map_pow, ← MulChar.pow_apply' _ (by norm_num), h3, MulChar.one_apply hyunit])
  exact lt_of_mul Nat.prime_three (show N = 3 * (9 * M) by rw [hM]; ring) key

/-- **Classification:** N = 9^a · q₁ ⋯ q_r with a ∈ {0,1}, distinct primes qᵢ ≡ 1 (mod 3). -/
theorem classification (h3 : Ψ ^ 3 = 1) (hne : Ψ ≠ 1) (hp : Ψ.IsPrimitive) :
    ∃ a : Bool, ∃ qs : List ℕ, qs.Nodup ∧ (∀ q ∈ qs, q.Prime) ∧ (∀ q ∈ qs, 3 ∣ q - 1) ∧
      (a = true ∨ qs ≠ []) ∧ N = (if a then 9 else 1) * qs.prod := by
  have h27 := not_27_dvd h3 hp
  have h3N : 3 ∣ N → 9 ∣ N := fun h => by
    by_contra h9
    have := three_dvd_sub_one h3 hp Nat.prime_three h (by simpa using h9)
    norm_num at this
  set a := decide (9 ∣ N)
  set m := if 9 ∣ N then N / 9 else N with hm
  have hNm : N = (if a then 9 else 1) * m := by
    by_cases h9 : 9 ∣ N
    · simp [a, hm, h9, Nat.mul_div_cancel' h9]
    · simp [a, hm, h9]
  have hm0 : m ≠ 0 := fun h => NeZero.ne N (by rw [hNm, h, mul_zero])
  have hmN : m ∣ N := ⟨_, by rw [hNm, mul_comm]⟩
  have h3m : ¬ 3 ∣ m := by
    intro h
    by_cases h9 : 9 ∣ N
    · obtain ⟨k, hk⟩ := h
      apply h27
      have : N = 9 * m := by rw [hm, if_pos h9, Nat.mul_div_cancel' h9]
      exact ⟨k, by rw [this, hk]; ring⟩
    · exact h9 (h3N (dvd_trans h (by rw [hm, if_neg h9])))
  have hsq : Squarefree m := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro x hx hxx
    have hx3 : x ≠ 3 := by rintro rfl; exact h3m (dvd_trans (dvd_mul_right 3 3) hxx)
    exact not_sq_dvd h3 hp hx hx3 (by rw [sq]; exact dvd_trans hxx hmN)
  refine ⟨a, m.primeFactorsList, (Nat.squarefree_iff_nodup_primeFactorsList hm0).mp hsq,
    fun q hq => Nat.prime_of_mem_primeFactorsList hq, fun q hq => ?_, ?_, ?_⟩
  · have hqp := Nat.prime_of_mem_primeFactorsList hq
    have hqm := Nat.dvd_of_mem_primeFactorsList hq
    have hq3 : q ≠ 3 := by rintro rfl; exact h3m hqm
    exact three_dvd_sub_one h3 hp hqp (dvd_trans hqm hmN) (not_sq_dvd h3 hp hqp hq3)
  · by_contra h
    obtain ⟨ha, hqs⟩ := not_or.mp h
    have hqs : m.primeFactorsList = [] := not_not.mp hqs
    have hm1 : m = 1 := by
      rw [← Nat.prod_primeFactorsList hm0, hqs, List.prod_nil]
    have hN1 : N = 1 := by rw [hNm, hm1]; simp [Bool.eq_false_iff.mpr ha]
    apply hne
    apply eq_one_iff_conductor_eq_one.mpr
    rw [hp, hN1]
  · rw [Nat.prod_primeFactorsList hm0]; exact hNm

/-- **A primitive cubic character of conductor N exists iff N = 9^a · q₁ ⋯ q_r.** -/
theorem hasPrimCubic_iff (N : ℕ) : CubicAssembly.HasPrimCubic N ↔
    ∃ a : Bool, ∃ qs : List ℕ, qs.Nodup ∧ (∀ q ∈ qs, q.Prime) ∧ (∀ q ∈ qs, 3 ∣ q - 1) ∧
      (a = true ∨ qs ≠ []) ∧ N = (if a then 9 else 1) * qs.prod := by
  constructor
  · rintro ⟨hN, Ψ, h3, hne, hp⟩
    have : NeZero N := ⟨by omega⟩
    exact classification h3 hne hp
  · rintro ⟨a, qs, hnd, hpr, hmod, hne, rfl⟩
    exact CubicAssembly.hasPrimCubic_conductor qs hnd hpr hmod a hne

end CubicClass

#print axioms CubicClass.not_sq_dvd
#print axioms CubicClass.three_dvd_sub_one
#print axioms CubicClass.not_27_dvd
#print axioms CubicClass.classification
#print axioms CubicClass.hasPrimCubic_iff
