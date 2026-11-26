import ConductorProduct
import ConductorCongruence

/-!
# CubicCharacterAssembly — primitive cubic characters of conductor 9^a · q₁ ⋯ q_r

Generic (imports only Mathlib-level files; no number fields). `IsPrimCubic ψ`: ψ³ = 1, ψ ≠ 1,
ψ primitive. `HasPrimCubic M`: 1 < M and some ψ mod M is `IsPrimCubic` (so its conductor is M).
* `hasPrimCubic_prime`: every prime q ≡ 1 (mod 3) (order-3 character mod q; prime level ⇒ primitive);
* `chi9`: an explicit order-3 character mod 9 (u = 2^k ↦ ω^k), `hasPrimCubic_nine`
  (conductor 9: 4 ≡ 1 mod 3 but χ₉(4) = ω² ≠ 1) — the conductor-9 part is an ordinary local
  component;
* `hasPrimCubic_mul`: coprime levels multiply (`CondProd.conductor_mulLift`,
  `CondProd.mulLift_pow_three`): the product of the local characters is primitive cubic of
  conductor the product of the levels;
* `hasPrimCubic_list`: any nonempty pairwise-coprime family (induction);
* `hasPrimCubic_conductor`: for distinct primes qᵢ ≡ 1 (mod 3) and a ∈ {0, 1}, not both empty,
  there is a primitive cubic character of conductor 9^a · ∏ qᵢ.
-/

open DirichletCharacter

namespace CubicAssembly

/-- ψ³ = 1, ψ ≠ 1, ψ primitive. -/
def IsPrimCubic {M : ℕ} (ψ : DirichletCharacter ℂ M) : Prop :=
  ψ ^ 3 = 1 ∧ ψ ≠ 1 ∧ ψ.IsPrimitive

/-- Some primitive cubic character has conductor M. -/
def HasPrimCubic (M : ℕ) : Prop := 1 < M ∧ ∃ ψ : DirichletCharacter ℂ M, IsPrimCubic ψ

/-- **Coprime levels multiply.** -/
theorem hasPrimCubic_mul {m n : ℕ} (hm : HasPrimCubic m) (hn : HasPrimCubic n)
    (hcop : m.Coprime n) : HasPrimCubic (m * n) := by
  obtain ⟨hm1, ψ₁, h₁3, h₁1, h₁p⟩ := hm
  obtain ⟨hn1, ψ₂, h₂3, -, h₂p⟩ := hn
  have : NeZero m := ⟨by omega⟩
  have : NeZero n := ⟨by omega⟩
  obtain ⟨h3, h1⟩ := CondProd.mulLift_pow_three hcop h₁3 h₂3 h₁1
  exact ⟨by nlinarith, CondProd.mulLift ψ₁ ψ₂, h3, h1, CondProd.isPrimitive_mulLift hcop h₁p h₂p⟩

/-- **Finite pairwise-coprime families.** -/
theorem hasPrimCubic_list : ∀ l : List ℕ, l ≠ [] → (∀ N ∈ l, HasPrimCubic N) →
    l.Pairwise Nat.Coprime → HasPrimCubic l.prod
  | [], h, _, _ => absurd rfl h
  | [a], _, hP, _ => by simpa using hP a (by simp)
  | a :: b :: t, _, hP, hpw => by
    rw [List.pairwise_cons] at hpw
    rw [List.prod_cons]
    apply hasPrimCubic_mul (hP a (by simp))
      (hasPrimCubic_list (b :: t) (by simp) (fun N hN => hP N (by simp [hN])) hpw.2)
    exact Nat.coprime_list_prod_right_iff.mpr hpw.1

/-- **Primes q ≡ 1 (mod 3).** -/
theorem hasPrimCubic_prime {q : ℕ} (hq : q.Prime) (hq3 : 3 ∣ q - 1) : HasPrimCubic q := by
  have : Fact q.Prime := ⟨hq⟩
  have hμ := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  obtain ⟨χ, hχ⟩ := MulChar.exists_mulChar_orderOf (ZMod q) (by rwa [ZMod.card]) hμ
  have h3 : χ ^ 3 = 1 := by rw [← hχ]; exact pow_orderOf_eq_one χ
  have hne : χ ≠ 1 := by rintro rfl; rw [orderOf_one] at hχ; norm_num at hχ
  refine ⟨hq.one_lt, χ, h3, hne, ?_⟩
  show conductor χ = q
  rcases (Nat.dvd_prime hq).mp (conductor_dvd_level χ) with h | h
  · exact absurd (eq_one_iff_conductor_eq_one.mpr h) hne
  · exact h

/-! ### The local character at 9 -/

/-- Discrete log base 2 mod 9, reduced mod 3 (2 has order 6). -/
def dlog9 : ZMod 9 → ZMod 3 := ![0, 0, 1, 0, 2, 2, 0, 1, 0]

theorem dlog9_mul : ∀ x y : ZMod 9, x.val.Coprime 9 → y.val.Coprime 9 →
    dlog9 (x * y) = dlog9 x + dlog9 y := by decide

theorem coprime_mul_iff : ∀ x y : ZMod 9,
    (x * y).val.Coprime 9 ↔ x.val.Coprime 9 ∧ y.val.Coprime 9 := by decide

/-- ω = e^{2πi/3}. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

theorem hω : IsPrimitiveRoot ω 3 := Complex.isPrimitiveRoot_exp 3 (by norm_num)

theorem ω_pow_add (a b : ZMod 3) : ω ^ (a + b).val = ω ^ a.val * ω ^ b.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.div_add_mod (a.val + b.val) 3, pow_add, pow_mul, hω.pow_eq_one, one_pow,
    one_mul]

open Classical in
/-- **χ₉**: u = 2^k ↦ ω^k on units mod 9. -/
noncomputable def chi9 : DirichletCharacter ℂ 9 where
  toFun x := if x.val.Coprime 9 then ω ^ (dlog9 x).val else 0
  map_one' := by
    rw [if_pos (by decide)]
    rw [show dlog9 1 = 0 by decide, ZMod.val_zero, pow_zero]
  map_mul' x y := by
    by_cases hx : x.val.Coprime 9 <;> by_cases hy : y.val.Coprime 9
    · rw [if_pos ((coprime_mul_iff x y).mpr ⟨hx, hy⟩), if_pos hx, if_pos hy, dlog9_mul x y hx hy,
        ω_pow_add]
    · rw [if_neg (fun h => hy ((coprime_mul_iff x y).mp h).2), if_neg hy, mul_zero]
    · rw [if_neg (fun h => hx ((coprime_mul_iff x y).mp h).1), if_neg hx, zero_mul]
    · rw [if_neg (fun h => hx ((coprime_mul_iff x y).mp h).1), if_neg hx, zero_mul]
  map_nonunit' x hx := by
    have : ¬ x.val.Coprime 9 := by
      intro h; apply hx
      rw [← ZMod.natCast_zmod_val x]; exact (ZMod.isUnit_iff_coprime _ _).mpr h
    show (if x.val.Coprime 9 then ω ^ (dlog9 x).val else 0) = 0
    rw [if_neg this]

theorem chi9_apply_unit (u : (ZMod 9)ˣ) : chi9 u = ω ^ (dlog9 u).val := by
  have hu : (u : ZMod 9).val.Coprime 9 := ZMod.val_coe_unit_coprime u
  show (if (u : ZMod 9).val.Coprime 9 then ω ^ (dlog9 u).val else 0) = _
  rw [if_pos hu]

theorem chi9_cube : chi9 ^ 3 = 1 := by
  apply MulChar.ext
  intro u
  rw [MulChar.pow_apply' _ (by norm_num), chi9_apply_unit, ← pow_mul, mul_comm, pow_mul,
    hω.pow_eq_one, one_pow, MulChar.one_apply u.isUnit]

theorem chi9_four : chi9 ((4 : ℕ) : ZMod 9) = ω ^ 2 := by
  show (if ((4 : ℕ) : ZMod 9).val.Coprime 9 then ω ^ (dlog9 ((4 : ℕ) : ZMod 9)).val else 0) = _
  rw [if_pos (by decide), show (dlog9 ((4 : ℕ) : ZMod 9)).val = 2 by decide]

theorem chi9_one : chi9 ((1 : ℕ) : ZMod 9) = 1 := by rw [Nat.cast_one, map_one]

/-- **9 carries a primitive cubic character** (conductor exactly 9). -/
theorem hasPrimCubic_nine : HasPrimCubic 9 := by
  have hω2 : ω ^ 2 ≠ 1 := hω.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hne : chi9 ≠ 1 := by
    intro h
    have := chi9_four
    rw [h, MulChar.one_apply (by decide)] at this
    exact hω2 this.symm
  refine ⟨by norm_num, chi9, chi9_cube, hne, ?_⟩
  show conductor chi9 = 9
  have hmem : conductor chi9 ∈ Nat.divisors 9 :=
    Nat.mem_divisors.mpr ⟨conductor_dvd_level chi9, by norm_num⟩
  rw [show Nat.divisors 9 = {1, 3, 9} by decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h
  · exact absurd (eq_one_iff_conductor_eq_one.mpr h) hne
  · exfalso
    have hf := factorsThrough_conductor chi9
    rw [h] at hf
    exact CondCong.not_factorsThrough chi9 (a := 4) (b := 1) (by norm_num) (by norm_num)
      (by decide) (by rw [chi9_four, chi9_one]; exact hω2) hf
  · exact h

/-! ### The general conductor -/

/-- **Primitive cubic characters of conductor 9^a · q₁ ⋯ q_r.** -/
theorem hasPrimCubic_conductor (qs : List ℕ) (hnd : qs.Nodup) (hprime : ∀ q ∈ qs, q.Prime)
    (hmod : ∀ q ∈ qs, 3 ∣ q - 1) (a : Bool) (hne : a = true ∨ qs ≠ []) :
    HasPrimCubic ((if a then 9 else 1) * qs.prod) := by
  have hq3 : ∀ q ∈ qs, q ≠ 3 := fun q hq h => by
    have := hmod q hq; rw [h] at this; norm_num at this
  have hpw : qs.Pairwise Nat.Coprime := by
    refine (List.pairwise_iff_get.mpr ?_)
    intro i j hij
    have hne : qs.get i ≠ qs.get j := fun h =>
      (ne_of_lt hij) (List.Nodup.get_inj_iff hnd |>.mp h)
    exact (Nat.coprime_primes (hprime _ (List.get_mem _ _)) (hprime _ (List.get_mem _ _))).mpr hne
  cases a with
  | false =>
    simp only [Bool.false_eq_true, if_false, one_mul]
    exact hasPrimCubic_list qs (by simpa using hne) (fun q hq => hasPrimCubic_prime
      (hprime q hq) (hmod q hq)) hpw
  | true =>
    simp only [if_true]
    rw [← List.prod_cons]
    apply hasPrimCubic_list (9 :: qs) (by simp)
    · intro N hN
      rcases List.mem_cons.mp hN with rfl | hN
      · exact hasPrimCubic_nine
      · exact hasPrimCubic_prime (hprime N hN) (hmod N hN)
    · refine List.Pairwise.cons (fun q hq => ?_) hpw
      have : Nat.Coprime 3 q := (Nat.coprime_primes Nat.prime_three (hprime q hq)).mpr
        (Ne.symm (hq3 q hq))
      simpa using this.pow_left 2

end CubicAssembly

#print axioms CubicAssembly.hasPrimCubic_mul
#print axioms CubicAssembly.hasPrimCubic_list
#print axioms CubicAssembly.hasPrimCubic_prime
#print axioms CubicAssembly.hasPrimCubic_nine
#print axioms CubicAssembly.hasPrimCubic_conductor
