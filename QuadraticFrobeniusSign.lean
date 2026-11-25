import CyclotomicFrobenius

/-!
# QuadraticFrobeniusSign — how Frobenius acts on a square root: Euler's criterion

L = ℚ(ζ_N), y ∈ L with y² = m ∈ ℤ, m ≠ 0. Every σ ∈ Gal(L/ℚ) sends y to ±y (`sign_cases`);
`sgn σ ∈ {±1}` records which (`apply_eq_sgn`), and σ ↦ sgn σ is a homomorphism
`sgnHom : Gal(L/ℚ) →* ℤˣ`.
* `sgn_sigmaP`: for a prime q ∤ N, q ≠ 2, q ∤ m, the Frobenius σ_q (σ_q(ζ) = ζ^q) has
  sgn σ_q = (m/q), the Legendre symbol.
Proof: y is integral; σ_q y ≡ y^q = y·m^{(q−1)/2} mod P for a prime P | q (`sigmaP_isArithFrobAt`),
y ∉ P since q ∤ m, so sgn σ_q ≡ m^{(q−1)/2} ≡ (m/q) mod q (Euler's criterion, `legendreSym.eq_pow`);
both are ±1 and q is odd, so they are equal.
-/

open NumberField Ideal

namespace QuadFrobSign

variable {N : ℕ} [NeZero N] {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {N} ℚ L]
  {y : L} {m : ℤ} (hy : y ^ 2 = m) (hm : m ≠ 0)

include hy in
theorem sign_cases (σ : Gal(L/ℚ)) : σ y = y ∨ σ y = -y := by
  have h : (σ y) ^ 2 = y ^ 2 := by rw [← map_pow, hy, map_intCast]
  have : (σ y - y) * (σ y + y) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h | h
  · left; linear_combination h
  · right; linear_combination h

include hy hm in
theorem y_ne_zero : y ≠ 0 := by
  rintro rfl; apply hm; exact_mod_cast (by simpa using hy.symm : (m : L) = 0)

open Classical in
/-- sgn σ = 1 if σ fixes y, −1 otherwise. -/
noncomputable def sgn (y : L) (σ : Gal(L/ℚ)) : ℤˣ := if σ y = y then 1 else -1

include hy in
theorem apply_eq_sgn (σ : Gal(L/ℚ)) : σ y = ((sgn y σ : ℤ) : L) * y := by
  unfold sgn
  split_ifs with h
  · simp [h]
  · rcases sign_cases hy σ with h' | h'
    · exact absurd h' h
    · simp [h']

include hy hm in
theorem sgn_eq_iff (σ : Gal(L/ℚ)) (s : ℤˣ) : σ y = ((s : ℤ) : L) * y ↔ sgn y σ = s := by
  constructor
  · intro h
    have h2 := (apply_eq_sgn hy σ).symm.trans h
    have := mul_right_cancel₀ (y_ne_zero hy hm) h2
    exact Units.ext (by exact_mod_cast this)
  · rintro rfl; exact apply_eq_sgn hy σ

include hy hm in
/-- **σ ↦ sgn σ is a character Gal(L/ℚ) → {±1}.** -/
noncomputable def sgnHom : Gal(L/ℚ) →* ℤˣ where
  toFun := sgn y
  map_one' := by
    classical
    unfold sgn; simp
  map_mul' σ τ := by
    rw [← sgn_eq_iff hy hm, AlgEquiv.mul_apply, apply_eq_sgn hy τ, map_mul, map_intCast,
      apply_eq_sgn hy σ, Units.val_mul, Int.cast_mul]
    ring

theorem sgnHom_apply (σ : Gal(L/ℚ)) : sgnHom hy hm σ = sgn y σ := rfl

include hy in
/-- **Frobenius sign = Legendre symbol:** sgn σ_q = (m/q). -/
theorem sgn_sigmaP (q : ℕ) [hq : Fact q.Prime] (hqN : q.Coprime N) (hq2 : q ≠ 2)
    (hqm : ¬ (q : ℤ) ∣ m) :
    ((sgn y (CycloFrob.sigmaP N L q hqN) : ℤˣ) : ℤ) = legendreSym q m := by
  set σ := CycloFrob.sigmaP N L q hqN
  have hspan : (span {(q : ℤ)}).IsMaximal :=
    (Ideal.span_singleton_prime (by exact_mod_cast hq.out.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hq.out) |>.isMaximal (by simp [hq.out.ne_zero])
  obtain ⟨⟨P, _, _⟩⟩ := (span {(q : ℤ)}).nonempty_primesOver (S := 𝓞 L)
  have : P.IsMaximal := IsMaximal.of_liesOver_isMaximal P (span {(q : ℤ)})
  have hF := CycloFrob.sigmaP_isArithFrobAt q P hqN
  have hint : IsIntegral ℤ y := IsIntegral.of_pow (n := 2) (by norm_num)
    (by rw [hy, ← eq_intCast (algebraMap ℤ L)]; exact isIntegral_algebraMap)
  set Y : 𝓞 L := ⟨y, hint⟩
  have hY2 : Y ^ 2 = (m : 𝓞 L) := by
    apply RingOfIntegers.coe_injective
    simpa using (show (algebraMap (𝓞 L) L Y) ^ 2 = m from hy)
  -- membership of integers in P
  have hZ : ∀ z : ℤ, (z : 𝓞 L) ∈ P ↔ (q : ℤ) ∣ z := by
    intro z
    have : (z : 𝓞 L) ∈ P ↔ z ∈ P.under ℤ := by simp [Ideal.mem_comap]
    rw [this, ← (LiesOver.over : span {(q : ℤ)} = P.under ℤ), mem_span_singleton]
  have hYP : Y ∉ P := by
    intro h
    have : Y ^ 2 ∈ P := P.pow_mem_of_mem h 2 (by norm_num)
    rw [hY2, hZ] at this
    exact hqm this
  have hfrob : σ • Y - Y ^ q ∈ P := by
    have := hF Y
    rwa [CycloFrob.card_under q P] at this
  set s : ℤ := (sgn y σ : ℤ)
  have hsY : σ • Y = (s : 𝓞 L) * Y := by
    ext; show σ y = _; rw [apply_eq_sgn hy σ]; simp [s]; rfl
  have hodd : q = 2 * (q / 2) + 1 := by
    have := hq.out.eq_one_or_self_of_dvd 2
    omega
  have hYq : Y ^ q = Y * (m : 𝓞 L) ^ (q / 2) := by
    conv_lhs => rw [hodd, pow_add, pow_mul, hY2, pow_one]
    ring
  have hmem : ((s - m ^ (q / 2) : ℤ) : 𝓞 L) * Y ∈ P := by
    have : ((s - m ^ (q / 2) : ℤ) : 𝓞 L) * Y = σ • Y - Y ^ q := by
      rw [hsY, hYq]; push_cast; ring
    rw [this]; exact hfrob
  have hdvd : (q : ℤ) ∣ s - m ^ (q / 2) := by
    rcases (Ideal.IsPrime.mem_or_mem inferInstance hmem) with h | h
    · exact (hZ _).mp h
    · exact absurd h hYP
  -- Euler's criterion
  have heul := legendreSym.eq_pow q m
  have hcong : ((s : ℤ) : ZMod q) = (legendreSym q m : ZMod q) := by
    rw [heul, ← Int.cast_pow, ← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hdvd
  have hs : s = 1 ∨ s = -1 := by
    rcases Int.units_eq_one_or (sgn y σ) with h | h <;> simp [s, h]
  have hm0 : (m : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hqm
  have hl := legendreSym.eq_one_or_neg_one q hm0
  have hq3 : 2 < q := lt_of_le_of_ne hq.out.two_le (Ne.symm hq2)
  have h2 : ((2 : ℤ) : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro h
    have := Int.le_of_dvd (by norm_num) h
    omega
  rcases hs with hs | hs <;> rcases hl with hl | hl <;> rw [hs, hl] at hcong ⊢ <;>
    first
    | rfl
    | (exfalso; apply h2; push_cast at hcong ⊢; linear_combination hcong)
    | (exfalso; apply h2; push_cast at hcong ⊢; linear_combination -hcong)

end QuadFrobSign

#print axioms QuadFrobSign.sgnHom
#print axioms QuadFrobSign.sgn_sigmaP
