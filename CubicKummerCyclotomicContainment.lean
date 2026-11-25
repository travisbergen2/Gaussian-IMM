import CubicGaussSumIdentity

/-!
# CubicKummerCyclotomicContainment — ℚ(ω)(∛(qJ)) = ℚ(ω, g(χ)) ⊆ ℚ(ζ_{3q})

q a prime with 3 ∣ q − 1, L = ℚ(ζ_{3q}) (`IsCyclotomicExtension {3q} ℚ L`), ζ = ζ_{3q},
ω = ζ^q (a primitive cube root of unity), ζ_q = ζ³, K₀ = ℚ⟮ω⟯ ≤ L.
χ : ZMod q → L of order 3, ψ(a) = ζ_q^a, g = g(χ) = Σ χ(a) ζ_q^a ∈ L, J = J(χ, χ).
* `chi_mem`, `J_mem`: χ(a) ∈ K₀ and J ∈ K₀ (values are cube roots of unity or 0);
* `gauss_cube`: the explicit root witness g ∈ ℚ(ζ_{3q}) of X³ − qJ: g³ = qJ;
* `tau`: σ_a with a ≡ 1 (mod 3), χ(a) ≠ 1 (CRT); it fixes ω, and σ_a(g) = χ(a)⁻¹ g
  (`gaussSum_mulShift`), so σ_a(g) ≠ g;
* `g_not_mem`: g ∉ K₀;
* `minpoly_g`: minpoly over K₀ of g is X³ − qJ (irreducible: a cube root of qJ in K₀ would be
  ω^k g ∈ K₀), so [K₀(g) : K₀] = 3 — g generates the Kummer extension K₀(∛(qJ));
* `cube_roots`: every y ∈ L with y³ = qJ is ω^k·g, so K₀(y) = K₀(g) ⊆ L for every chosen cube root.
-/

open Polynomial IntermediateField IsCyclotomicExtension

namespace CubicKummer

variable {q : ℕ} [hq : Fact q.Prime] (hq3 : 3 ∣ q - 1)
  {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {3 * q} ℚ L]

local notation "ζ" => IsCyclotomicExtension.zeta (3 * q) ℚ L

instance : NeZero (3 * q) := ⟨Nat.mul_ne_zero (by norm_num) hq.out.ne_zero⟩

theorem hζ : IsPrimitiveRoot (ζ) (3 * q) := zeta_spec (3 * q) ℚ L

/-- ω = ζ^q, a primitive cube root of unity. -/
noncomputable def ω : L := (ζ) ^ q
/-- ζ_q = ζ³, a primitive q-th root of unity. -/
noncomputable def ζq : L := (ζ) ^ 3

theorem hω : IsPrimitiveRoot (ω (q := q) (L := L)) 3 :=
  (hζ (q := q) (L := L)).pow (NeZero.pos _) (by ring)
theorem hζq : IsPrimitiveRoot (ζq (q := q) (L := L)) q :=
  (hζ (q := q) (L := L)).pow (NeZero.pos _) (by ring)

/-- The additive character a ↦ ζ_q^a. -/
noncomputable def ψ : AddChar (ZMod q) L := AddChar.zmodChar q (hζq (q := q) (L := L)).pow_eq_one

theorem ψ_prim : (ψ (q := q) (L := L)).IsPrimitive :=
  AddChar.zmodChar_primitive_of_primitive_root q (hζq (q := q) (L := L))

include hq3 in
/-- A cubic character χ : ZMod q → L exists (values in ⟨ω⟩). -/
theorem exists_chi : ∃ χ : MulChar (ZMod q) L, orderOf χ = 3 :=
  MulChar.exists_mulChar_orderOf (ZMod q) (by rwa [ZMod.card]) (hω (q := q) (L := L))

variable {χ : MulChar (ZMod q) L} (hχ : orderOf χ = 3)

local notation "K₀" => ℚ⟮(ω (q := q) (L := L))⟯

include hχ in
theorem chi_mem (x : ZMod q) : χ x ∈ K₀ := by
  by_cases hx : IsUnit x
  · have h3 : (χ x) ^ 3 = 1 := by
      rw [← MulChar.pow_apply' _ (by norm_num), CubicGauss.pow_three hχ, MulChar.one_apply hx]
    obtain ⟨i, -, hi⟩ := (hω (q := q) (L := L)).eq_pow_of_pow_eq_one h3
    rw [← hi]
    exact pow_mem (mem_adjoin_simple_self ℚ _) i
  · rw [MulChar.map_nonunit _ hx]; exact zero_mem _

include hχ in
theorem J_mem : jacobiSum χ χ ∈ K₀ :=
  sum_mem fun x _ => mul_mem (chi_mem hχ x) (chi_mem hχ _)

include hχ in
/-- **g³ = qJ** with g ∈ ℚ(ζ_{3q}). -/
theorem gauss_cube : gaussSum χ ψ ^ 3 = q * jacobiSum χ χ := by
  rw [CubicGauss.gaussSum_cube hχ ψ_prim, ZMod.card]

omit [NumberField L] [IsCyclotomicExtension {3 * q} ℚ L] in
theorem pow_mod_q {z : L} (hz : z ^ q = 1) (n : ℕ) : z ^ n = z ^ (n % q) := by
  conv_lhs => rw [← Nat.div_add_mod n q, pow_add, pow_mul, hz, one_pow, one_mul]

include hq3 hχ in
/-- A Galois parameter: a < 3q, a ≡ 1 (mod 3), a coprime to 3q, χ(a) ≠ 1. -/
theorem exists_a : ∃ a : ℕ, a < 3 * q ∧ a % 3 = 1 ∧ a.Coprime (3 * q) ∧ χ (a : ZMod q) ≠ 1 := by
  obtain ⟨u, hu⟩ := MulChar.ne_one_iff.mp (CubicGauss.ne_one hχ)
  have hq3' : q ≠ 3 := by rintro rfl; norm_num at hq3
  have hcop : Nat.Coprime 3 q := (Nat.coprime_primes Nat.prime_three hq.out).mpr (Ne.symm hq3')
  set r := (u : ZMod q).val
  let k := Nat.chineseRemainder hcop 1 r
  have hk1 : k.1 ≡ 1 [MOD 3] := k.2.1
  have hkr : k.1 ≡ r [MOD q] := k.2.2
  have hklt : k.1 < 3 * q := Nat.chineseRemainder_lt_mul hcop 1 r (by norm_num) hq.out.ne_zero
  have hkq : (k.1 : ZMod q) = u := by
    rw [← ZMod.natCast_zmod_val (u : ZMod q), ZMod.natCast_eq_natCast_iff]; exact hkr
  refine ⟨k.1, hklt, by unfold Nat.ModEq at hk1; omega, ?_, by rw [hkq]; exact hu⟩
  apply Nat.Coprime.mul_right
  · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    unfold Nat.ModEq at hk1; omega
  · rw [← ZMod.isUnit_iff_coprime, hkq]; exact u.isUnit

/-- τ = σ_a : ζ ↦ ζ^a. -/
noncomputable def tau (a : ℕ) (ha : a.Coprime (3 * q)) : Gal(L/ℚ) :=
  (Rat.galEquivZMod (3 * q) L).symm (ZMod.unitOfCoprime a ha)

theorem tau_ζ {a : ℕ} (ha : a.Coprime (3 * q)) (hlt : a < 3 * q) : tau a ha (ζ) = (ζ) ^ a := by
  have := Rat.galEquivZMod_apply_of_pow_eq (3 * q) L (tau a ha) (hζ (q := q) (L := L)).pow_eq_one
  rw [this, tau, MulEquiv.apply_symm_apply, ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt hlt]

theorem tau_ω {a : ℕ} (ha : a.Coprime (3 * q)) (hlt : a < 3 * q) (h1 : a % 3 = 1) :
    tau a ha (ω (q := q) (L := L)) = ω (q := q) (L := L) := by
  rw [ω, map_pow, tau_ζ ha hlt, ← pow_mul]
  have : a * q = 3 * q * (a / 3) + q := by
    conv_lhs => rw [← Nat.div_add_mod a 3, h1]
    ring
  rw [this, pow_add, pow_mul, (hζ (q := q) (L := L)).pow_eq_one, one_pow, one_mul]

theorem tau_ζq {a : ℕ} (ha : a.Coprime (3 * q)) (hlt : a < 3 * q) :
    tau a ha (ζq (q := q) (L := L)) = (ζq (q := q) (L := L)) ^ a := by
  rw [ζq, map_pow, tau_ζ ha hlt, ← pow_mul, ← pow_mul, Nat.mul_comm a 3]

theorem tau_fixes {a : ℕ} (ha : a.Coprime (3 * q)) (hlt : a < 3 * q) (h1 : a % 3 = 1)
    {x : L} (hx : x ∈ K₀) : tau a ha x = x := by
  have hle : Algebra.adjoin ℚ {(ω (q := q) (L := L))} ≤
      AlgHom.equalizer (tau a ha).toAlgHom (AlgHom.id ℚ L) :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr (by
      rw [SetLike.mem_coe, AlgHom.mem_equalizer, AlgHom.id_apply]
      exact tau_ω ha hlt h1))
  have hx' : x ∈ (K₀).toSubalgebra := hx
  rw [adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic _)] at hx'
  exact hle hx'

include hχ in
/-- **σ_a(g) = g(χ, ψ_a)**, hence χ(a)·σ_a(g) = g. -/
theorem tau_gauss {a : ℕ} (ha : a.Coprime (3 * q)) (hlt : a < 3 * q) (h1 : a % 3 = 1) :
    tau a ha (gaussSum χ ψ) = gaussSum χ ((ψ (q := q) (L := L)).mulShift (a : ZMod q)) := by
  have hζq1 := (hζq (q := q) (L := L)).pow_eq_one
  simp only [gaussSum, map_sum, map_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [tau_fixes ha hlt h1 (chi_mem hχ x), AddChar.mulShift_apply, ψ, AddChar.zmodChar_apply,
    AddChar.zmodChar_apply, map_pow, tau_ζq ha hlt, ← pow_mul, ZMod.val_mul, ZMod.val_natCast,
    pow_mod_q hζq1 (a * x.val), Nat.mod_mul_mod]

include hq3 hχ in
/-- **g ∉ ℚ(ω).** -/
theorem g_not_mem : gaussSum χ ψ ∉ K₀ := by
  intro hg
  obtain ⟨a, hlt, h1, ha, hχa⟩ := exists_a hq3 hχ
  have hfix := tau_fixes ha hlt h1 hg
  rw [tau_gauss hχ ha hlt h1] at hfix
  have hau : IsUnit (a : ZMod q) :=
    (ZMod.isUnit_iff_coprime a q).mpr (Nat.Coprime.coprime_dvd_right (dvd_mul_left q 3) ha)
  have hm := gaussSum_mulShift χ ψ hau.unit
  rw [IsUnit.unit_spec, hfix] at hm
  have hne : gaussSum χ (ψ (q := q) (L := L)) ≠ 0 :=
    gaussSum_ne_zero_of_nontrivial (by rw [ZMod.card]; exact_mod_cast hq.out.ne_zero)
      (CubicGauss.ne_one hχ) ψ_prim
  apply hχa
  have := mul_right_cancel₀ hne (hm.trans (one_mul _).symm)
  exact this

include hχ in
theorem gauss_ne_zero : gaussSum χ (ψ (q := q) (L := L)) ≠ 0 :=
  gaussSum_ne_zero_of_nontrivial (by rw [ZMod.card]; exact_mod_cast hq.out.ne_zero)
    (CubicGauss.ne_one hχ) ψ_prim

include hχ in
/-- **Every cube root of qJ in ℚ(ζ_{3q}) is ω^k · g.** -/
theorem cube_roots {y : L} (hy : y ^ 3 = q * jacobiSum χ χ) :
    ∃ k < 3, y = (ω (q := q) (L := L)) ^ k * gaussSum χ ψ := by
  have hg := gauss_ne_zero hχ
  have h3 : (y / gaussSum χ ψ) ^ 3 = 1 := by
    rw [div_pow, hy, ← gauss_cube hχ, div_self (pow_ne_zero 3 hg)]
  obtain ⟨k, hk, hk'⟩ := (hω (q := q) (L := L)).eq_pow_of_pow_eq_one h3
  exact ⟨k, hk, by rw [hk', div_mul_cancel₀ _ hg]⟩

/-- qJ as an element of K₀. -/
noncomputable def c : K₀ :=
  ⟨q * jacobiSum χ χ, mul_mem (IntermediateField.natCast_mem _ q) (J_mem hχ)⟩

include hq3 hχ in
/-- **minpoly_{ℚ(ω)} g = X³ − qJ**: g generates the cubic Kummer extension ℚ(ω)(∛(qJ)). -/
theorem minpoly_g : minpoly K₀ (gaussSum χ ψ) = X ^ 3 - C (c hχ) := by
  have hirr : Irreducible (X ^ 3 - C (c hχ) : K₀[X]) := by
    apply X_pow_sub_C_irreducible_of_prime Nat.prime_three
    intro b hb
    have hb' : ((b : L)) ^ 3 = q * jacobiSum χ χ := by
      have := congrArg (fun z : K₀ => (z : L)) hb
      simpa [c] using this
    obtain ⟨k, -, hk⟩ := cube_roots hχ hb'
    apply g_not_mem hq3 hχ
    have hωk : (ω (q := q) (L := L)) ^ k ≠ 0 :=
      pow_ne_zero _ ((hω (q := q) (L := L)).ne_zero (by norm_num))
    have : gaussSum χ ψ = (b : L) / (ω (q := q) (L := L)) ^ k := by
      rw [hk, mul_div_cancel_left₀ _ hωk]
    rw [this]
    exact div_mem b.2 (pow_mem (mem_adjoin_simple_self ℚ _) k)
  refine (minpoly.eq_of_irreducible_of_monic hirr ?_ (by monicity!)).symm
  simp only [map_sub, map_pow, aeval_X, aeval_C]
  rw [gauss_cube hχ, sub_eq_zero]
  rfl

include hq3 hχ in
/-- **[ℚ(ω)(g) : ℚ(ω)] = 3.** -/
theorem finrank_kummer : Module.finrank K₀ K₀⟮gaussSum χ ψ⟯ = 3 := by
  have hint : IsIntegral K₀ (gaussSum χ (ψ (q := q) (L := L))) :=
    ⟨X ^ 3 - C (c hχ), by monicity!, by
      rw [← aeval_def]; simp only [map_sub, map_pow, aeval_X, aeval_C]
      rw [gauss_cube hχ, sub_eq_zero]; rfl⟩
  rw [adjoin.finrank hint, minpoly_g hq3 hχ]
  compute_degree!

end CubicKummer

#print axioms CubicKummer.exists_chi
#print axioms CubicKummer.gauss_cube
#print axioms CubicKummer.g_not_mem
#print axioms CubicKummer.cube_roots
#print axioms CubicKummer.minpoly_g
#print axioms CubicKummer.finrank_kummer
