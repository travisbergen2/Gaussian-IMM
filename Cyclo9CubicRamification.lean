import Cyclo9CubicField
import CompositeLocalFactor

/-!
# Cyclo9CubicRamification — 3 is totally and wildly ramified in the cubic subfield of ℚ(ζ₉)

K = ℚ(ζ₉)^H, H = {1, 8}. Derived from the general decomposition/inertia machinery
(`CompositeLocal.fK_gK_ramified` with 9 = 3^{1+1}·1, `SubfieldDeg.gK_eK_fK`,
`CycloSub.gK_mul_fK`), not hardcoded:
* `data_three`: at 3, f = 1, g = 1, e = 3 (totally ramified); `wild_three`: 3 ∣ e (wild);
* `unramified`: every prime p ≠ 3 has e = 1, with g · f = 3.
-/

open NumberField Ideal GaloisEuler

namespace Cyclo9Cubic

variable {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {9} ℚ L]

local notation "K" => IntermediateField.fixedField (H (L := L))

theorem hn3 : (9 : ℕ) = 3 ^ (1 + 1) * 1 := by norm_num
theorem hm3 : ¬ (3 : ℕ) ∣ 1 := by decide

instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- **At 3: f = 1, g = 1, e = 3.** -/
theorem data_three :
    fK K 3 = 1 ∧ gK K 3 = 1 ∧ (span {((3 : ℕ) : ℤ)}).ramificationIdxIn (𝓞 K) = 3 := by
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {9} ℚ L
  obtain ⟨hf, hg⟩ := CompositeLocal.fK_gK_ramified (H (L := L)) hn3 hm3
  have hsub : Subsingleton (ZMod 1)ˣ := inferInstance
  have hord : ∀ x : (ZMod 1)ˣ ⧸ CompositeLocal.H'' (p := 3) (H (L := L)) hn3, orderOf x = 1 :=
    fun x => orderOf_eq_one_iff.mpr (QuotientGroup.induction_on x fun u => by
      rw [Subsingleton.elim u 1, QuotientGroup.mk_one])
  have hidx : (CompositeLocal.H'' (p := 3) (H (L := L)) hn3).index = 1 :=
    Subgroup.index_eq_one.mpr (Subsingleton.elim _ _)
  rw [hord] at hf hg
  rw [hidx] at hg
  have hgef := SubfieldDeg.gK_eK_fK (H (L := L)) 3
  rw [index_H] at hgef
  refine ⟨hf, hg, ?_⟩
  rw [gK] at hg; rw [fK] at hf
  rw [hf, hg] at hgef
  omega

/-- **3 is wildly ramified:** p = 3 divides e = 3. -/
theorem wild_three : 3 ∣ (span {((3 : ℕ) : ℤ)}).ramificationIdxIn (𝓞 K) := by
  rw [(data_three (L := L)).2.2]

/-- **Every prime p ≠ 3 is unramified in K**, with g · f = 3. -/
theorem unramified (p : ℕ) [Fact p.Prime] (hp3 : p ≠ 3) :
    (span {(p : ℤ)}).ramificationIdxIn (𝓞 K) = 1 ∧ gK K p * fK K p = 3 := by
  have hcop : p.Coprime 9 := by
    have : p.Coprime 3 := (Nat.coprime_primes Fact.out Nat.prime_three).mpr hp3
    simpa using this.pow_right 2
  obtain ⟨he, hgf⟩ := CycloSub.gK_mul_fK 9 L (H (L := L)) p hcop
  rw [index_H] at hgf
  exact ⟨he, hgf⟩

end Cyclo9Cubic

#print axioms Cyclo9Cubic.data_three
#print axioms Cyclo9Cubic.unramified
