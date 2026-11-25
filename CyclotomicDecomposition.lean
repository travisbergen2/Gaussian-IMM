import Mathlib

/-!
# CyclotomicDecomposition — inertia and decomposition groups at p ∣ n in ℚ(ζₙ)

Write n = p^{k+1} m with p ∤ m. Through Gal(ℚ(ζₙ)/ℚ) ≅ (ZMod n)ˣ and the reduction
red : (ZMod n)ˣ → (ZMod m)ˣ:

* `inertia_map`: the inertia group of any P above p is ker(red) (units ≡ 1 mod m);
* `stabilizer_map`: the decomposition group is red⁻¹⟨p mod m⟩.

Containments: η = ζ^{p^{k+1}} is a primitive m-th root of unity and stays primitive in the residue
field (p ∤ m); inertia fixes η̄, and the decomposition group acts on η̄ by a power of Frobenius,
i.e. η̄ ↦ η̄^{p^i}. Equality: cardinalities |I| = e = p^k(p−1) and |D| = e·f with f = ord_m(p)
(Mathlib), against |ker red| = φ(n)/φ(m) and |red⁻¹⟨p⟩|.
No project imports.
-/

open NumberField IsCyclotomicExtension IsCyclotomicExtension.Rat Ideal MulAction
open scoped Pointwise

namespace CycloDecomp

variable {n m p k : ℕ} [NeZero n] {L : Type*} [Field L] [NumberField L]
  [IsCyclotomicExtension {n} ℚ L] [hp : Fact (Nat.Prime p)]
  (P : Ideal (𝓞 L)) [P.IsMaximal] [P.LiesOver (span {(p : ℤ)})]
  (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m)

attribute [local instance] Ideal.Quotient.field

include hn in
theorem m_dvd : m ∣ n := ⟨p ^ (k + 1), by rw [hn, mul_comm]⟩

include hn in
theorem m_pos : 0 < m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp at hn; exact absurd hn (NeZero.ne n)
  · exact h

/-- The reduction map (ZMod n)ˣ → (ZMod m)ˣ. -/
noncomputable abbrev red (hn : n = p ^ (k + 1) * m) : (ZMod n)ˣ →* (ZMod m)ˣ :=
  ZMod.unitsMap (m_dvd hn)

/-- η = ζ^{p^{k+1}}, a primitive m-th root of unity in 𝓞 L. -/
noncomputable def η (n p k : ℕ) [NeZero n] (L : Type*) [Field L] [NumberField L]
    [IsCyclotomicExtension {n} ℚ L] : 𝓞 L :=
  (zeta_spec n ℚ L).toInteger ^ (p ^ (k + 1))

include hn in
theorem η_prim : IsPrimitiveRoot (η n p k L) m :=
  (zeta_spec n ℚ L).toInteger_isPrimitiveRoot.pow (NeZero.pos n) hn

include hn in
theorem η_pow_n : (η n p k L) ^ n = 1 := by
  rw [η, ← pow_mul, mul_comm, pow_mul, (zeta_spec n ℚ L).toInteger_isPrimitiveRoot.pow_eq_one,
    one_pow]

include hn hm in
theorem η_bar_prim : IsPrimitiveRoot (Ideal.Quotient.mk P (η n p k L)) m := by
  have : NeZero m := ⟨(m_pos hn).ne'⟩
  refine (η_prim hn).idealQuotient_mk (by simpa using IsMaximal.ne_top inferInstance) ?_
  rw [← pow_inertiaDeg p]
  exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm)

include hn hm in
/-- If σ moves η̄ to η̄^t, then red(σ) = t mod m. -/
theorem red_eq_of_mk (σ : Gal(L/ℚ)) (t : ℕ)
    (h : Ideal.Quotient.mk P (σ • η n p k L) = Ideal.Quotient.mk P (η n p k L) ^ t) :
    ((red hn (galEquivZMod n L σ) : (ZMod m)ˣ) : ZMod m) = (t : ZMod m) := by
  have : NeZero m := ⟨(m_pos hn).ne'⟩
  have h₀ := η_bar_prim P hn hm
  rw [galEquivZMod_smul_of_pow_eq n L σ (η_pow_n hn), map_pow,
    (h₀.isOfFinOrder (NeZero.ne _)).pow_inj_mod, ← h₀.eq_orderOf] at h
  rw [ZMod.unitsMap_val, ZMod.cast_eq_val, ← ZMod.natCast_eq_natCast_iff'] at *
  exact h

include hn hm in
/-- Inertia reduces to 1 mod m. -/
theorem red_of_mem_inertia {σ : Gal(L/ℚ)} (hσ : σ ∈ P.inertia Gal(L/ℚ)) :
    red hn (galEquivZMod n L σ) = 1 := by
  apply Units.ext
  rw [red_eq_of_mk P hn hm σ 1 (by
    rw [pow_one, Ideal.Quotient.eq]; exact (Ideal.mem_inertia.mp hσ) _)]
  simp

include hn hm in
/-- The decomposition group reduces into ⟨p mod m⟩. -/
theorem red_mem_zpowers_of_mem_stabilizer {σ : Gal(L/ℚ)} (hσ : σ ∈ stabilizer Gal(L/ℚ) P) :
    red hn (galEquivZMod n L σ) ∈
      Subgroup.zpowers (ZMod.unitOfCoprime p ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm)) := by
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {n} ℚ L
  let τ := IsFractionRing.stabilizerHom Gal(L/ℚ) (Ideal.span {(p : ℤ)}) P
     (ℤ ⧸ span {(p : ℤ)}) (𝓞 L ⧸ P) ⟨σ, hσ⟩
  have : CharP (ℤ ⧸ span {(p : ℤ)}) p := ringChar.of_eq <| Int.ringChar_idealQuot p
  obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow (ℤ ⧸ span {(p : ℤ)}) p (𝓞 L ⧸ P) τ
  have h₁ := IsFractionRing.stabilizerHom_apply_apply_mk Gal(L/ℚ) (Ideal.span {(p : ℤ)}) P
      (ℤ ⧸ span {(p : ℤ)}) (𝓞 L ⧸ P) ⟨σ, hσ⟩ (η n p k L)
  simp only [Algebra.algebraMap_self, RingHomCompTriple.comp_apply] at h₁
  specialize hi (Ideal.Quotient.mk P (η n p k L))
  rw [h₁, Int.card_ideal_quot] at hi
  have h := red_eq_of_mk P hn hm σ (p ^ i) hi
  refine ⟨i, Units.ext ?_⟩
  show ((ZMod.unitOfCoprime p _ ^ (i : ℤ) : (ZMod m)ˣ) : ZMod m) = _
  rw [h, zpow_natCast, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Nat.cast_pow]

include hn hm in
theorem card_units : Nat.card (ZMod n)ˣ = (p ^ k * (p - 1)) * Nat.card (ZMod m)ˣ := by
  have : NeZero m := ⟨(m_pos hn).ne'⟩
  have hcop : Nat.Coprime (p ^ (k + 1)) m :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    ZMod.card_units_eq_totient, hn, Nat.totient_mul hcop, Nat.totient_prime_pow_succ hp.out]

include hn hm in
theorem card_ker_red : Nat.card (red hn).ker = p ^ k * (p - 1) := by
  have : NeZero m := ⟨(m_pos hn).ne'⟩
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (red hn).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
    (ZMod.unitsMap_surjective (m_dvd hn))).toEquiv, card_units hn hm, mul_comm] at h
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h.symm

include hn hm in
/-- **Inertia group = kernel of reduction mod m.** -/
theorem inertia_map :
    (P.inertia Gal(L/ℚ)).map (galEquivZMod n L).toMonoidHom = (red hn).ker := by
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {n} ℚ L
  have hspan : (span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp.out).irreducible
  have hle : (P.inertia Gal(L/ℚ)).map (galEquivZMod n L).toMonoidHom ≤ (red hn).ker := by
    rintro _ ⟨σ, hσ, rfl⟩
    exact red_of_mem_inertia P hn hm hσ
  refine Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)
  rw [card_ker_red hn hm, Subgroup.card_map_of_injective (f := (galEquivZMod n L).toMonoidHom)
    (galEquivZMod n L).injective,
    card_inertia_eq_ramificationIdxIn (span {(p : ℤ)}) P, ramificationIdxIn_eq n L hn hm]

include hn hm in
/-- **Decomposition group = preimage of ⟨p mod m⟩ under reduction.** -/
theorem stabilizer_map :
    (stabilizer Gal(L/ℚ) P).map (galEquivZMod n L).toMonoidHom =
      (Subgroup.zpowers (ZMod.unitOfCoprime p
        ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm))).comap (red hn) := by
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {n} ℚ L
  have : NeZero m := ⟨(m_pos hn).ne'⟩
  have hspan : (span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp.out).irreducible
  set u := ZMod.unitOfCoprime p ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm)
  have hle : (stabilizer Gal(L/ℚ) P).map (galEquivZMod n L).toMonoidHom ≤
      (Subgroup.zpowers u).comap (red hn) := by
    rintro _ ⟨σ, hσ, rfl⟩
    exact red_mem_zpowers_of_mem_stabilizer P hn hm hσ
  refine Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)
  have hord : Nat.card (Subgroup.zpowers u) = orderOf (p : ZMod m) := by
    rw [Nat.card_zpowers, ← orderOf_injective _ Units.coeHom_injective, Units.coeHom_apply,
      ZMod.coe_unitOfCoprime]
  -- |red⁻¹⟨u⟩| = |ker| · |⟨u⟩| via indices
  have hidx := Subgroup.index_comap_of_surjective (Subgroup.zpowers u)
    (ZMod.unitsMap_surjective (m_dvd hn))
  have h1 := ((Subgroup.zpowers u).comap (red hn)).card_mul_index
  have h2 := (Subgroup.zpowers u).card_mul_index
  rw [hidx, card_units hn hm, ← h2, hord] at h1
  have hcomap : Nat.card ((Subgroup.zpowers u).comap (red hn)) =
      p ^ k * (p - 1) * orderOf (p : ZMod m) := by
    refine Nat.eq_of_mul_eq_mul_right
      (Nat.pos_of_ne_zero (Subgroup.zpowers u).index_ne_zero_of_finite) ?_
    rw [h1]; ring
  rw [hcomap, Subgroup.card_map_of_injective (f := (galEquivZMod n L).toMonoidHom)
    (galEquivZMod n L).injective, card_stabilizer_eq (span {(p : ℤ)}) P,
    ramificationIdxIn_eq n L hn hm, inertiaDegIn_eq n L hn hm]

end CycloDecomp

#print axioms CycloDecomp.inertia_map
#print axioms CycloDecomp.stabilizer_map
