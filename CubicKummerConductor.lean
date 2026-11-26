import CubicKummerDescent
import CompositeCyclotomicEulerProduct
import CompositeLocalFactor
import CyclotomicCharacterCorrespondence

/-!
# CubicKummerConductor — ζ_{K_q} = ζ · L(ψ) · L(ψ̄), ψ primitive cubic of conductor q

Setting of `CubicDescent`: q prime, 3 ∣ q − 1, L = ℚ(ζ_{3q}), χ : ZMod q → L of order 3,
K_q = L^{ker χ}. The Euler-product machinery uses ℂ-valued characters mod 3q, kept distinct from
the L-valued χ mod q:
* `H'_eq`: the image of Hq in (ZMod 3q)ˣ is ker(χ ∘ (mod q));
* `perpNontriv_eq`: H^⊥ ∖ {1} = {ψ, ψ²} for any nontrivial ψ ∈ H^⊥; `sq_eq_conj`: ψ² = ψ̄;
* `ker_eq`: ψ(u) = 1 ↔ χ(u mod q) = 1 — ψ and χ cut out the same subgroup, i.e. ψ is χ
  transported to ℂ up to inversion;
* `conductor_eq_q`: conductor ψ = conductor ψ² = q (ψ factors through q; ψ ≠ 1);
* `unramified_three`: 3 is unramified in K_q (e = 1, g·f = 3), although ramified in ℚ(ζ_{3q});
* `zeta_Kq`: ζ_{K_q}(s) = ζ(s) · L(s, ψ*) · L(s, (ψ²)*) for Re s > 1, ψ* primitive mod q.
-/

open NumberField IntermediateField IsCyclotomicExtension IsCyclotomicExtension.Rat
  DirichletCharacter CubicKummer CubicDescent GaloisEuler

namespace CubicConductor

variable {q : ℕ} [hq : Fact q.Prime] (hq3 : 3 ∣ q - 1)
  {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {3 * q} ℚ L]
  {χ : MulChar (ZMod q) L} (hχ : orderOf χ = 3)

/-- χ ∘ (mod q) on (ZMod 3q)ˣ. -/
noncomputable def chiU (χ : MulChar (ZMod q) L) : (ZMod (3 * q))ˣ →* Lˣ :=
  χ.toUnitHom.comp (ZMod.unitsMap (q_dvd (q := q)))

theorem H'_eq : CycloSubEuler.H' (3 * q) L (Hq χ) = (chiU χ).ker := by
  have : Hq χ = (chiU χ).ker.comap (galEquivZMod (3 * q) L).toMonoidHom := rfl
  rw [CycloSubEuler.H', this]
  exact Subgroup.map_comap_eq_self_of_surjective (galEquivZMod (3 * q) L).surjective _

theorem mem_perp {ψ : DirichletCharacter ℂ (3 * q)} :
    ψ ∈ CycloSubEuler.perp (3 * q) L (Hq χ) ↔ ∀ u ∈ (chiU χ).ker, ψ u = 1 := by
  rw [CycloSubEuler.mem_perp_iff, H'_eq]

include hχ in
theorem cube_mem (u : (ZMod (3 * q))ˣ) : u ^ 3 ∈ (chiU χ).ker := by
  rw [MonoidHom.mem_ker, map_pow]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, chiU, MonoidHom.comp_apply, MulChar.coe_toUnitHom, Units.val_one,
    ← MulChar.pow_apply' _ (by norm_num), CubicGauss.pow_three hχ, MulChar.one_apply (Units.isUnit _)]

include hχ in
theorem cube_eq_one {ψ : DirichletCharacter ℂ (3 * q)}
    (hψ : ψ ∈ CycloSubEuler.perp (3 * q) L (Hq χ)) : ψ ^ 3 = 1 := by
  apply MulChar.ext
  intro u
  rw [MulChar.pow_apply' _ (by norm_num), ← map_pow, ← Units.val_pow_eq_pow_val,
    (mem_perp.mp hψ) _ (cube_mem hχ u), MulChar.one_apply (Units.isUnit _)]

theorem sq_mem {ψ : DirichletCharacter ℂ (3 * q)}
    (hψ : ψ ∈ CycloSubEuler.perp (3 * q) L (Hq χ)) :
    ψ ^ 2 ∈ CycloSubEuler.perp (3 * q) L (Hq χ) := by
  rw [mem_perp] at hψ ⊢
  intro u hu
  rw [MulChar.pow_apply' _ (by norm_num), hψ u hu, one_pow]

include hq3 hχ in
theorem card_perpNontriv : (CycloSubEuler.perpNontriv (3 * q) L (Hq χ)).card = 2 := by
  classical
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {3 * q} ℚ L
  rw [CycloSubEuler.perpNontriv, Finset.card_erase_of_mem (CycloSubEuler.one_mem_perp _ L _),
    (CycloCharCorr.card_perp (3 * q) L (Hq χ)).1, index_Hq hq3 hχ]

include hq3 hχ in
/-- **H^⊥ ∖ {1} = {ψ, ψ²}.** -/
theorem perpNontriv_eq {ψ : DirichletCharacter ℂ (3 * q)}
    (hψ : ψ ∈ CycloSubEuler.perpNontriv (3 * q) L (Hq χ)) :
    CycloSubEuler.perpNontriv (3 * q) L (Hq χ) = {ψ, ψ ^ 2} := by
  classical
  have hψ' := hψ
  rw [CycloSubEuler.perpNontriv, Finset.mem_erase] at hψ'
  obtain ⟨hne, hp⟩ := hψ'
  have h3 := cube_eq_one hχ hp
  have hsq1 : ψ ^ 2 ≠ 1 := by
    intro h; apply hne
    rw [show ψ = ψ ^ 3 * (ψ ^ 2)⁻¹ by group, h3, h, inv_one, mul_one]
  have hsqψ : ψ ^ 2 ≠ ψ := by
    intro h; apply hne; rw [pow_two, mul_eq_left] at h; exact h
  have hsub : ({ψ, ψ ^ 2} : Finset _) ⊆ CycloSubEuler.perpNontriv (3 * q) L (Hq χ) := by
    intro φ hφ
    rw [Finset.mem_insert, Finset.mem_singleton] at hφ
    rcases hφ with rfl | rfl
    · exact hψ
    · exact Finset.mem_erase.mpr ⟨hsq1, sq_mem hp⟩
  exact (Finset.eq_of_subset_of_card_le hsub
    (by rw [card_perpNontriv hq3 hχ, Finset.card_pair (Ne.symm hsqψ)])).symm

include hχ in
/-- **ψ² = ψ̄.** -/
theorem sq_eq_conj {ψ : DirichletCharacter ℂ (3 * q)}
    (hψ : ψ ∈ CycloSubEuler.perp (3 * q) L (Hq χ)) (a : ZMod (3 * q)) :
    (ψ ^ 2) a = starRingEnd ℂ (ψ a) := by
  by_cases ha : IsUnit a
  · have h3 : (ψ a) ^ 3 = 1 := by
      rw [← MulChar.pow_apply' _ (by norm_num), cube_eq_one hχ hψ, MulChar.one_apply ha]
    have hnorm := Complex.norm_eq_one_of_pow_eq_one h3 (by norm_num)
    rw [MulChar.pow_apply' _ (by norm_num), ← Complex.inv_eq_conj hnorm]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h3])
  · rw [MulChar.map_nonunit _ ha, MulChar.map_nonunit _ ha, map_zero]

include hχ in
/-- **conductor ψ = q** for every nontrivial ψ ∈ H^⊥. -/
theorem conductor_eq_q {ψ : DirichletCharacter ℂ (3 * q)}
    (hψ : ψ ∈ CycloSubEuler.perpNontriv (3 * q) L (Hq χ)) : ψ.conductor = q := by
  rw [CycloSubEuler.perpNontriv, Finset.mem_erase] at hψ
  obtain ⟨hne, hp⟩ := hψ
  have hf : ψ.FactorsThrough q := by
    rw [factorsThrough_iff_ker_unitsMap (q_dvd (q := q))]
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    apply Units.ext
    rw [MulChar.coe_toUnitHom, Units.val_one]
    apply (mem_perp.mp hp) u
    rw [MonoidHom.mem_ker, chiU, MonoidHom.comp_apply, hu, map_one]
  have hdvd : conductor ψ ∣ q :=
    (mem_conductorSet_iff_conductor_dvd ψ (q_dvd (q := q))).mp hf
  rcases (Nat.dvd_prime hq.out).mp hdvd with h | h
  · exact absurd (eq_one_iff_conductor_eq_one.mpr h) hne
  · exact h

include hq3 hχ in
/-- **ψ and χ cut out the same subgroup:** ψ(u) = 1 ↔ χ(u mod q) = 1. -/
theorem ker_eq {ψ : DirichletCharacter ℂ (3 * q)}
    (hψ : ψ ∈ CycloSubEuler.perpNontriv (3 * q) L (Hq χ)) :
    ψ.toUnitHom.ker = (chiU χ).ker := by
  have hψ' := hψ
  rw [CycloSubEuler.perpNontriv, Finset.mem_erase] at hψ'
  obtain ⟨hne, hp⟩ := hψ'
  have hle : (chiU χ).ker ≤ ψ.toUnitHom.ker := by
    intro u hu
    rw [MonoidHom.mem_ker]; apply Units.ext
    rw [MulChar.coe_toUnitHom, Units.val_one]; exact (mem_perp.mp hp) u hu
  -- both kernels have index 3
  have hiχ : (chiU χ).ker.index = 3 := by
    rw [Subgroup.index_ker, chiU, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (ZMod.unitsMap_surjective (q_dvd (q := q))),
      ← MonoidHom.range_eq_map, ← range_chiGal, card_range hq3 hχ]
  have hiψ : ψ.toUnitHom.ker.index = 3 := by
    rw [Subgroup.index_ker]
    have hle3 : ψ.toUnitHom.range ≤ rootsOfUnity 3 ℂ := by
      rintro x ⟨u, rfl⟩
      rw [mem_rootsOfUnity]; apply Units.ext
      rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, Units.val_one,
        ← MulChar.pow_apply' _ (by norm_num), cube_eq_one hχ hp, MulChar.one_apply u.isUnit]
    have hdvd := Subgroup.card_dvd_of_le hle3
    rw [Complex.card_rootsOfUnity] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exfalso; apply hne
      rw [Subgroup.card_eq_one, MonoidHom.range_eq_bot_iff] at h
      apply MulChar.ext; intro u
      rw [← MulChar.coe_toUnitHom, h, MonoidHom.one_apply, Units.val_one, MulChar.one_apply u.isUnit]
    · exact h
  apply (Subgroup.eq_of_le_of_card_ge hle _).symm
  have h1 := (chiU χ).ker.card_mul_index
  have h2 := ψ.toUnitHom.ker.card_mul_index
  rw [hiχ] at h1; rw [hiψ] at h2
  omega

include hq3 hχ in
/-- **3 is unramified in K_q** (e = 1, g · f = 3), though ramified in ℚ(ζ_{3q}). -/
theorem unramified_three :
    (Ideal.span {((3 : ℕ) : ℤ)}).ramificationIdxIn (𝓞 (Kq χ)) = 1 ∧
      gK (Kq χ) 3 * fK (Kq χ) 3 = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {3 * q} ℚ L
  have hn : 3 * q = 3 ^ (0 + 1) * q := by ring
  have hq3' : q ≠ 3 := by rintro rfl; norm_num at hq3
  have hm : ¬ 3 ∣ q := fun h => hq3' ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq.out).mp h).symm
  obtain ⟨hf, hg⟩ := CompositeLocal.fK_gK_ramified (Hq χ) hn hm
  have hH'' : (CompositeLocal.H'' (Hq χ) hn).index = 3 := by
    have : CompositeLocal.H'' (Hq χ) hn = χ.toUnitHom.ker := by
      rw [CompositeLocal.H'', H'_eq, chiU, ← MonoidHom.comap_ker]
      exact Subgroup.map_comap_eq_self_of_surjective (ZMod.unitsMap_surjective _) _
    rw [this, Subgroup.index_ker, ← range_chiGal, card_range hq3 hχ]
  set o := orderOf (QuotientGroup.mk (CompositeLocal.u (p := 3) hm) :
    (ZMod q)ˣ ⧸ CompositeLocal.H'' (Hq χ) hn)
  have ho : o ∣ 3 := by
    rw [← hH'', Subgroup.index]; exact orderOf_dvd_natCard _
  have hgf : gK (Kq χ) 3 * fK (Kq χ) 3 = 3 := by
    rw [hf, hg, hH'']; exact Nat.div_mul_cancel ho
  refine ⟨?_, hgf⟩
  have hgef := SubfieldDeg.gK_eK_fK (Hq χ) 3
  rw [index_Hq hq3 hχ] at hgef
  have key : ∀ g e f : ℕ, g * f = 3 → g * (e * f) = 3 → e = 1 := by
    intro g e f h1 h2
    have hpos : 0 < g * f := by rw [h1]; norm_num
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc g * f * e = g * (e * f) := by ring
      _ = g * f * 1 := by rw [h2, mul_one, h1]
  rw [gK, fK] at hgf
  exact key _ _ _ hgf hgef

include hq3 hχ in
/-- **ζ_{K_q}(s) = ζ(s) · L(s, ψ*) · L(s, (ψ²)*)**, ψ of order 3, conductor q, ψ² = ψ̄. -/
theorem zeta_Kq {s : ℂ} (hs : 1 < s.re) :
    ∃ ψ : DirichletCharacter ℂ (3 * q), ψ ≠ 1 ∧ ψ ^ 3 = 1 ∧ ψ.conductor = q ∧
      (ψ ^ 2).conductor = q ∧ (∀ a, (ψ ^ 2) a = starRingEnd ℂ (ψ a)) ∧
      ψ.toUnitHom.ker = (chiU χ).ker ∧
      LSeries (fun m => (IdealCount.A (𝓞 (Kq χ)) m : ℂ)) s =
        riemannZeta s * LSeries (fun m => ψ.primitiveCharacter m) s *
          LSeries (fun m => (ψ ^ 2).primitiveCharacter m) s := by
  classical
  obtain ⟨ψ, hψ⟩ : (CycloSubEuler.perpNontriv (3 * q) L (Hq χ)).Nonempty := by
    rw [← Finset.card_pos, card_perpNontriv hq3 hχ]; norm_num
  have heq := perpNontriv_eq hq3 hχ hψ
  have hψ' := hψ
  rw [CycloSubEuler.perpNontriv, Finset.mem_erase] at hψ'
  obtain ⟨hne, hp⟩ := hψ'
  have hsq : ψ ^ 2 ∈ CycloSubEuler.perpNontriv (3 * q) L (Hq χ) := by rw [heq]; simp
  have hsqψ : ψ ^ 2 ≠ ψ := by
    intro h; apply hne; rw [pow_two, mul_eq_left] at h; exact h
  refine ⟨ψ, hne, cube_eq_one hχ hp, conductor_eq_q hχ hψ, conductor_eq_q hχ hsq,
    sq_eq_conj hχ hp, ker_eq hq3 hχ hψ, ?_⟩
  rw [CompositeEuler.LSeries_eq_zeta_mul_prod_primitive (3 * q) L (Hq χ) hs,
    Finset.prod_coe_sort (CycloSubEuler.perpNontriv (3 * q) L (Hq χ))
      (fun φ => LSeries (fun m => φ.primitiveCharacter m) s), heq,
    Finset.prod_pair (Ne.symm hsqψ), mul_assoc]

end CubicConductor

#print axioms CubicConductor.perpNontriv_eq
#print axioms CubicConductor.ker_eq
#print axioms CubicConductor.conductor_eq_q
#print axioms CubicConductor.unramified_three
#print axioms CubicConductor.zeta_Kq
