import QuadraticFrobeniusSign
import QuadraticZeta

/-!
# QuadraticCharacterIdentification — the character of a quadratic field is (d/·)

L = ℚ(ζ_N), H ≤ Gal(L/ℚ) of index 2, y ∈ L^H with y² = d ∈ ℤ, y ∉ ℚ.
* `epsD`: the Dirichlet character a ↦ sgn(σ_a) (σ_a(ζ) = ζ^a, σ_a y = sgn(σ_a)·y), trivial on H',
  nontrivial since y ∉ ℚ;
* `perp_eq_epsD`: it is THE nontrivial element of H^⊥ = {1, χ} (uniqueness, `QuadZeta.perp_two`);
* `chi_prime`: χ(q) = (d/q) for primes q ∤ N, q ≠ 2, q ∤ d (Frobenius + Euler's criterion,
  `QuadFrobSign.sgn_sigmaP`); the same holds for the primitive χ* (`pv_prime`).
For a quadratic field K:
* `exists_sqrt`: K = ℚ(√d) for some d ∈ ℤ (some γ ∈ K, γ ∉ ℚ, γ² = d);
* `quadratic_zeta_legendre`: ζ_K(s) = ζ(s) L(s, χ*) for Re s > 1, with χ*(q) = (d/q) for every
  d ∈ ℤ that is a square of a non-rational element of K and every prime q ∤ N, q ≠ 2, q ∤ d.
Not proved here: the relation of d to `NumberField.discr K` (D_K = d·(square)), nor the
determination of χ* from its prime values (Dirichlet's theorem on primes in progressions).
-/

open NumberField IntermediateField IsCyclotomicExtension.Rat

namespace QuadCharId

variable (N : ℕ) [NeZero N] {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {N} ℚ L]
  {y : L} {d : ℤ} (hy : y ^ 2 = d) (hd : d ≠ 0)

include hy hd in
/-- ε_d(a) = sgn(σ_a), as a Dirichlet character mod N. -/
noncomputable def epsD : DirichletCharacter ℂ N :=
  MulChar.equivToUnitHom.symm ((Units.map (Int.castRingHom ℂ).toMonoidHom).comp
    ((QuadFrobSign.sgnHom hy hd).comp (galEquivZMod N L).symm.toMonoidHom))

theorem epsD_apply (σ : Gal(L/ℚ)) :
    epsD N hy hd ((galEquivZMod N L σ : (ZMod N)ˣ) : ZMod N) = ((QuadFrobSign.sgn y σ : ℤ) : ℂ) := by
  rw [epsD, MulChar.equivToUnitHom_symm_coe]
  simp [QuadFrobSign.sgnHom_apply]

theorem epsD_mem_perp (H : Subgroup Gal(L/ℚ)) (hyH : y ∈ fixedField H) :
    epsD N hy hd ∈ CycloSubEuler.perp N L H := by
  rw [CycloSubEuler.mem_perp_iff]
  rintro u ⟨σ, hσ, rfl⟩
  have h1 : σ y = y := (mem_fixedField_iff H y).mp hyH σ hσ
  have : QuadFrobSign.sgn y σ = 1 := (QuadFrobSign.sgn_eq_iff hy hd σ 1).mp (by simp [h1])
  rw [show ((galEquivZMod N L).toMonoidHom σ) = galEquivZMod N L σ from rfl, epsD_apply, this]
  simp

theorem epsD_ne_one (hyQ : y ∉ Set.range (algebraMap ℚ L)) : epsD N hy hd ≠ 1 := by
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {N} ℚ L
  have : ∃ σ : Gal(L/ℚ), σ y ≠ y := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    apply hyQ
    rw [← mem_bot, ← IsGalois.fixedField_top (F := ℚ) (E := L), mem_fixedField_iff]
    exact fun σ _ => h σ
  obtain ⟨σ, hσ⟩ := this
  intro h1
  have hs : QuadFrobSign.sgn y σ = -1 := by
    rcases QuadFrobSign.sign_cases hy σ with h | h
    · exact absurd h hσ
    · exact (QuadFrobSign.sgn_eq_iff hy hd σ (-1)).mp (by simp [h])
  have := epsD_apply N hy hd σ
  rw [h1, MulChar.one_apply (Units.isUnit _), hs] at this
  norm_num at this

/-- **ε_d is the nontrivial character of H^⊥.** -/
theorem perp_eq_epsD (H : Subgroup Gal(L/ℚ)) [H.Normal] (hyH : y ∈ fixedField H)
    (hyQ : y ∉ Set.range (algebraMap ℚ L)) {χ : DirichletCharacter ℂ N}
    (hχ : CycloSubEuler.perpNontriv N L H = {χ}) : χ = epsD N hy hd := by
  classical
  have hmem : epsD N hy hd ∈ CycloSubEuler.perpNontriv N L H :=
    Finset.mem_erase.mpr ⟨epsD_ne_one N hy hd hyQ, epsD_mem_perp N hy hd H hyH⟩
  rw [hχ, Finset.mem_singleton] at hmem
  exact hmem.symm

include hy in
/-- **ε_d(q) = (d/q)** for primes q ∤ N, q ≠ 2, q ∤ d. -/
theorem epsD_prime (q : ℕ) [Fact q.Prime] (hqN : q.Coprime N) (hq2 : q ≠ 2)
    (hqd : ¬ (q : ℤ) ∣ d) : epsD N hy hd (q : ZMod N) = legendreSym q d := by
  have h := epsD_apply N hy hd (CycloFrob.sigmaP N L q hqN)
  rw [CycloFrob.sigmaP, MulEquiv.apply_symm_apply, ZMod.coe_unitOfCoprime] at h
  have h2 := QuadFrobSign.sgn_sigmaP hy q hqN hq2 hqd
  rw [CycloFrob.sigmaP] at h2
  rw [h, h2]

end QuadCharId

namespace QuadCharId

variable {K : Type*} [Field K] [NumberField K]

/-- **K = ℚ(√d):** some non-rational γ ∈ K has γ² = d ∈ ℤ. -/
theorem exists_sqrt (hK : Module.finrank ℚ K = 2) :
    ∃ d : ℤ, ∃ γ : K, γ ^ 2 = d ∧ γ ∉ Set.range (algebraMap ℚ K) := by
  obtain ⟨α, hα, hdeg⟩ := QuadKW.exists_primitive hK
  set b := (minpoly ℚ α).coeff 1
  set c := (minpoly ℚ α).coeff 0
  have hrel : α ^ 2 + algebraMap ℚ K b * α + algebraMap ℚ K c = 0 := by
    rw [← QuadKW.aeval_minpoly K hdeg α]; exact minpoly.aeval ℚ α
  set D : ℚ := b ^ 2 - 4 * c
  set γ : K := (D.den : K) * (2 * α + algebraMap ℚ K b)
  refine ⟨D.num * D.den, γ, ?_, ?_⟩
  · have hD : (2 * α + algebraMap ℚ K b) ^ 2 = algebraMap ℚ K D := by
      simp only [D, map_sub, map_pow, map_mul, map_ofNat]; linear_combination 4 * hrel
    have hden : (D.den : K) ≠ 0 := Nat.cast_ne_zero.mpr D.den_nz
    simp only [γ, mul_pow, hD]
    rw [eq_ratCast, Rat.cast_def]
    push_cast
    field_simp
  · rintro ⟨r, hr⟩
    have hα' : α ∈ (⊥ : IntermediateField ℚ K) := by
      rw [mem_bot]
      refine ⟨(r / D.den - b) / 2, ?_⟩
      have hden : (D.den : K) ≠ 0 := Nat.cast_ne_zero.mpr D.den_nz
      simp only [map_div₀, map_sub, map_natCast, map_ofNat, hr, γ]
      field_simp
      ring
    rw [← adjoin_simple_eq_bot_iff, hα] at hα'
    have := congrArg (fun E : IntermediateField ℚ K => Module.finrank ℚ E) hα'
    simp only [finrank_top', IntermediateField.finrank_bot, hK] at this
    norm_num at this

/-- **ζ_K = ζ · L(χ*) with χ*(q) = (d/q)** for every quadratic field K. -/
theorem quadratic_zeta_legendre (hK : Module.finrank ℚ K = 2) :
    ∃ N : ℕ, ∃ _ : NeZero N, ∃ χ : DirichletCharacter ℂ N, χ ≠ 1 ∧ χ ^ 2 = 1 ∧
      (∀ s : ℂ, 1 < s.re →
        LSeries (fun m => (IdealCount.A (𝓞 K) m : ℂ)) s =
          riemannZeta s * LSeries (fun m => χ.primitiveCharacter m) s) ∧
      ∀ (d : ℤ) (γ : K), γ ^ 2 = d → γ ∉ Set.range (algebraMap ℚ K) →
        ∀ (q : ℕ) [Fact q.Prime], q.Coprime N → q ≠ 2 → ¬ (q : ℤ) ∣ d →
          CompositeLocal.pv χ (q : ℤ) = legendreSym q d := by
  obtain ⟨N, hN0, hkw⟩ := QuadKW.quadratic_kronecker_weber hK
  have : NeZero N := ⟨hN0⟩
  have : NeZero (N : ℚ) := ⟨by exact_mod_cast hN0⟩
  let L := CyclotomicField N ℚ
  have := QuadKW.cyclotomicField_isCyclotomic N
  have : NumberField L := inferInstance
  obtain ⟨H, hH, ⟨e⟩⟩ := hkw L
  have : H.Normal := CycloSub.normal N H
  obtain ⟨χ, hne, hsq, hχ⟩ := QuadZeta.perp_two (N := N) H hH
  refine ⟨N, ⟨hN0⟩, χ, hne, hsq, fun s hs => ?_, ?_⟩
  · rw [IdealCountIso.LSeries_eq_of_equiv e.toRingEquiv s,
      CompositeEuler.LSeries_eq_zeta_mul_prod_primitive N L H hs,
      Finset.prod_coe_sort (CycloSubEuler.perpNontriv N L H)
        (fun χ => LSeries (fun m => χ.primitiveCharacter m) s), hχ, Finset.prod_singleton]
  · intro d γ hγ hγQ q _ hqN hq2 hqd
    set y : L := (e γ : L)
    have hy : y ^ 2 = d := by
      simp only [y]; rw [← IntermediateField.coe_pow, ← map_pow, hγ, map_intCast]; rfl
    have hyH : y ∈ fixedField H := (e γ).2
    have hyQ : y ∉ Set.range (algebraMap ℚ L) := by
      rintro ⟨r, hr⟩
      apply hγQ
      refine ⟨r, e.injective ?_⟩
      rw [AlgEquiv.commutes]
      exact Subtype.ext hr
    have hd : d ≠ 0 := by
      rintro rfl
      apply hγQ
      have h0 : γ = 0 := by simpa using hγ
      exact ⟨0, by simp [h0]⟩
    rw [QuadCharId.perp_eq_epsD N hy hd H hyH hyQ hχ, CompositeEuler.pv_of_coprime N hqN]
    exact QuadCharId.epsD_prime N hy hd q hqN hq2 hqd

end QuadCharId

#print axioms QuadCharId.perp_eq_epsD
#print axioms QuadCharId.epsD_prime
#print axioms QuadCharId.exists_sqrt
#print axioms QuadCharId.quadratic_zeta_legendre
