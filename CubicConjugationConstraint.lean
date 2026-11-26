import CubicKummerRepresentation

/-!
# CubicConjugationConstraint — ā / a² is a cube in ℚ(ω)

Setting of `CubicKummerRep`: K ⊆ ℂ Galois of degree 3, F = ℚ(ω), M = K(ω) = ℚ(ω, β),
a = β³ ∈ F, β ∉ F. Let c be complex conjugation restricted to M and τ ≠ 1 in Gal(M/F).
* `tau_beta`: τβ = ω^i β with i ∈ {1, 2} (τβ is a cube root of a; τβ = β would force τ = 1);
* with γ = cβ and δ = γ/β², τ and c commute (`CubicKummerRep.gal_comm`), so
  τγ = c(ω^i β) = ω^{2i} γ and τδ = δ — the eigenvalue computation forces the exponent 2;
* δ is fixed by ⟨τ⟩ = Gal(M/F), hence δ ∈ F;
* `conj_constraint`: ā = δ³ · a² with δ ∈ F, δ ≠ 0 — i.e. ā / a² ∈ F^{×3}.
Units of ℤ[ω] and prime valuations are not treated here.
-/

open IntermediateField Module CubicKummerRep

namespace CubicConj

local notation "ω" => CubicAssembly.ω

theorem ω_cube : ω ^ 3 = 1 := CubicAssembly.hω.pow_eq_one

/-- conj ω = ω². -/
theorem conj_ω : starRingEnd ℂ ω = ω ^ 2 := by
  have hn := Complex.norm_eq_one_of_pow_eq_one ω_cube (by norm_num)
  rw [← Complex.inv_eq_conj hn]
  exact inv_eq_of_mul_eq_one_left (by rw [← pow_succ, ω_cube])

variable (K : IntermediateField ℚ ℂ) [IsGalois ℚ K] (hK : finrank ℚ K = 3)

include hK in
/-- **ā = δ³ · a²**, δ ∈ F nonzero, for the Kummer radicand a = β³ of M = K(ω) = ℚ(ω, β). -/
theorem conj_constraint : ∃ β : ℂ, β ∈ M K ∧ β ^ 3 ∈ F ∧ β ∉ F ∧ M K = ℚ⟮ω, β⟯ ∧
    ∃ δ : ℂ, δ ∈ F ∧ δ ≠ 0 ∧ starRingEnd ℂ (β ^ 3) = δ ^ 3 * (β ^ 3) ^ 2 := by
  obtain ⟨β, hβM, hβ3, hβF, hM⟩ := kummer K hK
  refine ⟨β, hβM, hβ3, hβF, hM, ?_⟩
  have := finiteDimensional_K K hK
  have : FiniteDimensional ℚ (M K) := IntermediateField.finiteDimensional_sup K F
  have : IsGalois ℚ (M K) := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  -- the tower M / F' / ℚ inside Ω = M
  set K' : IntermediateField ℚ (M K) := restrict (le_sup_left : K ≤ M K)
  set F' : IntermediateField ℚ (M K) := restrict (le_sup_right : F ≤ M K)
  have eK : K ≃ₐ[ℚ] K' := AlgEquiv.ofInjectiveField (inclusion (le_sup_left : K ≤ M K))
  have eF : F ≃ₐ[ℚ] F' := AlgEquiv.ofInjectiveField (inclusion (le_sup_right : F ≤ M K))
  have : IsGalois ℚ K' := IsGalois.of_algEquiv eK
  have : FiniteDimensional ℚ K' := LinearEquiv.finiteDimensional eK.toLinearEquiv
  have hsup : K' ⊔ F' = ⊤ :=
    lift_injective _ (by simp [K', F', lift_sup, lift_restrict, lift_top])
  have : IsGalois F' (M K) := IsGalois.sup_right K' F' hsup
  have hF' : finrank ℚ F' = 2 := by rw [← eF.toLinearEquiv.finrank_eq, finrank_F]
  have : Module.Free F' (M K) := Module.Free.of_divisionRing _ _
  have hdeg : finrank F' (M K) = 3 := by
    have h := Module.finrank_mul_finrank ℚ F' (M K)
    rw [hF', finrank_M K hK] at h
    omega
  have : FiniteDimensional F' (M K) := Module.finite_of_finrank_pos (by rw [hdeg]; norm_num)
  have hcard : Nat.card Gal(M K/F') = 3 := by
    first
    | rw [IsGalois.card_aut_eq_finrank, hdeg]
    | rw [Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hdeg]
  have : Nontrivial Gal(M K/F') :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  obtain ⟨τ, hτ⟩ := exists_ne (1 : Gal(M K/F'))
  -- elements
  have hωF : ω ∈ F := mem_adjoin_simple_self ℚ ω
  set w : M K := ⟨ω, le_sup_right (a := K) hωF⟩
  have hwF' : w ∈ F' := (mem_restrict _ w).mpr hωF
  set b : M K := ⟨β, hβM⟩
  have hb0 : b ≠ 0 := by
    intro h
    apply hβF
    have : β = 0 := congrArg Subtype.val h
    rw [this]; exact zero_mem _
  have hτw : τ w = w := by
    have := τ.commutes ⟨w, hwF'⟩
    simpa using this
  have hτa : τ (b ^ 3) = b ^ 3 := by
    have hbF' : b ^ 3 ∈ F' := (mem_restrict _ (b ^ 3)).mpr hβ3
    have := τ.commutes ⟨b ^ 3, hbF'⟩
    simpa using this
  -- τ b = w^i b, i ∈ {1, 2}
  have hτb : ∃ i : ℕ, τ b = w ^ i * b := by
    have h3 : (τ b / b) ^ 3 = 1 := by
      rw [div_pow, ← map_pow, hτa, div_self (pow_ne_zero _ hb0)]
    have h3C : ((τ b / b : M K) : ℂ) ^ 3 = 1 := by
      rw [← (M K).coe_pow, h3]; rfl
    obtain ⟨i, -, hi⟩ := CubicAssembly.hω.eq_pow_of_pow_eq_one h3C
    refine ⟨i, ?_⟩
    have : w ^ i = τ b / b := Subtype.ext (by rw [(M K).coe_pow]; exact hi)
    rw [this, div_mul_cancel₀ _ hb0]
  obtain ⟨i, hi⟩ := hτb
  -- complex conjugation on M
  let cQ : ℂ ≃ₐ[ℚ] ℂ := Complex.conjAe.restrictScalars ℚ
  let c : Gal(M K/ℚ) := cQ.restrictNormal (M K)
  have hc : ∀ x : M K, ((c x : M K) : ℂ) = starRingEnd ℂ (x : ℂ) := fun x =>
    cQ.restrictNormal_commutes (M K) x
  have hcw : c w = w ^ 2 := Subtype.ext (by rw [hc, (M K).coe_pow]; exact conj_ω)
  -- commutation
  let τQ : Gal(M K/ℚ) := τ.restrictScalars ℚ
  have hcomm : τ (c b) = c (τ b) := by
    have := congrArg (fun g : Gal(M K/ℚ) => g b) (gal_comm K hK τQ c)
    simpa [τQ] using this
  -- δ = c b / b²
  set δ : M K := c b / b ^ 2
  have hw3 : w ^ 3 = 1 := Subtype.ext (by rw [(M K).coe_pow]; exact ω_cube)
  have hw0 : w ≠ 0 := by intro h; rw [h, zero_pow (by norm_num)] at hw3; exact zero_ne_one hw3
  have hτδ : τ δ = δ := by
    simp only [δ, map_div₀, map_pow, hcomm, hi, map_mul, hcw]
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 i]
    field_simp
  -- δ ∈ F'
  have hδbot : δ ∈ (⊥ : IntermediateField F' (M K)) := by
    rw [IsGalois.mem_bot_iff_fixed]
    intro g
    have hle : Subgroup.zpowers τ ≤ MulAction.stabilizer Gal(M K/F') δ :=
      Subgroup.zpowers_le.mpr (by rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]; exact hτδ)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hg := hle (by rw [zpowers_eq_top_of_prime_card hcard hτ]; trivial : g ∈ Subgroup.zpowers τ)
    rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at hg
  obtain ⟨f, hf⟩ := IntermediateField.mem_bot.mp hδbot
  have hδF : (δ : ℂ) ∈ F := by
    rw [← hf]; exact (mem_restrict _ (f : M K)).mp f.2
  have hδ0 : (δ : ℂ) ≠ 0 := by
    intro h
    have : δ = 0 := Subtype.ext h
    rw [div_eq_zero_iff] at this
    rcases this with h | h
    · exact hb0 (c.injective (by rw [h, map_zero]))
    · exact hb0 (pow_eq_zero_iff (by norm_num) |>.mp h)
  refine ⟨δ, hδF, hδ0, ?_⟩
  have key : c b = δ * b ^ 2 := by rw [div_mul_cancel₀ _ (pow_ne_zero _ hb0)]
  have := congrArg (fun x : M K => ((x : M K) : ℂ)) key
  simp only [hc] at this
  rw [map_pow, this]
  push_cast [b]
  ring

end CubicConj

#print axioms CubicConj.conj_constraint
