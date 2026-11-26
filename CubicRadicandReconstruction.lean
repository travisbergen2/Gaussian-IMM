import CubicJacobiPrimeMatching

/-!
# CubicRadicandReconstruction — the radicand is ω^j · Y³ · ∏ (q J_q), with an explicit cube root

R = 𝓞 F = ℤ[ω], z = ω ∈ R, κ = complex conjugation. A *Gauss cube* is G = q · J(χ, χ) for a
cubic character χ mod a prime q ≡ 1 (mod 3); then G = J² · J̄ (q = J J̄) and G = g(χ)³.
1. **Finite reconstruction** (`reconstruct`): if A ≠ 0 and C³ · κA = D³ · A² (C ≠ 0), then
   A = z^j · Y³ · G₁ ⋯ G_m with Y ∈ R and Gauss cubes Gᵢ. Strong induction on |N(A)|:
   * units: A = ±z^j (Mathlib `Units.mem`), and −1 = (−1)³ — the unit step, kept explicit;
   * a κ-fixed prime π ∣ A: 3 ∣ v_π(A), so A = π³ A' (`peel_cube`);
   * a Jacobi prime J ∣ A (J̄ = κJ, J J̄ = q, J ≁ J̄), x = v_J(A), y = v_J̄(A), y ≡ 2x (mod 3):
     x ≡ 0: A = J³ A'; x ≡ 2: J² J̄ = q J ∣ A; x ≡ 1: J J̄² = q J̄ ∣ A (the Gauss cube of χ⁻¹).
     Orientation convention: the factor removed is q · J(χ', χ') for the character χ' ∈ {χ, χ⁻¹}
     whose Jacobi sum carries the larger exponent class (`peel_gauss`, with G² = κG · W³).
   In each step A' satisfies the same constraint and |N(A')| < |N(A)|.
2. **Gauss-sum realization** (`gauss_realization`): ι(q J(χ, χ)) = g(χ_ℂ)³, χ_ℂ = χ composed
   with F ⊆ ℂ, g the Gauss sum with a primitive q-th root of unity.
3. **Unit resolution and cube root** (`radicand_cube_root`): with ζ₉ = e^{2πi/9} (ζ₉³ = ω),
   ι(A) = (ζ₉^j · ι(Y) · g₁ ⋯ g_m)³ for the integral Kummer radicand A of a cyclic cubic K.
-/

open IntermediateField Module NumberField CubicKummerRep CubicVal CubicMatch

namespace CubicRecon

local notation "ω" => CubicAssembly.ω
local notation "z" => hωF.toInteger

instance : IsPrincipalIdealRing (𝓞 F) := IsCyclotomicExtension.Rat.three_pid F

/-- **Gauss cube:** G = q · J(χ, χ), χ cubic mod a prime q ≡ 1 (mod 3). -/
def IsGaussCube (G : 𝓞 F) : Prop :=
  ∃ q : ℕ, ∃ _ : Fact q.Prime, 3 ∣ q - 1 ∧ ∃ χ : MulChar (ZMod q) F, ∃ hχ : orderOf χ = 3,
    G = (q : 𝓞 F) * EisJacobi.J hχ

theorem kappa_ne_zero {x : 𝓞 F} (hx : x ≠ 0) : κ x ≠ 0 :=
  fun h => hx (κ.injective (by rw [h, map_zero]))

/-- Removing a cube π³. -/
theorem peel_cube {A A' π C D : 𝓞 F} (hA : A = π ^ 3 * A') (h : C ^ 3 * κ A = D ^ 3 * A ^ 2) :
    (C * κ π) ^ 3 * κ A' = (D * π ^ 2) ^ 3 * A' ^ 2 := by
  subst hA; rw [map_mul, map_pow] at h; linear_combination h

/-- Removing G with G² = κG · W³. -/
theorem peel_gauss {A A' G W C D : 𝓞 F} (hA : A = G * A') (hG : G ^ 2 = κ G * W ^ 3)
    (hG0 : G ≠ 0) (h : C ^ 3 * κ A = D ^ 3 * A ^ 2) : C ^ 3 * κ A' = (D * W) ^ 3 * A' ^ 2 := by
  subst hA
  apply mul_left_cancel₀ (kappa_ne_zero hG0)
  rw [map_mul] at h
  linear_combination h + D ^ 3 * A' ^ 2 * hG

theorem natAbs_norm_ne_zero {Y : 𝓞 F} (hY : Y ≠ 0) : (Algebra.norm ℤ Y).natAbs ≠ 0 := by
  rw [Ne, Int.natAbs_eq_zero, Algebra.norm_eq_zero_iff]; exact hY

theorem natAbs_norm_lt {A A' X : 𝓞 F} (hA0 : A ≠ 0) (hA : A = X * A') (hX : ¬ IsUnit X) :
    (Algebra.norm ℤ A').natAbs < (Algebra.norm ℤ A).natAbs := by
  have hX0 : X ≠ 0 := by rintro rfl; rw [zero_mul] at hA; exact hA0 hA
  have hA'0 : A' ≠ 0 := by rintro rfl; rw [mul_zero] at hA; exact hA0 hA
  rw [hA, map_mul, Int.natAbs_mul]
  have h1 : (Algebra.norm ℤ X).natAbs ≠ 1 := fun h => hX (by
    rw [← Ideal.span_singleton_eq_top, ← Ideal.absNorm_eq_one_iff, absNorm_eq, h])
  have h2 := natAbs_norm_ne_zero hX0
  have h3 := natAbs_norm_ne_zero hA'0
  have ha : 2 ≤ (Algebra.norm ℤ X).natAbs := by omega
  have hb : 1 ≤ (Algebra.norm ℤ A').natAbs := by omega
  nlinarith

/-- P^a ∣ A and Q^b ∣ A for non-associated primes ⇒ P^a · Q^b ∣ A. -/
theorem pow_mul_pow_dvd {P Q A : 𝓞 F} (hP : Prime P) (hQ : Prime Q) (hne : ¬ Associated Q P)
    {a b : ℕ} (ha : P ^ a ∣ A) (hb : Q ^ b ∣ A) : P ^ a * Q ^ b ∣ A := by
  obtain ⟨B, rfl⟩ := ha
  have : Q ^ b ∣ B := hQ.pow_dvd_of_dvd_mul_left b
    (fun h => hne (hQ.associated_of_dvd hP (hQ.dvd_of_dvd_pow h))) hb
  exact mul_dvd_mul_left _ this

/-- **Finite reconstruction:** A = z^j · Y³ · ∏ Gᵢ with Gauss cubes Gᵢ. -/
theorem reconstruct : ∀ n : ℕ, ∀ A C D : 𝓞 F, (Algebra.norm ℤ A).natAbs = n → A ≠ 0 → C ≠ 0 →
    C ^ 3 * κ A = D ^ 3 * A ^ 2 →
    ∃ j : ℕ, ∃ Y : 𝓞 F, ∃ L : List (𝓞 F), (∀ G ∈ L, IsGaussCube G) ∧ A = z ^ j * Y ^ 3 * L.prod := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A C D hn hA0 hC0 hCD
  by_cases hu : IsUnit A
  · -- units: ±z^j
    obtain ⟨u, rfl⟩ := hu
    have hmem := IsCyclotomicExtension.Rat.Three.Units.mem hωF u
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h | h | h | h <;> rw [h]
    · exact ⟨0, 1, [], by simp, by simp⟩
    · exact ⟨0, -1, [], by simp, by simp <;> first | ring | rfl⟩
    · exact ⟨1, 1, [], by simp, by simp <;> first | ring | rfl⟩
    · exact ⟨1, -1, [], by simp, by simp <;> first | ring | rfl⟩
    · exact ⟨2, 1, [], by simp, by simp <;> first | ring | rfl⟩
    · exact ⟨2, -1, [], by simp, by simp <;> first | ring | rfl⟩
  obtain ⟨π, hπirr, hπA⟩ := WfDvdMonoid.exists_irreducible_factor hu hA0
  have hπ : Prime π := hπirr.prime
  have hfin := FiniteMultiplicity.of_prime_left hπ hA0
  by_cases hfix : Associated (κ π) π
  · -- κ-fixed prime: π³ ∣ A
    have h3 := three_dvd_of_fixed κ kappa_kappa hπ hfix hA0 hC0 hCD
    have h1 : 1 ≤ multiplicity π A := hfin.le_multiplicity_of_pow_dvd (by rwa [pow_one])
    obtain ⟨A', hA'⟩ := pow_dvd_of_le_multiplicity (show 3 ≤ multiplicity π A by omega)
    have hA'0 : A' ≠ 0 := by rintro rfl; rw [mul_zero] at hA'; exact hA0 hA'
    have hnu : ¬ IsUnit (π ^ 3) := fun h => hπ.not_isUnit (isUnit_pow_iff (by norm_num) |>.mp h)
    obtain ⟨j, Y, L, hL, hY⟩ := ih _ (hn ▸ natAbs_norm_lt hA0 hA' hnu) A' (C * κ π) (D * π ^ 2)
      rfl hA'0 (mul_ne_zero hC0 (kappa_ne_zero hπ.ne_zero)) (peel_cube hA' hCD)
    exact ⟨j, π * Y, L, hL, by rw [hA', hY]; ring⟩
  · -- a Jacobi-sum prime
    rcases prime_cases hπ with hf | ⟨q, hqF, hq3, -, χ, hχ, -, hass⟩
    · exact absurd hf hfix
    obtain ⟨χ', hχ', hπJ⟩ : ∃ χ' : MulChar (ZMod q) F, ∃ hχ' : orderOf χ' = 3,
        Associated π (EisJacobi.J hχ') := by
      rcases hass with h | h
      · exact ⟨χ, hχ, h⟩
      · exact ⟨χ⁻¹, by rw [orderOf_inv, hχ], h⟩
    set J := EisJacobi.J hχ' with hJdef
    set Jb := EisJacobi.Jbar hχ' with hJbdef
    have hJ : Prime J := EisJacobi.J_prime hχ' (by rw [ZMod.card]; exact hqF.out)
    have hJb : Prime Jb := Jbar_prime hχ'
    have hκJ : κ J = Jb := kappa_J hχ'
    have hκJb : κ Jb = J := by rw [← hκJ, kappa_kappa]
    have hJJb : J * Jb = (q : 𝓞 F) := by
      have := EisJacobi.J_mul_conj hχ'; rwa [ZMod.card] at this
    have hnf : ¬ Associated Jb J := fun h => hfix (fixed_of_assoc hπJ (hκJ ▸ h))
    have hnf' : ¬ Associated J Jb := fun h => hnf h.symm
    have hJA : J ∣ A := hπJ.symm.dvd.trans hπA
    have hfinJ := FiniteMultiplicity.of_prime_left hJ hA0
    have hx1 : 1 ≤ multiplicity J A := hfinJ.le_multiplicity_of_pow_dvd (by rwa [pow_one])
    have hxy : multiplicity Jb A % 3 = (2 * multiplicity J A) % 3 := by
      have := val_constraint κ kappa_kappa hJ hA0 hC0 hCD; rwa [hκJ] at this
    have hq0 : (q : 𝓞 F) ≠ 0 := by rw [← hJJb]; exact mul_ne_zero hJ.ne_zero hJb.ne_zero
    have hgc : ∀ (ψ : MulChar (ZMod q) F) (hψ : orderOf ψ = 3),
        IsGaussCube ((q : 𝓞 F) * EisJacobi.J hψ) := fun ψ hψ => ⟨q, hqF, hq3, ψ, hψ, rfl⟩
    rcases (by omega : multiplicity J A % 3 = 0 ∨ multiplicity J A % 3 = 1 ∨
      multiplicity J A % 3 = 2) with h0 | h1 | h2
    · -- J³ ∣ A
      obtain ⟨A', hA'⟩ := pow_dvd_of_le_multiplicity (show 3 ≤ multiplicity J A by omega)
      have hA'0 : A' ≠ 0 := by rintro rfl; rw [mul_zero] at hA'; exact hA0 hA'
      have hnu : ¬ IsUnit (J ^ 3) := fun h => hJ.not_isUnit (isUnit_pow_iff (by norm_num) |>.mp h)
      obtain ⟨j, Y, L, hL, hY⟩ := ih _ (hn ▸ natAbs_norm_lt hA0 hA' hnu) A' (C * κ J) (D * J ^ 2)
        rfl hA'0 (mul_ne_zero hC0 (kappa_ne_zero hJ.ne_zero)) (peel_cube hA' hCD)
      exact ⟨j, J * Y, L, hL, by rw [hA', hY]; ring⟩
    · -- x ≡ 1, y ≡ 2: J J̄² = q J̄ ∣ A (Gauss cube of χ'⁻¹)
      obtain ⟨A', hA'⟩ := pow_mul_pow_dvd hJ hJb hnf (a := 1) (b := 2)
        (pow_dvd_of_le_multiplicity hx1)
        (pow_dvd_of_le_multiplicity (show 2 ≤ multiplicity Jb A by omega))
      set G := (q : 𝓞 F) * Jb with hGdef
      have hAG : A = G * A' := by rw [hA', hGdef, ← hJJb]; ring
      have hG0 : G ≠ 0 := mul_ne_zero hq0 hJb.ne_zero
      have hGW : G ^ 2 = κ G * Jb ^ 3 := by
        rw [hGdef, map_mul, map_natCast, hκJb, ← hJJb]; ring
      have hnu : ¬ IsUnit G := fun h => hJb.not_isUnit (isUnit_of_mul_isUnit_right h)
      have hA'0 : A' ≠ 0 := by rintro rfl; rw [mul_zero] at hAG; exact hA0 hAG
      obtain ⟨j, Y, L, hL, hY⟩ := ih _ (hn ▸ natAbs_norm_lt hA0 hAG hnu) A' C (D * Jb)
        rfl hA'0 hC0 (peel_gauss hAG hGW hG0 hCD)
      have hχi : orderOf χ'⁻¹ = 3 := by rw [orderOf_inv, hχ']
      refine ⟨j, Y, G :: L, ?_, by rw [hAG, hY, List.prod_cons]; ring⟩
      intro G' hG'
      rcases List.mem_cons.mp hG' with rfl | hG'
      · exact hgc χ'⁻¹ hχi
      · exact hL G' hG'
    · -- x ≡ 2, y ≡ 1: J² J̄ = q J ∣ A (Gauss cube of χ')
      obtain ⟨A', hA'⟩ := pow_mul_pow_dvd hJ hJb hnf (a := 2) (b := 1)
        (pow_dvd_of_le_multiplicity (show 2 ≤ multiplicity J A by omega))
        (pow_dvd_of_le_multiplicity (show 1 ≤ multiplicity Jb A by omega))
      set G := (q : 𝓞 F) * J with hGdef
      have hAG : A = G * A' := by rw [hA', hGdef, ← hJJb]; ring
      have hG0 : G ≠ 0 := mul_ne_zero hq0 hJ.ne_zero
      have hGW : G ^ 2 = κ G * J ^ 3 := by
        rw [hGdef, map_mul, map_natCast, hκJ, ← hJJb]; ring
      have hnu : ¬ IsUnit G := fun h => hJ.not_isUnit (isUnit_of_mul_isUnit_right h)
      have hA'0 : A' ≠ 0 := by rintro rfl; rw [mul_zero] at hAG; exact hA0 hAG
      obtain ⟨j, Y, L, hL, hY⟩ := ih _ (hn ▸ natAbs_norm_lt hA0 hAG hnu) A' C (D * J)
        rfl hA'0 hC0 (peel_gauss hAG hGW hG0 hCD)
      refine ⟨j, Y, G :: L, ?_, by rw [hAG, hY, List.prod_cons]; ring⟩
      intro G' hG'
      rcases List.mem_cons.mp hG' with rfl | hG'
      · exact hgc χ' hχ'
      · exact hL G' hG'

/-- g is a cubic Gauss sum over a prime q ≡ 1 (mod 3), with values in ℂ. -/
def IsGaussSum (g : ℂ) : Prop :=
  ∃ q : ℕ, ∃ _ : Fact q.Prime, 3 ∣ q - 1 ∧ ∃ χ : MulChar (ZMod q) ℂ, orderOf χ = 3 ∧
    ∃ ζ : ℂ, ∃ hζ : IsPrimitiveRoot ζ q, g = gaussSum χ (AddChar.zmodChar q hζ.pow_eq_one)

/-- **Gauss-sum realization:** ι(q J(χ, χ)) = g(χ_ℂ)³. -/
theorem gauss_realization {G : 𝓞 F} (hG : IsGaussCube G) : ∃ g : ℂ, IsGaussSum g ∧ g ^ 3 = ι G := by
  obtain ⟨q, hqF, hq3, χ, hχ, rfl⟩ := hG
  set f : F →+* ℂ := F.val.toRingHom
  have hf : Function.Injective f := Subtype.val_injective
  set χC := χ.ringHomComp f
  have hχC : orderOf χC = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    apply orderOf_eq_prime
    · rw [MulChar.ringHomComp_pow, CubicGauss.pow_three hχ, MulChar.ringHomComp_one]
    · exact (MulChar.ringHomComp_ne_one_iff hf).mpr (CubicGauss.ne_one hχ)
  have hζ := Complex.isPrimitiveRoot_exp q hqF.out.ne_zero
  refine ⟨_, ⟨q, hqF, hq3, χC, hχC, _, hζ, rfl⟩, ?_⟩
  rw [CubicGauss.gaussSum_cube_zmod hχC hζ, map_mul, map_natCast, jacobiSum_ringHomComp]
  rfl

theorem gauss_list : ∀ L : List (𝓞 F), (∀ G ∈ L, IsGaussCube G) →
    ∃ gs : List ℂ, (∀ g ∈ gs, IsGaussSum g) ∧ gs.prod ^ 3 = ι L.prod
  | [], _ => ⟨[], by simp, by simp⟩
  | G :: L, h => by
    obtain ⟨g, hg, hg3⟩ := gauss_realization (h G (by simp))
    obtain ⟨gs, hgs, hgs3⟩ := gauss_list L (fun G' hG' => h G' (by simp [hG']))
    refine ⟨g :: gs, ?_, by rw [List.prod_cons, List.prod_cons, mul_pow, hg3, hgs3, map_mul]⟩
    intro g' hg'
    rcases List.mem_cons.mp hg' with rfl | hg'
    · exact hg
    · exact hgs g' hg'

/-- ζ₉ = e^{2πi/9}. -/
noncomputable def ζ₉ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 9)

theorem ζ₉_cube : ζ₉ ^ 3 = ω := by
  rw [ζ₉, ← Complex.exp_nat_mul]
  show Complex.exp _ = Complex.exp _
  congr 1; push_cast; ring

variable (K : IntermediateField ℚ ℂ) [IsGalois ℚ K] (hK : finrank ℚ K = 3)

include hK in
/-- **Explicit cube root of the radicand:** ι(A) = (ζ₉^j · ι(Y) · g₁ ⋯ g_m)³. -/
theorem radicand_cube_root : ∃ β : ℂ, β ∈ M K ∧ β ^ 3 ∈ F ∧ β ∉ F ∧ M K = ℚ⟮ω, β⟯ ∧
    ∃ s A : 𝓞 F, s ≠ 0 ∧ A ≠ 0 ∧ ι s ^ 3 * β ^ 3 = ι A ∧
      ∃ j : ℕ, ∃ Y : 𝓞 F, ∃ gs : List ℂ, (∀ g ∈ gs, IsGaussSum g) ∧
        ι A = (ζ₉ ^ j * ι Y * gs.prod) ^ 3 := by
  obtain ⟨β, hβM, hβ3, hβF, hM, s, A, C, D, hs0, hA0, hC0, hsA, hCD⟩ := integral_radicand K hK
  refine ⟨β, hβM, hβ3, hβF, hM, s, A, hs0, hA0, hsA, ?_⟩
  obtain ⟨j, Y, L, hL, hY⟩ := reconstruct _ A C D rfl hA0 hC0 hCD
  obtain ⟨gs, hgs, hgs3⟩ := gauss_list L hL
  refine ⟨j, Y, gs, hgs, ?_⟩
  rw [hY, map_mul, map_mul, map_pow, map_pow, ι_ω, mul_pow, mul_pow, ← pow_mul, mul_comm j 3,
    pow_mul, ζ₉_cube, hgs3]

end CubicRecon

#print axioms CubicRecon.reconstruct
#print axioms CubicRecon.gauss_realization
#print axioms CubicRecon.radicand_cube_root
