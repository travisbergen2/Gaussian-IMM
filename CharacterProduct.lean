import Mathlib

/-!
# CharacterProduct — ∏ over all characters of (1 − φ(a) x) = (1 − x^f)^{N/f}

Pure algebra. A finite commutative group A of order N, a ∈ A of order f, characters A →* ℂˣ:

    ∏_{φ : A →* ℂˣ} (1 − φ(a)·x) = (1 − x^f)^{N/f}.

Route: the evaluation map φ ↦ φ(a) has image exactly the f-th roots of unity (an extension of a
faithful character of ⟨a⟩ hits a primitive root), all fibers have the same size N/f, and
∏_{ζ^f = 1} (1 − ζx) = 1 − x^f.
-/

open Finset Polynomial

namespace CharProd

/-- ∏_{ζ^f = 1} (1 − ζ x) = 1 − x^f. -/
theorem prod_one_sub_roots {f : ℕ} (hf : 0 < f) (x : ℂ) :
    ∏ z ∈ nthRootsFinset f (1 : ℂ), (1 - z * x) = 1 - x ^ f := by
  have hζ := Complex.isPrimitiveRoot_exp f hf.ne'
  rcases eq_or_ne x 0 with rfl | hx
  · simp [hf.ne']
  have h := congrArg (eval x⁻¹) (X_pow_sub_one_eq_prod hf hζ)
  simp only [eval_sub, eval_pow, eval_X, eval_one, eval_prod, eval_C] at h
  calc ∏ z ∈ nthRootsFinset f (1 : ℂ), (1 - z * x)
      = ∏ z ∈ nthRootsFinset f (1 : ℂ), (x * (x⁻¹ - z)) := by
        refine prod_congr rfl fun z _ => ?_; field_simp
    _ = x ^ f * (x⁻¹ ^ f - 1) := by
        rw [prod_mul_distrib, prod_const, h, IsPrimitiveRoot.card_nthRootsFinset hζ]
    _ = 1 - x ^ f := by rw [inv_pow]; field_simp

variable {A : Type*} [CommGroup A] [Finite A]

/-- There is a character taking a to a primitive (orderOf a)-th root of unity. -/
theorem exists_char_primitive (a : A) :
    ∃ φ : A →* ℂˣ, IsPrimitiveRoot ((φ a : ℂˣ) : ℂ) (orderOf a) := by
  set Z := Subgroup.zpowers a
  set g : Z := ⟨a, Subgroup.mem_zpowers a⟩
  obtain ⟨e⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity Z ℂ
  set ψ := e.symm g
  have hgen : ∀ z : Z, ∃ m : ℤ, z = g ^ m := fun ⟨z, hz⟩ => by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ⟨m, Subtype.ext (by simp [g])⟩
  have hord : orderOf (ψ g) = orderOf a := by
    rw [← Subgroup.orderOf_mk a (Subgroup.mem_zpowers a), ← MulEquiv.orderOf_eq e.symm g]
    refine (orderOf_eq_orderOf_iff.mpr fun k => ?_).symm
    constructor
    · intro h; rw [← MonoidHom.pow_apply, h, MonoidHom.one_apply]
    · intro h
      refine MonoidHom.ext fun z => ?_
      obtain ⟨m, rfl⟩ := hgen z
      rw [MonoidHom.pow_apply, map_zpow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, h, one_zpow, MonoidHom.one_apply]
  obtain ⟨φ, hφ⟩ := MonoidHom.domRestrict_surjective (M := ℂ) Z ψ
  refine ⟨φ, ?_⟩
  have : φ a = ψ g := by rw [← hφ]; rfl
  rw [this, IsPrimitiveRoot.coe_units_iff, ← hord]
  exact IsPrimitiveRoot.orderOf _

theorem card_dual : Nat.card (A →* ℂˣ) = Nat.card A :=
  CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity A ℂ

theorem finite_dual : Finite (A →* ℂˣ) :=
  Nat.finite_of_card_ne_zero (by rw [card_dual]; exact Nat.card_pos.ne')

/-- **Character product:** ∏_φ (1 − φ(a) x) = (1 − x^f)^{N/f}, f = orderOf a, N = |A|. -/
theorem prod_one_sub_char [Fintype (A →* ℂˣ)] (a : A) (x : ℂ) :
    ∏ φ : A →* ℂˣ, (1 - ((φ a : ℂˣ) : ℂ) * x) =
      (1 - x ^ orderOf a) ^ (Nat.card A / orderOf a) := by
  classical
  have hf : 0 < orderOf a := orderOf_pos a
  have : NeZero (orderOf a) := ⟨hf.ne'⟩
  let E : (A →* ℂˣ) →* ℂ :=
    { toFun := fun φ => ((φ a : ℂˣ) : ℂ)
      map_one' := by simp
      map_mul' := fun φ ψ => by simp }
  have hE : ∀ φ, E φ = ((φ a : ℂˣ) : ℂ) := fun _ => rfl
  obtain ⟨φ0, hφ0⟩ := exists_char_primitive a
  have himage : univ.image E = nthRootsFinset (orderOf a) (1 : ℂ) := by
    ext z
    simp only [mem_image, mem_univ, true_and, mem_nthRootsFinset hf]
    constructor
    · rintro ⟨φ, rfl⟩
      rw [hE, ← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
    · intro hz
      obtain ⟨k, -, hk⟩ := hφ0.eq_pow_of_pow_eq_one hz
      exact ⟨φ0 ^ k, by rw [MonoidHom.map_pow E φ0 k, hE, hk]⟩
  have hcard_img : (univ.image E).card = orderOf a := by
    rw [himage, hφ0.card_nthRootsFinset]
  have hfib : ∀ z ∈ univ.image E, #{φ | E φ = z} = #{φ | E φ = 1} := by
    intro z hz
    obtain ⟨φ, -, rfl⟩ := mem_image.mp hz
    exact MonoidHom.card_fiber_eq_of_mem_range E ⟨φ, rfl⟩ ⟨1, map_one E⟩
  have htotal : Nat.card A = orderOf a * #{φ | E φ = 1} := by
    rw [← card_dual, Nat.card_eq_fintype_card, ← card_univ, card_eq_sum_card_image E univ,
      sum_congr rfl hfib, sum_const, hcard_img, smul_eq_mul]
  have hc : #{φ | E φ = 1} = Nat.card A / orderOf a := by
    rw [htotal, Nat.mul_div_cancel_left _ hf]
  have h1 : ∏ φ : A →* ℂˣ, (1 - ((φ a : ℂˣ) : ℂ) * x) =
      ∏ z ∈ univ.image E, (1 - z * x) ^ #{φ ∈ univ | E φ = z} :=
    prod_comp (fun z => 1 - z * x) E
  have h2 : ∏ z ∈ univ.image E, (1 - z * x) ^ #{φ ∈ univ | E φ = z} =
      ∏ z ∈ univ.image E, (1 - z * x) ^ (Nat.card A / orderOf a) :=
    prod_congr rfl fun z hz => by rw [← hc, ← hfib z hz]
  rw [h1, h2, prod_pow, himage, prod_one_sub_roots hf]

/-- Characters trivial on H ≃ characters of A ⧸ H. -/
noncomputable def perpEquiv (H : Subgroup A) :
    {φ : A →* ℂˣ // ∀ h ∈ H, φ h = 1} ≃ (A ⧸ H →* ℂˣ) :=
  (Equiv.subtypeEquivRight fun φ => by
      rw [MonoidHom.mem_ker, MonoidHom.domRestrictHom_apply, MonoidHom.domRestrict_eq_one_iff]).trans
    (MonoidHom.domRestrictHomKerEquiv ℂˣ H).toEquiv

theorem perpEquiv_apply (H : Subgroup A) (φ : {φ : A →* ℂˣ // ∀ h ∈ H, φ h = 1}) (g : A) :
    perpEquiv H φ (QuotientGroup.mk g) = φ.1 g := rfl

/-- **Characters trivial on H:** ∏ (1 − φ(g) x) = (1 − x^f)^{[A:H]/f}, f = order of gH in A/H. -/
theorem prod_one_sub_perp (H : Subgroup A) [Fintype {φ : A →* ℂˣ // ∀ h ∈ H, φ h = 1}]
    (g : A) (x : ℂ) :
    ∏ φ : {φ : A →* ℂˣ // ∀ h ∈ H, φ h = 1}, (1 - ((φ.1 g : ℂˣ) : ℂ) * x) =
      (1 - x ^ orderOf (QuotientGroup.mk g : A ⧸ H)) ^
        (H.index / orderOf (QuotientGroup.mk g : A ⧸ H)) := by
  classical
  have := finite_dual (A := A ⧸ H)
  have : Fintype (A ⧸ H →* ℂˣ) := Fintype.ofFinite _
  rw [Fintype.prod_equiv (perpEquiv H) _ (fun ψ => 1 - ((ψ (QuotientGroup.mk g) : ℂˣ) : ℂ) * x)
    (fun φ => by rw [perpEquiv_apply]), prod_one_sub_char]
  rfl

end CharProd

#print axioms CharProd.prod_one_sub_char
#print axioms CharProd.prod_one_sub_perp
