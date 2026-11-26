import Mathlib

/-!
# ConductorProduct — conductors multiply over coprime moduli

Generic (imports only Mathlib, no number fields). For Dirichlet characters χ₁ mod m, χ₂ mod n with
m, n coprime, let `mulLift χ₁ χ₂ = χ₁ · χ₂` lifted to level mn.
* `mulLift_apply_units`: (χ₁χ₂)(A) = χ₁(A mod m) · χ₂(A mod n) on units;
* `conductor_dvd`: cond(χ₁χ₂) ∣ cond χ₁ · cond χ₂ (both factor through their conductors);
* `dvd_conductor_of_component`: if χ (level N = mn) agrees with χ₁(A mod m) whenever A ≡ 1 (mod n),
  then cond χ₁ ∣ cond χ (lift a unit a mod m with a ≡ 1 mod gcd(cond χ, m) by CRT to A ≡ a mod m,
  A ≡ 1 mod n; then A ≡ 1 mod cond χ, so χ₁(a) = χ(A) = 1);
* `conductor_mulLift`: **cond(χ₁χ₂) = cond χ₁ · cond χ₂**;
* `isPrimitive_mulLift`: products of primitive characters of coprime levels are primitive;
* `orderOf_mulLift_three`: two order-3 characters of coprime levels multiply to an order-3 character.
-/

open DirichletCharacter

namespace CondProd

variable {R : Type*} [CommMonoidWithZero R] {m n : ℕ}

/-- χ₁ · χ₂ at level mn. -/
noncomputable def mulLift (χ₁ : DirichletCharacter R m) (χ₂ : DirichletCharacter R n) :
    DirichletCharacter R (m * n) :=
  changeLevel (dvd_mul_right m n) χ₁ * changeLevel (dvd_mul_left n m) χ₂

theorem mulLift_apply_units (χ₁ : DirichletCharacter R m) (χ₂ : DirichletCharacter R n)
    (A : (ZMod (m * n))ˣ) :
    mulLift χ₁ χ₂ A = χ₁ (ZMod.unitsMap (dvd_mul_right m n) A) *
      χ₂ (ZMod.unitsMap (dvd_mul_left n m) A) := by
  rw [mulLift, MulChar.coeToFun_mul, Pi.mul_apply, changeLevel_eq_cast_of_dvd,
    changeLevel_eq_cast_of_dvd, ZMod.unitsMap_val, ZMod.unitsMap_val]

/-- **cond(χ₁χ₂) ∣ cond χ₁ · cond χ₂.** -/
theorem conductor_dvd [NeZero m] [NeZero n] (χ₁ : DirichletCharacter R m)
    (χ₂ : DirichletCharacter R n) :
    conductor (mulLift χ₁ χ₂) ∣ conductor χ₁ * conductor χ₂ := by
  have h1 := conductor_dvd_level χ₁
  have h2 := conductor_dvd_level χ₂
  have hd : conductor χ₁ * conductor χ₂ ∣ m * n := Nat.mul_dvd_mul h1 h2
  have : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  apply (mem_conductorSet_iff_conductor_dvd _ hd).mp
  refine ⟨hd, mulLift χ₁.primitiveCharacter χ₂.primitiveCharacter, ?_⟩
  rw [mulLift, mulLift, map_mul, ← changeLevel_trans, ← changeLevel_trans]
  conv_lhs => rw [← changeLevel_primitiveCharacter χ₁, ← changeLevel_primitiveCharacter χ₂,
    ← changeLevel_trans, ← changeLevel_trans]

/-- **A component's conductor divides the conductor of the whole.** -/
theorem dvd_conductor_of_component {N : ℕ} [NeZero N] [NeZero m] (hN : N = m * n)
    (hcop : m.Coprime n) (hm : m ∣ N) (hn : n ∣ N) (χ : DirichletCharacter R N)
    (χ₁ : DirichletCharacter R m)
    (h : ∀ A : (ZMod N)ˣ, ZMod.unitsMap hn A = 1 → χ A = χ₁ (ZMod.unitsMap hm A)) :
    conductor χ₁ ∣ conductor χ := by
  set c := conductor χ
  have hc : c ∣ N := conductor_dvd_level χ
  set d := Nat.gcd c m
  have hdm : d ∣ m := Nat.gcd_dvd_right c m
  have : NeZero d := ⟨(Nat.gcd_pos_of_pos_right c (NeZero.pos m)).ne'⟩
  suffices hf : χ₁.FactorsThrough d from
    ((mem_conductorSet_iff_conductor_dvd χ₁ hdm).mp hf).trans (Nat.gcd_dvd_left c m)
  rw [factorsThrough_iff_ker_unitsMap hdm]
  intro a ha
  rw [MonoidHom.mem_ker] at ha ⊢
  apply Units.ext
  rw [MulChar.coe_toUnitHom, Units.val_one]
  -- CRT lift
  set av := (a : ZMod m).val
  obtain ⟨kv, hk1, hk2⟩ := Nat.chineseRemainder hcop av 1
  have hav : av.Coprime m := ZMod.val_coe_unit_coprime a
  have hkm : kv.Coprime m := by
    have := Nat.ModEq.gcd_eq hk1; rw [Nat.Coprime, this]; exact hav
  have hkn : kv.Coprime n := by
    have := Nat.ModEq.gcd_eq hk2; rw [Nat.Coprime, this, Nat.gcd_one_left]
  have hkN : kv.Coprime N := by rw [hN]; exact Nat.Coprime.mul_right hkm hkn
  set A := ZMod.unitOfCoprime kv hkN
  have hAm : ZMod.unitsMap hm A = a := by
    apply Units.ext
    rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ZMod.cast_natCast hm,
      ← ZMod.natCast_zmod_val (a : ZMod m), ZMod.natCast_eq_natCast_iff]
    exact hk1
  have hAn : ZMod.unitsMap hn A = 1 := by
    apply Units.ext
    rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ZMod.cast_natCast hn, Units.val_one,
      ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
    exact hk2
  -- A ≡ 1 mod c
  have havd : av ≡ 1 [MOD d] := by
    have h1 := congrArg (fun u : (ZMod d)ˣ => (u : ZMod d)) ha
    simp only [ZMod.unitsMap_val, Units.val_one] at h1
    rw [ZMod.cast_eq_val, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff] at h1
    exact h1
  have hkd : kv ≡ 1 [MOD d] := (hk1.of_dvd hdm).trans havd
  have hkdn : kv ≡ 1 [MOD d * n] :=
    (Nat.modEq_and_modEq_iff_modEq_mul (Nat.Coprime.coprime_dvd_left hdm hcop)).mp ⟨hkd, hk2⟩
  have hcdn : c ∣ d * n := Nat.dvd_gcd_mul_iff_dvd_mul.mpr (hN ▸ hc)
  have hkc : kv ≡ 1 [MOD c] := hkdn.of_dvd hcdn
  have hAc : ZMod.unitsMap hc A = 1 := by
    apply Units.ext
    rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ZMod.cast_natCast hc, Units.val_one,
      ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
    exact hkc
  have hχA : χ A = 1 := by
    have hker := (factorsThrough_iff_ker_unitsMap hc).mp (factorsThrough_conductor χ)
    have := hker (MonoidHom.mem_ker.mpr hAc)
    rw [MonoidHom.mem_ker] at this
    have := congrArg (fun u : Rˣ => (u : R)) this
    simpa [MulChar.coe_toUnitHom] using this
  rw [← hAm, ← h A hAn, hχA]

/-- **cond(χ₁χ₂) = cond χ₁ · cond χ₂** for coprime levels. -/
theorem conductor_mulLift [NeZero m] [NeZero n] (hcop : m.Coprime n)
    (χ₁ : DirichletCharacter R m) (χ₂ : DirichletCharacter R n) :
    conductor (mulLift χ₁ χ₂) = conductor χ₁ * conductor χ₂ := by
  have : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  apply Nat.dvd_antisymm (conductor_dvd χ₁ χ₂)
  have h1 : conductor χ₁ ∣ conductor (mulLift χ₁ χ₂) := by
    apply dvd_conductor_of_component rfl hcop (dvd_mul_right m n) (dvd_mul_left n m)
    intro A hA
    rw [mulLift_apply_units, hA, Units.val_one, map_one, mul_one]
  have h2 : conductor χ₂ ∣ conductor (mulLift χ₁ χ₂) := by
    apply dvd_conductor_of_component (mul_comm m n) hcop.symm (dvd_mul_left n m)
      (dvd_mul_right m n)
    intro A hA
    rw [mulLift_apply_units, hA, Units.val_one, map_one, one_mul]
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
    (Nat.Coprime.coprime_dvd_left (conductor_dvd_level χ₁)
      (Nat.Coprime.coprime_dvd_right (conductor_dvd_level χ₂) hcop)) h1 h2

/-- Products of primitive characters of coprime levels are primitive. -/
theorem isPrimitive_mulLift [NeZero m] [NeZero n] (hcop : m.Coprime n)
    {χ₁ : DirichletCharacter R m} {χ₂ : DirichletCharacter R n} (h₁ : χ₁.IsPrimitive)
    (h₂ : χ₂.IsPrimitive) : (mulLift χ₁ χ₂).IsPrimitive := by
  show conductor (mulLift χ₁ χ₂) = m * n
  rw [conductor_mulLift hcop, h₁, h₂]

/-- χ₁³ = χ₂³ = 1 ⇒ (χ₁χ₂)³ = 1, and the product is nontrivial if χ₁ is (coprime levels). -/
theorem mulLift_pow_three [NeZero m] [NeZero n] (hcop : m.Coprime n)
    {χ₁ : DirichletCharacter R m} {χ₂ : DirichletCharacter R n}
    (h₁ : χ₁ ^ 3 = 1) (h₂ : χ₂ ^ 3 = 1) (hne : χ₁ ≠ 1) :
    mulLift χ₁ χ₂ ^ 3 = 1 ∧ mulLift χ₁ χ₂ ≠ 1 := by
  refine ⟨?_, ?_⟩
  · rw [mulLift, mul_pow, ← map_pow, ← map_pow, h₁, h₂, map_one, map_one, one_mul]
  · intro h
    apply hne
    rw [eq_one_iff_conductor_eq_one] at h ⊢
    rw [conductor_mulLift hcop] at h
    exact Nat.eq_one_of_mul_eq_one_right h

end CondProd

#print axioms CondProd.conductor_dvd
#print axioms CondProd.dvd_conductor_of_component
#print axioms CondProd.conductor_mulLift
#print axioms CondProd.isPrimitive_mulLift
#print axioms CondProd.mulLift_pow_three
