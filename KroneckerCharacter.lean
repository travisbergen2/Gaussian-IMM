import Mathlib

/-!
# KroneckerCharacter — the quadratic Dirichlet character χ_D of a fundamental discriminant

Generic (imports only Mathlib; no number fields). For odd o, `jacobiChar o` is n ↦ J(n | o)
(Jacobi symbol), a Dirichlet character mod o. For an integer D let
* `oddPart D` = |D|/8 if 8 ∣ D, |D|/4 if 4 ∣ D, 8 ∤ D, |D| otherwise;
* `twoChar D` = χ₈ (8 ∣ D, D/8 ≡ 1 mod 4), χ₈′ (8 ∣ D, D/8 ≡ 3 mod 4), χ₄ (4 ∥ D), 1 (D odd),
  lifted to level |D|;
* `kronecker D = twoChar D · jacobiChar (oddPart D)`, a Dirichlet character mod |D|.
For a fundamental discriminant D the four cases are D ≡ 1 (4); D = 4m, m ≡ 3 (4); D = 8u with
u ≡ 1 or 3 (4).
* `kronecker_prime`: χ_D(q) = (D/q) (Legendre symbol) for every odd prime q ∤ D.
The sign and reciprocity bookkeeping is isolated in `jacobi_int_left`:
J(a | q) = (1 if a ≡ 1 mod 4, χ₄(q) otherwise) · J(q | |a|) for odd a and odd q.
-/

open ZMod

namespace Kronecker

/-! ### The Jacobi character -/

/-- n ↦ J(n | o) as a Dirichlet character mod o (o odd). -/
def jacobiChar (o : ℕ) [NeZero o] : DirichletCharacter ℂ o where
  toFun x := (jacobiSym (x.val : ℤ) o : ℂ)
  map_one' := by
    rcases eq_or_ne o 1 with h | h
    · subst h; simp [jacobiSym]
    · have : Fact (1 < o) := ⟨by have := NeZero.pos o; omega⟩
      simp [ZMod.val_one, jacobiSym.one_left]
  map_mul' x y := by
    show ((jacobiSym ((x * y).val : ℤ) o : ℤ) : ℂ) =
      ((jacobiSym (x.val : ℤ) o : ℤ) : ℂ) * ((jacobiSym (y.val : ℤ) o : ℤ) : ℂ)
    rw [← Int.cast_mul, ← jacobiSym.mul_left, ZMod.val_mul]
    congr 1
    apply jacobiSym.mod_left'
    push_cast
    simp [Int.emod_emod_of_dvd]
  map_nonunit' x hx := by
    have : jacobiSym (x.val : ℤ) o = 0 := by
      rw [jacobiSym.eq_zero_iff_not_coprime, Int.gcd_natCast_natCast]
      intro h
      apply hx
      rw [← ZMod.natCast_zmod_val x]
      exact (ZMod.isUnit_iff_coprime _ _).mpr h
    show ((jacobiSym (x.val : ℤ) o : ℤ) : ℂ) = 0
    rw [this, Int.cast_zero]

theorem jacobiChar_apply (o : ℕ) [NeZero o] (n : ℤ) :
    jacobiChar o (n : ZMod o) = (jacobiSym n o : ℂ) := by
  show ((jacobiSym ((n : ZMod o).val : ℤ) o : ℤ) : ℂ) = _
  rw [ZMod.val_intCast, ← jacobiSym.mod_left]

/-! ### Reciprocity bookkeeping -/

/-- J(a | q) for odd a, odd q, in terms of J(q | |a|). -/
theorem jacobi_int_left {a : ℤ} (ha : Odd a) {q : ℕ} (hq : Odd q) :
    jacobiSym a q = (if a % 4 = 1 then 1 else χ₄ q) * jacobiSym q a.natAbs := by
  have hq2 : q % 2 = 1 := Nat.odd_iff.mp hq
  have hn : Odd a.natAbs := Int.natAbs_odd.mpr ha
  have hrec := jacobiSym.quadratic_reciprocity hn hq
  have hχ := χ₄_eq_neg_one_pow hq2
  have hn4 : a.natAbs % 4 = 1 ∨ a.natAbs % 4 = 3 := by
    have := Nat.odd_iff.mp hn; omega
  rcases Int.natAbs_eq a with h | h
  · -- a ≥ 0
    rw [h] at hrec ⊢
    simp only [Int.natAbs_natCast] at hrec ⊢
    rw [hrec]
    rcases hn4 with h4 | h4
    · have : a.natAbs / 2 % 2 = 0 := by omega
      rw [if_pos (by omega), Even.neg_one_pow (Nat.even_mul.mpr (Or.inl (Nat.even_iff.mpr this)))]
    · rw [if_neg (by omega), hχ]
      have hodd : Odd (a.natAbs / 2) := Nat.odd_iff.mpr (by omega)
      rw [pow_mul, hodd.neg_one_pow]
  · rw [h, jacobiSym.neg _ hq, hrec]
    simp only [Int.natAbs_neg, Int.natAbs_natCast]
    rcases hn4 with h4 | h4
    · have : a.natAbs / 2 % 2 = 0 := by omega
      rw [Even.neg_one_pow (Nat.even_mul.mpr (Or.inl (Nat.even_iff.mpr this))), if_neg (by omega)]
      ring
    · have hodd : Odd (a.natAbs / 2) := Nat.odd_iff.mpr (by omega)
      rw [if_pos (by omega), pow_mul, hodd.neg_one_pow, ← hχ]
      have : χ₄ (q : ZMod 4) * χ₄ (q : ZMod 4) = 1 := by
        rw [hχ, ← pow_add, ← two_mul, pow_mul]; simp
      linear_combination (jacobiSym q a.natAbs) * this

theorem jacobi_four {q : ℕ} (hq : Odd q) : jacobiSym 4 q = 1 := by
  have : (4 : ℤ) = 2 ^ 2 := by norm_num
  rw [this]
  apply jacobiSym.sq_one'
  rw [Int.gcd_comm, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, Int.gcd_natCast_natCast]
  have := Nat.odd_iff.mp hq
  have h2 : Nat.Coprime 2 q := (Nat.Prime.coprime_iff_not_dvd (n := q) Nat.prime_two).mpr (by omega)
  first | exact h2 | exact h2.symm

/-! ### The 2-adic factor and the odd part -/

/-- χ₄, χ₈, χ₈′ as complex Dirichlet characters. -/
noncomputable def c4 : DirichletCharacter ℂ 4 := χ₄.ringHomComp (Int.castRingHom ℂ)
noncomputable def c8 : DirichletCharacter ℂ 8 := χ₈.ringHomComp (Int.castRingHom ℂ)
noncomputable def c8' : DirichletCharacter ℂ 8 := χ₈'.ringHomComp (Int.castRingHom ℂ)

open Classical in
/-- The 2-adic factor of χ_D, at level |D|. -/
noncomputable def twoChar (D : ℤ) : DirichletCharacter ℂ D.natAbs :=
  if h8 : 8 ∣ D.natAbs then
    (if D / 8 % 4 = 1 then DirichletCharacter.changeLevel h8 c8
      else DirichletCharacter.changeLevel h8 c8')
  else if h4 : 4 ∣ D.natAbs then DirichletCharacter.changeLevel h4 c4 else 1

open Classical in
/-- The odd part of |D| (for a fundamental discriminant). -/
noncomputable def oddPart (D : ℤ) : ℕ :=
  if 8 ∣ D.natAbs then D.natAbs / 8 else if 4 ∣ D.natAbs then D.natAbs / 4 else D.natAbs

theorem oddPart_dvd (D : ℤ) : oddPart D ∣ D.natAbs := by
  unfold oddPart; split_ifs <;> simp [*]

theorem oddPart_ne_zero {D : ℤ} (hD : D ≠ 0) : oddPart D ≠ 0 := fun h =>
  Int.natAbs_ne_zero.mpr hD (Nat.eq_zero_of_zero_dvd (h ▸ oddPart_dvd D))

/-- **The Kronecker character χ_D**, a Dirichlet character mod |D|. -/
noncomputable def kronecker (D : ℤ) (hD : D ≠ 0) : DirichletCharacter ℂ D.natAbs :=
  haveI : NeZero (oddPart D) := ⟨oddPart_ne_zero hD⟩
  twoChar D * DirichletCharacter.changeLevel (oddPart_dvd D) (jacobiChar (oddPart D))

open Classical in
/-- The value of the 2-adic factor at n. -/
noncomputable def twoVal (D : ℤ) (n : ℕ) : ℤ :=
  if 8 ∣ D.natAbs then (if D / 8 % 4 = 1 then χ₈ n else χ₈' n)
  else if 4 ∣ D.natAbs then χ₄ n else 1

theorem cast_lift {N M : ℕ} (h : M ∣ N) (χ : DirichletCharacter ℂ M) {n : ℕ} (hn : n.Coprime N) :
    DirichletCharacter.changeLevel h χ (n : ZMod N) = χ (n : ZMod M) := by
  rw [← ZMod.coe_unitOfCoprime n hn, DirichletCharacter.changeLevel_eq_cast_of_dvd,
    ZMod.coe_unitOfCoprime, ZMod.cast_natCast h]

/-- **χ_D(n) = twoVal · J(n | oddPart D)** for n coprime to D. -/
theorem kronecker_apply {D : ℤ} (hD : D ≠ 0) {n : ℕ} (hn : n.Coprime D.natAbs) :
    kronecker D hD (n : ZMod D.natAbs) = ((twoVal D n * jacobiSym n (oddPart D) : ℤ) : ℂ) := by
  have : NeZero (oddPart D) := ⟨oddPart_ne_zero hD⟩
  rw [kronecker, MulChar.coeToFun_mul, Pi.mul_apply, cast_lift _ _ hn, Int.cast_mul,
    ← Int.cast_natCast (R := ZMod (oddPart D)), jacobiChar_apply]
  congr 1
  unfold twoChar twoVal
  split_ifs <;> simp [cast_lift _ _ hn, c4, c8, c8']
  exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n _).mpr hn)

theorem jacobi_eight {q : ℕ} (hq : Odd q) : jacobiSym 8 q = χ₈ q := by
  rw [show (8 : ℤ) = 2 * 4 by norm_num, jacobiSym.mul_left, jacobi_four hq, jacobiSym.at_two hq,
    mul_one]

/-- **The integer identity:** (D/q) = twoVal D q · J(q | oddPart D). -/
theorem legendre_eq {D : ℤ} (hD : Int.IsFundamentalDiscr D) (q : ℕ) [Fact q.Prime]
    (hq2 : q ≠ 2) : legendreSym q D = twoVal D q * jacobiSym q (oddPart D) := by
  have hq : Odd q := (Fact.out : q.Prime).odd_of_ne_two hq2
  have h4i : ∀ k : ℕ, (k ∣ D.natAbs ↔ (k : ℤ) ∣ D) := fun k => Int.ofNat_dvd_left.symm
  rw [jacobiSym.legendreSym.to_jacobiSym]
  rcases Int.isFundamentalDiscr_iff_squarefree.mp hD with ⟨h1, -⟩ | ⟨h0, -, h23⟩
  · -- D ≡ 1 mod 4
    have n4 : ¬ 4 ∣ D.natAbs := by rw [h4i]; push_cast; omega
    have n8 : ¬ 8 ∣ D.natAbs := by rw [h4i]; push_cast; omega
    simp only [twoVal, oddPart, if_neg n4, if_neg n8, one_mul]
    rw [jacobi_int_left (Int.odd_iff.mpr (by omega)) hq, if_pos h1, one_mul]
  rcases h23 with h2 | h3
  · -- D = 8u
    have y8 : 8 ∣ D.natAbs := by rw [h4i]; push_cast; omega
    set u := D / 8
    have hDu : D = 8 * u := by omega
    have hu : Odd u := Int.odd_iff.mpr (by omega)
    have habs : D.natAbs / 8 = u.natAbs := by
      rw [Int.natAbs_ediv_of_dvd (by omega)]; rfl
    have hJ : jacobiSym D q = jacobiSym 8 q * jacobiSym u q := by
      rw [hDu, jacobiSym.mul_left]
    simp only [twoVal, oddPart, if_pos y8, habs, show D / 8 = u from rfl]
    rw [hJ, jacobi_eight hq, jacobi_int_left hu hq]
    split_ifs with hu1
    · ring
    · have := χ₈'_int_eq_χ₄_mul_χ₈ (q : ℤ)
      simp only [Int.cast_natCast] at this
      rw [this]; ring
  · -- D = 4m, m ≡ 3 mod 4
    have y4 : 4 ∣ D.natAbs := by rw [h4i]; push_cast; omega
    have n8 : ¬ 8 ∣ D.natAbs := by rw [h4i]; push_cast; omega
    set m := D / 4
    have hDm : D = 4 * m := by omega
    have hm : Odd m := Int.odd_iff.mpr (by omega)
    have habs : D.natAbs / 4 = m.natAbs := by
      rw [Int.natAbs_ediv_of_dvd (by omega)]; rfl
    have hJ : jacobiSym D q = jacobiSym 4 q * jacobiSym m q := by
      rw [hDm, jacobiSym.mul_left]
    simp only [twoVal, oddPart, if_neg n8, if_pos y4, habs]
    rw [hJ, jacobi_four hq, one_mul, jacobi_int_left hm hq, if_neg (by omega)]

/-- **χ_D(q) = (D/q)** for every odd prime q ∤ D. -/
theorem kronecker_prime {D : ℤ} (hD : Int.IsFundamentalDiscr D) (q : ℕ) [Fact q.Prime]
    (hq2 : q ≠ 2) (hqD : ¬ (q : ℤ) ∣ D) :
    kronecker D hD.ne_zero (q : ZMod D.natAbs) = (legendreSym q D : ℂ) := by
  have hcop : q.Coprime D.natAbs :=
    (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr (fun h => hqD (Int.ofNat_dvd_left.mpr h))
  rw [kronecker_apply hD.ne_zero hcop, legendre_eq hD q hq2]

end Kronecker

#print axioms Kronecker.jacobiChar
#print axioms Kronecker.jacobi_int_left
#print axioms Kronecker.kronecker
#print axioms Kronecker.kronecker_apply
#print axioms Kronecker.kronecker_prime
