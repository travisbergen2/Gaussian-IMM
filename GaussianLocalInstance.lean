import QuadraticLocalIdealCount
import GaussianIdealCounting

/-!
# GaussianLocalInstance — step 2: the generic local count recovers the Gaussian counts

For each kind of rational prime, the prime ideals of ℤ[i] over p (from the baseline's ideal
factorizations) are shown to satisfy the hypotheses of `LocalCount.card_ideals_norm_prime_pow`,
including **exhaustion** (every prime ideal dividing (p) is one of them). The generic theorem then
gives a(pᵏ), which is compared with the baseline's independently proved counts.
-/

open Ideal QuadraticAlgebra LocalCount

/-- A prime ideal dividing a prime ideal equals it. -/
theorem eq_of_prime_dvd_prime {Q P : Ideal Zi} (hQ : Prime Q) (hP : Prime P) (h : Q ∣ P) : Q = P :=
  associated_iff_eq.mp (hQ.associated_of_dvd hP h)

theorem prime_of_absNorm_prime {I : Ideal Zi} {p : ℕ} (hp : p.Prime) (h : absNorm I = p) :
    Prime I := by
  have h0 : I ≠ ⊥ := by intro hb; rw [hb, absNorm_bot] at h; exact hp.ne_zero h.symm
  exact prime_of_isPrime h0 (isPrime_of_absNorm_prime hp h)

/-! ## Ramified: p = 2, (f, g) = (1, 1) -/

theorem generic_ramified (k : ℕ) : a (2 ^ k) = 1 := by
  have hN := ramified_norm
  have hP := prime_of_absNorm_prime Nat.prime_two hN
  rw [a, card_ideals_norm_prime_pow (P := ![span {(1 + ω : Zi)}]) (f := 1) (by norm_num)
    (fun i => by fin_cases i; simpa using hP) (fun i j _ => Subsingleton.elim i j)
    (fun Q hQ hdvd => ⟨0, by
      rw [show ((2 : ℕ) : Zi) = 2 by norm_num, two_ramifies] at hdvd
      exact eq_of_prime_dvd_prime hQ hP (hQ.dvd_of_dvd_pow hdvd)⟩)
    (fun i => by fin_cases i; simpa using hN) k]
  exact card_ramified k

/-! ## Split: p ≡ 1 mod 4, (f, g) = (1, 2) -/

theorem generic_split {p : ℕ} [hp : Fact p.Prime] (h1 : p % 4 = 1) (k : ℕ) : a (p ^ k) = k + 1 := by
  obtain ⟨x, y, hxy, hsplit, hne⟩ := split_prime h1
  obtain ⟨n1, n2, -, -⟩ := split_factors_prime hp.out hxy
  have hP1 := prime_of_absNorm_prime hp.out n1
  have hP2 := prime_of_absNorm_prime hp.out n2
  rw [a, card_ideals_norm_prime_pow (P := ![span {(⟨x, y⟩ : Zi)}, span {(⟨x, -y⟩ : Zi)}]) (f := 1)
    hp.out.one_lt
    (fun i => by
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one] <;> assumption)
    (fun i j hij => by
      fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> first | exact hne hij | exact hne hij.symm)
    (fun Q hQ hdvd => by
      rw [hsplit] at hdvd
      rcases hQ.dvd_or_dvd hdvd with h | h
      · exact ⟨0, by simpa using eq_of_prime_dvd_prime hQ hP1 h⟩
      · exact ⟨1, by simpa using eq_of_prime_dvd_prime hQ hP2 h⟩)
    (fun i => by
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, pow_one] <;> assumption) k]
  exact card_split k

/-! ## Inert: p ≡ 3 mod 4, (f, g) = (2, 1) -/

theorem generic_inert {p : ℕ} [hp : Fact p.Prime] (h3 : p % 4 = 3) (k : ℕ) :
    a (p ^ k) = if Even k then 1 else 0 := by
  have hN := inert_norm p
  have h0 : span ({(p : Zi)} : Set Zi) ≠ ⊥ := by
    intro hb; rw [hb, absNorm_bot] at hN; exact pow_ne_zero 2 hp.out.ne_zero hN.symm
  have hP := prime_of_isPrime h0 (inert_prime h3)
  rw [a, card_ideals_norm_prime_pow (P := ![span {(p : Zi)}]) (f := 2) hp.out.one_lt
    (fun i => by fin_cases i; simpa using hP) (fun i j _ => Subsingleton.elim i j)
    (fun Q hQ hdvd => ⟨0, by simpa using eq_of_prime_dvd_prime hQ hP hdvd⟩)
    (fun i => by fin_cases i; simpa using hN) k]
  exact card_inert k

/-! ## Independence from the baseline's prime-power counting -/

open Lean Elab Command in
partial def projectClosure (env : Environment) (n : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[n]
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    let local? := match env.getModuleIdxFor? c with
      | none => true
      | some idx =>
        let m := (env.header.moduleNames[idx.toNat]!).toString
        m.startsWith "Gaussian" || m.startsWith "Quadratic"
    if !local? then continue
    if let some ci := env.find? c then
      for d in ci.type.getUsedConstants do todo := todo.push d
      let v? : Option Expr := match ci with
        | .thmInfo v => some v.value
        | .defnInfo v => some v.value
        | .opaqueInfo v => some v.value
        | _ => none
      if let some v := v? then
        for d in v.getUsedConstants do todo := todo.push d
  return seen

/-- The baseline's own prime-power counting route. -/
def baselineCounting : List Lean.Name :=
  [`a_split_prime_power, `a_inert_prime_power, `a_ramified_prime_power,
   `split_ideal_factorization, `exps_unique, `exps_unique_aux, `dvd_one_prime_pow,
   `dvd_two_prime_pows]

open Lean Elab Command in
elab "#check_avoids_baseline " thm:ident : command => do
  let cl := projectClosure (← getEnv) thm.getId
  let hits := baselineCounting.filter cl.contains
  if hits.isEmpty then logInfo m!"INDEPENDENT: {thm.getId} avoids {baselineCounting}"
  else throwError m!"NOT INDEPENDENT: {thm.getId} reaches {hits}"

open Lean Elab Command in
elab "#check_uses_baseline " thm:ident : command => do
  let cl := projectClosure (← getEnv) thm.getId
  if (baselineCounting.filter cl.contains).isEmpty then
    throwError m!"CONTROL FAILED: {thm.getId} should reach the baseline counting route"
  logInfo m!"CONTROL OK: {thm.getId} reaches the baseline counting route"

#check_avoids_baseline generic_ramified
#check_avoids_baseline generic_split
#check_avoids_baseline generic_inert

/-- Agreement: the generic route and the baseline route give the same values
(two independently derived equalities with identical right-hand sides). -/
theorem agree_split {p : ℕ} [Fact p.Prime] (h1 : p % 4 = 1) (k : ℕ) :
    a (p ^ k) = k + 1 ∧ a (p ^ k) = k + 1 :=
  ⟨generic_split h1 k, a_split_prime_power h1 k⟩

-- Negative control: a theorem that does cite the baseline count is detected.
#check_uses_baseline agree_split

#print axioms generic_ramified
#print axioms generic_split
#print axioms generic_inert
