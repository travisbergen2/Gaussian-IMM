import DedekindIdealCountMultiplicative
import GaussianIdealCounting
import EisensteinLocalInstance

/-!
# GenericMultiplicativeInstances — steps 2–3: one multiplicativity theorem, two fields

* Gaussian regression: the baseline count `a` is literally `IdealCount.A Zi`, and
  `a_mul_generic` recovers `a_mul_of_coprime` from the generic theorem. A proof scan confirms
  it does not use the Gaussian proof (`factor_recover`, `span_coprime`, `a_mul_of_coprime`).
* Eisenstein specialization: `a3 K = IdealCount.A (𝓞 K)`, so `a3_mul_of_coprime` is immediate.
-/

open NumberField

theorem a_eq_A (n : ℕ) : a n = IdealCount.A Zi n := rfl

/-- **Gaussian regression:** multiplicativity of `a` from the generic theorem. -/
theorem a_mul_generic {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) :
    a (m * n) = a m * a n :=
  IdealCount.A_mul_of_coprime hm hn hmn

theorem a3_eq_A (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K] (n : ℕ) :
    a3 K n = IdealCount.A (𝓞 K) n := rfl

/-- **Eisenstein:** multiplicativity of `a₋₃` from the same generic theorem. -/
theorem a3_mul_of_coprime (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) :
    a3 K (m * n) = a3 K m * a3 K n :=
  IdealCount.A_mul_of_coprime hm hn hmn

/-! ## The Gaussian proof is no longer needed -/

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
        m.startsWith "Gaussian" || m.startsWith "Eisenstein" || m.startsWith "Dedekind" ||
          m.startsWith "Quadratic"
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

def gaussianMulProof : List Lean.Name := [`factor_recover, `span_coprime, `a_mul_of_coprime]

open Lean Elab Command in
elab "#check_avoids_gaussian_mul " thm:ident : command => do
  let cl := projectClosure (← getEnv) thm.getId
  let hits := gaussianMulProof.filter cl.contains
  if hits.isEmpty then logInfo m!"INDEPENDENT: {thm.getId} avoids {gaussianMulProof}"
  else throwError m!"NOT INDEPENDENT: {thm.getId} reaches {hits}"

open Lean Elab Command in
elab "#check_uses_gaussian_mul " thm:ident : command => do
  let cl := projectClosure (← getEnv) thm.getId
  if (gaussianMulProof.filter cl.contains).isEmpty then
    throwError m!"CONTROL FAILED: {thm.getId} should reach the Gaussian proof"
  logInfo m!"CONTROL OK: {thm.getId} reaches the Gaussian multiplicativity proof"

/-- Control theorem: the same statement, proved the old way. -/
theorem a_mul_baseline {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) :
    a (m * n) = a m * a n :=
  a_mul_of_coprime hm hn hmn

-- Negative control: a theorem (not on the list) that relies on the Gaussian proof is detected.
#check_uses_gaussian_mul a_mul_baseline

#check_avoids_gaussian_mul a_mul_generic
#check_avoids_gaussian_mul a3_mul_of_coprime

#print axioms a_mul_generic
#print axioms a3_mul_of_coprime
