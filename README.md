# Gaussian layer — research record (frozen 2026-11-24)

## 1. Scope

Ideal counting in the Gaussian integers ℤ[i], and the factorization of its Dirichlet series.
Let a(n) be the number of ideals of ℤ[i] with ideal norm n. Proved:

- a(n) = Σ_{d ∣ n} χ₄(d) for every n > 0
- Σ_{n≥1} a(n)·n⁻ˢ = ζ(s) · L(s, χ₄) for Re s > 1

Classical mathematics, formalized in Lean 4 against Mathlib.

## 2. Files and responsibilities

| File | Responsibility |
| --- | --- |
| `GaussianGEquivalence_RingEquiv.lean` | Foundation. Travis's from-scratch `G` is a commutative ring, and `G ≃+* GaussianInt`. |
| `GaussianIdealCounting.lean` | Ideal norms, how primes factor, prime-power counts, multiplicativity. Works in `QuadraticAlgebra ℤ (-1) 0`, which has the ℤ-basis that `Ideal.absNorm` needs, linked to `GaussianInt` by `ziEquiv`. |
| `GaussianLSeries.lean` | The divisor sum r = 1 ⍟ χ₄, its convergence for Re s > 1, and L(r, s) = ζ(s)·L(χ₄, s). |
| `GaussianSynthesis.lean` | Coefficient equality a(n) = r(n) for n > 0, and the L-series identity for a. |

Key theorems, in proof order:

- `absNorm_span`: the ideal norm of (z) is re² + im²
- `two_ramifies`, `inert_prime`, `split_prime`, `split_factors_prime`: (2) = (1+ω)², (p) stays prime for p ≡ 3 mod 4, (p) = 𝔭𝔭̄ with 𝔭 ≠ 𝔭̄ for p ≡ 1 mod 4
- `a_split_prime_power`: a(pᵏ) = k + 1, through an explicit bijection with Fin (k+1)
- `a_inert_prime_power`: a(pᵏ) = 1 if k is even, 0 if k is odd
- `a_ramified_prime_power`: a(2ᵏ) = 1
- `factor_recover`, `a_mul_of_coprime`: a(mn) = a(m)·a(n) for coprime m and n
- `A_eq_R`, `a_eq_r`, `LSeries_ideal_count`: the synthesis

## 3. Build instructions

- Toolchain `leanprover/lean4:v4.37.0-rc1`, Mathlib commit `bce3fc3a37ff1790b2e3b0ccf8f941053aefde19`
- `GaussianLSeries` and `GaussianIdealCounting` each import only `Mathlib`. `GaussianSynthesis` imports both. `GaussianGEquivalence_RingEquiv` stands alone.
- Register the two imported files as libraries in `lakefile.toml`:

```toml
[[lean_lib]]
name = "GaussianLSeries"

[[lean_lib]]
name = "GaussianIdealCounting"
```

- Build: `lake build GaussianLSeries GaussianIdealCounting`, then `lake env lean GaussianSynthesis.lean`.

## 4. Verification

- All four files compile with zero errors and no `sorry`.
- Every audited theorem depends only on `propext`, `Classical.choice` and `Quot.sound`. The output is in `Gaussian_build.log`.
- SHA-256 of the frozen files:
  - `GaussianGEquivalence_RingEquiv.lean` d8c1c30b11b2cc7114ddb41da57740369416d2d89451c114e9e1c2a3b2e6cd9d
  - `GaussianIdealCounting.lean` 6022250b91ecf993e4f65847abd52d68d2a0de60f601453971679aa406158e73
  - `GaussianLSeries.lean` c5cad82a8f0d6f3e58fb8191299853a5c49924ccc77c5bf57ac5f16956014f56
  - `GaussianSynthesis.lean` 3d0993b892b5df3a67c406ff29517a25d502517c5cf3a37cf0740b2d76ebccc4
- Compiled in a Claude cloud session. It has not yet been rebuilt on Travis's pinned 4.36.0-rc1 toolchain.

## 5. Mathematical boundary

- What's proved is the factorization of the ideal-counting series of ℤ[i]. It is not formally identified with Mathlib's `NumberField.dedekindZeta ℚ(i)`.
- a(0) = 1 and r(0) = 0. The coefficient equality is stated for n > 0 only. The L-series never uses n = 0.
- There is no RH or GRH content. This is classical infrastructure connecting the (+i, −i) arithmetic to L(s, χ₄).

## 6. Future work (in a fifth file that imports this layer; the frozen files stay unchanged)

1. Certify that the discriminant −4 is fundamental (`Int.IsFundamentalDiscr`).
2. Identify the integral closure of ℤ in a concrete ℚ(i), checking the hypotheses and direction of `QuadraticAlgebra.algEquivIntegralClosure`.
3. Establish the equivalence of that ring of integers with `QuadraticAlgebra ℤ (-1) 0` and `GaussianInt`.
4. Transfer `LSeries_ideal_count` to `NumberField.dedekindZeta ℚ(i)`.

## 7. Update 2026-11-24: the bridge is done (`GaussianDedekindBridge.lean`)

All four future-work items are completed in a fifth file that imports the frozen layer. The four files above are unchanged.

- `gaussian_discr_fundamental`: −4 is a fundamental discriminant, via `Int.isFundamentalDiscr_four_mul` with m = −1.
- `gaussianIntegralClosureEquiv`: `QuadraticAlgebra ℤ (-1) 0 ≃ₐ[ℤ] integralClosure ℤ ℚ(i)`, from `QuadraticAlgebra.Int.algEquivIntegralClosure`. It runs from the integral quadratic order to the integral closure.
- The concrete field is `Qi := QuadraticAlgebra ℚ (-1) 0`, written with the same integer casts the API uses. It becomes a `NumberField` once the discriminant is shown not to be a square. Mathlib defines `𝓞 K` as `integralClosure ℤ K`, so `ringOfIntegersEquiv : Zi ≃+* 𝓞 Qi` follows directly.
- `absNorm_comap`, `card_ideals_eq`: a ring equivalence preserves ideal norms, so the count of ideals of norm n in `𝓞 Qi` equals a(n) for every n.
- `dedekindZeta_Qi`: for Re s > 1, **`NumberField.dedekindZeta Qi s = riemannZeta s * LSeries chi4 s`**.

Verification: no `sorry`, and every theorem depends only on the three standard axioms (`GaussianDedekindBridge_build.log`). To build it, also register `GaussianSynthesis` as a `lean_lib`. It's the same cloud toolchain caveat as above.

So the boundary in section 5 is now closed. What's proved is the classical factorization of Mathlib's own Dedekind zeta for ℚ(i), in the half-plane of absolute convergence. There is still no RH or GRH content.

## 8. Update 2026-11-24: continuation (`GaussianDedekindContinuation.lean`, milestones 1–2)

This imports the bridge. The bridge and the four original files are unchanged.

- `chi4C : DirichletCharacter ℂ 4` is χ₄ moved into ℂ, and `chi4C_ne_one` proves it is not the trivial character.
- `dedekindZetaCont s := riemannZeta s * DirichletCharacter.LFunction chi4C s` is the continuation, built from Mathlib's continued ζ and L(s, χ₄).
- `LFunction_chi4_eq`: the continued L(s, χ₄) equals the frozen `LSeries chi4` for Re s > 1.
- `dedekindZetaCont_eq`: **`dedekindZetaCont s = NumberField.dedekindZeta Qi s` for Re s > 1.**
- `LFunction_chi4_differentiable`: L(s, χ₄) is entire. `dedekindZetaCont_differentiableAt` says the continuation is holomorphic at every s ≠ 1, so s = 1 is the only possible singularity. Section 9 proves it really is a pole.

Verification: no `sorry`, and every theorem depends only on the three standard axioms (`GaussianDedekindContinuation_build.log`). To build it, also register `GaussianDedekindBridge` as a `lean_lib`.

Not yet done: milestone 3, the zero correspondence, and milestone 4, the conditional RH/GRH corollary. Any external RH/GRH theorem needs its exact formal statement and axioms inspected before it enters a proof.

## 9. Update 2026-11-24: zeros and the pole (`GaussianDedekindZeros.lean`, milestone 3)

This imports the continuation file. Every earlier file is unchanged.

- **The pole is real.** `LFunction_chi4_one_ne_zero` gives L(1, χ₄) ≠ 0, using Mathlib's non-vanishing at 1. `dedekindZetaCont_residue` shows (s − 1)·ζ_ℚ(i)(s) → L(1, χ₄) as s → 1. So s = 1 is a simple pole with that nonzero residue.
- **`dedekindZetaCont_zero_iff`** is the zero-product property at every s: the continuation is zero exactly when ζ(s) = 0 or L(s, χ₄) = 0. It's a statement about function values only, not about the continuation at its pole.
- **The trivial zeros, kept separate for each factor:**
  - `ZetaTrivial`: the negative even integers −2(n+1).
  - `LTrivial`: the negative odd integers −(2n) − 1.
  - `chi4C_odd` proves χ₄(−1) = −1, which is why L(s, χ₄) vanishes at the negative odd integers.
  - `trivial_is_zero` shows every point of either set is a zero of the continuation, and `trivial_disjoint` shows the two sets don't overlap.
- **`NontrivialZero s`** means a zero with s ≠ 1 that lies outside both trivial sets. `nontrivialZero_iff` shows these are exactly the zeros of ζ or of L(s, χ₄) away from 1 and outside both trivial sets.

Verification: no `sorry`, and every theorem depends only on the three standard axioms (`GaussianDedekindZeros_build.log`). To build it, also register `GaussianDedekindContinuation` as a `lean_lib`.

Milestone 4, the conditional statement "RH for ζ and GRH for χ₄ imply every `NontrivialZero` has Re s = ½", has not been written. It's waiting for a review of these definitions.

Review note: `trivial_disjoint` proves only that the two sets don't overlap. It does not prove that ζ is nonzero on `LTrivial`, or that L(s, χ₄) is nonzero on `ZetaTrivial`. `NontrivialZero` excludes both sets on purpose, so it doesn't quietly rely on either fact.

## 10. Update 2026-11-24: a conditional corollary (`GaussianDedekindRH.lean`, milestone 4)

**CONDITIONAL. This file does not prove RH or GRH.** Both appear as explicit hypotheses in the theorem signatures.

- `ZetaZeroLine`: every zero of ζ with s ≠ 1 that is outside `ZetaTrivial` has Re s = ½.
- `zetaZeroLine_iff_RH`: `ZetaZeroLine` is exactly Mathlib's `RiemannHypothesis`, with the same trivial set and the same exclusion of s = 1, only with the arguments in a different order. So the ζ hypothesis isn't a paraphrase of RH. It is Mathlib's RH.
- `Chi4ZeroLine`: every zero of L(s, χ₄) outside `LTrivial` has Re s = ½. This is written out by hand, because Mathlib at the audited commit has no named GRH. Its wording deserves the same scrutiny as the other definitions.
- `nontrivialZero_re_half`: `ZetaZeroLine` and `Chi4ZeroLine` together imply that every `NontrivialZero` of ζ_ℚ(i) has Re s = ½. `nontrivialZero_re_half_of_RH` states the same thing with Mathlib's `RiemannHypothesis` as the ζ hypothesis.

Verification: no `sorry`, and every theorem depends only on the three standard axioms (`GaussianDedekindRH_build.log`). To build it, also register `GaussianDedekindZeros` as a `lean_lib`.

**Terminology.** These predicates exclude the known trivial-zero sets. They don't restrict to the critical strip 0 < Re s < 1. Matching them to a critical-strip formulation also needs zero-free regions. For ζ these are available (Mathlib's Re ≥ 1 non-vanishing, carried over by the functional equation, as in SameComma). For L(s, χ₄) the Re ≤ 0 side needs its functional equation. That matching (item 3 of the plan) has **not** been done.

**Trivial zeros, one direction only.** `zeta_trivial_is_zero` and `L_trivial_is_zero` show that the listed points are zeros. They don't show these are the *only* zeros outside the critical strip. That converse is exactly what comparing `Chi4ZeroLine` with conventional GRH would need.

*(The critical-strip matching described above is done in section 11.)*

**External results.** No external RH or GRH theorem is imported. If Alpöge's formal results are ever substituted for these hypotheses, check their exact statements and axiom dependencies against `RiemannHypothesis` and `Chi4ZeroLine` independently first.

## 11. Update 2026-11-24: the zeros on the left half-plane and the GRH form (`GaussianChi4GRHForm.lean`)

This imports `GaussianDedekindRH`. Every earlier file and definition is unchanged. It uses only Mathlib's own definitions (`completedLFunction`, `gammaFactor χ s = Gammaℝ (s + 1)` for odd χ, `rootNumber`, and `IsPrimitive.completedLFunction_one_sub`). No textbook normalization is brought in.

- **Primitivity.** `chi4C_not_factorsThrough_two`: the unit 3 maps to 1 in (ℤ/2)ˣ, but χ₄(3) = −1, so χ₄ doesn't factor through level 2. `chi4C_isPrimitive` then follows: the conductor divides 4 and isn't 1 (χ₄ is non-trivial) or 2, so it equals 4.
- **The completed L-function is nonzero on Re s ≤ 0.**
  - `completed_inv_ne_zero_of_one_le_re`: on Re s ≥ 1, Λ(s, χ₄⁻¹) = L(s, χ₄⁻¹)·gammaFactor. The L factor is nonzero by `LFunction_ne_zero_of_one_le_re`, and the Gamma factor has no zeros there.
  - `completed_ne_zero_of_re_nonpos`: the functional equation gives Λ(s, χ₄) = 4^(1/2 − s) · rootNumber · Λ(1 − s, χ₄⁻¹). For Re s ≤ 0 we have Re(1 − s) ≥ 1, and rootNumber ≠ 0 by `rootNumber_ne_zero`, so Λ(s, χ₄) ≠ 0.
- **The central theorem, `LFunction_chi4_zero_iff_of_re_nonpos`:** for Re s ≤ 0, L(s, χ₄) = 0 ⟺ `LTrivial s`, meaning s = −1, −3, −5, …. Both directions are proved. Mathlib writes L = Λ / gammaFactor, and Λ ≠ 0 on this half-plane, so L vanishes exactly where gammaFactor = Gammaℝ(s + 1) does. Mathlib's `gammaFactor_eq_zero_iff_of_odd` gives those points as s + 1 = −2n. This is exactly the converse that section 10 said was missing.
- **The critical-strip form.** `Chi4StripLine` states the conventional critical-strip GRH for χ₄: every zero with 0 < Re s < 1 has Re s = ½. `chi4ZeroLine_iff_strip` proves **`Chi4ZeroLine ↔ Chi4StripLine`**. Zeros with Re s ≥ 1 are ruled out by non-vanishing, and on Re s ≤ 0 the only zeros are the trivial ones.
- **`nontrivialZero_re_half_of_RH_strip`:** the milestone-4 corollary using only conventional hypotheses, Mathlib's `RiemannHypothesis` and `Chi4StripLine`. **It is still CONDITIONAL.**

Verification: no `sorry`, and every theorem depends only on the three standard axioms (`GaussianChi4GRHForm_build.log`). To build it, also register `GaussianDedekindRH` as a `lean_lib`.

Status: the "conventional GRH equivalence for χ₄" item is now closed. Two items remain open: unconditional RH and GRH, which this project does not claim, and a rebuild on the user's pinned Lean and Mathlib versions.

## 12. Reproducibility audit (`lakefile.toml`, `verify.sh`, `SHA256SUMS`)

The open item, a rebuild on the pinned toolchain, is now a one-command procedure.

1. Put the nine `.lean` files, `lakefile.toml`, `verify.sh` and `SHA256SUMS` in one folder.
2. Set `rev` in `lakefile.toml` to the Mathlib commit that matches your `lean-toolchain`, then add that toolchain's `lean-toolchain` file to the folder.
3. Run `bash verify.sh`.

The script runs three stages and stops at the first failure:

- **HASHES:** every file matches the reference SHA-256 in `SHA256SUMS`.
- **BUILD:** `lake build` on all nine libraries, in dependency order.
- **AXIOMS:** every file is re-elaborated, with Lean's exit status checked explicitly, and there must be exactly 61 audit lines, the count for this frozen snapshot (`EXPECTED_AXIOM_LINES`). If you add audited declarations on purpose, update that count together with `SHA256SUMS`. Every `#print axioms` line is checked. Anything other than `propext`, `Classical.choice` or `Quot.sound` fails, and that includes `sorryAx`. A clean build and a clean axiom audit are reported separately, because `lake build` treats `sorry` as a warning, not an error.

The full output goes to `verify_build.log`.

I tested it in the cloud on v4.37.0-rc1 and Mathlib `bce3fc3a…`, and all three stages passed with 61 audited theorems. I also checked both failure paths. With one byte appended to a file, it stops at STAGE 1. With an injected `sorry` theorem, STAGE 2 passes and STAGE 3 fails on `sorryAx`. With one `#print axioms` line deleted, it fails STAGE 3 with "expected 61 audit lines, found 60", even when the manifest is updated to match. The 4.36.0-rc1 run on the user's machine is still the open check.
