# Publication record: Cyclic Cubic Fields and Primitive Cubic Characters

This record is additive. It changes no source file, manifest, script or build log.

```
Manuscript:          docs/CyclicCubicClassification.md
Manuscript commit:   39d4830e26caec94bb52c0986e9ecc255e9fd8fd   (branch cubic-classification-manuscript)
Manuscript SHA-256:  2089bd703a35e29fa8bc28f3c1daa7e85105dce2518e5ebd6243b0fa2dd1b563
Manuscript size:     27,041 bytes, 249 lines, UTF-8, LF line endings
Manuscript source:   Markdown export of the Claude Docs manuscript at revision 28

Verified Lean commit: f8276d301bab3d162c324b286321a2e11f372a30   (branch cubic-kronecker-weber)
Lean sources:        98 .lean files, unchanged since 9344d2311235687d9f5d7ec9ab4a27b83b3ff742
Build record:        CubicClassification_fresh_build.log, added in f8276d3
Build record SHA-256: 30109bab7e636d19d620df45931059b2e2e5c60f5fcd0a615ad7d0db13d65e9a
Validation:          leanprover/lean4:v4.36.0, Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842 (tag v4.36.0)
Development:         Lean 4.37.0-rc1, Mathlib bce3fc3a37ff1790b2e3b0ccf8f941053aefde19
Frozen base:         main at 9c55a1ea735752e5efc183509ecbaa0a27fade0f
Where run:           Claude cloud session (Linux x86_64), fresh clone. Not Travis's Windows machine.
Milestone tag:       cubic-classification-v1 -> f8276d3, not yet on GitHub (see Tag)
```

## The manuscript commit

Commit `39d4830` adds one file, `docs/CyclicCubicClassification.md`, on a branch that starts at `f8276d3`. No Lean file, `lakefile.toml`, `SHA256SUMS`, `verify.sh` or build log differs from `f8276d3`.

The file is the doc's own Markdown export at revision 28, byte for byte. Revision 28 is the one with the corrected §3.3 table: for 27 ∣ N, N = 27M, the row names the reduction (ℤ/N)ˣ → (ℤ/(N/3))ˣ and its kernel, the classes 1 + 9Mt, each a cube because (1 + 3Mt)³ ≡ 1 + 9Mt (mod 27M).

The exporter writes the date and byline as plain text, and it replaces the one embedded figure, the §4 overview of the six steps, with a one-line placeholder. The figure restates §4.1–4.6, and Appendix A.2 names the Lean file for each step.

The live doc can still be edited. The frozen manuscript is this file at this commit; a later revision would be frozen in a new commit with a new record.

## The verified Lean commit

`git diff --name-only 9344d23 f8276d3` lists only `CubicClassification_fresh_build.log`, so the Lean sources are those of `9344d23`. That log records:

- Lines 1–3: a fresh clone of `cubic-kronecker-weber` at `9344d23` built all 98 libraries under the validation toolchain (`Build completed successfully (18543 jobs).`, exit 0).
- Lines 4–6: `verify.sh` reported `ALL STAGES PASSED` (exit 0). It checks the nine frozen Gaussian files only: hashes against `SHA256SUMS`, build, and axioms.
- Lines 8–31: `#print axioms` for the 23 theorems indexed in Appendix A.2 of the manuscript, each `[propext, Classical.choice, Quot.sound]`.

The committed `lakefile.toml` pins the development Mathlib. The validation clone set the toolchain to v4.36.0 and the Mathlib `rev` to `fc4f59e5` locally, without committing them, as `REPRODUCIBILITY_lean_4.36.0.md` describes for the earlier branch. No `.lean` file at `f8276d3` contains `sorry`.

## Tag

`cubic-classification-v1` is an annotated tag on `f8276d3` in the cloud clone. Pushing it from the cloud session was refused (HTTP 403 from the session's proxy), so it is not on GitHub. To create it from your own clone:

```
git fetch origin
git tag -a cubic-classification-v1 f8276d3 -m "Milestone: classification of cyclic cubic fields by primitive cubic characters (Lean v4.36.0, Mathlib fc4f59e5)"
git push origin cubic-classification-v1
```

## How to check

In Git Bash or any shell with `sha256sum`:

```
git fetch origin
git diff --name-only f8276d3 39d4830     # docs/CyclicCubicClassification.md only
git diff --name-only 9344d23 f8276d3     # CubicClassification_fresh_build.log only
git show 39d4830:docs/CyclicCubicClassification.md | sha256sum            # 2089bd70...b563
git show f8276d3:CubicClassification_fresh_build.log | sha256sum         # 30109bab...5e9a
```

Hash the committed blob with `git show`, not a checked-out copy. On Windows with `core.autocrlf` set, a checkout converts line endings to CRLF and the hash of the file on disk will differ.

To rebuild, clone at `f8276d3`, add a `lean-toolchain` file containing `leanprover/lean4:v4.36.0`, set `rev` in `lakefile.toml` to `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, then run `lake exe cache get`, `lake build` and `bash verify.sh`. To repeat the audit, run `#print axioms` on the 23 names in a file that imports the cubic modules.
