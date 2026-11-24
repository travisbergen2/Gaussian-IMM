# Validated environment record (additive; no source, manifest or script changed)

```
Branch:          eisenstein-extension
Source commit:   c78ed80
Lean:            leanprover/lean4:v4.36.0
Lean commit:     611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9
Mathlib:         fc4f59e577feb1a4956671bc04ac18aaaf8cd842   (Mathlib tag v4.36.0)
Frozen baseline: 9/9 hashes, 9/9 builds, 61 axiom audits passed (verify.sh, all 3 stages)
Extension:       21 libraries built (lake build, exit 0), 34 additional axiom lines,
                 all [propext, Classical.choice, Quot.sound]
Where run:       Claude cloud session (Linux x86_64), fresh clone. Not Travis's Windows machine.
```

The only local changes for the run were an uncommitted `lean-toolchain` file and the Mathlib `rev`
in `lakefile.toml`. The 61-line baseline audit and the 34-line branch audit are separate operations:
verify.sh covers only the frozen nine.

## Lean 4.36.0-rc1 is not a valid target for this source tree

With Mathlib tag v4.36.0-rc1 (`625d8914…`), the build fails (`build_lean_4.36.0-rc1_cloud_FAILED.log`):
`GaussianDedekindBridge` uses `QuadraticAlgebra.Int.algEquivIntegralClosure`, which is absent from
the Mathlib tags v4.36.0-rc1 and v4.36.0-rc2 and present from v4.36.0. Two generic branch modules
also fail on typeclass interfaces that changed between the release candidate and the final release.
This is a library-interface mismatch, not a mathematical failure. The frozen files are not modified
to accommodate rc1.

Full output: `verify_lean_4.36.0_cloud.log`.
