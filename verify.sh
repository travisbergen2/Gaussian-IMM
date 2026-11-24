#!/usr/bin/env bash
# One-command reproducibility audit for the Gaussian layer.
#
# Run from the folder holding lakefile.toml, SHA256SUMS and the nine .lean files:
#     bash verify.sh
#
# Three separate stages. It stops at the first failure.
#   1. HASHES   every .lean file matches the reference manifest SHA256SUMS
#   2. BUILD    every file compiles, in dependency order (lake build)
#   3. AXIOMS   every #print axioms line uses only propext, Classical.choice, Quot.sound,
#               with no sorryAx and nothing else
# The full output is saved to verify_build.log.

set -euo pipefail

LOG="verify_build.log"
exec > >(tee "$LOG") 2>&1

FILES=(
  GaussianGEquivalence_RingEquiv
  GaussianIdealCounting
  GaussianLSeries
  GaussianSynthesis
  GaussianDedekindBridge
  GaussianDedekindContinuation
  GaussianDedekindZeros
  GaussianDedekindRH
  GaussianChi4GRHForm
)
ALLOWED='^(propext|Classical\.choice|Quot\.sound)$'
# Expected number of `#print axioms` lines in the frozen snapshot.
# If you deliberately add audited declarations, update this together with SHA256SUMS.
EXPECTED_AXIOM_LINES=61

echo "Gaussian layer verification — $(date -u +%Y-%m-%dT%H:%MZ)"
echo "lean-toolchain: $(cat lean-toolchain 2>/dev/null || echo '(none in folder; using elan default)')"
echo "lean --version: $(lake env lean --version 2>/dev/null || echo unknown)"
if [ -d .lake/packages/mathlib/.git ]; then
  echo "Mathlib commit: $(git -C .lake/packages/mathlib rev-parse HEAD)"
fi
echo

echo "=== STAGE 1: HASHES ==="
if command -v sha256sum >/dev/null; then
  sha256sum -c SHA256SUMS
else
  shasum -a 256 -c SHA256SUMS
fi
echo "STAGE 1 PASSED: all 9 files match the reference manifest."
echo

echo "=== STAGE 2: BUILD ==="
lake exe cache get || echo "(cache download failed or unavailable; building Mathlib from source)"
for f in "${FILES[@]}"; do
  echo "--- building $f"
  lake build "$f"
done
echo "STAGE 2 PASSED: all 9 files compiled."
echo

echo "=== STAGE 3: AXIOMS ==="
total=0
for f in "${FILES[@]}"; do
  if out=$(lake env lean "$f.lean" 2>&1); then
    status=0
  else
    status=$?
  fi
  if [ "$status" -ne 0 ] || echo "$out" | grep -Eq "(^|: )error"; then
    echo "$out"
    echo "STAGE 3 FAILED: re-elaborating $f.lean exited with status $status or reported an error."
    exit 1
  fi
  while IFS= read -r line; do
    [ -z "$line" ] && continue
    echo "$line"
    total=$((total + 1))
    if echo "$line" | grep -q "does not depend on any axioms"; then continue; fi
    axioms=$(echo "$line" | sed -n 's/.*depends on axioms: \[\(.*\)\]/\1/p' | tr ',' '\n' | sed 's/^ *//;s/ *$//')
    for ax in $axioms; do
      if ! echo "$ax" | grep -Eq "$ALLOWED"; then
        echo "STAGE 3 FAILED: disallowed axiom '$ax' in: $line"
        exit 1
      fi
    done
  done < <(echo "$out" | grep -E "depends on axioms|does not depend on any axioms")
done
if [ "$total" -ne "$EXPECTED_AXIOM_LINES" ]; then
  echo "STAGE 3 FAILED: expected $EXPECTED_AXIOM_LINES audit lines, found $total."
  exit 1
fi
echo "STAGE 3 PASSED: $total audited theorems, only propext / Classical.choice / Quot.sound."
echo
echo "ALL STAGES PASSED. Full output saved to $LOG."
