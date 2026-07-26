#!/usr/bin/env bash
# Trust clean-certification gate (advisory-lane kernel-Certified self-test).
#
# The superiority gate proves SAFE code is statically discharged (0 runtime
# checks). THIS gate proves the STRONGER property for the obligation classes the
# clean theorem prover can kernel-certify: clean's `Certified` tier actually
# FIRES on real compiled programs when advisory verification is requested.
#
# A `Certified` obligation was re-proved AND re-checked by the clean CIC kernel
# (`TypeChecker::check_type`, `infer_only = false`) with ZERO trust in the SMT
# solver — the de Bruijn criterion — so the solver is OUTSIDE the trusted base
# and codegen may soundly elide the runtime check. trustc surfaces this on a
# successful advisory-verifier compile as a note:
#   "of which N kernel-certified by the clean CIC kernel (zero-trust re-check…)"
#
#   clean_certified/proved/*.rs  -> advisory mode emits N>=1 kernel-certified
#                                   (clean's kernel independently re-checked it).
#   clean_certified/mutant/*.rs  -> advisory mode emits NO kernel-certified note
#                                   (clean NEVER certifies a buggy obligation —
#                                   the in-process ay solve returns SAT, the
#                                   zero-trust kernel re-check is never reached).
#
# This is the acceptance test for the clean engagement: it catches both a
# regression of the certification path (safe obligation no longer certified) and
# the cardinal soundness bug (a false `Certified` on an unsafe obligation).
#
# REQUIRES an executable `ay` SMT solver (AY_PATH or the trustc sibling) — see
# the superiority gate header for why. Reuses the same fixtures via
# symlinked lists below (the proved/mutant pairs whose contradiction lives in
# clean's zero-trust linear-Int fragment: guard-bounded slice + range loops).
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TRUSTC="${TRUSTC:-$REPO_ROOT/build/host/stage2/bin/trustc}"
TARGO="${TARGO:-$(dirname "$TRUSTC")/targo}"
AY_BIN="${AY_PATH:-$(dirname "$TRUSTC")/ay}"
SUP="$REPO_ROOT/tests/trust-falsification/superiority"
# The shims dir must EXIST: a missing LIBRARY_PATH entry makes ld warn
# "search path not found", which leaks into diagnostics-sensitive tests.
mkdir -p /tmp/trust_link_shims
export LIBRARY_PATH="/tmp/trust_link_shims:/opt/homebrew/opt/z3/lib:${LIBRARY_PATH:-}"

# Fixtures whose proved obligation's contradiction lies in clean's ZERO-TRUST
# linear-Int Farkas fragment (so the clean kernel can independently re-check it).
# Guard-bounded slice indexing and range-loop bounds qualify; modulo/bitmask/
# clamp/2D do NOT (they need modular/clamp reasoning outside the Farkas fragment
# and prove via the interval backend → Trusted, not Certified).
CERTIFIABLE=(
  guarded_slice_bound
  for_range_index_bound
  while_range_index_bound
  rev_range_index_bound
)

if [ ! -x "$TRUSTC" ]; then
  echo "ERROR: trustc not found at $TRUSTC (build it: ./x.py build --stage 2 compiler/rustc library/std)"
  exit 2
fi

if [ ! -x "$AY_BIN" ]; then
  echo "INFO: ay solver not available at $AY_BIN — building it (one-time, debug)…"
  if [ -x "$TARGO" ] \
     && ( cd "$REPO_ROOT/first-party/ay" && "$TARGO" --unverified build -p ay --features cli >/dev/null 2>&1 ) \
     && [ -x "$REPO_ROOT/first-party/ay/target/debug/ay" ]; then
    AY_BIN="$REPO_ROOT/first-party/ay/target/debug/ay"
    echo "INFO: using ay at $AY_BIN"
  else
    echo "ERROR: could not build the ay solver through canonical Targo; advisory mode has no SMT backend."
    exit 2
  fi
fi
export AY_PATH="$AY_BIN"

TMPDIR_GATE="$(mktemp -d)"
trap 'rm -rf "$TMPDIR_GATE"' EXIT

# Advisory verify -> echo the kernel-certified count (the N in the note), or
# 0 when the note is absent. A unique cache path per call avoids stale hits.
certified_count_of() {
  "$TRUSTC" --edition 2021 --crate-type lib -Z trust-policy=advisory "$1" \
      -o "$TMPDIR_GATE/$(basename "$1").rlib" 2>&1 \
    | sed -n 's/.*of which \([0-9]*\) kernel-certified.*/\1/p' \
    | head -1
}

# Warm ay + every certifiable fixture once (absorb debug-ay cold start, which can
# leave the first cold query runtime-checked / un-certified — see superiority gate).
printf '(set-logic QF_LIA)(declare-fun x () Int)(assert (and (< x 0)(> x 0)))(check-sat)\n' \
  | "$AY_BIN" >/dev/null 2>&1 || true
for name in "${CERTIFIABLE[@]}"; do
  certified_count_of "$SUP/proved/$name.rs" >/dev/null 2>&1
done

failed=0

for name in "${CERTIFIABLE[@]}"; do
  f="$SUP/proved/$name.rs"
  if [ ! -e "$f" ]; then
    echo "FAIL  proved   $name  — fixture missing"; failed=1; continue
  fi
  # Retry once: a real regression fails both attempts; a cold-start miss clears.
  n=0
  for _ in 1 2; do
    c="$(certified_count_of "$f")"
    n="${c:-0}"
    [ "$n" -ge 1 ] && break
  done
  if [ "$n" -ge 1 ]; then
    echo "PASS  proved   $name  — CLEAN-CERTIFIED: $n obligation(s) kernel-re-checked (zero-trust)"
  else
    echo "FAIL  proved   $name  — NOT clean-certified (expected >=1 kernel-certified)"
    failed=1
  fi
done

for name in "${CERTIFIABLE[@]}"; do
  f="$SUP/mutant/$name.rs"
  [ -e "$f" ] || continue
  c="$(certified_count_of "$f")"
  n="${c:-0}"
  if [ "$n" -eq 0 ]; then
    echo "PASS  mutant   $name  — sound: clean refused to certify the buggy obligation"
  else
    echo "FAIL  mutant   $name  — FALSE CERTIFIED: clean certified an unsafe obligation ($n)"
    failed=1
  fi
done

if [ "$failed" -eq 0 ]; then
  echo "CLEAN CERTIFICATION GATE: GREEN — clean kernel-certifies safe code, never certifies unsafe code"
  exit 0
else
  echo "CLEAN CERTIFICATION GATE: RED — certification regressed, or a false Certified was minted"
  exit 1
fi
