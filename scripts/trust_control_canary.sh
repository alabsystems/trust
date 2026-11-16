#!/usr/bin/env bash
# trust_control_canary.sh — the `is_whnf` MINT-GATE canary lane.
#
# ONE release test that answers one question: are the four anti-masquerade
# controls the MIR-grounded `is_whnf` mint is GATED on still DEMONSTRABLE in the
# environment the production path actually builds — and does a certificate
# therefore still issue?
#
#   crates/trust-certify/src/checker_core_is_whnf.rs
#     tests::mint_gate_canary_controls_demonstrable_and_mint_closes
#
# WHY THIS LANE EXISTS. Control 3 (`delta_reducing_const_kernel_rejected` ->
# `discriminating_delta_const`) used to assert one hardcoded, POSITIONALLY
# generated reflected-environment constant, `kcre_name_116`. The environment was
# regenerated, that name drifted into the no-delta-reduct set, the control could
# no longer be demonstrated — and because minting is GATED on it, EVERY `is_whnf`
# certificate was withheld from July until 2026-08-23 while every public mint
# returned a bare, reasonless `None`. The whole Certified tier for this lane was
# dark for a month and nothing said so, for two independent reasons:
#
#   1. every test on this path is `#[ignore]`d into the overnight lane
#      (scripts/trust_kernel_derivation_lane.sh, 555-1105 s EACH), and the one
#      non-ignored consumer (trust-integration-tests
#      checker_core_is_whnf_emit_discharge_e2e) was independently red, which
#      masked it;
#   2. no gate script ran ANY trust-certify test at all. Measured 2026-08-24:
#      `grep -rn trust-certify scripts/*.sh` hit only the overnight lane, and
#      run_tests_after_build.sh tier T1 named trust-loop / trust-vcgen /
#      trust-router only. A perfectly cheap canary in trust-certify's default
#      lane would still have been executed by nothing scripted.
#
# The control now DISCOVERS its witness (pinned fast-path candidates, then a
# bounded scan), so it self-heals. This lane is the instrument that reports when
# it cannot. Full write-up:
#   reports/2026-08-23-is-whnf-mint-blocked-by-control-3.md
#
# WHAT A GREEN RUN MEANS: the gate is OPEN — control 3 has a live witness, the
# other three controls still fail closed, and both mint bodies (MIR-grounded and
# model-level) produce a kernel-checked CleanCic. It does NOT mean the derivation
# is sound: this lane never re-checks a serialized certificate through an
# independently rebuilt spec and never exercises tamper / relineage / consumer
# independence. That evidence is the overnight lane's, and this is not a
# substitute for it.
#
# COST, measured on this host (release, one test per process):
#
#   Specification::new()                              209.582 s   <- 99.5%
#   discriminating_delta_const(env)                       0.004 s
#   both mints (link + kernel check + 4 controls + …)     0.016 s
#   ----------------------------------------------------------------
#   the test                                          ~210.6 s
#
# and this lane end-to-end, on 2026-08-24, WARM target dir: 244 s and 236 s wall
# — a 24 s incremental release build plus 220.03 s / 212.14 s of test, of which
# `Specification::new()` was 219.438 s / 211.213 s and control 3 was 4 ms both
# times.
#
# COLD target dir, measured the same day right after a 32-commit merge
# invalidated the release artifacts: 675 s wall (11m15s) — 214.67 s of test on
# top of a ~460 s (~7m40s) cold release build of clean-verify + trust-certify.
#
# SO: budget ~4 min warm, ~11 min COLD, and expect COLD after any merge that
# touches clean-verify, trust-certify or their dependencies — which is the
# common case when this lane matters. Anything time-boxing this lane must use
# the cold number; the earlier note here said only "budget for a cold build on
# top of that" without one, and the first real run overshot the ~4 min figure
# people had taken from the warm measurement.
#
# so this lane is ~3.1x cheaper than the single audited slow-lane test it
# partially stands in for (670 s) and roughly three orders of magnitude cheaper
# than the full overnight lane. RELEASE is not an optimization: the same spec
# build measures 3.37x slower in debug (~706 s), and the default `targo test`
# lane is debug — which is exactly why the test is `#[ignore]`d rather than
# inline. Measured before ignoring, per the sibling lane script's rule.
#
# CHEAPER ROUTES EVALUATED AND NOT TAKEN (recorded so they are not re-litigated):
#   * `Specification::new_substitution_test_spec()` builds in 26.9 s release /
#     90.4 s debug and the REAL control runs in it unchanged, finding the same
#     witness and minting both fixtures. Not adopted: it is a DIFFERENT
#     Environment from the one `certify_is_whnf_from_mir` builds, so it would
#     demonstrate the control in a subset env rather than in the production one;
#     and it is `#[cfg(any(test, feature = "test-utils"))]`, so wiring it means a
#     `clean-verify` dev-dependency with `test-utils` on, which (via feature
#     unification) changes the artifact under test in every trust-certify test
#     build. At 90 s debug it still could not go inline, so it buys a faster
#     opt-in lane at the price of testing a different environment. Rejected.
#   * `clean_verify::test_utils::shared_spec()` amortizes a spec across tests in
#     ONE binary; the FIRST build still costs 209.6 s, so it does nothing for a
#     lone canary — and it must never be applied to
#     `certify_is_whnf_from_mir`/`recheck_is_whnf_from_mir`, which rebuild a
#     fresh spec per call precisely to demonstrate consumer independence.
#   * Persisting a built spec to disk is ruled out by clean-verify's own module
#     docs: it drops `Environment`'s `#[serde(skip)]` declaration-verification
#     provenance, letting a run inherit a kernel claim it never rechecked.
#
# Usage:
#   scripts/trust_control_canary.sh          # build (release) + run the canary
#   scripts/trust_control_canary.sh --list   # print what would run, build nothing
#   scripts/trust_control_canary.sh --help
#
# Exit 0 = the mint gate is open. Non-zero = a control could not be demonstrated
# (the test's own failure message names WHICH one and both readings of it), the
# mint stopped closing, or the lane could not run the test at all.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache 2.0
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

TEST_NAME="checker_core_is_whnf::tests::mint_gate_canary_controls_demonstrable_and_mint_closes"

LIST_ONLY=0
case "${1:-}" in
  --list) LIST_ONLY=1 ;;
  -h|--help|help)
    awk 'NR > 1 && /^#/ { sub(/^# ?/, ""); print; next } NR > 1 { exit }' "${BASH_SOURCE[0]}"
    exit 0
    ;;
  "") ;;
  *) echo "Unknown argument: $1 (use --list or --help)" >&2; exit 2 ;;
esac

if [ "$LIST_ONLY" -eq 1 ]; then
  echo "$TEST_NAME"
  echo "  package: trust-certify (--lib, release, #[ignore]d — this lane opts in)"
  echo "  source:  crates/trust-certify/src/checker_core_is_whnf.rs"
  echo "  expect:  ~210 s of test time after the build (99.5% of it Specification::new())"
  exit 0
fi

# ── Driver ──────────────────────────────────────────────────────────────────
# targo, which scopes verification per unit — and nothing else: there is no
# stock-cargo fallback (the ATERM_STOCK_REASON
# escape was removed). A stage whose `targo`
# was never rebuilt ships upstream `cargo` UNDER THE NAME `targo`, and it then
# works while verifying nothing — so a candidate is only accepted when it
# ACCEPTS `--unverified`, which cargo-in-disguise rejects. (CLAUDE.md, "VERIFY
# YOUR targo IS TARGO".)
#
# Resolved into a SCALAR first, and the array is built only once a choice is
# made: `${#EMPTY[@]}` and `"${EMPTY[@]}"` are unbound-variable errors under
# `set -u` on bash 3.2, which is still what a stock macOS `/bin/bash` is.
TARGO_BIN=""
for candidate in \
  "${TARGO:-}" \
  "$REPO_ROOT/build/host/stage2/bin/targo" \
  "$(command -v targo 2>/dev/null || true)"
do
  [ -n "$candidate" ] || continue
  [ -x "$candidate" ] || continue
  if "$candidate" --unverified --version >/dev/null 2>&1; then
    TARGO_BIN="$candidate"
    break
  fi
done
if [ -n "$TARGO_BIN" ]; then
  DRIVER=("$TARGO_BIN" --unverified)
else
  echo "FAIL: no targo accepting --unverified found (\$TARGO, build/host/stage2/bin/targo," >&2
  echo "      targo on PATH) — cannot build the canary. Install/repair the Trust toolchain" >&2
  echo "      (aterm pkg doctor). Stock cargo is never used." >&2
  exit 2
fi

# An unbounded cargo job count gets this host's build OOM-killed.
export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-6}"

echo "=== is_whnf mint-gate canary ==="
echo "Driver: ${DRIVER[*]}"
echo "Building the trust-certify test binary (release) …"

BUILD_START=$(date +%s)
"${DRIVER[@]}" test --release --manifest-path Cargo.toml -p trust-certify --lib --no-run
BUILD_RC=$?
BUILD_ELAPSED=$(( $(date +%s) - BUILD_START ))
if [ "$BUILD_RC" -ne 0 ]; then
  echo "FAIL: could not build the trust-certify test binary (rc=$BUILD_RC, ${BUILD_ELAPSED}s)." >&2
  exit 1
fi
echo "Build: ${BUILD_ELAPSED}s"

# `--no-run` prints the binary path, but parsing its human output is brittle;
# ask for the machine-readable artifact instead. This second invocation is a
# no-op rebuild.
TEST_BIN="$("${DRIVER[@]}" test --release --manifest-path Cargo.toml -p trust-certify \
  --lib --no-run --message-format=json 2>/dev/null \
  | sed -n 's/.*"executable":"\([^"]*\)".*/\1/p' | tail -1)"
if [ -z "$TEST_BIN" ] || [ ! -x "$TEST_BIN" ]; then
  echo "FAIL: could not locate the built trust-certify test binary." >&2
  exit 1
fi
echo "Test binary: $TEST_BIN"
echo ""
echo "Running the canary. Expect ~3.5 min: one Specification::new() dominates it."
echo ""

LOG="$(mktemp "${TMPDIR:-/tmp}/is-whnf-canary.XXXXXX.log")"
RUN_START=$(date +%s)
"$TEST_BIN" --ignored --exact "$TEST_NAME" --test-threads=1 --nocapture 2>&1 | tee "$LOG"
RUN_RC="${PIPESTATUS[0]}"
RUN_ELAPSED=$(( $(date +%s) - RUN_START ))

echo ""
echo "Canary test time: ${RUN_ELAPSED}s (build ${BUILD_ELAPSED}s)"

# libtest exits 0 when its filter selected NOTHING, so a green exit code alone
# would let a RENAMED test report PASS forever — the same silent-zero-coverage
# failure this lane was written to end. Demand the one result.
if [ "$RUN_RC" -ne 0 ]; then
  echo ""
  echo "FAIL: the is_whnf mint gate is NOT open (rc=$RUN_RC). Log: $LOG"
  echo "      Read the assertion message above: it names which control could not be"
  echo "      demonstrated and gives both readings (benign environment drift vs a"
  echo "      masquerade hole). Do not silence this by widening the gate."
  exit 1
fi
if ! grep -q '^test result: ok\. 1 passed' "$LOG"; then
  echo ""
  echo "FAIL: the canary reported success without running exactly one test." >&2
  echo "      The filter selected nothing — most likely $TEST_NAME was renamed or" >&2
  echo "      un-ignored. Fix TEST_NAME in this script; an empty selection must" >&2
  echo "      never read as green." >&2
  exit 1
fi

rm -f "$LOG"
echo "PASS: control 3 has a live witness, all four anti-masquerade controls are"
echo "      demonstrable, and both mint bodies issue a kernel-checked CleanCic."
exit 0
