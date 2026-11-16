#!/bin/bash
# Self-test for scripts/trust_control_canary.sh — the `is_whnf` mint-gate canary.
#
# This test BUILDS NOTHING and runs no kernel work: it costs milliseconds and
# lives in the `fast` script-test lane. What it protects is the wiring, which is
# the half that failed before. The canary itself detects a closed mint gate, but
# a canary can only report if it is still SELECTED and still RUN:
#
#   * libtest exits 0 when its filter selects nothing, so renaming the test (or
#     un-ignoring it) would leave `--ignored --exact <old name>` reporting PASS
#     forever. The lane's own runtime guard catches that, but only once someone
#     pays a release build plus ~3.5 minutes — this catches it pre-push instead.
#   * a lane named by no orchestrator is a lane nobody runs. That is exactly how
#     the `is_whnf` mint stayed blocked from July to 2026-08-23; see
#     reports/2026-08-23-is-whnf-mint-blocked-by-control-3.md.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
set -uo pipefail

REPO_ROOT=$(cd -P "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)
CANARY="$REPO_ROOT/scripts/trust_control_canary.sh"
SOURCE_FILE="$REPO_ROOT/crates/trust-certify/src/checker_core_is_whnf.rs"

fail() {
  printf 'FAIL: %s\n' "$*" >&2
  exit 1
}

[ -f "$CANARY" ] || fail "missing $CANARY"
[ -x "$CANARY" ] || fail "$CANARY is not executable"
bash -n "$CANARY" || fail "$CANARY does not parse"

# --list must not build; it must name exactly one test.
LIST_OUT="$(bash "$CANARY" --list 2>&1)"
LIST_RC=$?
[ "$LIST_RC" -eq 0 ] || fail "--list exited $LIST_RC: $LIST_OUT"
TEST_PATH="$(printf '%s\n' "$LIST_OUT" | head -1)"
case "$TEST_PATH" in
  checker_core_is_whnf::tests::*) ;;
  *) fail "--list did not name a checker_core_is_whnf test, got: $TEST_PATH" ;;
esac
TEST_FN="${TEST_PATH##*::}"

# THE TRIPWIRE: the named test must still exist, and must still be `#[ignore]`d
# — the lane selects it with `--ignored --exact`, so an un-ignored test is
# selected by NOTHING and the lane would go permanently, silently vacuous.
[ -f "$SOURCE_FILE" ] || fail "missing $SOURCE_FILE"

# Returns 0 when `fn <name>` exists in the source AND carries both `#[test]` and
# `#[ignore]` within the four lines above it. Written as a function so the check
# can be MUTATED below: an assertion nobody has watched fail is not evidence.
selectable_ignored_test() {
  local name="$1" line attrs
  line="$(grep -n "fn ${name}(" "$SOURCE_FILE" | head -1 | cut -d: -f1)"
  [ -n "$line" ] || return 1
  attrs="$(sed -n "$(( line > 4 ? line - 4 : 1 )),$(( line - 1 ))p" "$SOURCE_FILE")"
  case "$attrs" in *'#[ignore'*) ;; *) return 2 ;; esac
  case "$attrs" in *'#[test]'*) ;; *) return 3 ;; esac
  return 0
}

selectable_ignored_test "$TEST_FN"
case $? in
  0) ;;
  1) fail "the canary names ${TEST_PATH}, but no \`fn ${TEST_FN}(\` exists in
      ${SOURCE_FILE#"$REPO_ROOT"/}. The test was renamed or removed; libtest would
      report PASS having run nothing. Fix TEST_NAME in scripts/trust_control_canary.sh." ;;
  2) fail "${TEST_FN} is no longer #[ignore]d, but the lane selects it with \`--ignored\`,
      which would then select nothing. Either restore the attribute (with its measured
      justification) or drop the \`--ignored\` flag from scripts/trust_control_canary.sh." ;;
  *) fail "${TEST_FN} has no #[test] attribute within 4 lines above it" ;;
esac

# MUTATION PROOF that the tripwire above can fail: a name that is not there must
# be rejected, and so must a `#[test]` that is not `#[ignore]`d. The second uses
# a real inline test from the same file — the module deliberately keeps cheap
# tests un-ignored, so this stays honest as the file changes.
if selectable_ignored_test "definitely_not_a_test_fn_$$"; then
  fail "the rename tripwire accepted a function that does not exist"
fi
UNIGNORED_FN="$(grep -B1 '^    fn ' "$SOURCE_FILE" \
  | grep -A1 '^    #\[test\]$' | sed -n 's/^    fn \([a-z0-9_]*\)(.*/\1/p' | head -1)"
if [ -n "$UNIGNORED_FN" ] && selectable_ignored_test "$UNIGNORED_FN"; then
  fail "the #[ignore] tripwire accepted ${UNIGNORED_FN}, which is an inline (non-ignored) test"
fi

# Argument handling: help is free and a typo must not be read as "run it".
HELP_OUT="$(bash "$CANARY" --help 2>&1)"
HELP_RC=$?
[ "$HELP_RC" -eq 0 ] || fail "--help exited $HELP_RC"
# NOT `grep -q`: this file runs under `set -o pipefail`, and `-q` exits at the
# FIRST match — line 1 of a ~6 KB header — so the `printf` feeding it is still
# writing when the pipe closes and dies of SIGPIPE (status 141), which pipefail
# then reports as the pipeline's status. Measured 2026-09-10 on macOS bash 3.2
# / BSD grep: PIPESTATUS=141 0 on every measured run — a timing race this
# machine lost every time, read as a false FAIL ("--help printed no header
# text") with the header fully present on stdout.
# Reading to EOF (no -q) is what makes the exit status mean "matched".
printf '%s\n' "$HELP_OUT" | grep -i 'mint-gate canary' >/dev/null \
  || fail "--help printed no header text"
bash "$CANARY" --definitely-not-a-flag >/dev/null 2>&1
BOGUS_RC=$?
[ "$BOGUS_RC" -eq 2 ] || fail "an unknown argument exited $BOGUS_RC, expected 2"

# ANTI-ORPHAN: some orchestrator must name the lane. A canary in no manifest row
# and no tier reproduces, one level up, the exact failure it was written for.
MANIFEST="$REPO_ROOT/tests/run_trust_comprehensive_harness.sh"
grep -qF 'scripts/trust_control_canary.sh' "$MANIFEST" \
  || fail "no gate-manifest row in tests/run_trust_comprehensive_harness.sh runs the canary"
grep -qF 'scripts/trust_control_canary.sh' "$REPO_ROOT/scripts/run_tests_after_build.sh" \
  || fail "no run_tests_after_build.sh tier runs the canary"

# The doc comment must keep citing the write-up: the reason this lane exists is
# not reconstructible from the code, and the report is where it lives.
REPORT="reports/2026-08-23-is-whnf-mint-blocked-by-control-3.md"
[ -f "$REPO_ROOT/$REPORT" ] || fail "$REPORT is gone; the canary's doc comment cites it"
grep -qF "$REPORT" "$SOURCE_FILE" || fail "$SOURCE_FILE no longer cites $REPORT"
grep -qF "$REPORT" "$CANARY" || fail "$CANARY no longer cites $REPORT"

echo "trust_control_canary_test: PASS (${TEST_PATH})"
exit 0
