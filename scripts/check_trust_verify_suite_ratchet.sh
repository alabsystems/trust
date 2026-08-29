#!/usr/bin/env bash
# Ratchet for the `compiler/rustc_mir_transform` unit suite.
#
# WHY THIS EXISTS. `e248b1a431` recorded this suite as "429 passed, 2 failed",
# both survivors with written causes. Measured 2026-08-26 on origin/main: EIGHT
# failed. Six regressions landed unseen, because NO pre-push lane EXECUTES this
# suite — the then-`fast.pr-gate` bundle invoked no cargo/targo at all, and the scoped
# `x.py check --stage 1` type-checks test targets without running them. Four of
# the eight were ONE ill-typed fixture constant (`ConstValue::Int` is the SIGNED
# widthless literal and never matches a `u32` place, so
# `validate_binary_assignment_types` refused the whole body and every loop VC
# vanished); see `c187f1d942`.
#
# WHY A NAMED SET, NOT A COUNT. A count is satisfied by "one fixed, one new" and
# would have reported green through exactly that. The baseline names each
# accepted failure with an owner and a reason, and this gate fails when the
# observed set is not a SUBSET of it. It ALSO fails when a baseline entry now
# passes — a quarantine row must not outlive its problem (CLAUDE.md), and a
# stale row is how a re-broken test gets silently re-accepted.
#
#   scripts/check_trust_verify_suite_ratchet.sh              # the gate
#   scripts/check_trust_verify_suite_ratchet.sh --selftest   # mutation proof
set -uo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"
BASELINE="tests/known-red/rustc_mir_transform.txt"

accepted_set() {
  # Comment- and blank-stripped, sorted, unique.
  sed -e 's/#.*//' -e 's/[[:space:]]//g' "$BASELINE" 2>/dev/null | grep -v '^$' | sort -u
}

observed_set() {
  # Test names from panic lines. `x.py test` exits non-zero on failure, which is
  # expected here — the SET is the signal, not the exit code.
  grep -oE "^thread '[a-z_]+::tests::[a-z0-9_]+" "$1" 2>/dev/null \
    | sed "s/.*tests:://" | sort -u
}

if [ "${1:-}" = "--selftest" ]; then
  # Mutation proof: a synthetic observation carrying a test NOT in the baseline
  # must be refused, and one missing a baseline entry must also be refused.
  tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
  acc="$tmp/accepted"; accepted_set > "$acc"
  if [ ! -s "$acc" ]; then echo "selftest: baseline is empty or missing" >&2; exit 2; fi
  first="$(head -1 "$acc")"

  # (a) a NEW failure must be caught
  { cat "$acc"; echo "a_brand_new_regression"; } | sort -u > "$tmp/obs_new"
  if comm -23 "$tmp/obs_new" "$acc" | grep -q .; then
    echo "selftest: NEW-failure detection works"
  else
    echo "selftest: FAILED — a new failure was not detected" >&2; exit 1
  fi

  # (b) a baseline entry that now passes must be caught
  grep -v "^${first}$" "$acc" > "$tmp/obs_fixed" || true
  if comm -13 "$tmp/obs_fixed" "$acc" | grep -q .; then
    echo "selftest: STALE-baseline detection works"
  else
    echo "selftest: FAILED — a stale baseline row was not detected" >&2; exit 1
  fi
  echo "selftest: PASS (both directions mutation-proved)"
  exit 0
fi

log="$(mktemp)"; trap 'rm -f "$log"' EXIT
echo "running: x.py test compiler/rustc_mir_transform --stage 1"
./x.py test compiler/rustc_mir_transform --stage 1 > "$log" 2>&1
xpy_status=$?

# A build/harness failure is NOT a clean red set — refuse rather than compare an
# empty observation against the baseline and call it progress. This is the
# vacuous-zero trap: 0 observed failures because nothing RAN looks identical to
# 0 because everything passed.
if ! grep -q "test result:" "$log"; then
  echo "REFUSE: the suite did not run to a result (x.py exit $xpy_status)."
  echo "        This is not a green — no test executed. Tail:"
  tail -20 "$log"
  exit 2
fi

obs="$(mktemp)"; acc="$(mktemp)"
trap 'rm -f "$log" "$obs" "$acc"' EXIT
observed_set "$log" > "$obs"
accepted_set > "$acc"

new_failures="$(comm -23 "$obs" "$acc")"
now_passing="$(comm -13 "$obs" "$acc")"

echo "observed failing: $(wc -l < "$obs" | tr -d ' ')   accepted: $(wc -l < "$acc" | tr -d ' ')"
grep -E "test result:" "$log" | head -3

status=0
if [ -n "$new_failures" ]; then
  echo ""
  echo "FAIL: NEW failing tests not in $BASELINE:"
  printf '  %s\n' $new_failures
  echo "  Fix them, or add a row with an OWNER and a REASON if the red is accepted."
  status=1
fi
if [ -n "$now_passing" ]; then
  echo ""
  echo "FAIL: these are listed as known-red but now PASS — delete their rows:"
  printf '  %s\n' $now_passing
  echo "  A quarantine row must not outlive its problem: leaving it lets a"
  echo "  re-break of the same test be silently re-accepted."
  status=1
fi
[ "$status" -eq 0 ] && echo "PASS: failing set is exactly the accepted baseline"
exit "$status"
