#!/usr/bin/env bash
# Ratchet for the `compiler/rustc_mir_transform` unit suite — and, with
# RATCHET_SUITE/RATCHET_BASELINE set, for any compiler crate's unit suite that
# has a named known-red set (scripts/check_compiler_unit_tests.sh hands it
# `compiler/rustc_codegen_trust_cg` with tests/known-red/rustc_codegen_trust_cg.txt).
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
# WHERE THE NAMES COME FROM (2026-09-27). The set is read from the libtest
# `failures:` LIST — the block of four-space-indented full test paths that
# closes every red suite — and its size must equal the summed `N failed` of the
# `test result:` lines, or nothing is judged. It used to be read from panic lines
# with `^thread '[a-z_]+::tests::[a-z0-9_]+`, which matched only a test exactly
# one module above `tests`: a failure in `trust_verify::bundled_borrow_provenance::tests`
# or `coverage::counters::node_flow::tests` was never observed at all (so the
# gate read PASS over it), one in `trust_verify::tests::runtime_config_tests` or
# `trust_verify::tests::whole_function_receipt_tests` was recorded under the
# submodule's name, and a failure that panics nowhere (a `#[should_panic]` test
# that returned) printed no panic line either. Baseline rows are therefore FULL
# libtest paths (`trust_verify::tests::name`).
#
#   scripts/check_trust_verify_suite_ratchet.sh                     # the gate
#   scripts/check_trust_verify_suite_ratchet.sh --judge <log> <rc>  # judge an
#                        # existing `x.py test compiler/rustc_mir_transform` log
#                        # and its exit status; builds nothing
#   scripts/check_trust_verify_suite_ratchet.sh --selftest          # mutation proof
#
# Exit 0: the failing set is exactly the baseline. 1: it is not. 2: nothing was
# judged (no suite reached a result, or the failures could not be attributed).
set -uo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"
SUITE="${RATCHET_SUITE:-compiler/rustc_mir_transform}"
BASELINE="${RATCHET_BASELINE:-tests/known-red/rustc_mir_transform.txt}"

accepted_set() {
  # Comment- and blank-stripped, sorted, unique. An EMPTY set is a valid
  # baseline — it is the state this ratchet exists to reach.
  sed -e 's/#.*//' -e 's/[[:space:]]//g' "$1" 2>/dev/null | grep -v '^$' | sort -u
}

strip_ansi() {
  LC_ALL=C sed $'s/\x1b\\[[0-9;]*[A-Za-z]//g' "$1"
}

observed_set() {
  # The libtest/bootstrap `failures:` LIST: a `failures:` line followed directly
  # by four-space-indented names. The earlier `failures:` line that opens the
  # captured-output section is followed by a BLANK line, so it contributes
  # nothing. `x.py test` exits non-zero on failure, which is expected here — the
  # SET is the signal, not the exit code.
  strip_ansi "$1" | awk '
    /^failures:$/ { inlist = 1; next }
    inlist && /^    [^ ]/ { sub(/^    /, ""); print; next }
    { inlist = 0 }
  ' | sort -u
}

failed_count() {
  # The sum of `N failed` over every `test result:` line.
  strip_ansi "$1" | sed -nE 's/^test result: .* ([0-9]+) failed;.*/\1/p' \
    | awk '{ s += $1 } END { print s + 0 }'
}

# THE comparator. The gate and the selftest both call this, so the selftest
# proves the code that judges a run, not a copy of it.
#   compare_sets <observed-file> <accepted-file>
# Prints the verdict; returns 0 only when the two sets are equal.
compare_sets() {
  local obs="$1" acc="$2" new_failures now_passing status=0
  new_failures="$(comm -23 "$obs" "$acc")"
  now_passing="$(comm -13 "$obs" "$acc")"
  echo "observed failing: $(wc -l < "$obs" | tr -d ' ')   accepted: $(wc -l < "$acc" | tr -d ' ')"
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
  return "$status"
}

# judge_log <log> <x.py-exit> <accepted-file> — the whole verdict on one run.
judge_log() {
  local log="$1" xpy_status="$2" acc="$3" clean obs counted named results rc
  # Strip once into a file and read only that. A `strip_ansi | grep -q`
  # pipeline is WRONG under `pipefail`: grep exits at its first match, the
  # stripper takes SIGPIPE on any log longer than a pipe buffer, and the
  # pipeline's failure reads as "no result" (measured on a real 5.7k-line x.py
  # log; the selftest's large-log case pins it).
  clean="$(mktemp)"; obs="$(mktemp)"
  strip_ansi "$log" > "$clean"
  results="$(grep -c "^test result:" "$clean")"
  # A build/harness failure is NOT a clean red set — refuse rather than compare an
  # empty observation against the baseline and call it progress. This is the
  # vacuous-zero trap: 0 observed failures because nothing RAN looks identical to
  # 0 because everything passed.
  if [ "$results" -eq 0 ]; then
    echo "REFUSE: the suite did not run to a result (x.py exit $xpy_status)."
    echo "        This is not a green — no test executed. Tail:"
    tail -20 "$log"
    rm -f "$clean" "$obs"
    return 2
  fi
  observed_set "$clean" > "$obs"
  counted="$(failed_count "$clean")"
  named="$(wc -l < "$obs" | tr -d ' ')"
  grep -E "^test result:" "$clean" | head -3
  rc=0
  if [ "$counted" -ne "$named" ]; then
    echo "REFUSE: the suites report $counted failed test(s) but the failures list"
    echo "        names $named — the red set cannot be attributed, so nothing is judged."
    rc=2
  elif [ "$xpy_status" -ne 0 ] && [ "$counted" -eq 0 ]; then
    echo "REFUSE: x.py exited $xpy_status with no failing test — something other than"
    echo "        a test failed (a build, a doctest harness, a crashed binary). Tail:"
    tail -20 "$log"
    rc=2
  else
    compare_sets "$obs" "$acc"
    rc=$?
  fi
  rm -f "$clean" "$obs"
  return "$rc"
}

if [ "${1:-}" = "--selftest" ]; then
  # Mutation proof of compare_sets and judge_log, over a SYNTHETIC baseline and
  # SYNTHETIC logs so it holds whatever the live baseline contains — including
  # nothing, which is where it is meant to end up. It used to derive its cases
  # from the live rows and refused an empty baseline, so emptying the known-red
  # list (the goal) would have turned this push lane red.
  if [ ! -f "$BASELINE" ]; then echo "selftest: baseline file $BASELINE is missing" >&2; exit 2; fi
  tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
  accepted_set "$BASELINE" > "$tmp/live"   # must parse; may be empty
  printf 'a::tests::accepted_red_one\na::tests::accepted_red_two\n' | sort -u > "$tmp/acc"
  : > "$tmp/empty"

  expect() {  # expect <want-status> <label> <observed> <accepted>
    local want="$1" label="$2" got
    compare_sets "$3" "$4" > "$tmp/out" 2>&1; got=$?
    if [ "$got" -ne "$want" ]; then
      echo "selftest: FAILED — $label (compare_sets returned $got, wanted $want)" >&2
      sed 's/^/  | /' "$tmp/out" >&2
      exit 1
    fi
    echo "selftest: $label"
  }
  { cat "$tmp/acc"; echo "a::tests::a_brand_new_regression"; } | sort -u > "$tmp/obs_new"
  grep -v '^a::tests::accepted_red_one$' "$tmp/acc" > "$tmp/obs_fixed"
  expect 1 "a NEW failure is refused" "$tmp/obs_new" "$tmp/acc"
  expect 1 "a STALE baseline row (now passing) is refused" "$tmp/obs_fixed" "$tmp/acc"
  expect 0 "the exact accepted set passes" "$tmp/acc" "$tmp/acc"
  expect 0 "an empty baseline with nothing failing passes" "$tmp/empty" "$tmp/empty"
  expect 1 "an empty baseline refuses any failure" "$tmp/obs_new" "$tmp/empty"
  expect 0 "the live baseline against itself passes" "$tmp/live" "$tmp/live"

  # judge_log over logs in bootstrap's renderer shape
  # (src/bootstrap/src/utils/render_tests.rs, render_suite_outcome).
  red_log() {  # red_log <file> <name>... — a red suite whose failures are <name>...
    local out="$1" n; shift
    {
      echo "running 12 tests"
      echo "......F.F..."
      printf '\nfailures:\n\n'
      for n in "$@"; do
        # Only a failure WITH captured output gets a `----` section; the
        # list below is the one place every failure is named.
        [ "$n" = "a::tests::silent_should_panic" ] && continue
        printf -- '---- %s stdout ----\n' "$n"
        printf "\nthread '%s' (4242) panicked at src/a.rs:1:1:\nboom\n" "$n"
        # captured output that itself looks like a list must not be read as one
        printf 'failures:\n\n    not_a_test_name\n'
        printf -- '---- %s stdout end ----\n' "$n"
      done
      printf '\nfailures:\n'
      for n in "$@"; do printf '    %s\n' "$n"; done
      printf '\ntest result: FAILED. %d passed; %d failed; 0 ignored; 0 measured; 0 filtered out; finished in 1.00s\n\n' \
        "$((12 - $#))" "$#"
    } > "$out"
  }
  judge() {  # judge <want-status> <label> <log> <x.py-exit> <accepted>
    local want="$1" label="$2" got
    judge_log "$3" "$4" "$5" > "$tmp/out" 2>&1; got=$?
    if [ "$got" -ne "$want" ]; then
      echo "selftest: FAILED — $label (judge_log returned $got, wanted $want)" >&2
      sed 's/^/  | /' "$tmp/out" >&2
      exit 1
    fi
    echo "selftest: $label"
  }
  printf 'running 12 tests\n............\n\ntest result: ok. 12 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 1.00s\n\n' > "$tmp/green.log"
  judge 0 "a green suite against an empty baseline passes" "$tmp/green.log" 0 "$tmp/empty"
  { awk 'BEGIN { for (i = 0; i < 20000; i++) print "   Compiling filler v0.0." i }'; cat "$tmp/green.log"; } > "$tmp/big.log"
  judge 0 "a green result after 20000 lines of build output is still read (no SIGPIPE)" \
    "$tmp/big.log" 0 "$tmp/empty"
  judge 1 "a green suite against a non-empty baseline is a stale row" "$tmp/green.log" 0 "$tmp/acc"
  red_log "$tmp/nested.log" "trust_verify::bundled_borrow_provenance::tests::a_provenance_test"
  judge 1 "a failure two modules deep is observed (the old panic regex never saw it)" \
    "$tmp/nested.log" 101 "$tmp/empty"
  red_log "$tmp/sub.log" "trust_verify::tests::runtime_config_tests::a_config_test"
  observed_set "$tmp/sub.log" > "$tmp/sub.obs"
  if [ "$(cat "$tmp/sub.obs")" != "trust_verify::tests::runtime_config_tests::a_config_test" ]; then
    echo "selftest: FAILED — a nested test is named by its full path, got: $(cat "$tmp/sub.obs")" >&2
    exit 1
  fi
  echo "selftest: a failure in a submodule of tests is named by its full path"
  red_log "$tmp/silent.log" "a::tests::silent_should_panic" "a::tests::accepted_red_one"
  judge 1 "a failure with no panic line and no captured output is observed" \
    "$tmp/silent.log" 101 "$tmp/empty"
  red_log "$tmp/acc.log" "a::tests::accepted_red_one" "a::tests::accepted_red_two"
  judge 0 "a red set equal to the baseline passes" "$tmp/acc.log" 101 "$tmp/acc"
  { red_log "$tmp/bad.log" "a::tests::one"; sed -i.bak 's/    a::tests::one//' "$tmp/bad.log"; }
  judge 2 "a failure count the list does not account for is refused, not judged" \
    "$tmp/bad.log" 101 "$tmp/empty"
  printf 'error: could not compile `rustc_mir_transform`\n' > "$tmp/nobuild.log"
  judge 2 "a run that reached no test result is refused" "$tmp/nobuild.log" 1 "$tmp/empty"
  judge 2 "x.py failing with every test green is refused, not passed" "$tmp/green.log" 1 "$tmp/empty"
  printf '\033[0mtest result: \033[31mFAILED\033[0m. 0 passed; 1 failed; 0 ignored; 0 measured; 0 filtered out\n' > "$tmp/color.log"
  if [ "$(failed_count "$tmp/color.log")" != 1 ]; then
    echo "selftest: FAILED — a coloured result line is not counted" >&2; exit 1
  fi
  echo "selftest: a coloured result line is counted"
  echo "selftest: PASS (both directions mutation-proved; live baseline has $(wc -l < "$tmp/live" | tr -d ' ') row(s))"
  exit 0
fi

acc="$(mktemp)"
if [ "${1:-}" = "--judge" ]; then
  [ $# -eq 3 ] || { echo "usage: $0 --judge <x.py-log> <x.py-exit-status>" >&2; exit 2; }
  trap 'rm -f "$acc"' EXIT
  accepted_set "$BASELINE" > "$acc"
  judge_log "$2" "$3" "$acc"
  exit $?
fi

log="$(mktemp)"; trap 'rm -f "$log" "$acc"' EXIT
# bootstrap takes its parallelism from `-j`, never from CARGO_BUILD_JOBS.
XPY_JOBS=()
[ -n "${CARGO_BUILD_JOBS:-}" ] && XPY_JOBS=(-j "$CARGO_BUILD_JOBS")
echo "running: x.py test $SUITE --stage 1 ${XPY_JOBS[*]:-} --no-fail-fast (baseline $BASELINE)"
./x.py test "$SUITE" --stage 1 ${XPY_JOBS[@]+"${XPY_JOBS[@]}"} --no-fail-fast > "$log" 2>&1
xpy_status=$?
accepted_set "$BASELINE" > "$acc"
judge_log "$log" "$xpy_status" "$acc"
exit $?
