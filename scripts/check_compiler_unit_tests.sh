#!/usr/bin/env bash
# Trust: RUN the unit tests of the compiler crates a change touched.
#
# WHY THIS EXISTS. Almost no lane executed a compiler crate's own `#[test]`s.
# The `crates/` cargo sweeps cannot reach `compiler/**` at all (those crates are
# members of the root workspace only; docs/VALIDATION_LADDER.md, rung 1), and
# `scoped.compiler-check` runs `x.py check --stage 1 --tests`, which COMPILES
# test targets and executes none of them. Two rows did run some:
# `slow.mir-transform-ratchet` (`rustc_mir_transform` alone) and
# `quick.compiler-unit-tests` (a FIXED list — rustc_driver_impl, rustc_session,
# rustc_mir_transform — in a profile no hook runs, last green `never`). Neither
# follows the change, and neither reaches rustc_metadata or a rustc_private
# crate. So a guard like rustc_metadata's TyEncodable MIR wire-layout golden (it fails when
# a MIR type's encoding changes without a METADATA_VERSION bump) could catch its
# defect only when someone happened to type `./x.py test compiler/rustc_metadata`.
# The same was true of the three rustc_private crates under `crates/`
# (trust-mir-extract, trust-thir-lower, trust-witness), which are EXCLUDED from
# the crates/ workspace and reachable only through bootstrap: the suites of the
# first two were red on origin/main 521477a0d2 (2026-09-24), and that was found
# only because agents working on something else ran them by hand.
#
# SCOPE — the diff decides. A full `x.py test compiler` is a whole-compiler
# build plus ~40 crates' suites, so this runs only the suites the change can
# have broken:
#
#   compiler/<crate>/**                    -> compiler/<crate>, when that crate
#                                             has a #[test] anywhere
#   compiler/rustc_middle/src/mir/**       -> ALSO compiler/rustc_metadata: the
#                                             MIR types are defined in
#                                             rustc_middle, but a guard that
#                                             pins their rmeta wire layout lives
#                                             in rustc_metadata's tests (selected
#                                             only while that crate has one)
#   crates/<rustc_private crate>/**        -> crates/<crate>; the list is
#                                             declared in RUSTC_PRIVATE_CRATES below
#   compiler/rustc_mir_transform/**        -> delegated to
#                                             scripts/check_trust_verify_suite_ratchet.sh,
#                                             which owns that suite's known-red
#                                             baseline
#   compiler/rustc_codegen_trust_cg/**     -> delegated to the SAME ratchet with
#                                             tests/known-red/rustc_codegen_trust_cg.txt
#                                             (its suite is red on main with ten
#                                             named failures, so a pass/fail bit
#                                             would judge nothing)
#   the trust-cg frontend's RUN-MAKE fixtures (tests/run-make/trust-cg-*,
#   trust-instance-*, trust-ir-emit*)      -> run at STAGE 1 (x.py test --stage 1
#                                             ... --force-rerun) when the change
#                                             touches rustc_codegen_trust_cg,
#                                             trust-thir-lower or one of those
#                                             fixtures. `suite.run-make` is a
#                                             stage-2 row that has never run, and
#                                             every trust-* run-make test is
#                                             IGNORED at stage 2
#                                             (docs/KNOWN_HAZARDS.md), so without
#                                             this no lane runs D17's differential
#                                             or the instance lane's fixtures.
#
# Every other path selects nothing: ordinary `crates/` members have cargo lanes
# of their own, and a docs-only change cannot break a unit test.
#
# A SKIP IS NOT A PASS. With nothing in scope the lane exits 0 (the convention
# of `scoped.compiler-check`), and prints a `WARN:` line so the harness surfaces
# it beside the PASS rather than filing it as evidence.
#
# WHY NOT A PUSH LANE. It is an `x.py test`, i.e. a BUILD that takes the
# build-tree lock. scripts/hooks/pre-push records what happened when
# `slow.mir-transform-ratchet` sat in the push tier beside
# `scoped.compiler-check`: the two collided on that lock and produced two red
# lanes and zero defects. So this lane is `slow` and its `--selftest`, which
# builds nothing, is the push-tier row.
#
# Usage:
#   check_compiler_unit_tests.sh [base-ref]     # default base: origin/main
#   check_compiler_unit_tests.sh --print [base-ref]
#                                               # print the selection; run nothing
#   check_compiler_unit_tests.sh --selftest     # mutation-proof the selection
#   check_compiler_unit_tests.sh [base-ref] --also "<paths>" [--run-make]
#                                               # add suites (scripts/land_gate.py
#                                               # passes the crates a change
#                                               # REACHES); never removes one
#
# The subject is the COMMITTED range `base...HEAD`, the same reading
# scripts/check_compiler_targets_build.sh takes. Exit 0 when every selected
# suite passes OR nothing is in scope (said out loud), 1 on a red suite, 2 when
# nothing could be judged (unresolvable base, preflight refusal, a build that
# never reached a test result, a rustc_private suite with no local sysroot).
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
set -uo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel 2>/dev/null)" || {
  echo "not inside a git worktree" >&2
  exit 2
}
cd "$REPO_ROOT" || exit 2

# These consumers are root members outside default-members. Their tests need
# bootstrap's compiler sysroot (dev-test.sh routes the same explicit requests).
RUSTC_PRIVATE_CRATES="trust-mir-extract trust-thir-lower trust-witness"
RATCHET_CRATE="compiler/rustc_mir_transform"
# The trust-cg backend's unit suite: `x.py test --stage 1 compiler/rustc_codegen_trust_cg`
# DOES reach it (measured at step 2 increment 3's landing head: 103 tests, all
# passing). It was once listed here as unreachable, which was false; it is judged
# against its own known-red set, EMPTY since 1ec945d698 repaired its ten failures,
# so the ratchet refuses any failure (and a row added back needs an owner and reason).
TRUST_CG_CRATE="compiler/rustc_codegen_trust_cg"
TRUST_CG_BASELINE="tests/known-red/rustc_codegen_trust_cg.txt"
# What the backend and its run-make fixtures depend on outside the crate itself: a
# change to any of these re-judges both (the crate's known-red ratchet and the
# fixtures). The first-party entries are gitlinks, spelled as `git diff --name-only`
# prints a pin move.
TRUST_CG_DEP_CRATES="trust-thir-lower trust-mir-extract trust-cg-bridge trust-ir-bridge trust-types"
TRUST_CG_DEP_GITLINKS="first-party/trust-ir first-party/trust-cg"
# The run-make fixtures of the trust-ir codegen frontend, and what selects them.
# trust-ir-template-*: the level-S producer and its template-instance TEST-ORACLE (PKG-C2d2).
TRUST_CG_RUN_MAKE="tests/run-make/trust-cg-* tests/run-make/trust-instance-* tests/run-make/trust-ir-emit* tests/run-make/trust-ir-template-*"

# crate_has_unit_tests <dir> — a #[test] anywhere under it. A crate without one
# would make x.py build the compiler to run zero tests. Probed under
# $CRATE_TREE (default: this checkout) so the selftest can use a synthetic tree.
CRATE_TREE="."
crate_has_unit_tests() {
  grep -rqsE '#\[test\]' "$CRATE_TREE/$1"
}

# select_suites — changed paths on stdin, one bootstrap path per line on stdout.
select_suites() {
  local path crate
  while IFS= read -r path; do
    case "$path" in
      compiler/rustc_middle/src/mir/*)
        echo "compiler/rustc_middle"
        echo "compiler/rustc_metadata"
        ;;
      compiler/*/*)
        crate="${path#compiler/}"; crate="compiler/${crate%%/*}"
        echo "$crate"
        ;;
      crates/*/*)
        crate="${path#crates/}"; crate="${crate%%/*}"
        case " $RUSTC_PRIVATE_CRATES " in *" $crate "*) echo "crates/$crate" ;; esac
        case " $TRUST_CG_DEP_CRATES " in *" $crate "*) echo "$TRUST_CG_CRATE" ;; esac
        ;;
      *)
        case " $TRUST_CG_DEP_GITLINKS " in *" $path "*) echo "$TRUST_CG_CRATE" ;; esac
        ;;
    esac
  done | sort -u | while IFS= read -r crate; do
    if [ "$crate" = "$RATCHET_CRATE" ] || [ "$crate" = "$TRUST_CG_CRATE" ] \
      || crate_has_unit_tests "$crate"; then
      echo "$crate"
    fi
  done
}

# also_suites <paths...> — the suites `--also` adds: each bootstrap path is
# spelled as a file under it and goes through select_suites, so the same rules
# apply (a #[test] somewhere, the ratchet crates, the rustc_private crates).
also_suites() {
  local p
  for p in "$@"; do printf '%s/src/lib.rs\n' "$p"; done | select_suites
}

# run_make_selected — changed paths on stdin; prints `yes` when the trust-cg
# run-make fixtures are in scope: the backend, anything it depends on
# (TRUST_CG_DEP_CRATES, TRUST_CG_DEP_GITLINKS), or a fixture itself changed.
run_make_selected() {
  local path crate hit=""
  while IFS= read -r path; do
    case "$path" in
      compiler/rustc_codegen_trust_cg/*) hit=yes ;;
      tests/run-make/trust-cg-*|tests/run-make/trust-instance-*|tests/run-make/trust-ir-emit*|tests/run-make/trust-ir-template-*) hit=yes ;;
      crates/*/*)
        crate="${path#crates/}"; crate="${crate%%/*}"
        case " $TRUST_CG_DEP_CRATES " in *" $crate "*) hit=yes ;; esac
        ;;
      *)
        case " $TRUST_CG_DEP_GITLINKS " in *" $path "*) hit=yes ;; esac
        ;;
    esac
  done
  [ -n "$hit" ] && echo yes
  return 0
}

# judge_run_make <log> <expected-fixture-count> — 0 green, 1 red, 2 nothing judged.
# Green needs EVERY expanded fixture to have PASSED: a run whose fixtures were all
# (or partly) IGNORED — `//@ only-aarch64`, `//@ needs-trust-cg-backend` on a host or
# compiler that cannot run them — prints `test result: ok. 0 passed; ... N ignored`,
# which would otherwise read as green while D17's differential never ran.
judge_run_make() {
  local log="$1" expected="$2" results passed ignored failed
  results="$(grep -c "^test result:" "$log" || true)"
  [ "$results" -eq 0 ] && return 2
  passed="$(grep "^test result:" "$log" | sed -n 's/.* \([0-9][0-9]*\) passed.*/\1/p' | awk '{s+=$1} END {print s+0}')"
  failed="$(grep "^test result:" "$log" | sed -n 's/.* \([0-9][0-9]*\) failed.*/\1/p' | awk '{s+=$1} END {print s+0}')"
  ignored="$(grep "^test result:" "$log" | sed -n 's/.* \([0-9][0-9]*\) ignored.*/\1/p' | awk '{s+=$1} END {print s+0}')"
  [ "$failed" -gt 0 ] && return 1
  if [ "$ignored" -gt 0 ] || [ "$passed" -ne "$expected" ]; then
    return 2
  fi
  return 0
}

# host_triple — the triple of the machine running this lane (the target the
# trust-cg run-make fixtures are pinned to). A configuration that builds more
# targets (scripts/recreate_bootstrap.py's builds both Apple architectures) makes
# `x.py test` run the fixtures once per target, and on the other target they are
# IGNORED by their `//@ only-aarch64`/backend directives: judged together, a
# green host run read as "not every fixture passed" (measured 2026-10-14 at the
# gates/trust-scale-select landing: aarch64 34 passed, x86_64 2 passed and 32
# ignored, REFUSE). The fixtures run for the host alone.
host_triple() {
  local os arch
  os="$(uname -s)"; arch="$(uname -m)"
  case "$arch" in arm64) arch=aarch64 ;; esac
  case "$os" in
    Darwin) echo "$arch-apple-darwin" ;;
    Linux) echo "$arch-unknown-linux-gnu" ;;
    *) echo "" ;;
  esac
}

# list_has <word> <words...> / list_has_prefix <prefix> <words...> — membership
# WITHOUT a pipe. `printf '%s\n' $list | grep -q ...` is a race under `pipefail`:
# grep -q exits at its first match, printf can then die of SIGPIPE, and the whole
# pipeline reads FALSE although the word is there. Measured 2026-10-01: a lane run
# printed "printf: write error: Broken pipe" and silently skipped the
# rustc_codegen_trust_cg ratchet it had selected — a green lane that judged
# nothing for that suite.
list_has() {
  local want="$1" word
  shift
  for word in "$@"; do [ "$word" = "$want" ] && return 0; done
  return 1
}
list_has_prefix() {
  local prefix="$1" word
  shift
  for word in "$@"; do
    case "$word" in "$prefix"*) return 0 ;; esac
  done
  return 1
}

# Stage-1 compiler-crate tests are built with the seed. Keep their all-target
# tests, and run the default suites with the in-tree compiler: the seed cannot
# judge current lint behavior or features stabilized after its own release.
# Default suites also build normal example binaries, whose main bodies can be
# absent from an all-target test harness's monomorphized code. Bootstrap selects
# stage N-1 as the compiler for these crate tests, hence stage 2 for this phase.
# Run both phases even if one fails, preserving --no-fail-fast across them.
run_compiler_suites() {
  local unit_rc current_rc
  echo "running: x.py test --stage 1 ${XPY_JOBS[*]:-} --all-targets --no-fail-fast $*"
  python3 x.py test --stage 1 ${XPY_JOBS[@]+"${XPY_JOBS[@]}"} --all-targets --no-fail-fast "$@"
  unit_rc=$?
  echo "running: x.py test --stage 2 ${XPY_JOBS[*]:-} --no-fail-fast $* (default suites, including normal examples and docs)"
  python3 x.py test --stage 2 ${XPY_JOBS[@]+"${XPY_JOBS[@]}"} --no-fail-fast "$@"
  current_rc=$?
  echo "compiler suite phases: seed targets exit $unit_rc; current default suites exit $current_rc"
  [ "$unit_rc" -eq 0 ] || return "$unit_rc"
  return "$current_rc"
}

if [ "${1:-}" = "--selftest" ]; then
  # Membership is exact and pipe-free (see `list_has`): a long list whose first
  # word is the one asked for, the case that lost the race, must still answer yes.
  long="compiler/rustc_codegen_trust_cg $(seq -f 'crates/filler-%g' 1 20000 | tr '\n' ' ')"
  # shellcheck disable=SC2086 # the list is word-split on purpose
  if list_has compiler/rustc_codegen_trust_cg $long && list_has_prefix crates/ $long \
    && ! list_has compiler/rustc_codegen_trust compiler/rustc_codegen_trust_cg \
    && ! list_has_prefix crates/ compiler/rustc_middle; then
    echo "selftest: list membership is exact and pipe-free"
    case "$(uname -s)" in
      Darwin|Linux)
        case "$(host_triple)" in
          *-apple-darwin|*-unknown-linux-gnu) echo "selftest: host_triple names this host ($(host_triple))" ;;
          *) echo "selftest: FAILED — host_triple gave '$(host_triple)'" >&2; exit 1 ;;
        esac ;;
    esac
  else
    echo "selftest: FAILED — list_has / list_has_prefix" >&2; exit 1
  fi
  # Mutation proof of select_suites over a SYNTHETIC crate tree, so every
  # expectation is fixed by this file and not by which crates happen to carry
  # tests today (rustc_metadata's layout guard, for one, lands on its own).
  tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
  plant() {  # plant <crate-dir> <with-test: 1|0>
    mkdir -p "$tmp/$1/src"
    if [ "$2" = 1 ]; then printf '#[test]\nfn t() {}\n' > "$tmp/$1/src/tests.rs"
    else printf 'pub fn f() {}\n' > "$tmp/$1/src/lib.rs"; fi
  }
  plant compiler/rustc_metadata 1
  plant compiler/rustc_middle 1
  plant compiler/rustc_notests 0
  plant compiler/rustc_mir_transform 0
  # Planted WITHOUT a test, so the case below pins the explicit TRUST_CG_CRATE clause.
  plant compiler/rustc_codegen_trust_cg 0
  for crate in $RUSTC_PRIVATE_CRATES; do plant "crates/$crate" 1; done
  plant crates/trust-vcgen 1

  fail=0
  # Exercise the actual runner with a recording x.py substitute. Each phase
  # must see every selected crate and the admitted share; neither a failed unit
  # phase nor a failed current-compiler phase may disappear behind the other's
  # success. The current phase must retain default example builds as well as docs.
  for codes in 0:0 1:0 0:1 1:1; do
    selftest_unit_rc="${codes%:*}"; selftest_current_rc="${codes#*:}"
    want_rc=0
    [ "$codes" = 0:0 ] || want_rc=1
    (
      python3() {
        printf '%s\n' "$*" >> "$tmp/stage-calls"
        case " $* " in
          *" --all-targets "*) return "$selftest_unit_rc" ;;
          *" --stage 2 "*) return "$selftest_current_rc" ;;
          *) return 99 ;;
        esac
      }
      XPY_JOBS=(-j 6)
      : > "$tmp/stage-calls"
      run_compiler_suites compiler/rustc_lint_defs crates/trust-witness > "$tmp/stage-log" 2>&1
      rc=$?
      printf '%s\n' \
        'x.py test --stage 1 -j 6 --all-targets --no-fail-fast compiler/rustc_lint_defs crates/trust-witness' \
        'x.py test --stage 2 -j 6 --no-fail-fast compiler/rustc_lint_defs crates/trust-witness' > "$tmp/stage-want"
      [ "$rc" -eq "$want_rc" ] && cmp -s "$tmp/stage-want" "$tmp/stage-calls"
    )
    if [ "$?" -eq 0 ]; then
      echo "selftest: seed targets and current default suites preserve coverage, share and failures ($codes)"
    else
      echo "selftest: FAILED — compiler suite phase coverage or status ($codes)" >&2
      fail=1
    fi
  done
  expect() {  # expect <label> <want (space-separated, sorted)> <paths...>
    local label="$1" want="$2" got
    shift 2
    got="$(printf '%s\n' "$@" | CRATE_TREE="$tmp" select_suites | tr '\n' ' ' | sed 's/ $//')"
    if [ "$got" = "$want" ]; then
      echo "selftest: $label"
    else
      echo "selftest: FAILED — $label: want [$want], got [$got]" >&2
      fail=1
    fi
  }
  expect "a docs-only change selects nothing" "" \
    docs/VALIDATION_LADDER.md README.md
  expect "a crates/ workspace member selects nothing (cargo lanes own it)" "" \
    crates/trust-vcgen/src/lib.rs targo-trust/src/main.rs
  expect "a compiler crate with unit tests selects itself" "compiler/rustc_metadata" \
    compiler/rustc_metadata/src/rmeta/mod.rs
  expect "a MIR type change also selects the rmeta layout guard" \
    "compiler/rustc_metadata compiler/rustc_middle" \
    compiler/rustc_middle/src/mir/statement.rs
  expect "a non-MIR rustc_middle change selects only rustc_middle" "compiler/rustc_middle" \
    compiler/rustc_middle/src/ty/mod.rs
  expect "each rustc_private crate selects itself (two are backend deps: + its ratchet)" \
    "compiler/rustc_codegen_trust_cg crates/trust-mir-extract crates/trust-thir-lower crates/trust-witness" \
    crates/trust-mir-extract/src/lib.rs crates/trust-thir-lower/src/lib.rs \
    crates/trust-witness/src/lib.rs
  expect "rustc_mir_transform is selected for its ratchet, tests or not" \
    "compiler/rustc_mir_transform" compiler/rustc_mir_transform/src/trust_verify.rs
  expect "duplicates collapse" "compiler/rustc_metadata" \
    compiler/rustc_metadata/src/lib.rs compiler/rustc_metadata/src/rmeta/encoder.rs
  expect "a compiler file outside any crate selects nothing" "" compiler/README.md
  expect "a crate without unit tests selects nothing" "" compiler/rustc_notests/src/lib.rs
  expect "a crate that does not exist selects nothing" "" compiler/rustc_gone/src/lib.rs
  expect "the trust-cg backend is selected for its known-red ratchet" \
    "compiler/rustc_codegen_trust_cg" compiler/rustc_codegen_trust_cg/src/lib.rs
  expect "a backend dependency (workspace crate) selects the backend's ratchet" \
    "compiler/rustc_codegen_trust_cg" crates/trust-cg-bridge/src/lower.rs
  expect "a rustc_private backend dependency selects itself and the backend's ratchet" \
    "compiler/rustc_codegen_trust_cg crates/trust-thir-lower" \
    crates/trust-thir-lower/src/instance_admission.rs
  expect "a first-party trust-ir or trust-cg pin move selects the backend's ratchet" \
    "compiler/rustc_codegen_trust_cg" first-party/trust-ir first-party/trust-cg
  expect "an unrelated first-party pin move selects nothing" "" first-party/ty
  got="$(CRATE_TREE="$tmp" also_suites compiler/rustc_metadata compiler/rustc_notests crates/trust-witness \
    compiler/rustc_mir_transform | tr '\n' ' ' | sed 's/ $//')"
  if [ "$got" = "compiler/rustc_metadata compiler/rustc_mir_transform crates/trust-witness" ]; then
    echo "selftest: --also adds reached crates with tests (and the ratchet crate), not one without"
  else
    echo "selftest: FAILED — also_suites gave [$got]" >&2; fail=1
  fi
  for case in "compiler/rustc_codegen_trust_cg/src/trust_ir_frontend.rs:yes" \
    "crates/trust-thir-lower/src/instance_admission.rs:yes" \
    "crates/trust-cg-bridge/src/verify_output_trust_ir.rs:yes" \
    "crates/trust-types/src/lib.rs:yes" \
    "first-party/trust-ir:yes" "first-party/trust-cg:yes" \
    "tests/run-make/trust-cg-f1-generic-instance/rmake.rs:yes" \
    "tests/run-make/trust-ir-emit/rmake.rs:yes" \
    "tests/run-make/trust-ir-template-instance-equivalence/rmake.rs:yes" \
    "first-party/ty:" "crates/trust-vcgen/src/lib.rs:" \
    "compiler/rustc_metadata/src/lib.rs:" "tests/run-make/other/rmake.rs:" "README.md:"; do
    got="$(printf '%s\n' "${case%%:*}" | run_make_selected)"
    if [ "$got" = "${case##*:}" ]; then
      echo "selftest: run-make selection for ${case%%:*} is [${case##*:}]"
    else
      echo "selftest: FAILED — run_make_selected(${case%%:*}) gave [$got]" >&2; fail=1
    fi
  done

  # The run-make judgement: green only when every expected fixture PASSED.
  judge_case() {  # judge_case <label> <want-rc> <expected> <log text>
    local rc
    printf '%s\n' "$4" > "$tmp/rm.log"
    judge_run_make "$tmp/rm.log" "$3"; rc=$?
    if [ "$rc" -eq "$2" ]; then echo "selftest: run-make judgement: $1"
    else echo "selftest: FAILED — run-make judgement: $1 gave $rc, want $2" >&2; fail=1; fi
  }
  judge_case "all expected fixtures passed is green" 0 17 \
    "test result: ok. 17 passed; 0 failed; 0 ignored; 0 measured; 549 filtered out"
  judge_case "an all-IGNORED run is nothing judged, not green" 2 17 \
    "test result: ok. 0 passed; 0 failed; 17 ignored; 0 measured; 549 filtered out"
  judge_case "a partly ignored run is nothing judged" 2 17 \
    "test result: ok. 4 passed; 0 failed; 13 ignored; 0 measured; 549 filtered out"
  judge_case "fewer passes than fixtures is nothing judged" 2 17 \
    "test result: ok. 16 passed; 0 failed; 0 ignored; 0 measured; 550 filtered out"
  judge_case "a failure is red" 1 17 \
    "test result: FAILED. 16 passed; 1 failed; 0 ignored; 0 measured; 549 filtered out"
  judge_case "no result line is nothing judged" 2 17 "error: build failed"

  if [ "$fail" -ne 0 ]; then echo "selftest: FAILED" >&2; exit 1; fi
  echo "selftest: PASS"
  exit 0
fi

PRINT_ONLY=0
if [ "${1:-}" = "--print" ]; then PRINT_ONLY=1; shift; fi
BASE="${1:-origin/main}"
[ "$#" -gt 0 ] && shift
# ADDITIVE SELECTION (2026-10-14, scripts/land_gate.py). `--also "<paths>"` adds
# bootstrap paths (compiler/<crate>, crates/<rustc_private crate>) to what the
# diff selects: the landing gate passes every crate the change REACHES through
# the dependency graph, where this lane's own rule takes only the crates a
# change TOUCHES. `--run-make` adds the trust-cg run-make fixtures. Both only
# add: a suite the diff selects is never dropped, and every added path goes
# through the same filter (a crate with no #[test] that is not a ratchet
# crate is not run) and the same judgement.
ALSO=""
FORCE_RUN_MAKE=""
while [ "$#" -gt 0 ]; do
  case "$1" in
    --also) ALSO="${2:-}"; shift 2 || shift ;;
    --run-make) FORCE_RUN_MAKE=yes; shift ;;
    *) echo "REFUSE: unknown argument '$1'" >&2; exit 2 ;;
  esac
done

if ! git rev-parse --verify --quiet "$BASE" >/dev/null; then
  # A base we cannot resolve is not a licence to skip, and there is no honest
  # subset to fall back on: every suite would be a whole-compiler run.
  echo "REFUSE: cannot resolve base ref '$BASE' — nothing was judged." >&2
  exit 2
fi
changed="$(git diff --name-only "$BASE"...HEAD 2>/dev/null | sed '/^$/d')"
selected="$(printf '%s\n' "$changed" | sed '/^$/d' | select_suites)"
if [ -n "$ALSO" ]; then
  # Each added path is spelled as a file under it, so select_suites applies its
  # own rules (has a #[test], ratchet crates, rustc_private crates) unchanged.
  # shellcheck disable=SC2086 # the list is word-split on purpose
  added="$(also_suites $ALSO)"
  selected="$(printf '%s\n%s\n' "$selected" "$added" | sed '/^$/d' | sort -u)"
fi
run_make="$(printf '%s\n' "$changed" | sed '/^$/d' | run_make_selected)"
[ -n "$FORCE_RUN_MAKE" ] && run_make=yes

if [ -z "$selected" ] && [ -z "$run_make" ]; then
  echo "SKIPPED: no compiler crate with unit tests and no rustc_private crate changed"
  echo "         against $BASE ($(printf '%s\n' "$changed" | sed '/^$/d' | wc -l | tr -d ' ') file(s) changed)."
  echo "WARN: compiler-unit-tests judged nothing against $BASE (out of scope, not a pass)."
  exit 0
fi
echo "in scope against $BASE:"
printf '  %s\n' $selected
[ -n "$run_make" ] && echo "  run-make at stage 1: $TRUST_CG_RUN_MAKE"
[ "$PRINT_ONLY" -eq 1 ] && exit 0

# bootstrap reads its parallelism from `-j`/bootstrap.toml, never from
# CARGO_BUILD_JOBS, so a caller's job cap would silently not apply to the one
# step that builds the compiler. Map it.
XPY_JOBS=()
[ -n "${CARGO_BUILD_JOBS:-}" ] && XPY_JOBS=(-j "$CARGO_BUILD_JOBS")

status=0
suites="$(printf '%s\n' $selected | grep -vx -e "$RATCHET_CRATE" -e "$TRUST_CG_CRATE" || true)"
if [ -n "$suites" ]; then
  log="$(mktemp -t trust-compiler-unit-tests.XXXXXX)"
  trap 'rm -f "$log"' EXIT
  # shellcheck disable=SC2086 # the list is word-split on purpose
  if list_has_prefix crates/ $suites; then
    # The rustc_private suites compile fixtures with a LOCAL Trust sysroot
    # (build/<host>/stage1: bin/trustc plus host core/std from this very
    # compiler) and refuse without one; `x.py test` builds only the compiler
    # crates. Measured 2026-09-25: without it, 99 of trust-mir-extract's 590
    # tests fail on that refusal, which would read as a red change.
    echo "running: x.py build --stage 1 library (the rustc_private suites need its sysroot)"
    python3 x.py build --stage 1 ${XPY_JOBS[@]+"${XPY_JOBS[@]}"} library 2>&1 | tee "$log"
    rc=${PIPESTATUS[0]}
    if [ "$rc" -ne 0 ]; then
      echo
      echo "REFUSE: the stage-1 sysroot build failed (x.py exit $rc) — NO test ran."
      exit 2
    fi
  fi
  # TRUST_SKIP_PREFLIGHT is deliberately NOT set (see check_compiler_targets_build.sh).
  # shellcheck disable=SC2086 # the list is word-split on purpose
  run_compiler_suites $suites 2>&1 | tee "$log"
  rc=${PIPESTATUS[0]}
  if grep -q "preflight found blocking problems" "$log"; then
    echo
    echo "REFUSE: the preflight refused to start a build; NO test ran. Clear the"
    echo "        blocker and re-run — this says nothing about the change."
    exit 2
  fi
  if grep -q "require a local Trust sysroot\|set TRUST_TEST_SYSROOT to the Trust sysroot" "$log"; then
    echo
    echo "REFUSE: a rustc_private suite found no local Trust sysroot matching this"
    echo "        compiler, so its fixture tests refused to run — nothing was judged."
    exit 2
  fi
  results="$(grep -c "^test result:" "$log" || true)"
  if [ "$results" -eq 0 ]; then
    # The vacuous-zero trap: a build that died before any suite ran prints no
    # failing test, which reads exactly like a clean run.
    echo
    echo "REFUSE: x.py exited $rc and no suite reached a test result — nothing was judged."
    exit 2
  fi
  if [ "$rc" -ne 0 ]; then
    echo
    echo "FAIL: a selected compiler unit-test suite is red (x.py exit $rc)."
    grep -E "^test result:|^failures:|^    [A-Za-z0-9_:]+$|targets? failed|^    \`" "$log" | head -60
    status=1
  else
    echo "PASS: $results suite result(s), all green"
  fi
fi
# fold_status <rc> — a red (1) outranks nothing-judged (2), which outranks green.
fold_status() {
  if [ "$1" -eq 2 ]; then
    [ "$status" -eq 0 ] && status=2
  elif [ "$1" -ne 0 ]; then
    status=1
  fi
}
# shellcheck disable=SC2086 # the list is word-split on purpose
if list_has "$RATCHET_CRATE" $selected; then
  echo "delegating $RATCHET_CRATE to its known-red ratchet"
  bash scripts/check_trust_verify_suite_ratchet.sh
  fold_status $?
fi
# shellcheck disable=SC2086 # the list is word-split on purpose
if list_has "$TRUST_CG_CRATE" $selected; then
  echo "delegating $TRUST_CG_CRATE to the known-red ratchet ($TRUST_CG_BASELINE)"
  RATCHET_SUITE="$TRUST_CG_CRATE" RATCHET_BASELINE="$TRUST_CG_BASELINE" \
    bash scripts/check_trust_verify_suite_ratchet.sh
  fold_status $?
fi
if [ -n "$run_make" ]; then
  # The fixtures build and run programs with the stage-1 compiler and its std.
  rm_log="$(mktemp -t trust-cg-run-make.XXXXXX)"
  RM_TARGET=()
  host="$(host_triple)"
  [ -n "$host" ] && RM_TARGET=(--target "$host")
  echo "running: x.py test --stage 1 ${RM_TARGET[*]:-} --force-rerun --no-fail-fast $TRUST_CG_RUN_MAKE"
  # shellcheck disable=SC2086 # the globs are the fixture list
  python3 x.py test --stage 1 ${XPY_JOBS[@]+"${XPY_JOBS[@]}"} ${RM_TARGET[@]+"${RM_TARGET[@]}"} \
    --force-rerun --no-fail-fast $TRUST_CG_RUN_MAKE 2>&1 | tee "$rm_log"
  rc=${PIPESTATUS[0]}
  # shellcheck disable=SC2086 # the globs are the fixture list
  expected="$(ls -d $TRUST_CG_RUN_MAKE 2>/dev/null | wc -l | tr -d ' ')"
  judge_run_make "$rm_log" "$expected"; judged=$?
  if [ "$judged" -eq 1 ] || { [ "$judged" -eq 0 ] && [ "$rc" -ne 0 ]; }; then
    echo "FAIL: a trust-cg run-make fixture is red (x.py exit $rc)."
    grep -E "^test result:|^    \[run-make\] " "$rm_log" | head -40
    fold_status 1
  elif [ "$judged" -eq 2 ]; then
    echo "REFUSE: the trust-cg run-make fixtures did not all PASS (x.py exit $rc):"
    grep -E "^test result:" "$rm_log" | head -5
    echo "        $expected fixture(s) expected to pass; an ignored or missing fixture"
    echo "        (e.g. //@ only-aarch64 on another host) means D17's differential and the"
    echo "        residual-citing rows were not judged here — nothing was judged."
    fold_status 2
  else
    echo "PASS: all $expected trust-cg run-make fixtures passed"
  fi
  rm -f "$rm_log"
fi
exit "$status"
