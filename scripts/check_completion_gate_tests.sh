#!/usr/bin/env bash
# Trust: the two-language completion gate's own test suite, as one scoped lane.
#
# WHY THIS EXISTS. `scripts/two_language_completion_gate.py` and its eight
# per-gate checkers under `scripts/completion_gates/` are the release verifier for
# the 100% claim (docs/TWO_LANGUAGE_100_PERCENT_GOAL.md). Their controls — the
# fourteen `scripts/tests/completion_gate*_test.py` / `two_language*_test.py`
# modules — ran in NO lane until 2026-09-27, and two things sat on main unseen
# because of it (docs/KNOWN_HAZARDS.md, "The completion gate's refusal of
# adversarial JSON depended on WHICH PYTHON ran it"):
#
#   * two G5 contract tests red on main, recorded only in a commit message;
#   * `completion_gate_malformed_input_test.py`, the deep-JSON control, RED under
#     CPython 3.14 (a 1100-deep array parsed cleanly where 3.9 refused) — the
#     control did its job and nobody ran it.
#
# The one pre-existing aggregate that globs scripts/tests/ (`scripts.tests.suite`
# via scripts/check_script_tests.sh) is fast-profile only, has never been green,
# and until this change ran each file as `python3 scripts/tests/<name>.py`, which
# dies with ModuleNotFoundError for every test that does `from scripts.tests
# import ...`. So this is a separate, narrow, push-profile lane.
#
# SCOPE — why this is not paid on every push. The suite is ~390 tests and takes
# ~4-5 minutes (measured 2026-09-27: 235-326 s under /usr/bin/python3 3.9.6,
# the high end on a loaded machine). It runs
# only when the push changes something the suite exercises: the gate, a checker,
# a suite module, or a tree file those load or execute (the list is IN_SCOPE_RE
# below, each entry read from the source, not guessed). Anything else prints
# SKIPPED and exits 0, the same idiom as scoped.compiler-check. A base that
# cannot be resolved RUNS the suite — failing toward running, never toward
# skipping.
#
# Usage: check_completion_gate_tests.sh [base-ref]
#   With base-ref, scope is `<base-ref>...HEAD`. Without it, scope is the pushed
#   refs in TRUST_PUSHED_REFS (scripts/hooks/pre-push exports them), else
#   `origin/main...HEAD` — see WHAT THIS PUSH CHANGES below. Exits 0 when green
#   OR out of scope.
#   Every out-of-scope exit (an empty diff included) prints a line beginning
#   `SKIPPED: `: the harness grades that SKIP, not PASS, so a run that tested
#   nothing can never advance this row's `last_green`.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
set -uo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel 2>/dev/null)" || {
  echo "not inside a git worktree" >&2
  exit 2
}
cd "$REPO_ROOT" || exit 2

# The suite, as a fixed list. A glob here would silently pick up (or drop) a
# module on a rename; the count is asserted below so a vanished module is loud.
MODULES=(
  completion_gate_malformed_input_test
  completion_gates_g1_test
  completion_gates_g2_test
  completion_gates_g3_test
  completion_gates_g4_test
  completion_gates_g5_g7_test
  completion_gates_g6_test
  completion_gates_g7_failclosed_test
  completion_gates_g8_test
  two_language_completion_gate_test
  two_language_producer_ratchets_test
  two_language_program_inventory_test
  two_language_program_refusal_test
  two_language_subject_index_test
)

# What the suite exercises, read from the checkers and the fourteen modules
# (2026-09-27; the G3 producer rows 2026-09-29). Paths only; each alternative names where it is loaded:
#   scripts/completion_gates/, scripts/two_language_completion_gate.py — the subject
#   scripts/tests/{completion_gate*,two_language*}_test.py — the suite itself
#   scripts/__init__.py — the package `-m unittest scripts.tests.<m>` imports through
#   scripts/check_completion_gate_tests.sh — this lane
#   scripts/trust_ir_producer_scorecard.py, scripts/rust_instance_census.py —
#       G3's scorecard replay (check_g3_producer_totality.py:565; the scorecard
#       loads the census by file path), copied by completion_gates_g3_test.py:302
#   scripts/two_language_producer_ratchets.py — loaded by
#       two_language_producer_ratchets_test.py:38
#   scripts/check_two_language_program_inventory.py — two_language_program_inventory_test.py:13
#   scripts/two_language_subject_index.py (the G3 producer; it loads
#       scripts/lean_island_census.py by file path) — two_language_subject_index_test.py,
#       which also reads scripts/tests/fixtures/lean-island-census/, loads
#       scripts/check_fixture_span_paths.py, and imports the census fixtures of
#       scripts/tests/trust_ir_producer_{census,scorecard_completion}_test.py
#   tests/e2e_two_language_programs.sh, tests/two-language-programs/ — read by the
#       inventory, refusal and producer-ratchet tests (ir-audit report, ir-* pins)
#   tests/upstream-rust/{baseline,test-exceptions,exceptions}.toml,
#   release/trust-version.toml — completion_gates_g1_test.py:686-695 parses the
#       REAL pinned ledgers through G1's TOML subset
#   first-party/clean — completion_gates_g2_test.py:1245 reads Clean's ledgers at
#       the gitlink from git objects
#   first-party/trust-ir, first-party/trust-cg — with clean, the gitlinks the
#       producer-ratchet mutation test builds its judges from
IN_SCOPE_RE='^(scripts/completion_gates/'
IN_SCOPE_RE+='|scripts/two_language_completion_gate\.py$'
IN_SCOPE_RE+='|scripts/tests/completion_gate[^/]*_test\.py$'
IN_SCOPE_RE+='|scripts/tests/two_language[^/]*_test\.py$'
IN_SCOPE_RE+='|scripts/__init__\.py$'
IN_SCOPE_RE+='|scripts/check_completion_gate_tests\.sh$'
IN_SCOPE_RE+='|scripts/trust_ir_producer_scorecard\.py$'
IN_SCOPE_RE+='|scripts/rust_instance_census\.py$'
IN_SCOPE_RE+='|scripts/two_language_producer_ratchets\.py$'
IN_SCOPE_RE+='|scripts/check_two_language_program_inventory\.py$'
IN_SCOPE_RE+='|scripts/two_language_subject_index\.py$'
IN_SCOPE_RE+='|scripts/lean_island_census\.py$'
IN_SCOPE_RE+='|scripts/check_fixture_span_paths\.py$'
IN_SCOPE_RE+='|scripts/tests/fixtures/lean-island-census/'
IN_SCOPE_RE+='|scripts/tests/trust_ir_producer_(census|scorecard_completion)_test\.py$'
IN_SCOPE_RE+='|tests/e2e_two_language_programs\.sh$'
IN_SCOPE_RE+='|tests/two-language-programs/'
IN_SCOPE_RE+='|tests/upstream-rust/(baseline|test-exceptions|exceptions)\.toml$'
IN_SCOPE_RE+='|release/trust-version\.toml$'
IN_SCOPE_RE+='|first-party/(clean|trust-ir|trust-cg)$'
IN_SCOPE_RE+=')'

# WHAT THIS PUSH CHANGES — the subject the scope is judged on. Three readings,
# and the `SUBJECT:` line says which one ran:
#
#   * a base-ref argument: `<base-ref>...HEAD`, as it always meant;
#   * otherwise, under scripts/hooks/pre-push, TRUST_PUSHED_REFS (one
#     "<local-ref> <local-sha> <remote-ref> <remote-sha>" line per update): the
#     UNION over every pushed update of the TREE diff `<remote-sha>..<local-sha>`
#     (for `git diff`, `A..B` is `A B`: the remote tip's tree against the pushed
#     tree); a new branch (all-zero remote-sha) contributes
#     `origin/main...<local-sha>`, and a deletion (all-zero local-sha) nothing;
#   * otherwise (unset, empty, or naming only deletions or lines that are not
#     four fields): `origin/main...HEAD`.
#
# TWO DOTS FOR AN UPDATE, three for a new branch. From f7a15dc698 until this
# fix (both 2026-09-27) an update was diffed `<remote-sha>...<local-sha>`, the
# changes since the MERGE BASE. For a fast-forward the merge base is the remote tip and
# the two agree; for a force push they do not: a push that DROPS the remote's
# in-scope commits and adds one docs commit was judged on the docs commit
# alone and SKIPPED, although the tree it installs differs from the remote's
# in scope. The tree diff also lists what the push removes. A new branch has no
# remote tree to compare with, so it keeps `origin/main...<local-sha>`, what the
# branch adds since it forked from history origin/main already carries. The
# two-dot tree diff against origin/main is NOT strictly safer there: a change
# the branch shares with main (a cherry-pick) drops out of it while `...` lists
# it, and it would charge a docs branch cut from an older main with every
# in-scope change main landed since, none of which this push carries.
# (scripts/check_crates_tests_scoped.py's resolve_ranges reads updates the
# same way; until later on 2026-09-27 it read every update three-dot.)
#
# Until 2026-09-27 (the day it was added) this lane read `origin/main...HEAD`
# whatever was pushed, so `git push origin topic` from a checkout whose HEAD
# touched no gate file skipped the suite however much of the gate `topic`
# changed.
#
# ONLY THE SCOPE DECISION reads the pushed refs. The suite below still runs on
# THIS WORKTREE, which is the pushed tip in the ordinary case: the hook runs from
# the worktree being pushed, and `git push` pushes its checked-out branch. A push
# of some OTHER ref is scoped by that ref's changes but tested against this
# worktree, not that ref's tree — a gap this lane does not close.
#
# A range whose diff cannot be computed (an unresolvable base, an object this
# clone lacks — a force push over a remote tip never fetched here — no merge
# base) is not a licence to skip: the suite runs.
#
# --no-renames (and diff.renames=false against a config that says otherwise):
# with rename detection on, which is git's default, a moved file is listed only
# under its NEW path. `git mv scripts/completion_gates/check_g1_rust_input.py
# scripts/g1_moved.py` would then show only an out-of-scope path and the lane
# would print SKIPPED while the suite is broken (reproduced 2026-09-27). Without
# rename detection the deletion of the old path is listed too, so a move OUT of
# scope is in scope.
#
# -z: without it git C-quotes a path holding non-ASCII bytes, `"` or `\`
# ("tests/two-language-programs/\303\251.rs", leading quote included), which the
# anchored patterns below would never match (reproduced 2026-09-27).
#
# --ignore-submodules=none: the first-party/{clean,trust-ir,trust-cg} gitlinks
# are in scope, and a plain `git diff` drops a moved pin when
# diff.ignoreSubmodules or a .gitmodules `ignore = all` says so. Git reads .gitmodules from the WORKTREE even for a
# commit-to-commit diff, so a push that adds that line and bumps a pin printed
# SKIPPED (reproduced 2026-09-27). Only the flag overrides both settings;
# `-c diff.ignoreSubmodules=none` does not override .gitmodules.
#
# scripts/check_compiler_targets_build.sh computes its subject with the same
# block; scripts/tests/scoped_lane_push_scope_test.py drives BOTH lanes through
# every reading above, so the two copies cannot drift apart unseen.
ranges=()
if [ -n "${1:-}" ]; then
  ranges=("$1...HEAD")
  against="$1"
  subject="$1...HEAD (explicit base argument; TRUST_PUSHED_REFS not read)"
else
  while read -r _local_ref local_sha _remote_ref remote_sha _rest; do
    [ -n "${remote_sha:-}" ] || continue                  # not a four-field ref line
    case "$local_sha" in *[!0]*) ;; *) continue ;; esac   # a deletion pushes nothing
    case "$remote_sha" in
      *[!0]*) ranges+=("$remote_sha..$local_sha") ;;      # an update: remote tree vs pushed tree
      *) ranges+=("origin/main...$local_sha") ;;          # a new branch: what it adds since its fork
    esac
  done <<<"${TRUST_PUSHED_REFS:-}"
  if [ "${#ranges[@]}" -gt 0 ]; then
    against="the pushed refs"
    subject="the pushed refs (TRUST_PUSHED_REFS, ${#ranges[@]} update(s)); an update is the tree diff <remote>..<local>, a new branch origin/main...<local>: ${ranges[*]}"
  else
    ranges=("origin/main...HEAD")
    against="origin/main"
    if [ -n "${TRUST_PUSHED_REFS:-}" ]; then
      subject="origin/main...HEAD (TRUST_PUSHED_REFS names no update to diff, only deletions or malformed lines)"
    else
      subject="origin/main...HEAD (no push in flight; TRUST_PUSHED_REFS unset or empty)"
    fi
  fi
fi
echo "SUBJECT: $subject"

changed=""
undiffable=""
for range in "${ranges[@]}"; do
  if part="$(set -o pipefail; git -c diff.renames=false diff --no-renames --ignore-submodules=none --name-only -z "$range" 2>/dev/null | tr '\0' '\n')"; then
    [ -z "$part" ] || changed+="$part"$'\n'
  else
    undiffable="$range"
    break
  fi
done
changed="$(printf '%s' "$changed" | LC_ALL=C sort -u)"
if [ -n "$undiffable" ]; then
  echo "cannot compute the diff $undiffable — running rather than assuming safe"
elif [ -z "$changed" ]; then
  echo "SKIPPED: no changes against $against — nothing to check"
  exit 0
elif ! grep -qE "$IN_SCOPE_RE" <<<"$changed"; then
  echo "SKIPPED: no completion-gate checker, gate, suite module, or file the suite"
  echo "         loads changed against $against — this lane cannot be broken by this push."
  echo "         (changed: $(wc -l <<<"$changed" | tr -d ' ') file(s))"
  exit 0
else
  echo "in scope: $(grep -cE "$IN_SCOPE_RE" <<<"$changed") relevant file(s) changed vs $against:"
  grep -E "$IN_SCOPE_RE" <<<"$changed" | head -20 | sed 's/^/  /'
fi

# The gate's reference interpreter is /usr/bin/python3 (the one the release row
# and the 2026-09-27 measurement used); fall back to PATH only when it is absent.
if [ -x /usr/bin/python3 ]; then
  PYTHON_BIN=/usr/bin/python3
elif command -v python3 >/dev/null 2>&1; then
  PYTHON_BIN="$(command -v python3)"
else
  echo "FAIL: no python3 — the completion-gate suite cannot run" >&2
  exit 2
fi

# PREREQUISITES ARE A FAILURE, NOT A SKIP. In scope means this push changes the
# release verifier or what it reads; a lane that then prints SKIPPED (exit 0)
# because the machine is missing a tool would be exactly a lane that passes
# without running, which is how the G5 reds went unseen. And the suite would not
# say so on its own: completion_gates_g8_test.py wraps its signing tests in
# `skipUnless(/usr/bin/ssh-keygen)`, so a missing ssh-keygen turns into quiet
# skips inside an "OK", while a git older than the gate's MIN_GIT_VERSION (2.41,
# for --attr-source) makes the runner refuse every fixture and the tests fail
# for a reason that reads as a gate defect. Name the real cause instead. A
# machine that genuinely cannot host this lane quarantines it with an owned,
# expiring row in tests/trust-comprehensive/divergences.toml — visibly.
prereq_fail=0
git_version="$(git --version 2>/dev/null)"
if [[ "$git_version" =~ ^git\ version\ ([0-9]+)\.([0-9]+) ]]; then
  git_major="${BASH_REMATCH[1]}"
  git_minor="${BASH_REMATCH[2]}"
  if [ "$git_major" -lt 2 ] || { [ "$git_major" -eq 2 ] && [ "$git_minor" -lt 41 ]; }; then
    echo "FAIL: $git_version is older than 2.41, the completion gate's MIN_GIT_VERSION" >&2
    echo "      (scripts/two_language_completion_gate.py: --attr-source). The suite" >&2
    echo "      would fail on the runner's refusal, not on a defect. Install git >= 2.41." >&2
    prereq_fail=1
  fi
else
  echo "FAIL: cannot read the git version ('$git_version')" >&2
  prereq_fail=1
fi
# The gate and the suite are written for CPython >= 3.9 (`dict[str, str]`
# annotations evaluated at import, str.removeprefix in completion_gates_g2_test).
# An older interpreter fails at import with a TypeError that names neither.
if ! "$PYTHON_BIN" -c 'import sys; sys.exit(0 if sys.version_info >= (3, 9) else 1)' 2>/dev/null; then
  echo "FAIL: $PYTHON_BIN ($("$PYTHON_BIN" --version 2>&1)) is older than 3.9, which the" >&2
  echo "      completion gate and its suite require. Install python3 >= 3.9." >&2
  prereq_fail=1
fi
if [ ! -x /usr/bin/ssh-keygen ]; then
  echo "FAIL: /usr/bin/ssh-keygen is missing. The gate verifies the owner signature" >&2
  echo "      with it (SSH_KEYGEN in scripts/two_language_completion_gate.py) and" >&2
  echo "      completion_gates_g8_test.py would SKIP its signing tests inside a green run." >&2
  prereq_fail=1
fi
# A stale Clean submodule. completion_gates_g2_test's real-ledger test skips when
# the Clean module directory is absent, but when it exists WITHOUT the pinned
# commit it errors with "cannot read pinned Clean blob". That is the ordinary
# state after a `git pull` that moved the pin in this repo, where
# fetch.recurseSubmodules=no, and it is not a gate defect. Name the real cause
# and the sanctioned fix instead (CLAUDE.md, "Before you debug anything").
#
# WHICH store. Git keeps a LINKED worktree's submodule objects under that
# worktree's own git dir (`git rev-parse --git-path modules/first-party/clean`,
# e.g. .git/worktrees/<wt>/modules/first-party/clean), not under the common dir;
# the common dir's store belongs to the main checkout, which scripts/submodule_sync.sh
# run in the linked worktree never touches. Until 2026-09-28 this check (and
# completion_gates_g2_test) read ONLY the common store, so a push from a synced
# linked worktree went red whenever the main checkout lagged the pin — and the
# advice below could not fix it. A sparse worktree that never initialised the
# submodule has only the common store. Objects are content-addressed, so every
# store holding the pinned commit reads the same bytes: the suite reads the
# first one that does (own store first), and the lane is red only when a store
# exists and none holds the pin. completion_gates_g2_test resolves the same way.
clean_common="$(git rev-parse --git-common-dir 2>/dev/null)"
case "$clean_common" in /*) ;; *) clean_common="$REPO_ROOT/$clean_common" ;; esac
clean_own="$(git rev-parse --git-path modules/first-party/clean 2>/dev/null)"
case "$clean_own" in /*|'') ;; *) clean_own="$REPO_ROOT/$clean_own" ;; esac
clean_pin="$(git ls-tree HEAD first-party/clean 2>/dev/null | awk '{print $3}')"
clean_stores=()
for candidate in "$clean_own" "$clean_common/modules/first-party/clean"; do
  [ -n "$candidate" ] && [ -d "$candidate" ] && clean_stores+=("$candidate")
done
if [ -n "$clean_pin" ] && [ "${#clean_stores[@]}" -gt 0 ]; then
  clean_has_pin=0
  for candidate in "${clean_stores[@]}"; do
    if git --git-dir="$candidate" cat-file -e "$clean_pin^{commit}" 2>/dev/null; then
      clean_has_pin=1
      break
    fi
  done
  if [ "$clean_has_pin" -eq 0 ]; then
    echo "FAIL: the Clean submodule objects lack the pinned commit $clean_pin" >&2
    echo "      (searched: ${clean_stores[*]}). completion_gates_g2_test reads Clean's" >&2
    echo "      real ledgers at that pin. Run scripts/submodule_sync.sh (never a blanket" >&2
    echo "      \`git submodule update\`), then push again." >&2
    prereq_fail=1
  fi
fi
if [ "$prereq_fail" -ne 0 ]; then
  echo "completion-gate tests NOT RUN — this is a red, not a pass." >&2
  exit 1
fi

for module in "${MODULES[@]}"; do
  if [ ! -f "scripts/tests/$module.py" ]; then
    echo "FAIL: suite module scripts/tests/$module.py is missing — update MODULES" >&2
    exit 1
  fi
done
# The reverse direction: a new completion-gate test module not listed above
# would run nowhere. Refuse rather than let it sit unrun.
for path in scripts/tests/completion_gate*_test.py scripts/tests/two_language*_test.py; do
  [ -f "$path" ] || continue
  name="$(basename "$path" .py)"
  case " ${MODULES[*]} " in
    *" $name "*) ;;
    *) echo "FAIL: $path is a completion-gate test module this lane does not run — add it to MODULES" >&2
       exit 1 ;;
  esac
done

echo "interpreter: $PYTHON_BIN ($("$PYTHON_BIN" --version 2>&1))"
echo "git: $git_version"
echo "running: ${#MODULES[@]} modules in one unittest invocation (~4-5 min)"

targets=()
for module in "${MODULES[@]}"; do targets+=("scripts.tests.$module"); done

LOG="$(mktemp -t trust-completion-gate-tests.XXXXXX)"
CFG_HOME="$(mktemp -d -t trust-completion-gate-home.XXXXXX)"
mkdir -p "$CFG_HOME/xdg"
trap 'rm -rf "$LOG" "$CFG_HOME"' EXIT
# The neutral HOME still carries an inert identity: a fixture repo without its
# own (a clone inherits no local config) would otherwise need hostname
# auto-detection, which fails on a host whose name has no domain -- the lane
# went red on all 37 such commits under user.useConfigOnly (measured
# 2026-09-27). Each fixture's own local identity still takes precedence.
printf '[user]\n\tname = completion-gate-lane\n\temail = completion-gate-lane@example.invalid\n' \
    >"$CFG_HOME/.gitconfig"
# A NEUTRAL GIT CONFIG. Three modules (g1, g8, completion_gate)
# build fixture repos with a plain `git commit`, so the operator's global and
# system config reach them. A developer with `commit.gpgsign=true` whose signer
# cannot run under the hook turns this lane red with ~170 unexplained "git commit
# returned non-zero exit status 128" errors, and one whose signer works is asked
# to sign hundreds of fixture commits with stdin at /dev/null (measured
# 2026-09-27). The pre-push hook's `--local-env-vars` scrub does not remove
# GIT_CONFIG_GLOBAL, GIT_CONFIG_SYSTEM or HOME. So the suite gets an empty HOME
# and XDG_CONFIG_HOME, no system config, and no GIT_CONFIG_GLOBAL/SYSTEM
# override. It must NOT be GIT_CONFIG_GLOBAL=/dev/null:
# two_language_completion_gate_test's
# test_operator_global_and_xdg_git_config_cannot_hide_untracked_files plants its
# hostile operator config through HOME, and an ambient GIT_CONFIG_GLOBAL
# overrides that and fails the test (measured). The repo's own local config
# still applies, which is what the tests read from ROOT.
#
# -B: no bytecode written into the tree. </dev/null: a test must not read the
# hook's stdin. Streamed through tee so a 4-minute run shows progress, captured
# so the summary can be checked for a zero-test run.
env -u GIT_CONFIG_GLOBAL -u GIT_CONFIG_SYSTEM \
    HOME="$CFG_HOME" XDG_CONFIG_HOME="$CFG_HOME/xdg" GIT_CONFIG_NOSYSTEM=1 \
    "$PYTHON_BIN" -B -m unittest "${targets[@]}" </dev/null 2>&1 | tee "$LOG"
rc=${PIPESTATUS[0]}

ran="$(sed -nE 's/^Ran ([0-9]+) tests? in .*/\1/p' "$LOG" | tail -1)"
if [ -z "$ran" ] || [ "$ran" -eq 0 ]; then
  echo "FAIL: the completion-gate suite ran ZERO tests — an empty run is not a pass" >&2
  exit 1
fi
if [ "$rc" -ne 0 ]; then
  echo "FAIL: completion-gate tests red (unittest exit $rc, $ran tests ran)" >&2
  exit 1
fi
# Report skips: a machine where the mutation test or the case-alias tests skip
# must not look the same as a full run.
skipped="$(sed -nE 's/^OK \(.*skipped=([0-9]+).*\)$/\1/p' "$LOG" | tail -1)"
echo "completion-gate tests: PASS ($ran tests, ${skipped:-0} skipped)"
exit 0
