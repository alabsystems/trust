#!/usr/bin/env bash
# Trust: does the compiler still COMPILE — including its test targets?
#
# WHY THIS EXISTS. `main` was broken three separate times on 2026-08-12/13, each
# by a push that never built the superproject:
#
#   #40/#41  a gitlink naming a sibling commit whose API the superproject calls
#   #47      a pin advance that dropped the k-unroll API `crates/trust-bmc` uses
#   #51      a merge-conflict resolution that left `independent_replay_summary`
#            undefined and a 7-arg call passed 6 — and, worse, left the
#            `retained_obligation` parameter it added USED NOWHERE, so the
#            "fresh replay" the commit promised had a signature and a summary
#            string with no check between them
#
# All three are the same shape: the tree does not compile, and nothing between
# the author and `origin` said so. The existing three pre-push lanes are drift
# and pin checks; none of them compiles a line of the compiler.
#
# #51 is the one that makes this worth a slow lane. A build break is loud the
# moment anyone pulls. A build break that ALSO hides a dropped soundness check
# is not: the obvious repair (delete the unused parameter) compiles in thirty
# seconds and makes the missing binding permanent and invisible.
#
# SCOPE — why this is not simply slow for everyone. `x.py check --stage 1` takes
# ~9-11 minutes, and a gate that slow on EVERY push is one people learn to skip
# with --no-verify, which is worse than no gate. So it runs only when the push
# actually touches something `x.py check` reads: `compiler/`, `crates/`,
# `library/`, `src/tools/`, `vendor/`, the root `Cargo.lock`, `src/bootstrap/`,
# `targo-trust/`, a `first-party/` gitlink, and the other inputs IN_SCOPE_RE lists.
# A docs- or UI-fixture-only push skips it and says so.
#
# It checks TEST TARGETS too, via the `--tests` fix from #46 — before that,
# `x.py check` compiled only lib targets while claiming in a comment to cover
# tests, which is how the trust_verify test target rotted through six separate
# signature changes.
#
# Usage: check_compiler_targets_build.sh [base-ref]
#   With base-ref, scope is `<base-ref>...HEAD`. Without it, scope is the pushed
#   refs in TRUST_PUSHED_REFS (scripts/hooks/pre-push exports them), else
#   `origin/main...HEAD` — see WHAT THIS PUSH CHANGES below. Exits 0 when clean
#   OR when out of scope.
#   Every out-of-scope exit (an empty diff included) prints a line beginning
#   `SKIPPED: `: the harness grades that SKIP, not PASS, so a run that checked
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
# Until 2026-09-27 this lane always read `origin/main...HEAD`, which is not what
# is pushed: `git push origin topic` from a checkout whose HEAD touches only docs
# skipped the lane however much compiler/ code `topic` carried.
#
# ONLY THE SCOPE DECISION reads the pushed refs. `x.py check` below still checks
# THIS WORKTREE, which is the pushed tip in the ordinary case: the hook runs from
# the worktree being pushed, and `git push` pushes its checked-out branch. A push
# of some OTHER ref is scoped by that ref's changes but checked against this
# worktree, not that ref's tree — a gap this lane does not close.
#
# A range whose diff cannot be computed (an unresolvable base, an object this
# clone lacks — a force push over a remote tip never fetched here — no merge
# base) is not a licence to skip: the check runs. Until 2026-09-27 a failing
# diff here produced empty output, which printed "SKIPPED: no changes" —
# fail-open.
#
# --no-renames (and diff.renames=false against a config that says otherwise):
# with rename detection on, which is git's default, a moved file is listed only
# under its NEW path, so `git mv compiler/x.rs docs/x.rs` listed only an
# out-of-scope path and the lane printed SKIPPED. Without rename detection the
# deletion of the old path is listed too, so a move OUT of scope is in scope.
# -z: without it git C-quotes a path holding non-ASCII bytes, `"` or `\`
# ("compiler/\303\251.rs", leading quote included), which the anchored pattern
# below never matches. Both were fixed first in scripts/check_completion_gate_tests.sh
# (3db0e0b0fd).
#
# --ignore-submodules=none: the first-party/ gitlinks are in scope, and a plain
# `git diff` drops a moved pin when diff.ignoreSubmodules or a .gitmodules
# `ignore = all` says so. Git reads .gitmodules from the WORKTREE even for a
# commit-to-commit diff, so a push that adds that line and bumps a pin printed
# SKIPPED (reproduced 2026-09-27). Only the flag overrides both settings;
# `-c diff.ignoreSubmodules=none` does not override .gitmodules.
#
# scripts/check_completion_gate_tests.sh computes its subject with the same
# block; scripts/tests/scoped_lane_push_scope_test.py drives BOTH lanes through
# every reading above, so the two copies cannot drift apart unseen.
#
# WHAT `x.py check --stage 1` READS — the scope is that set, not the directories
# this lane was first written for. Until 2026-09-28 the list was compiler/,
# crates/, src/bootstrap/, targo-trust/ and first-party/ only, so a push touching
# nothing but library/, src/tools/, the root Cargo.lock or vendor/ printed SKIPPED
# although the check compiles every one of them (measured from the check stamps
# and cargo dep-info of a lane run, docs/issues/2026-09-28-scoped-lane-verdict-cache.md
# §"holes"). The check builds and checks std (library/), the default tool steps
# (src/tools/*, and trustdoc from src/librustdoc/), rustc_llvm against the
# vendored LLVM (src/llvm-project/, keyed by bootstrap's LLVM stamp), every
# vendored and locked dependency (vendor/, the root Cargo.toml/Cargo.lock,
# .cargo/), and bootstrap reads its own inputs (src/stage0, src/version,
# src/rust-compat-version, release/trust-version.toml, x.py, tools/preflight.*,
# the native build-tree manager). Two in-tree files outside those are compiled
# in: scripts/frozen-files.txt (trust-thir-lower's build.rs) and
# tests/fixtures/binary_decomp/ (include_str!). Over-inclusion only costs a
# check; a missing prefix is a push this lane waves through unchecked.
IN_SCOPE_RE='^(compiler/|crates/|library/|src/bootstrap/|src/tools/|src/librustdoc/'
IN_SCOPE_RE+='|src/llvm-project/|src/stage0$|src/version$|src/rust-compat-version$'
IN_SCOPE_RE+='|targo-trust/|first-party/|vendor/|\.cargo/|Cargo\.(toml|lock)$'
IN_SCOPE_RE+='|release/trust-version\.toml$|x\.py$|tools/preflight\.|scripts/trust_build_lock\.sh$'
IN_SCOPE_RE+='|scripts/frozen-files\.txt$|tests/fixtures/binary_decomp/)'

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
  echo "cannot compute the diff $undiffable — checking rather than assuming safe"
elif [ -z "$changed" ]; then
  echo "SKIPPED: no changes against $against — nothing to check"
  exit 0
elif ! grep -qE "$IN_SCOPE_RE" <<<"$changed"; then
  echo "SKIPPED: no change against $against to anything x.py check reads (compiler/,"
  echo "         crates/, library/, src/tools/, vendor/, Cargo.lock, first-party/, ... —"
  echo "         IN_SCOPE_RE) — this lane cannot be broken by this push."
  echo "         (changed: $(wc -l <<<"$changed" | tr -d ' ') file(s))"
  exit 0
else
  echo "in scope: $(grep -cE "$IN_SCOPE_RE" <<<"$changed") relevant file(s) changed vs $against"
fi

# Consult the permanent development policy BEFORE the generic src/compiler
# fallback: the supported execution components live under src/. Unknown
# owners/errors retain the preexisting safe full-check fallback.
selector_says_no() {
  local mode="$1" range r_base r_head answer rc
  local -a selector_args
  for range in "${ranges[@]}"; do
    case "$range" in
      *...*) r_base="$(git merge-base "${range%%...*}" "${range##*...}" 2>/dev/null)"; r_head="${range##*...}" ;;
      *..*) r_base="${range%%..*}"; r_head="${range##*..}" ;;
      *) return 1 ;;
    esac
    [ -n "$r_base" ] || return 1
    selector_args=(needs compiler-check)
    if [ "$mode" = development ]; then selector_args+=(--development); else selector_args+=(--verify-graph); fi
    answer="$(python3 scripts/land_gate.py "${selector_args[@]}" --base "$r_base" --head "$r_head" 2>&1)"
    rc=$?
    echo "  $answer"
    [ "$rc" -eq 1 ] || return 1
  done
  return 0
}
if [ -z "$undiffable" ] && [ -f scripts/land_gate.py ]; then
  if selector_says_no development; then
    echo "SKIPPED: no required full compiler-check for these ranges: the selector"
    echo "         names the development policy and its focused checks above."
    echo "         Diagnostic SKIP is not compiler-check PASS; canonical --development run owns fresh focused checks."
    exit 0
  fi
  # Preserve the old normal readset consultation for non-src leaf changes.
  if ! grep -qE '^(compiler|library|src)/' <<<"$changed" && selector_says_no full; then
    echo "SKIPPED: no changed path reaches what x.py check compiles (the full build graph)."
    exit 0
  fi
fi

# x.py reads its job count from -j/bootstrap.toml, not CARGO_BUILD_JOBS.
# A managed lane must explicitly forward its admitted CPU share. Preserve
# ordinary unmanaged invocations, and refuse a lost share before any build.
XPY_JOBS=()
if [ "${BUILD_SLOT_HELD:-}" = 1 ]; then
  admitted_jobs="$(python3 - <<'PY_ADMISSION'
import os, re, sys
raw = os.environ.get("CARGO_BUILD_JOBS", "")
try:
    if not re.fullmatch(r"[0-9]+", raw) or int(raw) < 1:
        raise ValueError
    print(int(raw))
except ValueError:
    sys.stderr.write("compiler-check: BUILD_SLOT_HELD=1 requires positive integer CARGO_BUILD_JOBS; nothing was judged\n")
    sys.exit(2)
PY_ADMISSION
)" || exit 2
  XPY_JOBS=(-j "$admitted_jobs")
fi

echo "running: x.py check --stage 1 ${XPY_JOBS[*]:-} (~9-11 min; includes test targets)"
# TRUST_SKIP_PREFLIGHT is deliberately NOT set: the preflight catches submodule
# pin drift, which is exactly failure mode #40/#41/#47 and is far cheaper to
# report than a compile error twelve minutes later.
# Trust (#60, 2026-08-19): capture as well as stream. `x.py check` exits non-zero
# for two situations that need OPPOSITE responses, and this lane used to report
# both with "the compiler does not check":
#
#   1. a real compile error -- the thing this gate exists to catch;
#   2. the PREFLIGHT REFUSING TO START -- submodule pin drift, or another x.py
#      already running. Nothing was compiled at all.
#
# Measured 2026-08-17/19: three consecutive pushes tripped this lane and NONE was
# a compile error (two pin waves from a concurrent rebase, one parallel build from
# another session). Each cost a read of a ~4000-line log to tell which case it
# was, because the summary line is identical. Streaming through `tee` keeps the
# live progress an 11-minute command needs while letting us classify the failure.
CHECK_LOG=$(mktemp -t trust-compiler-check.XXXXXX)
trap 'rm -f "$CHECK_LOG"' EXIT
set +e
python3 x.py check --stage 1 ${XPY_JOBS[@]+"${XPY_JOBS[@]}"} 2>&1 | tee "$CHECK_LOG"
CHECK_RC=${PIPESTATUS[0]}
set -e
if [ "$CHECK_RC" -eq 0 ]; then
  echo "compiler and its test targets check clean"
  exit 0
fi

if grep -q "preflight found blocking problems" "$CHECK_LOG"; then
  echo
  echo "THE COMPILER WAS NOT CHECKED — the preflight refused to start a build."
  echo "This is NOT a compile error: nothing was compiled, so this says NOTHING"
  echo "about whether your change is sound. Clear the blocker and re-run."
  echo
  echo "the blocking preflight item(s):"
  grep -E "^\s+FAIL " "$CHECK_LOG" | sed 's/^/  /' || true
  echo
  if grep -q "BUILD IS ALREADY RUNNING" "$CHECK_LOG"; then
    echo "  -> another x.py is running (a second one corrupts both). Wait for it;"
    echo "     do not pass TRUST_SKIP_PREFLIGHT to get around it."
  fi
  if grep -qE "submodule update|pin" "$CHECK_LOG"; then
    echo "  -> submodule pin drift. Fetch each submodule FIRST so ancestry is"
    echo "     computable, THEN restore — a restore before the fetch cannot act:"
    echo "       for m in \$(git config -f .gitmodules --get-regexp path | awk '{print \$2}'); do"
    echo "         git -C \"\$m\" fetch --all -q; done"
    echo "       bash scripts/submodule_sync.sh --restore"
  fi
  exit 1
fi

echo
echo "the compiler does not check. Do NOT push this."
echo "If the break is in a first-party sibling's API, fix the sibling at source"
echo "and pin forward — do not delete the caller to make it compile, and do not"
echo "delete an unused parameter without checking whether the code that USED it"
echo "was dropped too (that is #51, and it hid a soundness check)."
exit 1
