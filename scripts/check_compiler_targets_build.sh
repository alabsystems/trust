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
# actually touches code it could break: `compiler/`, `crates/`, `src/bootstrap/`,
# `targo-trust/`, or a `first-party/` gitlink. A docs- or fixtures-only push
# skips it and says so. Most pushes skip it.
#
# It checks TEST TARGETS too, via the `--tests` fix from #46 — before that,
# `x.py check` compiled only lib targets while claiming in a comment to cover
# tests, which is how the trust_verify test target rotted through six separate
# signature changes.
#
# Usage: check_compiler_targets_build.sh [base-ref]
#   base-ref defaults to `origin/main`. Exits 0 when clean OR when out of scope.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
set -uo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel 2>/dev/null)" || {
  echo "not inside a git worktree" >&2
  exit 2
}
cd "$REPO_ROOT" || exit 2

BASE="${1:-origin/main}"

# A base we cannot resolve is not a licence to skip: fall back to checking.
if git rev-parse --verify --quiet "$BASE" >/dev/null; then
  changed="$(git diff --name-only "$BASE"...HEAD 2>/dev/null)"
  if [ -z "$changed" ]; then
    echo "no changes against $BASE — nothing to check"
    exit 0
  fi
  if ! grep -qE '^(compiler/|crates/|src/bootstrap/|targo-trust/|first-party/)' <<<"$changed"; then
    echo "SKIPPED: no compiler/, crates/, src/bootstrap/, targo-trust/ or first-party/"
    echo "         change against $BASE — this lane cannot be broken by this push."
    echo "         (changed: $(wc -l <<<"$changed") file(s))"
    exit 0
  fi
  echo "in scope: $(grep -cE '^(compiler/|crates/|src/bootstrap/|targo-trust/|first-party/)' <<<"$changed") relevant file(s) changed vs $BASE"
else
  echo "cannot resolve base ref '$BASE' — checking rather than assuming safe"
fi

echo "running: x.py check --stage 1  (~9-11 min; includes test targets)"
# TRUST_SKIP_PREFLIGHT is deliberately NOT set: the preflight catches submodule
# pin drift, which is exactly failure mode #40/#41/#47 and is far cheaper to
# report than a compile error twelve minutes later.
if python3 x.py check --stage 1; then
  echo "compiler and its test targets check clean"
  exit 0
fi
echo
echo "the compiler does not check. Do NOT push this."
echo "If the break is in a first-party sibling's API, fix the sibling at source"
echo "and pin forward — do not delete the caller to make it compile, and do not"
echo "delete an unused parameter without checking whether the code that USED it"
echo "was dropped too (that is #51, and it hid a soundness check)."
exit 1
