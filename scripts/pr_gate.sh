#!/usr/bin/env bash
# Trust lightweight PR gate (no stage2 build required).
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# This is the COMMITTABLE, runnable equivalent of .github/workflows/trust-gate.yml
# (which cannot be pushed without a `workflow`-scoped token). It runs the cheap,
# no-stage2 checkers that catch the drift classes which silently broke `./x.py
# build` and the soundness gates: the toolchain-rebrand / removed-`-Z`-flag
# coherence tripwire, and the test-parity ledger expirations.
#
# Use it three ways:
#   * by hand:        bash scripts/pr_gate.sh
#   * as a hook:      bash scripts/install-git-hooks.sh, which points
#                     core.hooksPath at the tracked scripts/hooks/ and makes
#                     this the first of the pre-push lanes
#   * in CI:          activate .github/workflows-pending/*.yml with a
#                     `workflow`-scoped token (they run exactly these steps
#                     plus a documented skip note for the stage2-only gates).
#
# Deliberately SCOPED to no-stage2 work so it stays fast and always-runnable.
# The heavier gates (scripts/check_all.sh, libstd verification, the upstream
# parity scorecard) need a built stage2 trustc and belong to a post-build job.
#
# Exit 0 = clean; non-zero = a drift / expired-ledger problem (do not push).
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

# Prefer a Python 3.11+ (stdlib tomllib for the ledger TOML); fall back to python3.
PYTHON_BIN=""
for c in python3.14 python3.13 python3.12 python3.11 python3 python; do
  if command -v "$c" >/dev/null 2>&1; then PYTHON_BIN="$c"; break; fi
done
if [ -z "$PYTHON_BIN" ]; then
  echo "pr-gate: no python3 found on PATH" >&2
  exit 2
fi

FAILED=0
step() {
  local title="$1"; shift
  echo ""
  echo "=== $title ==="
  if "$@"; then
    echo "PASS: $title"
  else
    echo "FAIL: $title"
    FAILED=1
  fi
}

# 1. Toolchain coherence: stage0 bin surface == bootstrap authority, and every
#    `-Z trust-*` flag in scripts/ is still accepted by trustc. Catches the
#    rebrand / removed-flag drift that neutered the build + the soundness gates.
step "Toolchain coherence (stage0 bins + -Z flags vs trustc)" \
  "$PYTHON_BIN" scripts/check_toolchain_coherence.py

# 2. Stage0 cadence: the seed must be a PREVIOUS Trust release, never a newer
# one. Trust versions its own toolchain, so there is no N-1 window and no
# staircase escape hatch — an older seed is simply valid.
step "Stage0 seed freshness" \
  "$PYTHON_BIN" scripts/check_seed_freshness.py

# 3. Test-parity ledger: no expired entries / active entries missing expires_on.
#    Drop-in-by-construction depends on this ledger staying live.
if [ -f scripts/check_ledger_expirations.py ]; then
  step "Test-parity ledger expirations (warn window 14d)" \
    "$PYTHON_BIN" scripts/check_ledger_expirations.py --warn-days 14
else
  echo ""
  echo "=== Test-parity ledger expirations ==="
  echo "SKIP: scripts/check_ledger_expirations.py not present"
fi

echo ""
echo "Note: stage2-dependent gates (scripts/check_all.sh, libstd verification,"
echo "the upstream parity scorecard) are intentionally NOT run here — they need a"
echo "built stage2 trustc and belong to a heavier post-build job."

echo ""
if [ "$FAILED" -eq 0 ]; then
  echo "PR GATE: GREEN — no toolchain drift, no expired ledger entries."
  exit 0
else
  echo "PR GATE: RED — see failures above; do not push until resolved."
  exit 1
fi
