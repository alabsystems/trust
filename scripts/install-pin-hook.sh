#!/usr/bin/env bash
# Install the NARROW pin-coherence git hooks (scripts/hooks-pin/) in this clone.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# There are two hook directories in this repo and they are not interchangeable:
#
#   scripts/hooks/      the FULL pre-push gate — every gate-manifest row carrying
#                       the `push` profile (19 lanes/15.7s when measured 2026-08-27 — drifts; `--list push` is authoritative:
#                       drift, supply-chain, freeze, provenance, pin lanes and
#                       their selftests) plus `x.py check --stage 1` (~9-11 min)
#                       on any push touching compiler/ crates/ src/bootstrap/
#                       targo-trust/ first-party/. Installed by
#                       scripts/install-git-hooks.sh. Correct for a machine that
#                       is yours; a large thing to switch on for every other lane
#                       sharing a clone.
#
#   scripts/hooks-pin/  THIS one — a fixed, hand-listed set of pin/provenance
#                       checkers. 0.49s measured for the pin lane. No build, no
#                       x.py, and it does NOT read the gate manifest.
#
# `core.hooksPath` names ONE directory, so these two are mutually exclusive by
# construction. This script refuses to take over any other configuration rather
# than silently downgrading someone's full gate.
#
# Usage:
#   bash scripts/install-pin-hook.sh              # install (idempotent)
#   bash scripts/install-pin-hook.sh --status     # report what is installed
#   bash scripts/install-pin-hook.sh --uninstall  # stop using these hooks
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

HOOKS_DIR="scripts/hooks-pin"
FULL_DIR="scripts/hooks"

configured() { git config --local --get core.hooksPath 2>/dev/null || true; }

status() {
  local current
  current="$(configured)"
  case "$current" in
    "$HOOKS_DIR")
      echo "Trust pin hooks: INSTALLED (core.hooksPath = $HOOKS_DIR)"
      echo "  pre-push runs EIGHT checkers (~4s): pin coherence, revert rationale,"
      echo "  frozen files, measurement provenance, bridge pin, IR cohort,"
      echo "  submodule remote reachability, and cfg(test) caller skew — the last"
      echo "  of which is the only one about SOURCE. See scripts/hooks-pin/pre-push."
      echo "  post-merge / post-rewrite / post-checkout are advisory drift notices."
      return 0
      ;;
    "$FULL_DIR")
      echo "Trust pin hooks: NOT installed — the FULL gate ($FULL_DIR) is active."
      echo "  That gate already includes pin coherence. Nothing to do."
      return 1
      ;;
    "")
      echo "Trust pin hooks: NOT installed (core.hooksPath = <unset>)"
      echo "  This clone is UNGATED: no pin check runs on push."
      echo "  run: bash scripts/install-pin-hook.sh"
      return 1
      ;;
    *)
      echo "Trust pin hooks: NOT installed (core.hooksPath = $current)"
      return 1
      ;;
  esac
}

case "${1:-install}" in
  --status|status|--check) status; exit $? ;;
  --uninstall|uninstall)
    if [ "$(configured)" = "$HOOKS_DIR" ]; then
      git config --local --unset core.hooksPath
      echo "Trust pin hooks: uninstalled. This clone is now ungated on push."
    else
      echo "Trust pin hooks: nothing to uninstall (core.hooksPath is not ours)."
    fi
    exit 0
    ;;
  ""|install|--install) : ;;
  *) echo "usage: $0 [--status|--uninstall]" >&2; exit 2 ;;
esac

if [ ! -f "$HOOKS_DIR/pre-push" ]; then
  echo "ERROR: $HOOKS_DIR/pre-push is missing; nothing to install." >&2
  exit 1
fi

current="$(configured)"
if [ -n "$current" ] && [ "$current" != "$HOOKS_DIR" ]; then
  echo "ERROR: core.hooksPath is already set to '$current'." >&2
  if [ "$current" = "$FULL_DIR" ]; then
    echo "       That is the FULL gate, which already runs pin coherence." >&2
    echo "       Installing this narrow gate would REMOVE most of the \`push\`" >&2
    echo "       profile and the compiler check. If that is what you want:" >&2
  else
    echo "       Refusing to take over another hook configuration. Clear it with:" >&2
  fi
  echo "         git config --local --unset core.hooksPath" >&2
  exit 1
fi

for hook in "$HOOKS_DIR"/*; do
  [ -f "$hook" ] || continue
  case "$hook" in
    *.txt|*.md) continue ;;
  esac
  chmod +x "$hook"
done

git config --local core.hooksPath "$HOOKS_DIR"
echo "Trust pin hooks: installed (core.hooksPath = $HOOKS_DIR)"
echo
echo "  pre-push  BLOCKING, ~4s: EIGHT checkers, none of which runs a build or"
echo "            moves a pointer — check_pin_coherence.sh (scoped per submodule"
echo "            by scripts/hooks-pin/pin-waivers.txt), check_revert_rationale.sh,"
echo "            check_frozen_files.sh, check_measurement_provenance.sh,"
echo "            check_bridge_pin.sh, check_ir_cohort.py,"
echo "            check_submodule_remote_reachability.py, and"
echo "            check_cfg_test_caller_skew.py."
echo "  post-*    ADVISORY: announce pin drift right after a pull/rebase/switch."
echo
echo "  NOT run by this directory: most of the gate manifest's \`push\` profile,"
echo "  and x.py check --stage 1. For those, use scripts/install-git-hooks.sh."
echo
echo "  Read the last one as a NET, not as a type check. check_cfg_test_caller_skew.py"
echo "  catches the arity/field skew that a #[cfg(test)] construction site can carry"
echo "  past every build (a #[cfg(test)] body is in no lib target, so x.py build and"
echo "  x.py test tests/ui cannot see it). It does NOT type-check anything. Only"
echo "  scoped.compiler-check in the FULL set does that, and this directory is"
echo "  deliberately not that set."
