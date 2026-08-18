#!/usr/bin/env bash
# Install the NARROW pin-coherence git hooks (scripts/hooks-pin/) in this clone.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# There are two hook directories in this repo and they are not interchangeable:
#
#   scripts/hooks/      the FULL pre-push gate — pr_gate (11.6s) + pin coherence
#                       + bridge pin + `x.py check --stage 1` (~9-11 min) on any
#                       push touching compiler/ crates/ src/bootstrap/
#                       targo-trust/ first-party/. Installed by
#                       scripts/install-git-hooks.sh. Correct for a machine that
#                       is yours; a large thing to switch on for every other lane
#                       sharing a clone.
#
#   scripts/hooks-pin/  THIS one — submodule pin coherence and nothing else.
#                       0.49s measured. No build, no x.py, no pr_gate.
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
      echo "  pre-push runs scripts/check_pin_coherence.sh only (~0.5s)."
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
    echo "       Installing this narrow gate would REMOVE pr_gate, the bridge" >&2
    echo "       pin check and the compiler check. If that is what you want:" >&2
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
echo "  pre-push  BLOCKING, ~0.5s: scripts/check_pin_coherence.sh, scoped per"
echo "            submodule by scripts/hooks-pin/pin-waivers.txt. It never moves"
echo "            a pointer and never runs a build."
echo "  post-*    ADVISORY: announce pin drift right after a pull/rebase/switch."
echo
echo "  NOT run by this directory: scripts/pr_gate.sh, check_bridge_pin.sh, and"
echo "  x.py check --stage 1. For those, use scripts/install-git-hooks.sh."
