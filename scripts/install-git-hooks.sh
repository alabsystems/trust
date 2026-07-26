#!/usr/bin/env bash
# Point this clone's git hooks at the tracked hooks in `scripts/hooks/`.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# Trust has no CI: pushing `.github/workflows/*` needs a GitHub PAT with
# `workflow` scope that the toolchain token lacks, so the gate runs locally, on
# push. What makes that trustworthy is where the hook body lives. It lives in
# `scripts/hooks/`, tracked and reviewed, and this sets `core.hooksPath` to that
# directory — so a hook change lands with the commit that makes it and no clone
# can be running a stale copy of one. (An earlier version of this script
# generated a copy into `.git/hooks/`; that copy is untracked, invisible to
# review, and silently outlives the tree it came from. It is removed on
# install.)
#
# Usage:
#   bash scripts/install-git-hooks.sh             # install (idempotent)
#   bash scripts/install-git-hooks.sh --status    # report what is installed
#   bash scripts/install-git-hooks.sh --uninstall # stop using the tracked hooks
#
# There is no environment-variable bypass. A lane that is legitimately red gets
# an owned, expiring quarantine row in `tests/trust-comprehensive/divergences.toml`
# that the hook reads — visible, reviewed, and self-retiring. The only way past
# the hook is `git push --no-verify`, which is git's own and shows up in the
# reflog rather than in a habit.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

HOOKS_DIR="scripts/hooks"
LEGACY_MARKER="# trust-managed-pre-push-hook v1"
GIT_HOOK_DIR="$(git rev-parse --git-path hooks 2>/dev/null || echo "$REPO_ROOT/.git/hooks")"

action="${1:-install}"
configured() { git config --local --get core.hooksPath 2>/dev/null || true; }

status() {
  local current
  current="$(configured)"
  if [ "$current" = "$HOOKS_DIR" ]; then
    echo "Trust git hooks: INSTALLED (core.hooksPath = $HOOKS_DIR)"
    return 0
  fi
  echo "Trust git hooks: NOT installed (core.hooksPath = ${current:-<unset>})"
  echo "  run: bash scripts/install-git-hooks.sh"
  return 1
}

case "$action" in
  --status|status|--check)
    status
    exit $?
    ;;
  --uninstall|uninstall)
    if [ "$(configured)" = "$HOOKS_DIR" ]; then
      git config --local --unset core.hooksPath
      echo "Trust git hooks: uninstalled."
    else
      echo "Trust git hooks: nothing to uninstall (core.hooksPath is not ours)."
    fi
    exit 0
    ;;
  ""|install|--install)
    :
    ;;
  *)
    echo "usage: $0 [--status|--uninstall]" >&2
    exit 2
    ;;
esac

if [ ! -f "$HOOKS_DIR/pre-push" ]; then
  echo "ERROR: $HOOKS_DIR/pre-push is missing; nothing to install." >&2
  exit 1
fi

current="$(configured)"
if [ -n "$current" ] && [ "$current" != "$HOOKS_DIR" ]; then
  echo "ERROR: core.hooksPath is already set to '$current'." >&2
  echo "       Refusing to take over another hook configuration. Clear it with:" >&2
  echo "         git config --local --unset core.hooksPath" >&2
  exit 1
fi

# A pre-push hook this script wrote in its previous form is dead weight once
# core.hooksPath moves: git stops reading it, but it stays on disk looking
# authoritative. Remove exactly our own; never touch a hook someone else wrote.
LEGACY_HOOK="$GIT_HOOK_DIR/pre-push"
if [ -f "$LEGACY_HOOK" ] && grep -qF "$LEGACY_MARKER" "$LEGACY_HOOK"; then
  rm -f "$LEGACY_HOOK"
  echo "Removed the superseded generated hook at $LEGACY_HOOK."
elif [ -f "$LEGACY_HOOK" ]; then
  echo "NOTE: a foreign hook remains at $LEGACY_HOOK; core.hooksPath makes git" >&2
  echo "      ignore it. Chain it from $HOOKS_DIR/pre-push if you still want it." >&2
fi

for hook in "$HOOKS_DIR"/*; do
  [ -f "$hook" ] || continue
  chmod +x "$hook"
done

git config --local core.hooksPath "$HOOKS_DIR"
echo "Trust git hooks: installed (core.hooksPath = $HOOKS_DIR)"
echo "  pre-push runs scripts/pr_gate.sh, scripts/check_pin_coherence.sh, and"
echo "  scripts/check_bridge_pin.sh --check. A known-red lane needs an owned,"
echo "  expiring row in tests/trust-comprehensive/divergences.toml."
