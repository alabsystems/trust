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
# that the hook reads — visible, reviewed, and self-retiring. A red the
# destination already has, unchanged, is graded INHERITED by the hook itself
# (scripts/hooks/pre-push, "INHERITED-RED").
#
# SSH KEEPALIVE (2026-10-24, docs/DECISION_QUEUE.md PUSH-PATH-SSH-KEEPALIVE).
# git holds the push's ssh connection idle for the whole hook run, and GitHub
# closes an idle one after about six minutes (scripts/hooks/_ssh_keepalive.sh
# has the measurement), so with default ssh a green hook still lost its push.
# Install therefore also sets this clone's
#     core.sshCommand = ssh -o ServerAliveInterval=30 -o ServerAliveCountMax=10
# unless an ssh command is already chosen: a core.sshCommand of any scope
# (yours stays; add -o ServerAliveInterval=30 to it if it has none), or GIT_SSH
# in the environment (core.sshCommand would silently override that program).
# GIT_SSH_COMMAND does not stop it: git prefers the variable whenever it is
# set, and the config covers every push made without it. --status reports the
# keepalive git would use for origin; --uninstall removes the value only when
# it is still exactly the one this script wrote.
#
# GIT CLIENT TUNING (2026-11-04, docs/DECISION_QUEUE.md GIT-CLIENT-TUNING-1).
# Install also applies the tuning scripts/git-clone.gitconfig declares: as
# committed, core.untrackedCache and feature.manyFiles in this clone's config
# (every linked worktree reads it), core.untrackedCache alone in each populated
# submodule's (trust-cg's host boundary refuses feature.manyFiles), and this
# worktree's index moved to format 4: scripts/hooks/_git_client_tuning.sh, which
# scripts/install-pin-hook.sh shares. A value already chosen in any scope is
# kept. It never sets core.fsmonitor, which the completion gate, G2's checker
# and recreate_bootstrap.py refuse. --status reports the tuning and writes
# nothing; --uninstall leaves it, since it is not a hook (`git config --local
# --unset <key>` removes one).
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

HOOKS_DIR="scripts/hooks"
LEGACY_MARKER="# trust-managed-pre-push-hook v1"
# git's OWN hooks directory, where the previous form of this script wrote: not
# `git rev-parse --git-path hooks`, which answers core.hooksPath once that is
# set, so every install after the first called scripts/hooks/pre-push itself a
# "foreign hook" (2026-10-24).
GIT_HOOK_DIR="$(git rev-parse --path-format=absolute --git-common-dir 2>/dev/null || echo "$REPO_ROOT/.git")/hooks"

action="${1:-install}"
configured() { git config --local --get core.hooksPath 2>/dev/null || true; }

# shellcheck source=hooks/_ssh_keepalive.sh
. "$HOOKS_DIR/_ssh_keepalive.sh"
# shellcheck source=hooks/_git_client_tuning.sh
. scripts/hooks/_git_client_tuning.sh
local_ssh_command() { git config --local --get core.sshCommand 2>/dev/null || true; }

# keepalive_status: one line on what git would use for origin's push URL.
# Exit 0 when keepalive is on, origin is not ssh, or there is no origin; 1 when
# it is off; 2 when it cannot be read.
keepalive_status() {
  local url line rc=0
  url="$(git remote get-url --push origin 2>/dev/null)" || {
    echo "ssh keepalive: no origin remote; nothing to check"
    return 0
  }
  line="$(trust_ssh_keepalive "$url")" || rc=$?
  case $rc in
    0) echo "ssh keepalive: $line for origin ($url)" ;;
    1)
      echo "ssh keepalive: OFF, $line, for origin ($url)"
      echo "  GitHub closes an idle ssh connection after about 6 minutes and the pre-push"
      echo "  hook runs longer, so the hook refuses such a push before any lane."
      if [ -n "$(local_ssh_command)" ] || git config --get core.sshCommand >/dev/null 2>&1 || [ -n "${GIT_SSH:-}" ]; then
        echo "  Your own ssh command is in use: add -o ServerAliveInterval=30 to it, or"
        echo "  ServerAliveInterval 30 to ~/.ssh/config."
      else
        echo "  run: bash scripts/install-git-hooks.sh"
      fi
      ;;
    2) echo "ssh keepalive: $line for origin ($url)" ;;
    *) echo "ssh keepalive: origin ($url) is not an ssh URL; nothing to check"; rc=0 ;;
  esac
  return "$rc"
}

status() {
  local current rc=0
  current="$(configured)"
  if [ "$current" = "$HOOKS_DIR" ]; then
    echo "Trust git hooks: INSTALLED (core.hooksPath = $HOOKS_DIR)"
  else
    echo "Trust git hooks: NOT installed (core.hooksPath = ${current:-<unset>})"
    echo "  run: bash scripts/install-git-hooks.sh"
    rc=1
  fi
  keepalive_status || [ $? -eq 2 ] || rc=1
  trust_git_tuning_status "$REPO_ROOT"
  trust_registry_prefetch "$REPO_ROOT" --check
  return "$rc"
}

# set_keepalive: write TRUST_SSH_KEEPALIVE_COMMAND as this clone's
# core.sshCommand unless an ssh command is already chosen (header).
set_keepalive() {
  local mine scope_value
  mine="$(local_ssh_command)"
  if [ "$mine" = "$TRUST_SSH_KEEPALIVE_COMMAND" ]; then
    echo "  ssh keepalive: core.sshCommand already set by this script"
    return 0
  fi
  if [ -n "$mine" ]; then
    echo "  ssh keepalive: this clone's own core.sshCommand ($mine) is kept"
    return 0
  fi
  if scope_value="$(git config --show-scope --get core.sshCommand 2>/dev/null)"; then
    echo "  ssh keepalive: core.sshCommand is set in your ${scope_value%%$'\t'*} config; it is kept"
    return 0
  fi
  if [ -n "${GIT_SSH:-}" ]; then
    echo "  ssh keepalive: GIT_SSH ($GIT_SSH) is set; core.sshCommand would override it, so none is set"
    return 0
  fi
  git config --local core.sshCommand "$TRUST_SSH_KEEPALIVE_COMMAND"
  echo "  ssh keepalive: set core.sshCommand = $TRUST_SSH_KEEPALIVE_COMMAND"
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
    if [ "$(local_ssh_command)" = "$TRUST_SSH_KEEPALIVE_COMMAND" ]; then
      git config --local --unset core.sshCommand
      echo "Trust git hooks: removed the core.sshCommand this script set."
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

# Git records which tracked files are executables. Repair their execute bits
# without making interpreter-only helpers or data executable and dirtying a
# clean checkout. NUL-delimited records preserve spaces in tracked paths.
while IFS= read -r -d '' entry; do
  case "$entry" in
    100755\ *)
      hook="${entry#*$'\t'}"
      [ -f "$hook" ] || continue
      chmod +x "$hook"
      ;;
  esac
done < <(git ls-files --stage -z -- "$HOOKS_DIR")

git config --local core.hooksPath "$HOOKS_DIR"
echo "Trust git hooks: installed (core.hooksPath = $HOOKS_DIR)"
set_keepalive
keepalive_status | sed 's/^/  /' || true
trust_git_tuning_apply "$REPO_ROOT"
trust_registry_prefetch "$REPO_ROOT"
echo "  pre-push runs every gate-manifest row carrying the \`push\` profile; it"
echo "  hand-lists nothing. See the current set with:"
echo "      bash tests/run_trust_comprehensive_harness.sh --list push"
echo "  A known-red lane needs an owned, expiring row in"
echo "  tests/trust-comprehensive/divergences.toml; a red the destination already"
echo "  has, unchanged, is graded INHERITED and does not block."
echo
echo "  commit-msg runs scripts/check_measurement_provenance.sh's R1/R2 on the"
echo "  commit being made, so a missing or wrong Measured-on: stamp is refused at"
echo "  commit time, not at push."
echo
echo "  post-merge / post-rewrite / post-checkout are ADVISORY: they announce"
echo "  submodule pin drift right after a pull, rebase or branch switch — the"
echo "  moment the gitlinks move and the submodule worktrees do not. They print"
echo "  to stderr, never block, and never mutate a worktree."
