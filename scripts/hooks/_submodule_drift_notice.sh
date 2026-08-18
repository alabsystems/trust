#!/usr/bin/env bash
# Shared body for the advisory post-merge / post-rewrite / post-checkout hooks.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# `git pull --rebase` moves the gitlinks recorded at HEAD and does NOT move the
# submodule worktrees. That single fact is the whole pin-drift bug: the moment a
# lane rebases onto someone else's pin bump, this worktree is stale and nothing
# says so until a build fails somewhere unrecognisable. These hooks fire exactly
# at that moment and say so.
#
# ADVISORY ONLY — always exits 0. It must never fail a pull, a rebase or a
# checkout: this is a notice about state, not a judgement about the operation,
# and a hook that can block `git pull` is a hook people uninstall. The
# fail-closed counterpart is scripts/check_pin_coherence.sh, which runs pre-push.
#
# It also never mutates. Restoring a submodule worktree is a deliberate act
# (see the concurrency note in scripts/submodule_sync.sh), never a side effect
# of a git command someone else's build is racing.

REPO_ROOT="$(git rev-parse --show-toplevel 2>/dev/null)" || exit 0
SYNC="$REPO_ROOT/scripts/submodule_sync.sh"
[ -f "$SYNC" ] || exit 0

out="$(bash "$SYNC" --quiet 2>/dev/null)" || true
case "$out" in
  *DRIFT*)
    printf '\n%s\n' "$out" >&2
    printf '%s\n\n' "  (advisory: this pull/checkout moved pins your submodule worktrees have not followed)" >&2
    ;;
esac

exit 0
