#!/usr/bin/env bash
# Align an owned branch with remote main and push without rewriting history.
# Before invoking it, build the changed source and run `python3
# scripts/land_gate.py plan` and `run`. The installed hook checks live
# verification and proof-input integrity; it does not yet run the broad suites
# (a defect, docs/STATUS.md; owner, 2026-11-09: "we want verification on and
# for it to work."). This helper makes no proof or release-completion claim.
#
# Usage: scripts/prewarm_push.sh [--dry-run] [--remote origin] [--dest main]
#        [--network-home DIR] [--base COMMIT] [--max-rounds N] [--log-dir DIR]
# --base records the caller's evidence base and must be an ancestor of HEAD.
# A zero round limit retries ordinary advancing-main races without a fixed cap.
# --selftest checks failure classification and hook-path ownership only.
# Author: Andrew Yates. Copyright 2026. License: Apache-2.0 OR MIT.
set -uo pipefail

REMOTE="origin"
DEST="main"
MAX_ROUNDS=0
BASE=""
NETWORK_HOME="${HOME:-}"
PYTHON="${PYTHON:-python3}"
ORIGINAL_ARGS=("$@")
DRY_RUN=0
LOG_DIR=""

die() { echo "prewarm_push: $*" >&2; exit 2; }

# ---------------------------------------------------------------------------
# The race classifier. A push that failed ONLY because the destination ref
# moved between our fetch and the remote's update is a race; everything else —
# including a RED hook, which prints `PRE-PUSH: RED` and makes git report
# "failed to push some refs" — is not.
# ---------------------------------------------------------------------------
classify_push_failure() {
  local log="$1"
  if grep -q 'PRE-PUSH: RED' "$log"; then
    echo "hook-red"; return
  fi
  # The hook's own stale-destination stop (scripts/hooks/pre-push, `PRE-PUSH:
  # STALE`, exit 2): every pushed ref moved on the destination while the hook
  # ran, so it stopped before the next scoped lane with no verdict. That is this
  # loop's race, caught earlier; a lane that had already failed prints RED above.
  if grep -q 'PRE-PUSH: STALE' "$log"; then
    echo "race"; return
  fi
  if grep -qE '\[rejected\].*\((fetch first|non-fast-forward|stale info)\)' "$log" \
     || grep -qE '\[remote rejected\].*(cannot lock ref|incorrect old value|failed to update ref)' "$log"; then
    echo "race"; return
  fi
  echo "other"
}

selftest() {
  local dir fails=0 got
  dir="$(mktemp -d "${TMPDIR:-/tmp}/prewarm-selftest.XXXXXX")" || exit 2
  check() {
    local want="$1" text="$2"
    printf '%s\n' "$text" > "$dir/log"
    got="$(classify_push_failure "$dir/log")"
    if [ "$got" = "$want" ]; then
      echo "  PASS  $want <- $(printf '%s' "$text" | head -1)"
    else
      echo "  FAIL  want $want, got $got <- $(printf '%s' "$text" | head -1)"
      fails=$((fails + 1))
    fi
  }
  check race ' ! [rejected]        e6/slice1 -> main (fetch first)
error: failed to push some refs to '"'"'github.com:x/trust.git'"'"
  check race ' ! [rejected]        e6/slice1 -> main (non-fast-forward)'
  check race ' ! [rejected]        main -> main (stale info)'
  check race ' ! [remote rejected] main -> main (cannot lock ref '"'"'refs/heads/main'"'"': is at 1234 but expected 5678)'
  check hook-red 'PRE-PUSH: RED — fix the lanes above
error: failed to push some refs to '"'"'x'"'"
  check other 'error: failed to push some refs to x'
  check other 'fatal: unable to access remote: Could not resolve host'
  check other ' ! [remote rejected] main -> main (protected branch hook declined)'
  # A RED hook that ALSO mentions a rejection is still RED: the lane result wins.
  check hook-red 'PRE-PUSH: RED
 ! [rejected]        main -> main (fetch first)'
  # The hook's stale-destination stop is a race: no lane failed, main moved.
  check race 'PRE-PUSH: STALE — every ref this push updates moved on the destination while this hook ran:
  refs/heads/main  now 66f3ab373de1
error: failed to push some refs to '"'"'x'"'"
  # A lane that failed before the stop still ends RED, never a race.
  check hook-red 'pre-push: every ref this push updates moved on the destination (fetch first):
PRE-PUSH: RED'
  selftest_hooks "$dir/hooks"
  fails=$((fails + $?))
  rm -rf "$dir"
  if [ "$fails" -ne 0 ]; then echo "SELFTEST: $fails FAILED"; exit 1; fi
  echo "SELFTEST: all cases PASS"
  exit 0
}

# ---------------------------------------------------------------------------
# The hook verdict: does core.hooksPath gate a push from the checkout at $1?
# Prints `own <dir>`, `main-of-linked <dir>` or `refuse <reason>` and returns 0
# only for the first two. It reads git state and changes nothing.
#   own             this checkout's scripts/hooks (a relative hooksPath is read
#                   from the worktree top, where git runs hooks);
#   main-of-linked  this is a LINKED worktree and hooksPath is the scripts/hooks
#                   of the main worktree of the SAME repository (same
#                   --git-common-dir) — the shared absolute path
#                   install-git-hooks.sh writes;
#   refuse          anything else: unset, not a directory, no executable
#                   pre-push in it (git then runs no hook at all), another
#                   repository's hooks, another linked worktree's, or a main
#                   worktree's hooks from a checkout that is not linked to it.
# Paths are compared physically (cd -P), so a symlinked or `..`-spelled path
# names the directory it resolves to, never a string that happens to match.
# ---------------------------------------------------------------------------
physical_dir() {
  [ -n "${1:-}" ] || return 1
  ( cd -P -- "$1" 2>/dev/null && pwd -P )
}

hooks_verdict() {
  local top="$1" hooks hp own git_dir common_dir main_root mp main_common
  hooks="$(git -C "$top" config --get core.hooksPath || true)"
  if [ -z "$hooks" ]; then echo "refuse core.hooksPath is unset, so a push runs no hook"; return 1; fi
  case "$hooks" in
    /*) hp="$(physical_dir "$hooks")" ;;
    *) hp="$(physical_dir "$top/$hooks")" ;;
  esac
  if [ -z "$hp" ]; then echo "refuse core.hooksPath='$hooks' is not a directory"; return 1; fi
  if [ ! -f "$hp/pre-push" ] || [ ! -x "$hp/pre-push" ]; then
    echo "refuse $hp/pre-push is not an executable file, so a push runs no hook"; return 1
  fi
  own="$(physical_dir "$top/scripts/hooks")"
  if [ -n "$own" ] && [ "$hp" = "$own" ]; then echo "own $hp"; return 0; fi
  git_dir="$(physical_dir "$(git -C "$top" rev-parse --path-format=absolute --git-dir 2>/dev/null)")"
  common_dir="$(physical_dir "$(git -C "$top" rev-parse --path-format=absolute --git-common-dir 2>/dev/null)")"
  if [ -z "$git_dir" ] || [ -z "$common_dir" ] || [ "$git_dir" = "$common_dir" ]; then
    echo "refuse core.hooksPath='$hooks' is not this checkout's scripts/hooks, and this checkout is not a linked worktree"
    return 1
  fi
  # `git worktree list` names the main worktree first.
  main_root="$(git -C "$top" worktree list --porcelain | awk 'NR == 1 && /^worktree / { print substr($0, 10) }')"
  mp="$(physical_dir "$main_root/scripts/hooks")"
  main_common="$(physical_dir "$(git -C "$main_root" rev-parse --path-format=absolute --git-common-dir 2>/dev/null)")"
  if [ -n "$mp" ] && [ "$hp" = "$mp" ] && [ "$main_common" = "$common_dir" ]; then
    echo "main-of-linked $hp"; return 0
  fi
  echo "refuse core.hooksPath='$hooks' is neither this linked worktree's scripts/hooks nor its main worktree's (${main_root:-?}/scripts/hooks)"
  return 1
}

# The verdict on throwaway repositories: a main worktree `main` with linked
# worktrees `linked` and `linked2`, and an unrelated repository `other` with a
# linked worktree `other-linked`. Returns the number of failed cases.
selftest_hooks() {
  local root="$1"
  (
    export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1
    unset GIT_DIR GIT_WORK_TREE GIT_COMMON_DIR GIT_INDEX_FILE GIT_OBJECT_DIRECTORY
    fails=0
    mkrepo() {
      git init -q "$1" && mkdir -p "$1/scripts/hooks" \
        && printf '#!/bin/sh\nexit 0\n' > "$1/scripts/hooks/pre-push" \
        && chmod +x "$1/scripts/hooks/pre-push" && git -C "$1" add -A \
        && git -C "$1" -c user.name=t -c user.email=t@example.invalid -c commit.gpgsign=false commit -qm init
    }
    { mkrepo "$root/main" && mkrepo "$root/other" \
        && git -C "$root/main" worktree add -q "$root/linked" -b linked \
        && git -C "$root/main" worktree add -q "$root/linked2" -b linked2 \
        && git -C "$root/other" worktree add -q "$root/other-linked" -b other-linked \
        && ln -s "$root/main" "$root/main-link"; } >/dev/null 2>&1 \
      || { echo "  FAIL  could not build the hooksPath fixture under $root"; exit 1; }
    expect() { # <want: own|main-of-linked|refuse> <checkout> <hooksPath or ""> <label>
      local want="$1" at="$2" path="$3" label="$4" got repo
      repo="$(git -C "$at" rev-parse --path-format=absolute --git-common-dir)"
      if [ -n "$path" ]; then git --git-dir="$repo" config core.hooksPath "$path"; else git --git-dir="$repo" config --unset core.hooksPath; fi
      got="$(hooks_verdict "$at")"
      if [ "${got%% *}" = "$want" ]; then
        echo "  PASS  $want <- $label"
      else
        echo "  FAIL  want $want, got '$got' <- $label"
        fails=$((fails + 1))
      fi
    }
    local_main="$root/main" linked="$root/linked"
    expect main-of-linked "$linked" "$local_main/scripts/hooks" \
      "linked worktree, hooksPath = the main worktree's scripts/hooks (was: refused)"
    expect own "$local_main" "$local_main/scripts/hooks" "main worktree, hooksPath = its own scripts/hooks"
    expect own "$linked" "scripts/hooks" "linked worktree, relative scripts/hooks = its own"
    expect own "$local_main" "./scripts/hooks" "main worktree, relative ./scripts/hooks = its own"
    expect main-of-linked "$linked" "$local_main/scripts/../scripts/hooks" "linked, the main's hooks spelled with .."
    expect main-of-linked "$linked" "$root/main-link/scripts/hooks" "linked, the main's hooks through a symlink"
    expect refuse "$linked" "" "linked worktree, core.hooksPath unset"
    expect refuse "$linked" "$root/other/scripts/hooks" "linked worktree, another repository's hooks"
    expect refuse "$linked" "$root/linked2/scripts/hooks" "linked worktree, a SIBLING linked worktree's hooks"
    expect refuse "$local_main" "$linked/scripts/hooks" "main worktree, a linked worktree's hooks"
    expect refuse "$root/other" "$local_main/scripts/hooks" "an unrelated main worktree, this repo's main hooks"
    expect refuse "$root/other-linked" "$local_main/scripts/hooks" \
      "a linked worktree of ANOTHER repository, this repo's main hooks"
    expect refuse "$linked" "$root/nowhere/scripts/hooks" "linked worktree, a hooksPath that does not exist"
    chmod -x "$local_main/scripts/hooks/pre-push"
    expect refuse "$linked" "$local_main/scripts/hooks" "linked, the main's hooks with a NON-executable pre-push"
    rm -f "$local_main/scripts/hooks/pre-push"
    expect refuse "$linked" "$local_main/scripts/hooks" "linked, the main's hooks with NO pre-push"
    exit "$fails"
  )
}

case "${1:-}" in
  --selftest) selftest ;;
esac

while [ "$#" -gt 0 ]; do
  case "$1" in
    --dry-run) DRY_RUN=1 ;;
    --remote) shift; REMOTE="${1:?--remote needs a value}" ;;
    --dest) shift; DEST="${1:?--dest needs a value}" ;;
    --network-home) shift; NETWORK_HOME="${1:?--network-home needs a value}" ;;
    --base) shift; BASE="${1:?--base needs a value}" ;;
    --max-rounds) shift; MAX_ROUNDS="${1:?--max-rounds needs a value}" ;;
    --log-dir) shift; LOG_DIR="${1:?--log-dir needs a value}" ;;
    -h|--help) sed -n '2,/^set -uo/p' "$0" | sed -e '$d' -e 's/^# \{0,1\}//'; exit 0 ;;
    *) die "unknown argument '$1' (see --help)" ;;
  esac
  shift
done
case "$MAX_ROUNDS" in ''|*[!0-9]*) die "--max-rounds must be a nonnegative integer" ;; esac

case "$NETWORK_HOME" in /*) ;; *) die "--network-home must be an absolute directory" ;; esac
[ -d "$NETWORK_HOME" ] || die "--network-home directory does not exist"
network_git() { HOME="$NETWORK_HOME" git "$@"; }

ROOT="$(git rev-parse --show-toplevel 2>/dev/null)" || die "not inside a git worktree"
cd "$ROOT" || exit 2
"$PYTHON" -c 'import sys; sys.exit(sys.version_info < (3, 11))' || die "PYTHON must select Python >= 3.11"
SELF="$ROOT/scripts/prewarm_push.sh"
[ -f "$SELF" ] || die "run from a checkout that carries scripts/prewarm_push.sh"

BRANCH="$(git symbolic-ref --quiet --short HEAD)" || die "detached HEAD: check out the branch you want to land"
LOCAL_REF="refs/heads/$BRANCH"
REMOTE_REF="refs/heads/$DEST"
TRACKING="refs/remotes/$REMOTE/$DEST"
LOCATION="$(network_git remote get-url --push "$REMOTE" 2>/dev/null)" || die "no remote named '$REMOTE'"
FETCH_LOCATION="$(network_git remote get-url "$REMOTE")" || die "no fetch URL for $REMOTE"

# The gate must be the one that runs on push. An unset core.hooksPath is an
# UNGATED push, and this script never makes one (hooks_verdict).
HOOKS="$(git config --get core.hooksPath || true)"
HOOKS_OK=0
if HOOKS_VERDICT="$(hooks_verdict "$ROOT")"; then HOOKS_OK=1; fi
HOOKS_DIR="${HOOKS_VERDICT#* }"
# From a linked worktree the MAIN worktree's pre-push runs, not this checkout's.
hook_note() {
  case "$HOOKS_VERDICT" in
    main-of-linked\ *)
      echo "  hook            the MAIN worktree's $HOOKS_DIR/pre-push gates this linked worktree's push;"
      echo "                  it reads the lane manifest and lane scripts from this worktree ($ROOT)"
      if ! cmp -s "$HOOKS_DIR/pre-push" "$ROOT/scripts/hooks/pre-push"; then
        echo "  NOTE            that pre-push differs from this checkout's scripts/hooks/pre-push: the main worktree's is the one that runs"
      fi
      ;;
  esac
}

tree_is_clean() {
  local status
  status="$(git status --porcelain --untracked-files=no --ignore-submodules=all)" || return 1
  [ -z "$status" ]
}

# Fetch an explicit tracking ref even when this clone's fetch refspec is narrow.
# No '+' and no force: a remote history rewrite is not an advancing-main race.
fetch_dest() {
  local fetched advertised previous
  while :; do
    [ "$(network_git remote get-url --push "$REMOTE")" = "$LOCATION" ] || return 1
    [ "$(network_git remote get-url "$REMOTE")" = "$FETCH_LOCATION" ] || return 1
    previous="$(git rev-parse --verify "$TRACKING^{commit}" 2>/dev/null || true)"
    network_git fetch --quiet --no-recurse-submodules "$REMOTE" "$REMOTE_REF:$TRACKING" || return 1
    fetched="$(git rev-parse --verify "$TRACKING^{commit}")" || return 1
    if [ -n "$previous" ]; then
      git merge-base --is-ancestor "$previous" "$fetched" || return 1
    fi
    advertised="$(network_git ls-remote --exit-code "$REMOTE" "$REMOTE_REF")" || return 1
    [ "$(printf '%s\n' "$advertised" | wc -l | tr -d ' ')" = 1 ] || return 1
    advertised="${advertised%%[[:space:]]*}"
    if [ "$advertised" = "$fetched" ]; then
      printf '%s\n' "$fetched"
      return 0
    fi
    # Main advanced even during fetch/readback. Repeat without recursive
    # stack growth; no source or gate result is changed by this observation.
  done
}

sync_submodules() (
  export HOME="$NETWORK_HOME"
  bash scripts/submodule_sync.sh >/dev/null 2>&1 && return 0
  echo "prewarm_push: submodule worktrees differ from the merged pins; restoring the lossless subset"
  bash scripts/submodule_sync.sh --restore || true
  bash scripts/submodule_sync.sh
)

if [ "$DRY_RUN" -eq 1 ]; then
  echo "prewarm_push DRY RUN — nothing is merged, built or pushed"
  echo "  branch          $BRANCH ($(git rev-parse --short HEAD))"
  echo "  destination     $REMOTE $REMOTE_REF   location $LOCATION"
  echo "  network HOME    $NETWORK_HOME (gate HOME remains ${HOME:-unset})"
  if [ "$HOOKS_OK" -eq 1 ]; then
    echo "  hook            core.hooksPath=$HOOKS (proof-input checks run on push)"
    hook_note
  else
    echo "  hook            REFUSE: ${HOOKS_VERDICT#refuse } — a real run stops here"
  fi
  if tree_is_clean; then echo "  worktree        clean"; else echo "  worktree        REFUSE: uncommitted changes — a real run stops here"; fi
  if ! base="$(fetch_dest)"; then die "fetch of $REMOTE $REMOTE_REF failed"; fi
  echo "  fetched         $TRACKING = $base"
  if git merge-base --is-ancestor "$base" HEAD; then
    echo "  merge           none: HEAD already contains $TRACKING"
  else
    echo "  merge           git merge --no-edit $base   ($(git rev-list --count HEAD.."$base") commit(s) behind; stop on conflict)"
  fi
  echo "  submodules      bash scripts/submodule_sync.sh (then --restore for the lossless subset only)"
  echo "  validation      caller's source build and focused regression evidence; proof-input hook on push"
  echo "  then            re-fetch; merge again if the destination advanced"
  echo "  push            git push $REMOTE $LOCAL_REF:$REMOTE_REF   (hook runs; never --no-verify, never --force)"
  echo "  on rejection    confirmed advancing destination -> next round (limit $MAX_ROUNDS; 0 = none); all real failures stop"
  echo "  logs            ${LOG_DIR:-the worktree Git directory/trust-prewarm (created on a real run)}"
  exit 0
fi

# One admitted owner spans source alignment, proof-input checks and every retry.
if [ "${BUILD_SLOT_HELD:-}" != 1 ]; then
  # ${a[@]+"${a[@]}"}: bash 3.2 (macOS /bin/bash) calls an empty array unbound
  # under set -u, and a bare `scripts/prewarm_push.sh` passes no arguments.
  exec "$PYTHON" -B scripts/build-slot -- bash "$SELF" ${ORIGINAL_ARGS[@]+"${ORIGINAL_ARGS[@]}"}
fi
if [ -z "$LOG_DIR" ]; then
  LOG_DIR="$(git rev-parse --path-format=absolute --git-dir)/trust-prewarm"
fi
mkdir -p "$LOG_DIR" || die "cannot create $LOG_DIR"
LOG_DIR="$(physical_dir "$LOG_DIR")" || die "cannot resolve log directory"

[ "$HOOKS_OK" -eq 1 ] || die "${HOOKS_VERDICT#refuse }; refusing an ungated push (bash scripts/install-git-hooks.sh)"
tree_is_clean || die "uncommitted changes in the worktree; commit them first"
hook_note

# Signals request a stop; do not release the source lease while a foreground
# gate is still closing its own children. Bash dispatches these traps after the
# foreground command returns. The first requested stop keeps its exit status.
stop_code=0
request_stop() { if [ "$stop_code" -eq 0 ]; then stop_code="$1"; fi; }
check_stop() { if [ "$stop_code" -ne 0 ]; then exit "$stop_code"; fi; }
trap 'request_stop 130' INT
trap 'request_stop 143' TERM
trap 'request_stop 129' HUP

# Keep ordinary source/build custody through merges as well as compiler work.
# If our caller owns a normal reentrant token, never release its lease here.
old_token="${TRUST_BUILD_LOCK_TOKEN:-}"
lease="$(trap '' INT TERM HUP; "${TARGO:-targo}" trust repo lock acquire --repo-root "$ROOT" --kind build --purpose 'automatic main alignment and landing' --pid "$$")" || die "normal source lease refused"
[ -n "$lease" ] || die "normal source lease returned no token"
export TRUST_BUILD_LOCK_TOKEN="$lease"
release_lease() {
  rc=$?
  trap - EXIT
  if [ "$lease" != "$old_token" ]; then
    (trap '' INT TERM HUP; "${TARGO:-targo}" trust repo lock release "$lease" --repo-root "$ROOT") || rc=2
  fi
  if [ "$stop_code" -ne 0 ]; then rc="$stop_code"; fi
  exit "$rc"
}
trap release_lease EXIT
check_stop

if [ -n "$BASE" ]; then
  BASE="$(git rev-parse --verify "$BASE^{commit}")" || die "invalid initial --base"
  git merge-base --is-ancestor "$BASE" HEAD || die "evidence base is not contained in HEAD"
fi
round=0
while [ "$MAX_ROUNDS" -eq 0 ] || [ "$round" -lt "$MAX_ROUNDS" ]; do
  check_stop
  round=$((round + 1))
  tree_is_clean || die "source changed between rounds"
  [ "$(git symbolic-ref --quiet HEAD)" = "$LOCAL_REF" ] || die "branch changed between rounds"
  if ! hooks_verdict "$ROOT" >/dev/null; then die "push hook no longer configured"; fi
  base="$(fetch_dest)" || { echo "prewarm_push: canonical fetch/readback failed" >&2; exit 5; }
  echo "=== round $round: $TRACKING = $base"
  if ! git merge-base --is-ancestor "$base" HEAD; then
    before_merge="$(git rev-parse HEAD)" || exit 2
    echo "merging $base into $BRANCH"
    if ! network_git merge --no-edit "$base"; then
      echo "prewarm_push: merge failed; any conflicts are left intact for resolution" >&2
      git diff --name-only --diff-filter=U >&2
      exit 3
    fi
    # The caller's source build cannot cover code introduced by this merge.
    # Keep the merge, then return for a focused build of those new inputs.
    if git diff --quiet "$before_merge" HEAD -- compiler library crates targo-trust first-party src \
        Cargo.toml Cargo.lock .cargo ':(glob)rust-toolchain*' release/trust-version.toml; then
      :
    else
      rc=$?
      [ "$rc" -eq 1 ] || die "cannot inspect merged compiler inputs"
      echo "prewarm_push: merged compiled inputs; build the changed source and rerun" >&2
      exit 4
    fi
  fi
  check_stop
  sync_submodules || { echo "prewarm_push: submodule worktrees are not at the merged pins; stopping" >&2; exit 7; }
  check_stop
  tree_is_clean || die "source is dirty after submodule synchronization"
  selected="$(git rev-parse HEAD)" || exit 2
  selected_tree="$(git rev-parse HEAD^{tree})" || exit 2
  attempt="$(mktemp -d "$LOG_DIR/round-XXXXXX")" || die "cannot create round evidence"
  printf 'head=%s\ntree=%s\nremote=%s\nevidence_base=%s\npolicy=source-build-and-focused-validation\n' \
    "$selected" "$selected_tree" "$base" "$BASE" > "$attempt/source.txt"
  now="$(fetch_dest)" || { echo "prewarm_push: canonical readback failed" >&2; exit 5; }
  check_stop
  if [ "$now" != "$base" ]; then
    git merge-base --is-ancestor "$base" "$now" || die "destination history did not advance normally"
    echo "$TRACKING advanced; aligning before push"
    continue
  fi
  [ "$(git rev-parse HEAD)" = "$selected" ] && tree_is_clean || die "source changed before push"
  check_stop
  plog="$attempt/push.log"
  echo "destination unchanged; pushing $LOCAL_REF -> $REMOTE $REMOTE_REF (log: $plog)"
  network_git push "$REMOTE" "$LOCAL_REF:$REMOTE_REF" 2>&1 | tee "$plog"
  rc=${PIPESTATUS[0]}
  check_stop
  if [ "$rc" -eq 0 ]; then
    now="$(fetch_dest)" || { echo "prewarm_push: push returned 0 but final readback failed" >&2; exit 5; }
    git merge-base --is-ancestor "$selected" "$now" || die "push returned 0 but canonical main does not contain selected source"
    echo "LANDED: $REMOTE $REMOTE_REF contains $selected (readback $now) in round $round"
    exit 0
  fi
  case "$(classify_push_failure "$plog")" in
    race)
      now="$(fetch_dest)" || { echo "prewarm_push: cannot confirm destination race" >&2; exit 5; }
      if [ "$now" = "$base" ] || ! git merge-base --is-ancestor "$base" "$now"; then
        echo "prewarm_push: failed push did not have a confirmed advancing destination; stopping" >&2
        exit 5
      fi
      echo "confirmed destination advance during push; aligning and retrying"
      ;;
    hook-red) echo "prewarm_push: the pre-push hook is RED; not a race. See $plog" >&2; exit 5 ;;
    *) echo "prewarm_push: genuine push failure; not a destination race. See $plog" >&2; exit 5 ;;
  esac
done
echo "prewarm_push: explicit limit $MAX_ROUNDS reached; landing INCOMPLETE; resume with --log-dir $LOG_DIR" >&2
exit 6
