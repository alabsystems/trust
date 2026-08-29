#!/usr/bin/env bash
# check_pin_regression.sh — refuse a SILENT BACKWARD move of a first-party pin.
#
# THE BUG THIS EXISTS FOR (measured 2026-08-25, commit 3e9efe9aac):
#
#   A lane whose `first-party/*` worktrees were STALE committed unrelated work.
#   Staging swept the stale gitlinks in, so the commit rolled three pins back to
#   older commits — silently. Its message is about a coverage measurement and
#   mentions "pin", "submodule", "first-party" and "revert" exactly zero times.
#   The effect: a landed dependency-severance (third-party `serde` blockers
#   6 -> 2) was undone on main, and nothing said so. It was found only because
#   someone re-measured the blocker count by hand a day later.
#
# WHY NO EXISTING GATE CATCHES IT. `check_pin_coherence.sh` asks whether every
# pin RESOLVES and whether the worktree sits AT it. On the authoring machine
# both were consistently OLD, so it passed — correctly, for the question it
# asks. A backward move is invisible at a single commit: it is only a fact
# ABOUT A PAIR of commits. This gate supplies the missing comparison.
#
# WHAT IT CHECKS — the NET effect of the push, not each commit in isolation.
# For every gitlink under first-party/, compare the pin at the range's BASE
# against the pin at its TIP. Fail when the tip pin is a PROPER ANCESTOR of the
# base pin — i.e. the push, taken as a whole, moves that pin strictly backward.
#
# Why net and not per-commit: merging someone else's accidental revert and then
# restoring the pin in the next commit is exactly how this gets REPAIRED, and a
# per-commit rule flags the merge and blocks the repair. Measured — the first
# version of this gate refused the very push that fixed the second revert.
# Nothing is lost when a range reverts and re-restores, so nothing should fail.
# A range that reverts and does NOT restore still has a backward net and is
# still refused, which is the case this exists for.
#
# Forward moves, sideways moves onto an unrelated history (a deliberate re-pin),
# additions and removals are all allowed and silent: only "strictly behind"
# is refused, because only that is unambiguously a loss of landed work.
#
# THE ESCAPE HATCH IS DISCLOSURE, NOT SUPPRESSION. A deliberate rollback is
# legitimate — you just have to say so in the commit message:
#
#     pin-rollback: <path> <why>
#
# There is no env-var off switch, matching the repo's gate convention.
#
# Usage:
#   check_pin_regression.sh [<range>]   # default: origin/main..HEAD
#   check_pin_regression.sh --stdin     # read pre-push "<lref> <lsha> <rref> <rsha>" lines
#   check_pin_regression.sh --push-context  # --stdin via $TRUST_PUSHED_REFS
#   check_pin_regression.sh --selftest  # mutation-prove that the gate can FAIL
#
# Exit 0 when no undisclosed backward move exists in the range.
set -euo pipefail

# --push-context is --stdin with the ref lines taken from TRUST_PUSHED_REFS.
# A manifest command string is fixed and receives no stdin, so scripts/hooks/pre-push
# exports the refs instead and the SAME row text runs in both runners. UNSET means
# no push is in flight, and the subject WIDENS to this gate's default
# `origin/main..HEAD` reading rather than narrowing to nothing. Unset, not empty:
# an empty-but-set var is a real push with no updated refs, and --stdin already
# judges origin/main..HEAD for that case. SUBJECT: says which reading it took,
# so a `push` run outside a hook cannot be mistaken for a rehearsal of one.
if [ "${1:-}" = "--push-context" ]; then
  shift
  self="$0"; case "$self" in /*) ;; *) self="$PWD/$self" ;; esac
  if [ -n "${TRUST_PUSHED_REFS+x}" ]; then
    refcount="$(printf '%s' "$TRUST_PUSHED_REFS" | grep -c . || true)"
    echo "SUBJECT: push ($refcount ref update(s))"
    exec bash "$self" --stdin "$@" <<< "$TRUST_PUSHED_REFS"
  fi
  echo "SUBJECT: origin/main..HEAD (no push in flight; TRUST_PUSHED_REFS unset)"
  exec bash "$self" "$@"
fi

# Resolve the toplevel of the CALLER's repository, not of the script's own
# location. Anchoring on the script path hard-wires this gate to the Trust
# checkout, which makes it un-selftestable: the selftest builds a throwaway
# superproject in a tmpdir and runs the gate inside it, and an $0-anchored cd
# would send it back to Trust and "fail to enumerate" the range it was handed.
cd "$(git rev-parse --show-toplevel)"

# --------------------------------------------------------------------------
# Pin of <path> at <commit>, or empty when the path is not a gitlink there.
# --------------------------------------------------------------------------
pin_at() {
  git ls-tree "$1" -- "$2" 2>/dev/null | awk '$1 == "160000" && $2 == "commit" { print $3 }'
}

# gitlinks under first-party/ at <commit>
gitlinks_at() {
  git ls-tree -r "$1" 2>/dev/null \
    | awk '$1 == "160000" && $2 == "commit" { sub(/^[^\t]*\t/, ""); print }' \
    | grep '^first-party/' || true
}

# --------------------------------------------------------------------------
# judge_range <range>
# --------------------------------------------------------------------------
judge_range() {
  local range="$1"
  local fail=0
  local -a problems=()

  # Resolve the range's BASE and TIP. `A..B` -> base A, tip B; a bare `B` (new
  # branch) -> compare against B's first parent, or skip when B is a root.
  local base tip
  if [[ "$range" == *".."* ]]; then
    base="${range%%..*}"; tip="${range##*..}"
  else
    tip="$range"; base="$(git rev-parse --verify --quiet "${range}^1" || true)"
  fi
  tip="$(git rev-parse --verify --quiet "${tip:-HEAD}" || true)"
  [ -z "$tip" ] && { echo "PIN REGRESSION: cannot resolve tip of '$range'" >&2; return 2; }
  if [ -z "$base" ] || ! git rev-parse --verify --quiet "$base" >/dev/null; then
    echo "PIN REGRESSION OK: '$range' has no base to compare against (root push)"
    return 0
  fi
  base="$(git rev-parse --verify "$base")"

  local n_commits
  n_commits="$(git rev-list --count "${base}..${tip}" 2>/dev/null || echo 0)"
  [ "$n_commits" = "0" ] && { echo "PIN REGRESSION OK: range '$range' introduces no commits"; return 0; }

  # Disclosure may appear in ANY commit the push introduces.
  local msgs
  msgs="$(git log --format=%B "${base}..${tip}" 2>/dev/null || true)"

  local n_moved=0 path
  while IFS= read -r path; do
    [ -z "$path" ] && continue
    local new old
    new="$(pin_at "$tip" "$path")"
    old="$(pin_at "$base" "$path")"
    if [ -z "$new" ] || [ -z "$old" ]; then continue; fi
    if [ "$new" = "$old" ]; then continue; fi
    n_moved=$((n_moved + 1))

    if [ ! -e "$path/.git" ]; then continue; fi
    if ! git -C "$path" cat-file -e "$new" 2>/dev/null || \
       ! git -C "$path" cat-file -e "$old" 2>/dev/null; then
      problems+=("UNJUDGEABLE  $path  (fetch it: git -C $path fetch --all)")
      fail=1
      continue
    fi

    if git -C "$path" merge-base --is-ancestor "$new" "$old" 2>/dev/null; then
      if printf '%s' "$msgs" | grep -qiE "^[[:space:]]*pin-rollback:[[:space:]]*(.*)$path"; then
        continue
      fi
      local behind
      behind="$(git -C "$path" rev-list --count "${new}..${old}" 2>/dev/null || echo '?')"
      problems+=("BACKWARD     $path  ${old:0:10} -> ${new:0:10}  (loses $behind commit(s))")
      fail=1
    fi
  done < <(gitlinks_at "$tip")

  if [ "$fail" -ne 0 ]; then
    echo "PIN REGRESSION: this push moves a first-party pin BACKWARD, net, with no disclosure"
    printf '  %s\n' "${problems[@]}"
    cat <<'EOF'

  A backward pin move silently un-lands whatever the newer commits carried.
  This is usually NOT deliberate: it is what committing with stale submodule
  worktrees produces. Check before anything else:

      bash scripts/submodule_sync.sh

  If the rollback IS deliberate, say so in any commit message in the push:

      pin-rollback: <path> <why>
EOF
    return 1
  fi
  echo "PIN REGRESSION OK: $n_commits commit(s), $n_moved pin move(s), none backward on net"
  return 0
}

# --------------------------------------------------------------------------
# SELFTEST — the gate must be SEEN to fail, or it is decoration.
# --------------------------------------------------------------------------
selftest() {
  local sub super rc out
  sub="$(mktemp -d)"; super="$(mktemp -d)"
  trap 'rm -rf "$sub" "$super"' RETURN

  git -C "$sub" init -q; git -C "$sub" config user.email t@t; git -C "$sub" config user.name t
  echo one > "$sub/f"; git -C "$sub" add f; git -C "$sub" commit -qm one
  local c1; c1="$(git -C "$sub" rev-parse HEAD)"
  echo two > "$sub/f"; git -C "$sub" add f; git -C "$sub" commit -qm two
  local c2; c2="$(git -C "$sub" rev-parse HEAD)"

  git -C "$super" init -q; git -C "$super" config user.email t@t; git -C "$super" config user.name t
  git -C "$super" config protocol.file.allow always
  mkdir -p "$super/first-party"
  git -C "$super" -c protocol.file.allow=always submodule add -q "$sub" first-party/m 2>/dev/null
  git -C "$super" -C first-party/m checkout -q "$c2"
  git -C "$super" add first-party/m .gitmodules
  git -C "$super" commit -qm "base at c2"
  local base; base="$(git -C "$super" rev-parse HEAD)"

  # Move the pin BACKWARD, exactly as the real bug did.
  git -C "$super" -C first-party/m checkout -q "$c1"
  git -C "$super" add first-party/m
  git -C "$super" commit -qm "unrelated work"      # no disclosure

  local script; script="$(cd "$(dirname "$0")" && pwd)/$(basename "$0")"
  local passed=0 failed=0
  check() {  # check <label> <expected-rc>
    # `out="$(...)"` propagates the substitution's status, so under `set -e` a
    # non-zero run aborts the selftest BEFORE `rc=$?` is read — and a selftest
    # whose whole point is to observe a failure then dies silently at its first
    # real case. Capture the status explicitly instead.
    rc=0
    out="$(cd "$super" && bash "$script" "${base}..HEAD" 2>&1)" || rc=$?
    if [ "$rc" -eq "$2" ]; then echo "  [ok ] $1"; passed=$((passed+1))
    else echo "  [BAD] $1 (rc=$rc, want $2)"; echo "$out" | sed 's/^/        /'; failed=$((failed+1)); fi
  }

  echo "PIN-REGRESSION SELFTEST"
  check "an undisclosed backward pin move: the gate FAILS, as it must" 1

  # Disclosed: must pass.
  git -C "$super" commit -q --amend -m "unrelated work

pin-rollback: first-party/m deliberate, testing the disclosure path"
  check "the same move, DISCLOSED: the gate passes" 0

  # Forward move: must pass.
  git -C "$super" -C first-party/m checkout -q "$c2"
  git -C "$super" add first-party/m
  git -C "$super" commit -qm "advance it again"
  check "a FORWARD pin move: the gate passes" 0

  # REVERT-THEN-RESTORE in one range: net zero, nothing lost, must PASS. This is
  # the case that motivated net semantics — a per-commit rule flags the revert
  # commit and blocks the very push that repairs it.
  local base2; base2="$(git -C "$super" rev-parse HEAD)"
  git -C "$super" -C first-party/m checkout -q "$c1"
  git -C "$super" add first-party/m; git -C "$super" commit -qm "someone reverts it"
  git -C "$super" -C first-party/m checkout -q "$c2"
  git -C "$super" add first-party/m; git -C "$super" commit -qm "and I restore it"
  rc=0; out="$(cd "$super" && bash "$script" "${base2}..HEAD" 2>&1)" || rc=$?
  if [ "$rc" -eq 0 ]; then echo "  [ok ] revert THEN restore in one push: the gate passes (net zero)"; passed=$((passed+1))
  else echo "  [BAD] revert-then-restore should pass (rc=$rc)"; echo "$out" | sed 's/^/        /'; failed=$((failed+1)); fi

  # And a revert that is NOT restored in the same range must still FAIL.
  local base3; base3="$(git -C "$super" rev-parse HEAD)"
  git -C "$super" -C first-party/m checkout -q "$c1"
  git -C "$super" add first-party/m; git -C "$super" commit -qm "revert, unrepaired"
  git -C "$super" commit -q --allow-empty -m "some later unrelated work"
  rc=0; out="$(cd "$super" && bash "$script" "${base3}..HEAD" 2>&1)" || rc=$?
  if [ "$rc" -eq 1 ]; then echo "  [ok ] revert left UNREPAIRED across the range: the gate FAILS, as it must"; passed=$((passed+1))
  else echo "  [BAD] unrepaired revert should fail (rc=$rc)"; echo "$out" | sed 's/^/        /'; failed=$((failed+1)); fi

  echo "PIN-REGRESSION SELFTEST: $passed passed, $failed failed"
  [ "$failed" -eq 0 ]
}

case "${1:-}" in
  --selftest) selftest ;;
  --stdin)
    refs="$(cat 2>/dev/null || true)"
    rc=0
    if [ -z "$refs" ]; then
      judge_range "origin/main..HEAD" || rc=$?
    else
      while read -r _lref lsha _rref rsha; do
        [ -z "${lsha:-}" ] && continue
        case "$lsha" in *[!0]*) ;; *) continue ;; esac   # deletion
        if [ -z "${rsha:-}" ] || [ "$rsha" = "0000000000000000000000000000000000000000" ]; then
          judge_range "$lsha" || rc=$?
        else
          judge_range "${rsha}..${lsha}" || rc=$?
        fi
      done <<< "$refs"
    fi
    exit $rc
    ;;
  "") judge_range "origin/main..HEAD" ;;
  *)  judge_range "$1" ;;
esac
