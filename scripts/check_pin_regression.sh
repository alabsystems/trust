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
# WHAT IS A PAIR. A pin is paired by the submodule's IDENTITY, not only by its
# path: a tip gitlink with no pin at the same path in the base is looked up by
# its `.gitmodules` name in the base's `.gitmodules` (then by URL, taking only a
# base path the tip no longer holds). Until 2026-09-27 pairing was by path, so
# `git mv first-party/X first-party/Y` committed together with a stale X pin
# read as "removal plus addition" and rolled X back unflagged. A gitlink moved
# INTO or OUT OF first-party/ is judged as well: either side names it.
#
# WHAT A PUSH IS JUDGED AGAINST (one reading per pre-push line):
#   * an UPDATE (`<rsha>` not all zeros): the remote's current tip against the
#     pushed tip — the state the remote ref leaves for the state it takes. That
#     comparison runs even when the push introduces NO commit: a force push that
#     REWINDS a ref (the local sha an ancestor of the remote's) takes the
#     dropped pin advances off the ref, and until 2026-09-27 "introduces no
#     commits" returned OK before any pin was read. A rewind carries no commit
#     that could hold the disclosure, so a backward rewind is refused; disclose
#     it in a new commit pushed on top instead.
#   * a NEW REF (all-zero `<rsha>`): what the ref introduces beyond every ref
#     this clone tracks for the destination (`<lsha> --not --remotes=<remote>`),
#     judged against each boundary commit it grows from. A new ref at a commit
#     the remote already has introduces nothing and passes; a new branch of
#     [undisclosed backward move, unrelated commit] is refused. Until 2026-09-27
#     a new ref was compared with its first parent alone, which did both wrong.
#     The destination is TRUST_PUSH_REMOTE (git's second pre-push argument, the
#     URL) mapped back to its configured remote name, else `origin`.
#   * a base this clone does not HOLD — above all a remote tip another clone
#     pushed and this one never fetched — is UNJUDGEABLE and refused (exit 2),
#     never "no commits". `git rev-parse --verify` accepts a well-formed sha
#     without looking for the object, and until 2026-09-27 the failed rev-list
#     that followed was read as zero commits, so a force push over unfetched
#     work passed. Any other git failure while computing the subject refuses too.
#
# THE ESCAPE HATCH IS DISCLOSURE, NOT SUPPRESSION. A deliberate rollback is
# legitimate — you just have to say so in the commit message:
#
#     pin-rollback: <path> <why>
#
# There is no env-var off switch, matching the repo's gate convention.
#
# Usage:
#   check_pin_regression.sh [<base>..<tip>]   # default: origin/main..HEAD
#   check_pin_regression.sh <commit>    # judge <commit> as a NEW ref (see above)
#   check_pin_regression.sh --stdin     # read pre-push "<lref> <lsha> <rref> <rsha>" lines
#   check_pin_regression.sh --push-context  # --stdin via $TRUST_PUSHED_REFS
#   check_pin_regression.sh --selftest  # mutation-prove that the gate can FAIL
#
# Exit 0 when no undisclosed backward move exists in the range, 1 when one
# does (or a moved pin's objects are missing), 2 when the range itself cannot
# be computed in this clone.
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

# Every gitlink path at <commit> (non-zero when the tree cannot be listed).
# Not only first-party/: a gitlink renamed out of first-party/ is still one.
gitlinks_at() {
  git ls-tree -r "$1" | awk '$1 == "160000" && $2 == "commit" { sub(/^[^\t]*\t/, ""); print }'
}

# The full sha of the COMMIT <rev> names, or non-zero when this clone does not
# hold one. `^{commit}` makes git look the object up: a bare
# `rev-parse --verify <40-hex>` succeeds for an object that is not here.
commit_of() {
  git rev-parse --verify --quiet "$1^{commit}" 2>/dev/null
}

# gm_get <commit> <name> <var>: submodule.<name>.<var> in <commit>'s
# .gitmodules; empty when there is no .gitmodules or no such key, exit 2 when
# the file exists and git cannot read it.
gm_get() {
  git cat-file -e "$1:.gitmodules" 2>/dev/null || return 0
  local v rc=0
  v="$(git config --blob "$1:.gitmodules" --get "submodule.$2.$3")" || rc=$?
  case "$rc" in 0) printf '%s\n' "$v" ;; 1) ;; *) return 2 ;; esac
}

# gm_names_where <commit> <var> <value>: every submodule name whose <var> is
# exactly <value> in <commit>'s .gitmodules. -z so a name or value holding
# spaces cannot split; records are "key\nvalue", NUL-terminated.
gm_names_where() {
  git cat-file -e "$1:.gitmodules" 2>/dev/null || return 0
  local var="$2" want="$3" out rc=0 rec key val name
  out="$(git config -z --blob "$1:.gitmodules" --get-regexp "^submodule\\..*\\.${var}\$" \
           | tr '\000' '\036')" || rc=$?
  case "$rc" in 0) ;; 1) return 0 ;; *) return 2 ;; esac
  while IFS= read -r -d $'\036' rec; do
    key="${rec%%$'\n'*}"; val="${rec#*$'\n'}"
    [ "$val" = "$want" ] || continue
    name="${key#submodule.}"; name="${name%.$var}"
    printf '%s\n' "$name"
  done <<< "$out"
}

# base_paths_of <base> <tip> <path>: the path(s) at <base> that hold the SAME
# submodule as the gitlink at <path> in <tip> — the same path when <base> has a
# gitlink there, else the base path of its .gitmodules name, else (the name
# changed too) the base path of any submodule with its URL that <tip> no longer
# holds. Empty for a genuine addition; exit 2 when a .gitmodules is unreadable.
base_paths_of() {
  local base="$1" tip="$2" path="$3" name bp url cands cand
  if [ -n "$(pin_at "$base" "$path")" ]; then printf '%s\n' "$path"; return 0; fi
  name="$(gm_names_where "$tip" path "$path")" || return 2
  name="${name%%$'\n'*}"
  [ -z "$name" ] && return 0
  bp="$(gm_get "$base" "$name" path)" || return 2
  if [ -n "$bp" ] && [ -n "$(pin_at "$base" "$bp")" ]; then printf '%s\n' "$bp"; return 0; fi
  url="$(gm_get "$tip" "$name" url)" || return 2
  [ -z "$url" ] && return 0
  cands="$(gm_names_where "$base" url "$url")" || return 2
  while IFS= read -r cand <&4; do
    [ -z "$cand" ] && continue
    bp="$(gm_get "$base" "$cand" path)" || return 2
    [ -n "$bp" ] && [ "$bp" != "$path" ] || continue
    [ -n "$(pin_at "$base" "$bp")" ] || continue
    [ -z "$(pin_at "$tip" "$bp")" ] || continue      # still there: not this one
    printf '%s\n' "$bp"
  done 4<<< "$cands"
}

# disclosed <msgs> <path>...: a `pin-rollback:` line naming any of the paths.
disclosed() {
  local lines p
  lines="$(printf '%s\n' "$1" | grep -iE '^[[:space:]]*pin-rollback:' || true)"
  shift
  [ -z "$lines" ] && return 1
  for p in "$@"; do
    grep -qiF -- "$p" <<< "$lines" && return 0
  done
  return 1
}

# The destination's remote NAME, for `--remotes=`: TRUST_PUSH_REMOTE is git's
# second pre-push argument, the URL, so it is matched against every configured
# remote.<name>.url / .pushurl (taken verbatim when it already IS a name);
# several matches prefer origin; unset or unmatched falls back to origin. The
# same resolution as scripts/check_dependency_cycle_anchor.py's.
PUSH_REMOTE=""; PUSH_REMOTE_HOW=""
resolve_push_remote() {
  [ -n "$PUSH_REMOTE" ] && return 0
  local value="${TRUST_PUSH_REMOTE:-}" out rec key url name matched=""
  if [ -z "$value" ]; then
    PUSH_REMOTE=origin; PUSH_REMOTE_HOW="TRUST_PUSH_REMOTE unset; assuming origin"; return 0
  fi
  out="$(git config -z --get-regexp '^remote\..*\.(push)?url$' | tr '\000' '\036' || true)"
  while IFS= read -r -d $'\036' rec; do
    key="${rec%%$'\n'*}"; url="${rec#*$'\n'}"
    name="${key#remote.}"; name="${name%.pushurl}"; name="${name%.url}"
    if [ "$name" = "$value" ]; then
      PUSH_REMOTE="$value"; PUSH_REMOTE_HOW="TRUST_PUSH_REMOTE names remote '$value'"; return 0
    fi
    if [ "$url" = "$value" ]; then
      if [ "$name" = origin ] || [ -z "$matched" ]; then matched="$name"
      elif [ "$matched" != origin ] && [[ "$name" < "$matched" ]]; then matched="$name"; fi
    fi
  done <<< "$out"
  if [ -n "$matched" ]; then
    PUSH_REMOTE="$matched"; PUSH_REMOTE_HOW="TRUST_PUSH_REMOTE is the URL of remote '$matched'"
  else
    PUSH_REMOTE=origin; PUSH_REMOTE_HOW="TRUST_PUSH_REMOTE matches no configured remote; assuming origin"
  fi
}

# --------------------------------------------------------------------------
# judge_pins <label> <tip> <n_commits> <msgs> <base>...
#   Compare every gitlink of <tip> against its pair in each <base>; refuse an
#   undisclosed strictly-backward move against ANY base.
# --------------------------------------------------------------------------
judge_pins() {
  local label="$1" tip="$2" n_commits="$3" msgs="$4"; shift 4
  local nbases="$#" fail=0 rewind=0 n_moved=0
  local -a problems=()
  local links base tag path new pairs oldpath old shown behind ancestry_rc
  links="$(gitlinks_at "$tip")" || { echo "PIN REGRESSION: cannot list the tree of $tip ('$label')" >&2; return 2; }

  for base in "$@"; do
    tag=""; [ "$nbases" -gt 1 ] && tag="  [against ${base:0:10}]"
    while IFS= read -r path <&3; do
      [ -z "$path" ] && continue
      new="$(pin_at "$tip" "$path")"
      if ! pairs="$(base_paths_of "$base" "$tip" "$path")"; then
        problems+=("UNJUDGEABLE  $path  (a .gitmodules git cannot read; cannot pair it with ${base:0:10})")
        fail=1; continue
      fi
      while IFS= read -r oldpath <&4; do
        [ -z "$oldpath" ] && continue
        case "$path" in first-party/*) ;; *) case "$oldpath" in first-party/*) ;; *) continue ;; esac ;; esac
        old="$(pin_at "$base" "$oldpath")"
        if [ -z "$new" ] || [ -z "$old" ]; then continue; fi
        if [ "$new" = "$old" ]; then continue; fi
        n_moved=$((n_moved + 1))
        shown="$path"; [ "$oldpath" != "$path" ] && shown="$oldpath -> $path"

        if [ ! -e "$path/.git" ]; then continue; fi
        if ! git -C "$path" cat-file -e "$new" 2>/dev/null || \
           ! git -C "$path" cat-file -e "$old" 2>/dev/null; then
          problems+=("UNJUDGEABLE  $shown  (fetch it: git -C $path fetch --all)$tag")
          fail=1
          continue
        fi

        ancestry_rc=0
        git -C "$path" merge-base --is-ancestor "$new" "$old" 2>/dev/null || ancestry_rc=$?
        if [ "$ancestry_rc" -gt 1 ]; then
          problems+=("UNJUDGEABLE  $shown  (Git ancestry read failed with exit $ancestry_rc; restore its real commit history)$tag")
          fail=1
          continue
        fi
        if [ "$ancestry_rc" -eq 0 ]; then
          if disclosed "$msgs" "$path" "$oldpath"; then continue; fi
          behind="$(git -C "$path" rev-list --count "${new}..${old}" 2>/dev/null || echo '?')"
          problems+=("BACKWARD     $shown  ${old:0:10} -> ${new:0:10}  (loses $behind commit(s))$tag")
          fail=1
          [ "$n_commits" = "0" ] && rewind=1
        fi
      done 4<<< "$pairs"
    done 3<<< "$links"
  done

  if [ "$fail" -ne 0 ]; then
    echo "PIN REGRESSION: this push moves a first-party pin BACKWARD, net, with no disclosure ($label)"
    printf '  %s\n' "${problems[@]}"
    cat <<'EOF2'

  A backward pin move silently un-lands whatever the newer commits carried.
  This is usually NOT deliberate: it is what committing with stale submodule
  worktrees produces. Check before anything else:

      bash scripts/submodule_sync.sh

  If the rollback IS deliberate, say so in any commit message in the push:

      pin-rollback: <path> <why>
EOF2
    if [ "$rewind" -ne 0 ]; then
      cat <<'EOF2'

  This push REWINDS the ref: it introduces no commit, so none can carry that
  line. Push a new commit on top of the rewound tip that carries it instead.
EOF2
    fi
    return 1
  fi
  echo "PIN REGRESSION OK: $label: $n_commits commit(s), $n_moved pin move(s), none backward on net"
  return 0
}

# --------------------------------------------------------------------------
# judge_update <label> <base-rev> <tip-rev>: the remote's tip against the
# pushed tip (or an explicit <base>..<tip>). An empty side means HEAD, as in git.
# --------------------------------------------------------------------------
judge_update() {
  local label="$1" base tip n msgs
  if ! tip="$(commit_of "${3:-HEAD}")"; then
    echo "PIN REGRESSION: cannot resolve the tip of '$label' to a commit in this clone" >&2
    return 2
  fi
  if ! base="$(commit_of "${2:-HEAD}")"; then
    resolve_push_remote
    echo "PIN REGRESSION: UNJUDGEABLE '$label': its base '${2:-HEAD}' is not a commit this clone holds." >&2
    echo "  The pins the push replaces cannot be read, and an unread base is not 'no change'" >&2
    echo "  (a remote tip pushed from elsewhere and never fetched here). Fetch, then retry:" >&2
    echo "      git fetch $PUSH_REMOTE" >&2
    return 2
  fi
  if [ "$base" = "$tip" ]; then
    echo "PIN REGRESSION OK: $label: the tip does not change"
    return 0
  fi
  # A rewind (tip an ancestor of base) counts 0 and is STILL judged below.
  if ! n="$(git rev-list --count "${base}..${tip}")"; then
    echo "PIN REGRESSION: cannot list the commits of '$label'" >&2; return 2
  fi
  # Disclosure may appear in ANY commit the push introduces.
  if ! msgs="$(git log --format=%B "${base}..${tip}")"; then
    echo "PIN REGRESSION: cannot read the commit messages of '$label'" >&2; return 2
  fi
  judge_pins "$label" "$tip" "$n" "$msgs" "$base"
}

# --------------------------------------------------------------------------
# judge_new_ref <commit>: what a NEW remote ref at <commit> introduces beyond
# the destination's remote-tracking refs, against each boundary it grows from.
# --------------------------------------------------------------------------
judge_new_ref() {
  local lsha="$1" tip introduced boundary bases n msgs label
  if ! tip="$(commit_of "$lsha")"; then
    if git cat-file -e "$lsha" 2>/dev/null; then
      echo "PIN REGRESSION OK: new ref at $lsha names no commit, so it carries no pin"
      return 0
    fi
    echo "PIN REGRESSION: cannot resolve '$lsha' to an object in this clone" >&2
    return 2
  fi
  resolve_push_remote
  label="new ref at ${tip:0:10}, beyond --remotes=$PUSH_REMOTE"
  if ! introduced="$(git rev-list "$tip" --not --remotes="$PUSH_REMOTE")"; then
    echo "PIN REGRESSION: cannot list what '$label' introduces" >&2; return 2
  fi
  if [ -z "$introduced" ]; then
    echo "PIN REGRESSION OK: $label: introduces no commit ($PUSH_REMOTE_HOW)"
    return 0
  fi
  n="$(printf '%s\n' "$introduced" | grep -c .)"
  if ! boundary="$(git rev-list --boundary "$tip" --not --remotes="$PUSH_REMOTE")"; then
    echo "PIN REGRESSION: cannot list the boundary of '$label'" >&2; return 2
  fi
  bases="$(printf '%s\n' "$boundary" | sed -n 's/^-//p')"
  if [ -z "$bases" ]; then
    echo "PIN REGRESSION OK: $label: $n commit(s) sharing no history with $PUSH_REMOTE — no pin there to lose ($PUSH_REMOTE_HOW)"
    return 0
  fi
  if ! msgs="$(git log --format=%B "$tip" --not --remotes="$PUSH_REMOTE")"; then
    echo "PIN REGRESSION: cannot read the commit messages of '$label'" >&2; return 2
  fi
  local -a base_list=()
  local b
  while IFS= read -r b; do [ -n "$b" ] && base_list+=("$b"); done <<< "$bases"
  judge_pins "$label" "$tip" "$n" "$msgs" "${base_list[@]}"
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

  # The remaining cases drive the gate as the pre-push hook does (--stdin) or
  # with an explicit argument, and name the exit they want.
  verdict() {  # verdict <label> <expected-rc>
    if [ "$rc" -eq "$2" ]; then echo "  [ok ] $1"; passed=$((passed+1))
    else echo "  [BAD] $1 (rc=$rc, want $2)"; echo "$out" | sed 's/^/        /'; failed=$((failed+1)); fi
  }
  expect_arg() {  # expect_arg <label> <expected-rc> <range-or-commit>
    rc=0; out="$(cd "$super" && bash "$script" "$3" 2>&1)" || rc=$?
    verdict "$1" "$2"
  }
  expect_push() {  # expect_push <label> <expected-rc> <pre-push line> [<TRUST_PUSH_REMOTE>]
    rc=0
    out="$(cd "$super" && printf '%s\n' "$3" | TRUST_PUSH_REMOTE="${4:-}" bash "$script" --stdin 2>&1)" || rc=$?
    verdict "$1" "$2"
  }
  local zero=0000000000000000000000000000000000000000

  # REWIND: a force push whose local sha is an ANCESTOR of the remote's
  # introduces no commit, yet takes the pin advance off the ref.
  local r0; r0="$(git -C "$super" rev-parse HEAD)"      # m at c1 (the case above)
  git -C "$super" -C first-party/m checkout -q "$c2"
  git -C "$super" add first-party/m; git -C "$super" commit -qm "r1: advance m (landed work)"
  local r1; r1="$(git -C "$super" rev-parse HEAD)"
  expect_push "a force push REWINDING main past a pin advance: the gate FAILS" 1 \
    "refs/heads/main $r0 refs/heads/main $r1"
  git -C "$super" commit -q --allow-empty -m "r2: pin-neutral work"
  local r2; r2="$(git -C "$super" rev-parse HEAD)"
  expect_push "a rewind that drops only pin-neutral commits: the gate passes" 0 \
    "refs/heads/main $r1 refs/heads/main $r2"
  local r3; r3="$(git -C "$super" commit-tree "${r0}^{tree}" -p "$r0" -m "roll m back

pin-rollback: first-party/m deliberate, disclosed on top of the rewound tip")"
  expect_push "the same rewind DISCLOSED in a commit on top: the gate passes" 0 \
    "refs/heads/main $r3 refs/heads/main $r1"

  # UNFETCHED: a remote tip this clone does not hold cannot be compared with,
  # and a well-formed sha still passes `rev-parse --verify`.
  local absent=deadbeefdeadbeefdeadbeefdeadbeefdeadbeef
  expect_push "a force push over a remote tip never fetched here: UNJUDGEABLE, refused" 2 \
    "refs/heads/main $r0 refs/heads/main $absent"
  expect_arg "an explicit range whose base does not resolve: UNJUDGEABLE, not a root push" 2 \
    "no-such-ref-here..HEAD"

  # NEW REF: judged by what it introduces beyond the destination's tracked refs.
  git -C "$super" update-ref refs/remotes/origin/main "$r1"
  git -C "$super" -C first-party/m checkout -q "$c1"
  git -C "$super" add first-party/m; git -C "$super" commit -qm "A: unrelated work"
  local fa; fa="$(git -C "$super" rev-parse HEAD)"
  git -C "$super" commit -q --allow-empty -m "B: more unrelated work"
  local fb; fb="$(git -C "$super" rev-parse HEAD)"
  expect_push "a NEW branch of [undisclosed backward move, unrelated commit]: the gate FAILS" 1 \
    "refs/heads/topic $fb refs/heads/topic $zero"
  git -C "$super" remote add canon "$sub"
  git -C "$super" update-ref refs/remotes/canon/main "$fb"
  expect_push "the same new branch to a destination (named by URL) that already has it: passes" 0 \
    "refs/heads/topic $fb refs/heads/topic $zero" "$sub"
  git -C "$super" update-ref refs/remotes/origin/main "$fa"
  expect_push "a NEW tag at a backward commit the remote already has: passes (introduces nothing)" 0 \
    "refs/tags/bisect $fa refs/tags/bisect $zero"
  expect_arg "the same commit as a bare argument (a new ref): passes" 0 "$fa"

  # RENAME: a pin is paired by submodule identity, not by path.
  git -C "$super" -C first-party/m checkout -q "$c2"
  git -C "$super" add first-party/m; git -C "$super" commit -qm "n0: m at c2"
  local n0; n0="$(git -C "$super" rev-parse HEAD)"
  git -C "$super" mv first-party/m first-party/m2
  git -C "$super" -C first-party/m2 checkout -q "$c1"
  git -C "$super" add first-party/m2; git -C "$super" commit -qm "move m, stale pin swept in"
  expect_arg "a gitlink RENAMED with its pin moved backward: the gate FAILS" 1 "${n0}..HEAD"
  git -C "$super" commit -q --amend -m "move m, stale pin swept in

pin-rollback: first-party/m deliberate, disclosed under the OLD path"
  expect_arg "the same rename-and-rollback DISCLOSED under the old path: passes" 0 "${n0}..HEAD"
  git -C "$super" -C first-party/m2 checkout -q "$c2"
  git -C "$super" add first-party/m2; git -C "$super" commit -qm "n1: m2 at c2"
  local n1; n1="$(git -C "$super" rev-parse HEAD)"
  git -C "$super" mv first-party/m2 first-party/m3; git -C "$super" commit -qm "plain rename"
  expect_arg "a gitlink renamed with its pin unchanged: the gate passes" 0 "${n1}..HEAD"
  local n2; n2="$(git -C "$super" rev-parse HEAD)"
  git -C "$super" mv first-party/m3 first-party/m4
  git -C "$super" config -f "$super/.gitmodules" --rename-section submodule.first-party/m submodule.renamed
  git -C "$super" -C first-party/m4 checkout -q "$c1"
  git -C "$super" add .gitmodules first-party/m4; git -C "$super" commit -qm "rename it, name and all"
  expect_arg "renamed AND re-named (paired by URL) with its pin moved backward: the gate FAILS" 1 "${n2}..HEAD"


  # Both endpoints may exist while an intermediate parent is absent. A fatal
  # graph read is unknown ancestry, never evidence of a forward/sideways move.
  local mrepo="$super/first-party/m4" c3 base_missing object_dir missing_obj held_obj
  c3="$(git -C "$mrepo" -c user.name=Test -c user.email=t@t commit-tree "${c2}^{tree}" -p "$c2" -m "third ancestry point")"
  git -C "$mrepo" checkout -q "$c3"
  git -C "$super" add first-party/m4
  git -C "$super" commit -qm "ancestry control at third commit"
  base_missing="$(git -C "$super" rev-parse HEAD)"
  git -C "$mrepo" checkout -q "$c1"
  git -C "$super" add first-party/m4
  git -C "$super" commit -qm "retained older ancestry endpoint"
  expect_arg "complete ancestry still refuses the undisclosed rollback" 1 "${base_missing}..HEAD"
  object_dir="$(git -C "$mrepo" rev-parse --absolute-git-dir)/objects"
  missing_obj="$object_dir/${c2:0:2}/${c2:2}"
  held_obj="$super/.git/held-missing-ancestor-object"
  test -f "$missing_obj"
  mv "$missing_obj" "$held_obj"
  git -C "$mrepo" cat-file -e "${c1}^{commit}"
  git -C "$mrepo" cat-file -e "${c3}^{commit}"
  expect_arg "present endpoints with a missing intermediate commit: UNJUDGEABLE, refused" 1 "${base_missing}..HEAD"
  mv "$held_obj" "$missing_obj"
  expect_arg "restored real ancestry still refuses the same undisclosed rollback" 1 "${base_missing}..HEAD"

  echo "PIN-REGRESSION SELFTEST: $passed passed, $failed failed"
  [ "$failed" -eq 0 ]
}

# judge_arg <range-or-commit>: `A..B` (or `A...B`) is an explicit base/tip; a
# bare commit is judged as a new ref.
judge_arg() {
  case "$1" in
    *..*) judge_update "$1" "${1%%..*}" "${1##*..}" ;;
    *)    judge_new_ref "$1" ;;
  esac
}

case "${1:-}" in
  --selftest) selftest ;;
  --stdin)
    refs="$(cat 2>/dev/null || true)"
    rc=0
    if [ -z "$refs" ]; then
      judge_arg "origin/main..HEAD" || rc=$?
    else
      while read -r _lref lsha _rref rsha; do
        [ -z "${lsha:-}" ] && continue
        case "$lsha" in *[!0]*) ;; *) continue ;; esac   # deletion
        case "${rsha:-}" in
          *[!0]*) judge_update "${rsha}..${lsha}" "$rsha" "$lsha" || rc=$? ;;
          *)      judge_new_ref "$lsha" || rc=$? ;;      # new ref (all-zero or absent rsha)
        esac
      done <<< "$refs"
    fi
    exit $rc
    ;;
  "") judge_arg "origin/main..HEAD" ;;
  *)  judge_arg "$1" ;;
esac
