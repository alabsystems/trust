#!/usr/bin/env bash
# submodule_sync.sh — do the submodule WORKTREES match the pins recorded at HEAD?
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHY THIS EXISTS
# ---------------
# A superproject gitlink is a pointer, and `git pull --rebase` moves the pointer
# without moving the worktree. Lanes bump `first-party/*` pins in superproject
# commits; every other lane then rebases onto those commits and its submodule
# worktrees silently stay where they were. The next build fails somewhere deep in
# the compiler with what reads like a source bug — the canonical one being
#
#     compiler/rustc_parse/src/parser/item.rs:59
#     error: no variant named `Codata` found for `SurfaceDecl`
#
# which is not a source bug at all: it is "your first-party/clean checkout is 396
# commits behind the pin". Diagnosed three times in one day, each time by an
# agent reading Rust instead of reading `git submodule status`. Full history:
# reports/submodule-pin-drift.md.
#
# WHAT THIS DOES THAT `git submodule status` DOES NOT
# ---------------------------------------------------
# `git submodule status` prints a bare `+` for "differs from the pin". That single
# character covers three situations with opposite correct responses:
#
#   BEHIND     the worktree is an ancestor of the pin. Restoring is lossless —
#              every commit on disk is already contained in the pin.
#   AHEAD      the pin is an ancestor of the worktree. The worktree holds commits
#              the pin does not. Restoring MOVES OFF unlanded work.
#   DIVERGENT  both sides hold commits the other lacks. Restoring discards the
#              worktree's side.
#
# BEHIND is always safe to automate. This script separates the three, counts the
# commits, and prints the exact command for the safe subset only. That separation
# is the whole safety property of this tool; scripts/tests/submodule_sync_test.sh
# proves it against a purpose-built fixture that contains every state at once.
#
# ANCHORED — the second provably-lossless case
# --------------------------------------------
# "Restoring loses work" is a claim about DESTRUCTION, not about ancestry. A
# worktree commit that the pin lacks is destroyed by a checkout only if nothing
# else holds it. If a durable ref holds it, the checkout moves a pointer and the
# commit stays fetchable by sha forever.
#
# That case is not hypothetical: it was hit three times in one day, always the
# same superseded `chore(deps): pin ay ...` commit, always already anchored on a
# `refs/pins/<sha>` ref on the remote (put there by
# scripts/audit_first_party_pins.py --anchor). Each time a human read the AHEAD
# classification, listed the commits, ran `git ls-remote origin 'refs/pins/*'`,
# concluded it was safe, and bypassed this tool's own --restore by hand. A safety
# tool that must be overridden by hand on its most common case teaches people to
# override it, which is how the guard stops working. So the rule is encoded here.
#
# ANCHORED is a FLAG on AHEAD/DIVERGENT, not a replacement state, because the two
# answer different questions and one is not derivable from the other:
#   * the state is TOPOLOGY — cheap, local, deterministic, and it is what the
#     ahead/behind counts describe. Collapsing AHEAD and DIVERGENT into one
#     ANCHORED row would delete the fact that a DIVERGENT module also LACKS
#     commits the pin has, which is a different (still real) hazard.
#   * anchoring is RECOVERABILITY — it depends on refs that a `git gc`, a `git
#     tag -d`, or a force-push can change under you, and on a remote read that
#     can fail. It is a property of the moment, so it is reported as one.
# `--json` therefore keeps `"state":"AHEAD"` and adds `"anchored":1`.
#
# THE SAFETY PREDICATE, exactly
#   Let U = `git rev-list <ondisk> ^<pin>` — EVERY commit the worktree has and the
#   pin lacks, not just HEAD. The module is ANCHORED iff
#     (1) U is non-empty and enumerable, AND
#     (2) the worktree is clean (uncommitted work is in no commit, so no ref can
#         hold it — dirty is never anchored), AND
#     (3) for EVERY c in U, at least one of:
#           a. some ref in this submodule's own ref namespace contains c
#              (`git for-each-ref --contains c` over refs/heads, refs/tags,
#              refs/remotes, refs/pins, ...). HEAD is deliberately NOT a ref for
#              this purpose: HEAD is precisely what a restore moves.
#           b. the module's remote advertises a `refs/pins/*` ref that points at
#              c, or that points at a commit which is present locally and has c
#              as an ancestor.
#   ONE unanchored commit in U means the module is NOT anchored and stays in the
#   needs-a-human list, with the offending commit named. Any failure to read the
#   remote fails CLOSED: not anchored, and the report says the read failed.
#
# COST
#   The remote read (`git ls-remote --refs <remote> 'refs/pins/*'`) happens only
#   on the drifted-AND-ahead path, only for commits that no local ref already
#   holds, and is cached per remote URL per run. The all-synced path — the
#   overwhelmingly common one — issues no network call at all and is unchanged.
#
# USAGE
#   scripts/submodule_sync.sh              classify and report (default)
#   scripts/submodule_sync.sh --quiet      one line, for hooks and prompts
#   scripts/submodule_sync.sh --json       machine-readable records
#   scripts/submodule_sync.sh --restore    check out ONLY the provably-lossless ones
#   scripts/submodule_sync.sh --root DIR   operate on DIR's superproject (self-test)
#   scripts/submodule_sync.sh --offline    never touch the network; unanchored-unless
#                                          a LOCAL ref proves it (fail closed)
#   scripts/submodule_sync.sh --restore --force   restore even while a build runs
#
# EXIT CODES
#   0  every submodule worktree is at its recorded pin
#   1  drift, and every drifted module is provably lossless to restore
#      (BEHIND, or AHEAD/DIVERGENT with every unique commit ANCHORED)
#   2  drift, and at least one module needs a human (UNANCHORED AHEAD /
#      DIVERGENT / dirty / unrelated / pin object missing locally)
#   3  usage or environment error
#   4  --restore refused: a build appears to be running against this repo
#
# NEVER run x.py to test this. Use `cargo check --locked` (see
# reports/submodule-pin-drift.md §4 for the bootstrap environment it needs).

set -uo pipefail

usage() {
  sed -n '/^# USAGE/,/^#   4 /p' "$0" | sed 's/^# \{0,1\}//'
}

MODE="report"
FORCE=0
OFFLINE=0
ROOT_ARG=""
while [ "$#" -gt 0 ]; do
  case "$1" in
    --quiet|-q)   MODE="quiet" ;;
    --json)       MODE="json" ;;
    --restore)    MODE="restore" ;;
    --force)      FORCE=1 ;;
    --offline)    OFFLINE=1 ;;
    --root)       ROOT_ARG="${2:-}"; shift ;;
    --root=*)     ROOT_ARG="${1#--root=}" ;;
    -h|--help)    usage; exit 0 ;;
    *) echo "submodule_sync: unknown argument '$1'" >&2; usage >&2; exit 3 ;;
  esac
  shift
done

# Resolve against the SCRIPT's repository, not $PWD: "am I at the pins" is a
# question about the superproject, and an agent that asks it from inside
# first-party/clean means the superproject too. `--root` exists so the self-test
# can drive this same code path against a fixture.
if [ -n "$ROOT_ARG" ]; then
  ROOT="$(git -C "$ROOT_ARG" rev-parse --show-toplevel 2>/dev/null)"
else
  ROOT="$(git -C "$(dirname "${BASH_SOURCE[0]}")" rev-parse --show-toplevel 2>/dev/null)"
fi
if [ -z "$ROOT" ]; then
  echo "submodule_sync: not inside a git repository" >&2
  exit 3
fi
cd "$ROOT" || exit 3

# ---------------------------------------------------------------------------
# Classification
#
# Records are TAB-separated and held in one indexed array: macOS ships bash 3.2,
# which has no associative arrays, and this script must run on the machine that
# has the problem rather than on a hypothetical newer shell.
#
# fields: display parent rel state ahead behind ondisk pin dirty anchored note
#
# NO FIELD IS EVER EMPTY — "-" stands in. TAB is an IFS *whitespace* character,
# so a run of tabs collapses into one delimiter and an empty field would silently
# shift every field after it.
# ---------------------------------------------------------------------------
RECORDS=()
TAB=$'\t'

# ---------------------------------------------------------------------------
# Durable-ref anchoring (see "ANCHORED" in the header for the exact predicate)
# ---------------------------------------------------------------------------
NET_UNREACHABLE="!UNREACHABLE"
NET_TIMEOUT="${SUBMODULE_SYNC_NET_TIMEOUT:-20}"
NET_CACHE_URLS=()
NET_CACHE_REFS=()
TIMEOUT_BIN=""
for _cand in timeout gtimeout; do
  if command -v "$_cand" >/dev/null 2>&1; then TIMEOUT_BIN="$_cand"; break; fi
done

# A hung remote must not hang the tool a human runs before every build. Bound it
# where a bound is available, and never let git open an interactive prompt.
net_git() {
  if [ -n "$TIMEOUT_BIN" ]; then
    "$TIMEOUT_BIN" "$NET_TIMEOUT" env GIT_TERMINAL_PROMPT=0 git "$@"
  else
    env GIT_TERMINAL_PROMPT=0 git "$@"
  fi
}

module_remote() { # <moddir> -> "<name> <url>", empty if the module has no remote
  local moddir="$1" names name url
  names="$(git -C "$moddir" remote 2>/dev/null)"
  [ -n "$names" ] || return 1
  if printf '%s\n' "$names" | grep -qx 'origin'; then
    name="origin"
  else
    name="$(printf '%s\n' "$names" | head -1)"
  fi
  url="$(git -C "$moddir" remote get-url "$name" 2>/dev/null)"
  [ -n "$url" ] || url="$name"
  printf '%s %s' "$name" "$url"
}

# These three return through globals, never through `$(...)`. A command
# substitution is a subshell, and a cache that a subshell writes dies with it —
# which is the difference between one ls-remote per remote and one per module.
REMOTE_PINS_OUT=""
ANCHORED_OUT=0
ANCHOR_NOTE_OUT="-"

remote_pins_for() { # <moddir> <remote-name> <url> -> REMOTE_PINS_OUT
  # Cached per remote URL per run: several modules share a forge, and the cost
  # this function exists to control is the round trip, not the parsing.
  local moddir="$1" name="$2" url="$3"
  local i=0 n="${#NET_CACHE_URLS[@]}" out rc
  while [ "$i" -lt "$n" ]; do
    if [ "${NET_CACHE_URLS[$i]}" = "$url" ]; then
      REMOTE_PINS_OUT="${NET_CACHE_REFS[$i]}"
      return 0
    fi
    i=$((i + 1))
  done

  if [ "$OFFLINE" -eq 1 ]; then
    out="$NET_UNREACHABLE"
  else
    [ -z "${SUBMODULE_SYNC_TRACE_NET:-}" ] || echo "net: ls-remote $url" >&2
    out="$(net_git -C "$moddir" ls-remote --refs "$name" 'refs/pins/*' 2>/dev/null \
           | awk 'NF >= 2 { print $1, $2 }')"
    rc=$?
    # Fail CLOSED. A remote that cannot be read is not a remote that said yes.
    [ "$rc" -eq 0 ] || out="$NET_UNREACHABLE"
  fi
  NET_CACHE_URLS+=("$url")
  NET_CACHE_REFS+=("$out")
  REMOTE_PINS_OUT="$out"
}

match_remote_pin() { # <moddir> <commit> <pin-lines> -> the anchoring ref, or empty
  local moddir="$1" c="$2" lines="$3" sha name
  [ -n "$lines" ] || return 1
  # Exact hit first: `--anchor` pushes <sha>:refs/pins/<sha>, so the common case
  # is decided without touching the object store.
  while IFS=' ' read -r sha name; do
    [ -n "$sha" ] || continue
    if [ "$sha" = "$c" ]; then printf 'remote %s' "$name"; return 0; fi
  done <<EOF
$lines
EOF
  # Otherwise the pin ref may be a descendant. Containment on the remote is not
  # computable from an ls-remote alone, so this only claims it for tips whose
  # objects are present locally, where ancestry is a fact and not a guess.
  # One batch-check decides which those are; a fork per advertised ref would
  # make a repo with many anchors quadratically expensive to classify.
  local have
  have="$(printf '%s\n' "$lines" | awk '{print $1}' \
          | git -C "$moddir" cat-file --batch-check='%(objectname) %(objecttype)' 2>/dev/null \
          | awk '$2 == "commit" { printf "%s ", $1 }')"
  [ -n "$have" ] || return 1
  while IFS=' ' read -r sha name; do
    [ -n "$sha" ] || continue
    case " $have " in *" $sha "*) ;; *) continue ;; esac
    if git -C "$moddir" merge-base --is-ancestor "$c" "$sha" 2>/dev/null; then
      printf 'remote %s (contains it)' "$name"
      return 0
    fi
  done <<EOF
$lines
EOF
  return 1
}

anchor_check() { # <moddir> <ondisk> <pin> -> ANCHORED_OUT, ANCHOR_NOTE_OUT
  local moddir="$1" ondisk="$2" pin="$3"
  local uniques c ref evidence="" unresolved="" pair rname rurl pins hit suffix=""

  ANCHORED_OUT=0
  ANCHOR_NOTE_OUT="-"

  # EVERY commit the worktree has and the pin lacks — not just HEAD. This
  # enumeration is the safety property; a shortcut here is the whole bug.
  uniques="$(git -C "$moddir" rev-list "$ondisk" "^$pin" 2>/dev/null)"
  if [ -z "$uniques" ]; then
    ANCHOR_NOTE_OUT="the unique-commit list could not be enumerated"
    return
  fi

  for c in $uniques; do
    ref="$(git -C "$moddir" for-each-ref --contains "$c" --count=1 \
             --format='%(refname)' 2>/dev/null)"
    if [ -n "$ref" ]; then
      evidence="${evidence}${c} ${ref};"
    else
      unresolved="${unresolved}${c} "
    fi
  done

  if [ -n "$unresolved" ]; then
    # Only now is the network worth a round trip — and only for the commits no
    # local ref already holds.
    pair="$(module_remote "$moddir")"
    if [ -z "$pair" ]; then
      ANCHOR_NOTE_OUT="$(printf '%.8s is on no local ref and the module has no remote to check refs/pins/* on' \
        "$(printf '%s' "$unresolved" | awk '{print $1}')")"
      return
    fi
    rname="${pair%% *}"; rurl="${pair#* }"
    remote_pins_for "$moddir" "$rname" "$rurl"
    pins="$REMOTE_PINS_OUT"
    if [ "$pins" = "$NET_UNREACHABLE" ]; then
      [ "$OFFLINE" -eq 0 ] || suffix=" (--offline: no probe attempted)"
      ANCHOR_NOTE_OUT="NOT ANCHORED, fail-closed: could not read refs/pins/* from ${rname} <${rurl}>${suffix}"
      return
    fi
    for c in $unresolved; do
      hit="$(match_remote_pin "$moddir" "$c" "$pins")"
      if [ -z "$hit" ]; then
        ANCHOR_NOTE_OUT="$(printf '%.8s is held by no local ref and by no refs/pins/* ref on %s' "$c" "$rname")"
        return
      fi
      evidence="${evidence}${c} ${hit};"
    done
  fi

  ANCHORED_OUT=1
  ANCHOR_NOTE_OUT="$evidence"
}

classify_one() {
  local parent="$1" rel="$2" display="$3"
  local pin ondisk state ahead behind dirty counts anchored anote

  pin="$(git -C "$parent" ls-tree HEAD -- "$rel" 2>/dev/null | awk '$2 == "commit" { print $3 }')"
  if [ -z "$pin" ]; then
    # No gitlink at HEAD. Either the path is not a submodule at this commit (the
    # `first-party/trust` symlink is exactly this case) or the gitlink was removed.
    RECORDS+=("${display}${TAB}${parent}${TAB}${rel}${TAB}NO-GITLINK${TAB}0${TAB}0${TAB}-${TAB}-${TAB}0${TAB}0${TAB}-")
    return
  fi

  if [ ! -e "$parent/$rel/.git" ]; then
    RECORDS+=("${display}${TAB}${parent}${TAB}${rel}${TAB}ABSENT${TAB}0${TAB}0${TAB}-${TAB}${pin}${TAB}0${TAB}0${TAB}-")
    return
  fi

  ondisk="$(git -C "$parent/$rel" rev-parse HEAD 2>/dev/null)"
  if [ -z "$ondisk" ]; then
    RECORDS+=("${display}${TAB}${parent}${TAB}${rel}${TAB}NO-HEAD${TAB}0${TAB}0${TAB}-${TAB}${pin}${TAB}0${TAB}0${TAB}-")
    return
  fi

  if [ "$ondisk" = "$pin" ]; then
    # Synced. Deliberately skip the dirty probe here: `git status` is the
    # expensive call (~0.1-0.2s per module) and local edits on a module that is
    # AT its pin are nobody's drift problem. Skipping keeps the all-synced case
    # — the overwhelmingly common one — free of both `git status` and, since the
    # anchor probe hangs off `ahead > 0`, of any network call whatsoever.
    RECORDS+=("${display}${TAB}${parent}${TAB}${rel}${TAB}SYNCED${TAB}0${TAB}0${TAB}${ondisk}${TAB}${pin}${TAB}0${TAB}0${TAB}-")
    return
  fi

  # Drifted. From here on accuracy outweighs speed.
  dirty="$(git -C "$parent/$rel" status --porcelain 2>/dev/null | wc -l | tr -d ' ')"

  if ! git -C "$parent/$rel" cat-file -e "${pin}^{commit}" 2>/dev/null; then
    # The recorded pin is not in the local object store, so ancestry cannot be
    # computed at all and no restore can be attempted without a fetch (a write).
    RECORDS+=("${display}${TAB}${parent}${TAB}${rel}${TAB}PIN-MISSING${TAB}0${TAB}0${TAB}${ondisk}${TAB}${pin}${TAB}${dirty}${TAB}0${TAB}-")
    return
  fi

  if ! git -C "$parent/$rel" merge-base "$ondisk" "$pin" >/dev/null 2>&1; then
    # No merge base: `rev-list ondisk ^pin` would be the module's ENTIRE history,
    # so "is every unique commit anchored" is not the question anyone is asking.
    # Left as needs-a-human, exactly as before.
    RECORDS+=("${display}${TAB}${parent}${TAB}${rel}${TAB}UNRELATED${TAB}0${TAB}0${TAB}${ondisk}${TAB}${pin}${TAB}${dirty}${TAB}0${TAB}-")
    return
  fi

  # left = reachable from the worktree but not the pin (AHEAD of the pin)
  # right = reachable from the pin but not the worktree (BEHIND the pin)
  counts="$(git -C "$parent/$rel" rev-list --left-right --count "${ondisk}...${pin}" 2>/dev/null)"
  ahead="$(printf '%s' "$counts" | awk '{print $1}')"
  behind="$(printf '%s' "$counts" | awk '{print $2}')"
  [ -n "$ahead" ] || ahead=0
  [ -n "$behind" ] || behind=0

  if [ "$ahead" -gt 0 ] && [ "$behind" -gt 0 ]; then
    state="DIVERGENT"
  elif [ "$ahead" -gt 0 ]; then
    state="AHEAD"
  else
    state="BEHIND"
  fi

  # The anchor probe — the only path that may touch the network — is gated on
  # `ahead > 0`: with no unique commits there is nothing that could be lost, and
  # BEHIND is already covered by ancestry.
  anchored=0
  anote="-"
  if [ "$ahead" -gt 0 ]; then
    if [ "$dirty" -ne 0 ]; then
      # Uncommitted work lives in no commit, so no ref can hold it. Not anchored,
      # and not worth a round trip to find that out.
      anote="${dirty} uncommitted change(s) exist in no commit, so no ref can hold them"
    else
      anchor_check "$parent/$rel" "$ondisk" "$pin"
      anchored="$ANCHORED_OUT"
      anote="$ANCHOR_NOTE_OUT"
      [ -n "$anote" ] || anote="-"
      [ "$anchored" = "1" ] || anchored=0
    fi
  fi

  RECORDS+=("${display}${TAB}${parent}${TAB}${rel}${TAB}${state}${TAB}${ahead}${TAB}${behind}${TAB}${ondisk}${TAB}${pin}${TAB}${dirty}${TAB}${anchored}${TAB}${anote}")
}

walk() {
  local parent="$1" prefix="$2"
  local rel display
  [ -f "$parent/.gitmodules" ] || return 0
  while IFS= read -r rel; do
    [ -n "$rel" ] || continue
    if [ -n "$prefix" ]; then display="$prefix/$rel"; else display="$rel"; fi
    classify_one "$parent" "$rel" "$display"
    # Recurse so that a `--recursive` restore is never recommended blind: a
    # nested module that is itself AHEAD must not be swept up by a parent's
    # checkout. trust-cg carries three of these (third_party/*).
    if [ -e "$parent/$rel/.git" ]; then
      walk "$parent/$rel" "$display"
    fi
  done < <(git -C "$parent" config --file "$parent/.gitmodules" \
             --get-regexp 'submodule\..*\.path' 2>/dev/null | awk '{print $2}')
}

walk "$ROOT" ""

if [ "${#RECORDS[@]}" -eq 0 ]; then
  echo "submodule_sync: no submodules recorded in .gitmodules" >&2
  exit 3
fi

# ---------------------------------------------------------------------------
# Tally
# ---------------------------------------------------------------------------
# Pure-bash field split. `cut` in a subshell is correct but this is called on the
# order of a hundred times per run, and a hundred forks is most of the runtime of
# a tool whose entire premise is that it is too cheap to skip.
field() {
  local rec="$1" n="$2" oldifs="$IFS" parts
  set -f
  IFS="$TAB"
  parts=($rec)
  IFS="$oldifs"
  set +f
  printf '%s' "${parts[$((n - 1))]}"
}

# Split evidence/reason text (";"-joined "sha ref" items) into printable lines.
anchor_lines() { # <rec> <indent>
  local rec="$1" ind="$2" note entry oldifs
  note="$(field "$rec" 11)"
  [ "$note" != "-" ] || return 0
  oldifs="$IFS"
  set -f
  IFS=';'
  for entry in $note; do
    [ -n "$entry" ] || continue
    printf '%s%s\n' "$ind" "$entry"
  done
  IFS="$oldifs"
  set +f
}

TOTAL=0; N_SYNCED=0; N_DRIFT=0; N_SAFE=0; N_REVIEW=0; N_ANCHORED=0
SAFE_ROWS=(); REVIEW_ROWS=(); DRIFT_ROWS=()

for rec in "${RECORDS[@]}"; do
  state="$(field "$rec" 4)"
  dirty="$(field "$rec" 9)"
  TOTAL=$((TOTAL + 1))
  case "$state" in
    SYNCED)
      N_SYNCED=$((N_SYNCED + 1))
      ;;
    NO-GITLINK)
      # Not a submodule at this commit; not drift. Counted as neither.
      TOTAL=$((TOTAL - 1))
      ;;
    BEHIND)
      N_DRIFT=$((N_DRIFT + 1)); DRIFT_ROWS+=("$rec")
      if [ "$dirty" -eq 0 ]; then
        N_SAFE=$((N_SAFE + 1)); SAFE_ROWS+=("$rec")
      else
        N_REVIEW=$((N_REVIEW + 1)); REVIEW_ROWS+=("$rec")
      fi
      ;;
    ABSENT)
      # Never checked out. `--init` is the intended repair and cannot lose work,
      # because there is no worktree to lose.
      N_DRIFT=$((N_DRIFT + 1)); DRIFT_ROWS+=("$rec")
      N_SAFE=$((N_SAFE + 1)); SAFE_ROWS+=("$rec")
      ;;
    AHEAD|DIVERGENT)
      # The worktree holds commits the pin lacks. Restorable ONLY if every one of
      # them is held by a durable ref (field 10), which also implies a clean
      # worktree — see anchor_check. Anything else is unchanged from before: it
      # needs a human.
      N_DRIFT=$((N_DRIFT + 1)); DRIFT_ROWS+=("$rec")
      if [ "$(field "$rec" 10)" = "1" ]; then
        N_SAFE=$((N_SAFE + 1)); SAFE_ROWS+=("$rec")
        N_ANCHORED=$((N_ANCHORED + 1))
      else
        N_REVIEW=$((N_REVIEW + 1)); REVIEW_ROWS+=("$rec")
      fi
      ;;
    *)
      N_DRIFT=$((N_DRIFT + 1)); DRIFT_ROWS+=("$rec")
      N_REVIEW=$((N_REVIEW + 1)); REVIEW_ROWS+=("$rec")
      ;;
  esac
done

if [ "$N_DRIFT" -eq 0 ]; then
  RC=0
elif [ "$N_REVIEW" -eq 0 ]; then
  RC=1
else
  RC=2
fi

restore_cmd_for() {
  # One explicit path per invocation, run from the module's own parent. No bare
  # repo-wide `git submodule update`, and no `--recursive`: both would sweep in
  # modules this script has not cleared, which is precisely the mistake the
  # BEHIND/AHEAD split exists to prevent.
  local rec="$1" parent rel
  parent="$(field "$rec" 2)"; rel="$(field "$rec" 3)"
  if [ "$parent" = "$ROOT" ]; then
    printf '    git -C %s submodule update --init -- %s\n' "$ROOT" "$rel"
  else
    printf '    git -C %s submodule update --init -- %s\n' "$parent" "$rel"
  fi
}

# ---------------------------------------------------------------------------
# Output
# ---------------------------------------------------------------------------
emit_json() {
  # v2 adds "anchored" and "anchor_detail". The state field is unchanged on
  # purpose: a consumer that matches "state":"AHEAD" keeps working, and learns
  # about recoverability from a field it can choose to read.
  local first=1 rec note
  printf '{"schema":"trust.submodule-sync.v2","root":"%s","total":%d,"synced":%d,"drifted":%d,"restorable":%d,"anchored":%d,"needs_review":%d,"exit":%d,"modules":[' \
    "$ROOT" "$TOTAL" "$N_SYNCED" "$N_DRIFT" "$N_SAFE" "$N_ANCHORED" "$N_REVIEW" "$RC"
  for rec in "${RECORDS[@]}"; do
    [ "$first" -eq 1 ] || printf ','
    first=0
    note="$(field "$rec" 11)"
    note="${note//\\/ }"
    note="${note//\"/\'}"
    printf '{"path":"%s","state":"%s","ahead":%s,"behind":%s,"worktree":"%s","pin":"%s","dirty":%s,"anchored":%s,"anchor_detail":"%s"}' \
      "$(field "$rec" 1)" "$(field "$rec" 4)" "$(field "$rec" 5)" "$(field "$rec" 6)" \
      "$(field "$rec" 7)" "$(field "$rec" 8)" "$(field "$rec" 9)" "$(field "$rec" 10)" "$note"
  done
  printf ']}\n'
}

emit_quiet() {
  local anch=""
  [ "$N_ANCHORED" -eq 0 ] || anch=", ${N_ANCHORED} of them ANCHORED"
  if [ "$RC" -eq 0 ]; then
    echo "submodule sync: OK — $N_SYNCED/$TOTAL worktrees at their recorded pins."
  else
    echo "submodule sync: DRIFT — $N_DRIFT/$TOTAL worktrees disagree with the pins recorded at HEAD (${N_SAFE} restorable${anch}, ${N_REVIEW} needing review). Run: scripts/submodule_sync.sh"
  fi
}

emit_report() {
  if [ "$RC" -eq 0 ]; then
    echo "submodule sync: OK — all $TOTAL submodule worktrees are at the pins recorded at HEAD."
    return
  fi

  echo "submodule sync: DRIFT"
  echo
  echo "  $N_DRIFT of $TOTAL submodule worktrees disagree with the pins recorded at"
  echo "  superproject HEAD. Until this is resolved, a build compiles source that is"
  echo "  NOT the source the pins name, and any error it reports may be an artifact"
  echo "  of the drift rather than a real defect."
  echo
  printf '  %-34s %-14s %-22s %s\n' "MODULE" "STATE" "DELTA" "WORKTREE -> PIN"
  printf '  %-34s %-14s %-22s %s\n' "----------------------------------" "--------------" "----------------------" "--------------------"
  local rec state ahead behind delta note
  for rec in "${DRIFT_ROWS[@]}"; do
    state="$(field "$rec" 4)"; ahead="$(field "$rec" 5)"; behind="$(field "$rec" 6)"
    case "$state" in
      BEHIND)      delta="${behind} behind" ;;
      AHEAD)       delta="${ahead} ahead" ;;
      DIVERGENT)   delta="${ahead} ahead, ${behind} behind" ;;
      ABSENT)      delta="not checked out" ;;
      PIN-MISSING) delta="pin not in object store" ;;
      *)           delta="-" ;;
    esac
    [ "$(field "$rec" 10)" = "1" ] && state="${state}+ANCH"
    [ "$(field "$rec" 9)" -eq 0 ] 2>/dev/null && note="" || note="  +$(field "$rec" 9) dirty"
    printf '  %-34s %-14s %-22s %.8s -> %.8s%s\n' \
      "$(field "$rec" 1)" "$state" "$delta" \
      "$(field "$rec" 7)" "$(field "$rec" 8)" "$note"
  done
  echo

  if [ "${#SAFE_ROWS[@]}" -gt 0 ]; then
    echo "  RESTORABLE — provably lossless. Either the worktree is an ancestor of the"
    echo "  pin (every commit on disk is already contained in it), or it is ANCHORED:"
    echo "  it holds commits the pin lacks, but EVERY ONE of them is held by a durable"
    echo "  ref, so moving HEAD to the pin destroys nothing."
    echo
    for rec in "${SAFE_ROWS[@]}"; do
      if [ "$(field "$rec" 10)" = "1" ]; then
        printf '    %s  [%s, ANCHORED]  — %s commit(s) the pin lacks, each held by:\n' \
          "$(field "$rec" 1)" "$(field "$rec" 4)" "$(field "$rec" 5)"
        anchor_lines "$rec" "        "
      fi
      restore_cmd_for "$rec"
    done
    echo
    echo "  or let this script do exactly that set and nothing else:"
    echo
    echo "    scripts/submodule_sync.sh --restore"
    echo
  fi

  if [ "${#REVIEW_ROWS[@]}" -gt 0 ]; then
    echo "  NEEDS A HUMAN — do NOT auto-restore these. Each holds something the pin"
    echo "  does not, or cannot be reasoned about without a network fetch:"
    echo
    for rec in "${REVIEW_ROWS[@]}"; do
      state="$(field "$rec" 4)"
      printf '    %s  [%s]\n' "$(field "$rec" 1)" "$state"
      case "$state" in
        AHEAD)
          printf '      %s commits exist only on the worktree side.\n' "$(field "$rec" 5)"
          printf '      NOT ANCHORED: %s\n' "$(field "$rec" 11)"
          printf '      inspect:  git -C %s log --oneline %.8s..%.8s\n' \
            "$(field "$rec" 2)/$(field "$rec" 3)" "$(field "$rec" 8)" "$(field "$rec" 7)"
          printf '      Restoring is only correct if those commits are landed elsewhere\n'
          printf '      or genuinely unwanted. That is a judgement, not a script.\n'
          ;;
        DIVERGENT)
          printf '      %s commits only on the worktree, %s only on the pin.\n' "$(field "$rec" 5)" "$(field "$rec" 6)"
          printf '      NOT ANCHORED: %s\n' "$(field "$rec" 11)"
          printf '      inspect:  git -C %s log --oneline --left-right %.8s...%.8s\n' \
            "$(field "$rec" 2)/$(field "$rec" 3)" "$(field "$rec" 7)" "$(field "$rec" 8)"
          ;;
        PIN-MISSING)
          printf '      The pin is absent from the local object store; ancestry is not\n'
          printf '      computable and no restore is possible without a fetch (a write).\n'
          # `fetch --all` is the WRONG advice here and used to be what this said.
          # It fetches each remote's default refspec — branches — and a pin that
          # needs this branch of the code is typically one that is on NO branch:
          # that is exactly what `audit_first_party_pins.py --anchor` exists for,
          # parking such commits under `refs/pins/*`. Measured 2026-08-30 on
          # first-party/ay b851ff38: `fetch --all` returned 0 and left the object
          # still absent, so the report kept saying PIN-MISSING after the reader
          # had done what it asked. Fetch the sha, which works whether the commit
          # is on a branch, on an anchor ref, or reachable only by identity.
          printf '      inspect:  git -C %s fetch origin %s\n' \
            "$(field "$rec" 2)/$(field "$rec" 3)" "$(field "$rec" 8)"
          printf '                # NOT `fetch --all`: it fetches branches, and an\n'
          printf '                # anchored pin (refs/pins/*) is on no branch.\n'
          ;;
        UNRELATED)
          printf '      No merge base with the pin. Treat as a re-pin to a different history.\n'
          ;;
        BEHIND)
          printf '      Behind by %s, but the worktree has %s uncommitted change(s).\n' "$(field "$rec" 6)" "$(field "$rec" 9)"
          printf '      inspect:  git -C %s status\n' "$(field "$rec" 2)/$(field "$rec" 3)"
          ;;
        *)
          printf '      inspect:  git -C %s status\n' "$(field "$rec" 2)/$(field "$rec" 3)"
          ;;
      esac
      echo
    done
  fi
}

# ---------------------------------------------------------------------------
# Restore — the safe subset only
# ---------------------------------------------------------------------------
builds_running() {
  # Mutating a submodule worktree under a running build is worse than leaving it
  # stale: the build then mixes pre- and post-checkout sources and can SUCCEED
  # against a tree that never existed. Several lanes build concurrently on this
  # machine, so check before touching anything.
  #
  # Scoped to THIS repo on purpose. A bare `pgrep cargo` is true almost always on
  # this machine — sibling repos build constantly — and a guard that fires every
  # time is a guard everyone learns to `--force` past. A process counts if its cwd
  # is inside the superproject or its command line names it.
  #
  # `pgrep -x bootstrap` is a SEPARATE probe, not another alternative in the -f
  # pattern, and it is not optional: the python `x.py` wrapper can exit while its
  # bootstrap child keeps compiling (observed 2026-08-01, attempt 8), and matching
  # on `x.py` alone then sees nothing while the tree is being written. Matching the
  # executable NAME also assumes nothing about argument order — `bootstrap build`
  # as a -f pattern never matches, because `x.py --stage 1 build` produces
  # `.../bootstrap --stage 1 build` and the two words are not adjacent.
  local cands pid_csv by_cmd by_cwd
  cands="$( { pgrep -f 'x\.py|[/ ]cargo |[/ ]rustc |[/ ]targo ' 2>/dev/null
              pgrep -x bootstrap 2>/dev/null; } | sort -un | head -40)"
  [ -n "$cands" ] || return 0

  if ! command -v lsof >/dev/null 2>&1; then
    # No way to read cwd: fall back to the broad list. Over-refusing is the safe
    # direction for a guard whose failure mode is a corrupted build.
    printf '%s\n' "$cands"
    return 0
  fi

  pid_csv="$(printf '%s' "$cands" | tr '\n' ',' | sed 's/,$//')"
  by_cmd="$(ps -o pid=,command= -p $(printf '%s' "$cands" | tr '\n' ' ') 2>/dev/null \
            | grep -F "$ROOT" | awk '{print $1}')"
  by_cwd="$(lsof -a -d cwd -p "$pid_csv" -Fpn 2>/dev/null \
            | awk -v root="$ROOT" '
                /^p/ { pid = substr($0, 2) }
                /^n/ { path = substr($0, 2)
                       if (path == root || index(path, root "/") == 1) print pid }')"
  printf '%s\n%s\n' "$by_cmd" "$by_cwd" | grep -E '^[0-9]+$' | sort -un
}

do_restore() {
  if [ "${#SAFE_ROWS[@]}" -eq 0 ]; then
    echo "submodule_sync --restore: nothing is provably safe to restore."
    [ "$N_REVIEW" -gt 0 ] && echo "  $N_REVIEW module(s) need a human; see scripts/submodule_sync.sh"
    return
  fi

  local pids
  pids="$(builds_running)"
  if [ -n "$pids" ] && [ "$FORCE" -ne 1 ]; then
    echo "submodule_sync --restore: REFUSED — a build appears to be running." >&2
    echo >&2
    echo "  Swapping a submodule worktree mid-build produces a binary compiled from" >&2
    echo "  two different source trees, which can pass while being meaningless." >&2
    echo "  Wait for the build, or re-run with --force if you know these are yours:" >&2
    echo >&2
    ps -o pid=,command= -p $(printf '%s' "$pids" | tr '\n' ' ') 2>/dev/null | cut -c1-140 | sed 's/^/    /' >&2
    exit 4
  fi

  local rec parent rel display rc=0
  for rec in "${SAFE_ROWS[@]}"; do
    display="$(field "$rec" 1)"; parent="$(field "$rec" 2)"; rel="$(field "$rec" 3)"
    # An ANCHORED restore MOVES OFF commits the pin does not have. That is the
    # act this tool exists to prevent doing blindly, so it never happens
    # silently: name the commits and the ref that keeps each one alive. Without
    # this the output is indistinguishable from the unsafe restore.
    if [ "$(field "$rec" 10)" = "1" ]; then
      printf 'ANCHORED %s — %s commit(s) the pin lacks, none of them lost:\n' \
        "$display" "$(field "$rec" 5)"
      anchor_lines "$rec" "    "
      printf '  each stays fetchable by sha from the ref above after this checkout.\n'
    fi
    printf 'restoring %s ... ' "$display"
    if git -C "$parent" submodule update --init -- "$rel" >/dev/null 2>&1; then
      printf 'ok (%.8s)\n' "$(git -C "$parent/$rel" rev-parse HEAD 2>/dev/null)"
    else
      printf 'FAILED\n'
      rc=1
    fi
  done

  if [ "$N_REVIEW" -gt 0 ]; then
    echo
    echo "NOT restored — $N_REVIEW module(s) hold work the pin does not, or need a fetch:"
    for rec in "${REVIEW_ROWS[@]}"; do
      printf '  %s  [%s]\n' "$(field "$rec" 1)" "$(field "$rec" 4)"
    done
    echo "Run scripts/submodule_sync.sh for the per-module reasoning."
    rc=2
  fi
  exit "$rc"
}

case "$MODE" in
  json)    emit_json ;;
  quiet)   emit_quiet ;;
  restore) do_restore ;;
  *)       emit_report ;;
esac

exit "$RC"
