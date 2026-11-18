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
# FETCH — missing pins, incomplete objects or unreadable ancestry
# -------------------------------------------------------------
# --fetch acquires missing pins by exact SHA, then reclassifies rather than
# blindly restoring. Present pins with unreadable ancestry may be refetched
# without negotiation; that repair path changes no durable ref or FETCH_HEAD.
# Genuine unrelated histories are not repaired. Reads suppress promisor lazy
# fetching. An unreadable root tree is PIN-INCOMPLETE: explicit --fetch repairs
# canonical HTTPS GitHub pins through the recreator's owner-routed Agh fetch,
# retaining source identity, deadline and private-ref checks, with no Git
# fallback after refusal. Only readable pin/root data reaches classification.
# The all-synced path remains network-free. --fetch --restore realigns only
# where the resulting complete safety evidence permits it.
#
# USAGE
#   scripts/submodule_sync.sh              classify and report (default)
#   scripts/submodule_sync.sh --quiet      one line, for hooks and prompts
#   scripts/submodule_sync.sh --json       machine-readable records
#   scripts/submodule_sync.sh --restore    check out ONLY the provably-lossless ones
#   scripts/submodule_sync.sh --fetch      acquire missing pins, repair canonical
#                                          incomplete pins or unreadable ancestry
#   scripts/submodule_sync.sh --root DIR   operate on DIR's superproject (self-test)
#   scripts/submodule_sync.sh --offline    never touch the network; unanchored-unless
#                                          a LOCAL ref proves it (fail closed).
#                                          Cold local clones require file in the
#                                          explicit GIT_ALLOW_PROTOCOL whitelist.
#   scripts/submodule_sync.sh --restore --force   restore even while a build runs
#
# EXIT CODES
#   0  every submodule worktree is at its recorded pin
#   1  drift, and every drifted module is provably lossless to restore
#      (BEHIND, ABSENT, UNREGISTERED, DISCONNECTED, or AHEAD/DIVERGENT with
#      unique commits ANCHORED)
#   2  drift, and at least one module needs a human (UNANCHORED AHEAD /
#      DIVERGENT / dirty / unrelated / ancestry unreadable / pin object missing)
#   3  usage or environment error
#   4  --restore refused: a build appears to be running against this repo
#
# NEVER run x.py to test this. Use `targo --unverified check --locked` (see
# reports/submodule-pin-drift.md §4 for the bootstrap environment it needs).

set -uo pipefail

usage() {
  sed -n '/^# USAGE/,/^#   4 /p' "$0" | sed 's/^# \{0,1\}//'
}

MODE="report"
FORCE=0
OFFLINE=0
FETCH=0
ROOT_ARG=""
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
while [ "$#" -gt 0 ]; do
  case "$1" in
    --quiet|-q)   MODE="quiet" ;;
    --json)       MODE="json" ;;
    --restore)    MODE="restore" ;;
    --force)      FORCE=1 ;;
    --offline)    OFFLINE=1 ;;
    --fetch)      FETCH=1 ;;
    --root)       ROOT_ARG="${2:-}"; shift ;;
    --root=*)     ROOT_ARG="${1#--root=}" ;;
    -h|--help)    usage; exit 0 ;;
    *) echo "submodule_sync: unknown argument '$1'" >&2; usage >&2; exit 3 ;;
  esac
  shift
done
if [ "$FETCH" -eq 1 ] && [ "$OFFLINE" -eq 1 ]; then
  echo "submodule_sync: --fetch and --offline contradict each other" >&2
  exit 3
fi

offline_clone_protocols() {
  # --no-fetch controls explicit later fetches, not clone or promisor reads.
  # Preserve only the caller's explicit local transport permission.
  case ":${GIT_ALLOW_PROTOCOL-}:" in *:file:*) printf '%s' file ;; esac
  return 0
}
# A diagnostic object read must not silently repair a partial clone. Explicit
# --fetch and anchor probes remain separately controlled below; Git must report
# missing local commits/trees instead of hiding them through a promisor fetch.
export GIT_NO_LAZY_FETCH=1
if [ "$OFFLINE" -eq 1 ]; then
  # Apply before every Git read: missing promised objects can otherwise make
  # even ls-tree, status or cat-file contact a remote. The transport whitelist
  # also protects children/older Git; explicit local initialization still works.
  export GIT_ALLOW_PROTOCOL="$(offline_clone_protocols)"
fi

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
# A fetch moves objects, not just refs, so it gets a transfer-sized bound. The
# default suits a sibling of ordinary size. It is settable because one is not:
# on 2026-11-10 first-party/trust-ir's pin was a 17 GiB transfer, about twenty
# minutes on the link that measured it, and two bounded attempts discarded
# 13 GiB and reported the pin as not provided (fetch_missing_pin, below).
FETCH_TIMEOUT="${SUBMODULE_SYNC_FETCH_TIMEOUT:-600}"
case "$FETCH_TIMEOUT" in
  ''|*[!0-9]*|0*)
    echo "submodule_sync: SUBMODULE_SYNC_FETCH_TIMEOUT='$FETCH_TIMEOUT' is not a positive number of seconds" >&2
    exit 3 ;;
esac
# The most a probe may write, in KiB (probe_pin, below). A probe asks for a
# pin's commits alone, a few hundred bytes each; a remote that ignores the
# request sends their files too, and this is where that stops.
PROBE_LIMIT_KB="${SUBMODULE_SYNC_PROBE_LIMIT_KB:-65536}"
case "$PROBE_LIMIT_KB" in
  ''|*[!0-9]*|0*)
    echo "submodule_sync: SUBMODULE_SYNC_PROBE_LIMIT_KB='$PROBE_LIMIT_KB' is not a positive number of KiB" >&2
    exit 3 ;;
esac
# The most one fetch for a NEW checkout may add to a store other checkouts
# read, in KiB (shared_fetch, below). Past it nothing enters the store and
# that one module gets a store of its own, the pin alone. What a pin's
# missing history weighs is not known before it is sent. Measured on
# 2026-11-14 for one worktree's pins against a first checkout's shallow
# stores, in MiB: trust-vc 3, trust-mc 11, trust-cg 162, ty 374, ny 674,
# clean 1266, and trust-ir more than 2048 where the pin alone was 35.
LINK_LIMIT_KB="${SUBMODULE_SYNC_LINK_LIMIT_KB:-1048576}"
case "$LINK_LIMIT_KB" in
  ''|*[!0-9]*|0*)
    echo "submodule_sync: SUBMODULE_SYNC_LINK_LIMIT_KB='$LINK_LIMIT_KB' is not a positive number of KiB" >&2
    exit 3 ;;
esac
# The longest one sync waits for another's lock on a store (lock_store,
# below), in seconds. The holder's longest step is a probe and a fetch, each
# under SUBMODULE_SYNC_FETCH_TIMEOUT, or one Agh fetch under its own ten
# minutes; past that the store reads as busy, and the waiter gives its
# module a store of its own or reports the pin missing.
LOCK_WAIT="${SUBMODULE_SYNC_LOCK_WAIT:-}"
if [ -z "$LOCK_WAIT" ]; then
  LOCK_WAIT=$((2 * FETCH_TIMEOUT))
  [ "$LOCK_WAIT" -ge 600 ] || LOCK_WAIT=600
  LOCK_WAIT=$((LOCK_WAIT + 60))
fi
case "$LOCK_WAIT" in
  ''|*[!0-9]*|0*)
    echo "submodule_sync: SUBMODULE_SYNC_LOCK_WAIT='$LOCK_WAIT' is not a positive number of seconds" >&2
    exit 3 ;;
esac
FETCH_ATTEMPTED_KEYS=()
FETCH_FAILED_KEYS=()
NET_CACHE_URLS=()
NET_CACHE_REFS=()
TIMEOUT_BIN=""
for _cand in timeout gtimeout; do
  if command -v "$_cand" >/dev/null 2>&1; then TIMEOUT_BIN="$_cand"; break; fi
done

# A hung remote must not hang the tool a human runs before every build. Bound it
# where a bound is available, and never let git open an interactive prompt.
net_git() { net_git_within "$NET_TIMEOUT" "$@"; }
# Descriptor 9 is a store's lock while one is held (lock_store). No git started
# here inherits it: a helper it leaves behind (a credential cache, a detached
# maintenance run) would hold the lock long after the fetch.
net_git_within() { # <seconds> <git args...>
  local secs="$1"; shift
  if [ -n "$TIMEOUT_BIN" ]; then
    "$TIMEOUT_BIN" "$secs" env GIT_TERMINAL_PROMPT=0 git "$@" 9>&-
  else
    env GIT_TERMINAL_PROMPT=0 git "$@" 9>&-
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

# scripts/lib/github_source_transport.py owns GitHub URL selection and Agh refs.
github_source() {
  local python
  for python in python3.14 python3.13 python3.12 python3.11 python3; do
    if command -v "$python" >/dev/null 2>&1; then
      "$python" -B "$SCRIPT_DIR/lib/github_source_transport.py" "$@"
      return $?
    fi
  done
  echo 'submodule_sync: Python is required to select source transport' >&2
  return 2
}

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
    local repository transport_rc
    repository="$(github_source repository "$url")"; transport_rc=$?
    if [ "$transport_rc" -eq 0 ]; then
      out="$(github_source pins "$url" --timeout "$NET_TIMEOUT")"; rc=$?
    elif [ "$transport_rc" -eq 1 ]; then
      out="$(net_git -C "$moddir" ls-remote --refs "$name" 'refs/pins/*' 2>/dev/null \
             | awk 'NF >= 2 { print $1, $2 }')"; rc=$?
    else
      out=""; rc=2
    fi
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

# --fetch: bring exactly <pin> into <moddir>'s object store, by sha.
# A refetch can repair an unreadable ancestor graph even when the pin already
# exists. It names no destination and creates no new anchoring ref.
fetch_pin() { # <moddir> <pin> <display> [missing|refetch]
  local moddir="$1" pin="$2" display="$3" mode="${4:-missing}"
  local pair rname rurl key i=0 fetch_rc gitdir store="" how=""
  # Restore rescans after each checkout. Each kind of acquisition gets one
  # attempt per selected pin, including a successful but insufficient refetch.
  key="${moddir}${TAB}${pin}${TAB}${mode}"
  while [ "$i" -lt "${#FETCH_ATTEMPTED_KEYS[@]}" ]; do
    [ "${FETCH_ATTEMPTED_KEYS[$i]}" != "$key" ] || return 1
    i=$((i + 1))
  done
  FETCH_ATTEMPTED_KEYS+=("$key")
  if ! pair="$(module_remote "$moddir")"; then
    printf 'submodule_sync --fetch: %s: no remote to fetch pin %.8s from\n' "$display" "$pin" >&2
    return 1
  fi
  rname="${pair%% *}"; rurl="${pair#* }"
  gitdir="$(git -C "$moddir" rev-parse --absolute-git-dir 2>/dev/null)"
  # A linked checkout: its store is one several worktrees read (a second
  # worktree's, below).
  if [ -n "$gitdir" ] && [ -f "$gitdir/commondir" ]; then
    store="$(git -C "$moddir" rev-parse --path-format=absolute --git-common-dir 2>/dev/null)"
  fi
  local repository transport_rc
  repository="$(github_source repository "$rurl")"; transport_rc=$?
  if [ "$transport_rc" -eq 0 ]; then
    # A GitHub pin comes through Agh alone, never plain git. One sync at a
    # time tests for it and fetches it (lock_store): a sync in another
    # worktree may be deciding about this same pin and store. A store other
    # checkouts read gets Agh's unfiltered exact fetch with its history
    # (shared_agh_fetch); a checkout's own store keeps the closure fetch
    # (repair_incomplete_pin), and so does the first checkout's own shallow
    # store, which the exact fetch would fill with the pin's whole history
    # (docs/OPEN_ISSUES.md, AGH-CLOSURE-SHARED-STORE-1).
    local shared="$store" lock_rc=1
    [ -n "$shared" ] || ! store_has_linked_checkouts "$gitdir" || store_is_shallow "$gitdir" \
      || shared="$gitdir"
    if [ -n "${store:-$gitdir}" ]; then
      lock_store "${store:-$gitdir}"
      lock_rc=$?
    fi
    if [ "$lock_rc" -eq 2 ]; then
      fetch_rc=1
    elif [ "$mode" = missing ] && git -C "$moddir" cat-file -e "${pin}^{commit}" 2>/dev/null \
       && pin_root_tree_readable "$moddir" "$pin" \
       && { [ -z "$shared" ] || pin_whole "$shared" "$pin"; }; then
      fetch_rc=0
    elif [ -n "$shared" ]; then
      shared_agh_fetch "$shared" "https://github.com/$repository.git" "$pin" "$LINK_LIMIT_KB"
      fetch_rc=$?
      if [ "$fetch_rc" -eq 0 ]; then
        printf 'submodule_sync --fetch: %s: fetched pin %.8s into %s, a store other checkouts read (%s, %s)\n' \
          "$display" "$pin" "$shared" "$mode" "$SHARED_FETCH_OUT" >&2
      else
        printf 'submodule_sync --fetch: %s: pin %.8s did not come into %s, a store other checkouts read (%s: %s)\n' \
          "$display" "$pin" "$shared" "$mode" "$SHARED_FETCH_OUT" >&2
      fi
    else
      repair_incomplete_pin "$moddir" "$pin" "$display"
      fetch_rc=$?
    fi
    unlock_store
    return "$fetch_rc"
  elif [ "$transport_rc" -ne 1 ]; then
    return 1
  fi
  if [ "$mode" = refetch ]; then
    # Negotiation can assume a locally present commit includes its ancestors.
    # Refetch transfers the selected closure without that assumption. Keep all
    # durable refs and FETCH_HEAD untouched on this repair-only path.
    set -- -C "$moddir" fetch -q --no-tags --recurse-submodules=no --refetch --no-write-fetch-head
    if [ -n "$store" ]; then
      # A refetch names no commit the store has, so the remote sends every
      # object from the pin down: to the roots of a shallow store, or past
      # them where a line of the pin's history goes round them. That is a
      # second copy of the store at the least, in the store the first
      # checkout reads, so a shallow shared store is not refetched.
      if store_is_shallow "$store"; then
        printf 'submodule_sync --fetch: %s: not refetched: its store %s is shallow and other checkouts read it, and a refetch has no bound there\n' "$display" "$store" >&2
        return 1
      fi
      set -- "$@" --no-auto-maintenance
    fi
    [ -z "${SUBMODULE_SYNC_TRACE_NET:-}" ] || echo "net: refetch $rurl $pin" >&2
    net_git_within "$FETCH_TIMEOUT" "$@" "$rname" "$pin" >/dev/null 2>&1
    fetch_rc=$?
  elif [ -n "$store" ]; then
    # The pin alone, by sha, as shared_fetch bounds it: no tracking ref moves
    # under the other checkouts, no FETCH_HEAD is written and no maintenance
    # starts (the rule scripts/hooks-pin/pre-push states for a shared store).
    shared_fetch "$store" "$rname" "$rurl" "$pin"
    fetch_rc=$?
    how="$SHARED_FETCH_OUT"
  else
    # One sync at a time tests for a pin and fetches it (lock_store): a sync
    # in a second worktree may be deciding about this same pin and store.
    lock_store "$gitdir"
    if [ "$?" -eq 2 ]; then
      printf 'submodule_sync --fetch: %s: pin %.8s not fetched: another sync held its store\n' "$display" "$pin" >&2
      return 1
    elif git -C "$moddir" cat-file -e "${pin}^{commit}" 2>/dev/null; then
      fetch_rc=0
    else
      # Preserve the existing missing-pin acquisition's tracking-ref refresh.
      net_git_within "$FETCH_TIMEOUT" -C "$moddir" fetch -q --no-tags --recurse-submodules=no \
        "$rname" >/dev/null 2>&1 || true
      [ -z "${SUBMODULE_SYNC_TRACE_NET:-}" ] || echo "net: fetch $rurl $pin" >&2
      net_git_within "$FETCH_TIMEOUT" -C "$moddir" fetch -q --no-tags --recurse-submodules=no \
        "$rname" "$pin" >/dev/null 2>&1
      fetch_rc=$?
    fi
    unlock_store
  fi
  if [ "$fetch_rc" -eq 0 ] && git -C "$moddir" cat-file -e "${pin}^{commit}" 2>/dev/null; then
    printf 'submodule_sync --fetch: %s: fetched pin %.8s from %s (%s%s)\n' "$display" "$pin" "$rname" "$mode" "${how:+, $how}" >&2
    return 0
  fi
  if [ "$fetch_rc" -eq 124 ] && [ -n "$TIMEOUT_BIN" ]; then
    # The bound ended the transfer. That says nothing about whether the remote
    # holds the pin, and "did not provide" sent a reader to look for an
    # unpublished pin that was in fact being sent.
    printf 'submodule_sync --fetch: %s: fetching pin %.8s from %s <%s> did not finish within %ss (%s); the remote was still answering\n' "$display" "$pin" "$rname" "$rurl" "$FETCH_TIMEOUT" "$mode" >&2
    if [ -n "$store" ]; then
      # A plain `git fetch` there has no bound and starts maintenance in a
      # store other checkouts read.
      printf '  raise the bound (SUBMODULE_SYNC_FETCH_TIMEOUT=<seconds>)\n' >&2
    else
      printf '  raise the bound (SUBMODULE_SYNC_FETCH_TIMEOUT=<seconds>), or fetch it unbounded:  git -C %s fetch %s %s\n' "$moddir" "$rname" "$pin" >&2
    fi
    printf '  an interrupted fetch can leave a partial objects/pack/tmp_pack_* file in the module\n' >&2
    return 1
  fi
  printf 'submodule_sync --fetch: %s: %s <%s> did not provide pin %.8s (%s%s)\n' "$display" "$rname" "$rurl" "$pin" "$mode" "${how:+: $how}" >&2
  return 1
}

# Commit ancestry does not establish that checkout data is available. Check only
# the pin's root tree here, not an expensive full object-closure walk on every
# build. Deeper missing objects remain native checkout failures with stderr.
pin_root_tree_readable() {
  local moddir="$1" pin="$2" tree object_type
  PIN_TREE_NOTE_OUT=""
  if ! tree="$(git -C "$moddir" cat-file -p "${pin}^{commit}" 2>/dev/null | sed -n '1s/^tree //p')" \
     || [ -z "$tree" ]; then
    PIN_TREE_NOTE_OUT="pin commit header is unreadable; local object closure is incomplete"
    return 1
  fi
  if ! object_type="$(git -C "$moddir" cat-file -t "$tree" 2>&1)" \
     || [ "$object_type" != tree ]; then
    object_type="${object_type//$'\n'/; }"
    object_type="${object_type//$'\r'/ }"
    object_type="${object_type//$'\t'/ }"
    PIN_TREE_NOTE_OUT="pin commit exists but root tree $tree is missing or unreadable: $object_type"
    return 1
  fi
  return 0
}

# One exact GitHub pin into <dir>'s object store through owner-routed Agh,
# under a private refs/agh/trust-source-pins/<pin> ref. By default that is the
# pin's ancestry metadata and its checkout's files (Agh's selected-checkout
# closure, a blob-filtered fetch). With `native`, Agh's unfiltered fetch
# negotiated against the store instead (shared_agh_fetch, below). <dir> is a
# checkout or a git directory. Descriptor 9 (lock_store) is not handed on,
# for the reason net_git_within gives.
agh_fetch_pin() { # <dir> <canonical GitHub url> <pin> [native]
  local dir="$1" rurl="$2" pin="$3" python
  for python in python3.14 python3.13 python3.12 python3.11 python3; do
    command -v "$python" >/dev/null 2>&1 && break
    python=""
  done
  [ -n "$python" ] || return 1
  [ -z "${SUBMODULE_SYNC_TRACE_NET:-}" ] || echo "net: agh source-pin${4:+ $4} $rurl $pin" >&2
  "$python" -B "$SCRIPT_DIR/recreate_bootstrap.py" fetch-source-pin \
    --url "$rurl" --directory "$dir" --pin "$pin" ${4:+--native-exact} >&2 9>&-
}

# A store other checkouts read: a linked checkout's common directory, or a
# checkout's own git directory that registers linked checkouts.
store_has_linked_checkouts() { # <git dir>
  local reg
  for reg in "$1"/worktrees/*/gitdir; do [ -f "$reg" ] && return 0; done
  return 1
}

# <pin> is in <git dir> with every object it reaches past what the store's
# refs and checkouts' HEADs reach (`--all` names every worktree's HEAD). A
# commit can be present while a parent, a tree or a file is not: a depth
# fetch killed after its pack was installed and before its `shallow` line
# was written, or a blob-filtered fetch installed without a promisor marker.
# Such a pin is not "already there": it is fetched again.
pin_whole() { # <git dir> <pin>
  git --git-dir="$1" cat-file -e "${2}^{commit}" 2>/dev/null &&
    git --git-dir="$1" rev-list --objects --quiet "$2" --not --all >/dev/null 2>&1
}

# A GitHub pin into <store>, a store other checkouts read, under its lock
# (the caller holds it). Agh's selected-checkout closure is the wrong fetch
# there: it is blob-filtered and installed with no promisor marker, so the
# commits between the store's tips and the pin would be reachable without
# their files, and gc, `log -p` and a checkout of them would fail in every
# checkout of the store, with no later fetch to repair it (negotiation tells
# the remote the store has them). So Agh's exact, unfiltered fetch is used,
# negotiated against the store, which sends what the store lacks. It writes
# <limit> KiB at most (`ulimit -f`), as shared_fetch's plain fetch does. A
# shallow store is not fetched into: the exact fetch negotiates nothing under
# its roots and would bring the pin's whole history. Afterwards every object
# the pin reaches past what the store held must be there; otherwise the
# module is not shared. Agh's private ref is removed either way: in a store
# several checkouts read no fetch leaves a ref (shared_fetch), the checkout
# made next holds the pin, and such refs would pile up and anchor the first
# checkout's AHEAD commits.
shared_agh_fetch() { # <store> <canonical GitHub url> <pin> [limit KiB] -> SHARED_FETCH_OUT
  local store="$1" rurl="$2" pin="$3" limit="${4:-}" before rc
  SHARED_FETCH_OUT=""
  if store_is_shallow "$store"; then
    SHARED_FETCH_OUT="the store is shallow, and Agh's exact fetch would bring the pin's whole history into it"
    return 1
  fi
  before="$( { git --git-dir="$store" for-each-ref --format='%(objectname)'
               store_head_commits "$store"; } 2>/dev/null)"
  # NEGATIVE CONTROL (scripts/tests/submodule_sync_test.sh, fixture WA):
  # without `native` the stand-in installs the blob-filtered closure and the
  # check below refuses it.
  ( ulimit -c 0 2>/dev/null
    [ -z "$limit" ] || ulimit -f "$limit" || exit 1
    agh_fetch_pin "$store" "$rurl" "$pin" native )
  rc=$?
  if [ "$rc" -eq 0 ]; then
    if { printf '%s\n' "$pin"; printf '%s\n' "$before" | sed -n 's/^\([0-9a-f]\)/^\1/p'; } |
         git --git-dir="$store" rev-list --objects --missing=print --stdin 2>/dev/null |
         awk '/^\?/ { missing = 1 } END { exit missing }'; then
      SHARED_FETCH_OUT="through Agh, with its history"
    else
      rc=2
      SHARED_FETCH_OUT="Agh brought it without every object its history needs; nothing of it is used"
    fi
  else
    SHARED_FETCH_OUT="the Agh source fetch did not bring it (exit $rc); no Git fallback"
  fi
  git --git-dir="$store" update-ref -d "refs/agh/trust-source-pins/$pin" 2>/dev/null
  [ "$rc" -eq 0 ] || return 1
  return 0
}

repair_incomplete_pin() { # <moddir> <pin> <display>; explicit --fetch only
  local moddir="$1" pin="$2" display="$3" pair rurl key i=0 rc
  [ "$FETCH" -eq 1 ] && [ "$OFFLINE" -eq 0 ] || return 1
  pair="$(module_remote "$moddir")" || return 1
  rurl="${pair#* }"
  # The maintained provider validates the full canonical URL. Other transports
  # retain their existing local behavior; none is a fallback from Agh refusal.
  local repository
  repository="$(github_source repository "$rurl")" || return 1
  rurl="https://github.com/$repository.git"
  key="${moddir}${TAB}${pin}"
  while [ "$i" -lt "${#FETCH_FAILED_KEYS[@]}" ]; do
    [ "${FETCH_FAILED_KEYS[$i]}" != "$key" ] || return 1
    i=$((i + 1))
  done
  if agh_fetch_pin "$moddir" "$rurl" "$pin"; then
    if git -C "$moddir" cat-file -e "${pin}^{commit}" 2>/dev/null \
        && pin_root_tree_readable "$moddir" "$pin"; then
      printf 'submodule_sync --fetch: %s: repaired exact pin %.8s through Agh\n' "$display" "$pin" >&2
      return 0
    fi
    rc=2
  else
    rc=$?
  fi
  printf 'submodule_sync --fetch: %s: Agh pin repair failed (exit %s); no Git fallback\n' "$display" "$rc" >&2
  FETCH_FAILED_KEYS+=("$key")
  return 1
}

classify_one() {
  local parent="$1" rel="$2" display="$3"
  local pin ondisk state ahead behind dirty counts anchored anote reg_output reg_rc merge_rc merge_err repaired=0

  if ! pin="$(git -C "$parent" ls-tree HEAD -- "$rel" 2>/dev/null | awk '$2 == "commit" { print $3 }')"; then
    RECORDS+=("${display}${TAB}${parent}${TAB}${rel}${TAB}PIN-UNREADABLE${TAB}0${TAB}0${TAB}-${TAB}-${TAB}0${TAB}0${TAB}HEAD gitlink could not be read")
    return
  fi
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
    # Git cannot read the checkout. Two causes are plain git's own, run in
    # another worktree of this repository, and each has one right repair that
    # moves nothing (reconnect_children): those are DISCONNECTED, and lossless.
    state="NO-HEAD"
    anote="-"
    if own_store_names_another_worktree "$parent" "$rel"; then
      state="DISCONNECTED"
      anote="its git directory names another worktree (core.worktree)"
    elif shared_store_registers_child "$parent" "$rel"; then
      state="DISCONNECTED"
      anote="its .git file names no repository, and the store it shares still registers it"
    fi
    RECORDS+=("${display}${TAB}${parent}${TAB}${rel}${TAB}${state}${TAB}0${TAB}0${TAB}-${TAB}${pin}${TAB}0${TAB}0${TAB}${anote}")
    return
  fi

  if [ "$ondisk" = "$pin" ]; then
    if ! pin_root_tree_readable "$parent/$rel" "$pin" \
        && ! repair_incomplete_pin "$parent/$rel" "$pin" "$display"; then
      RECORDS+=("${display}${TAB}${parent}${TAB}${rel}${TAB}PIN-INCOMPLETE${TAB}0${TAB}0${TAB}${ondisk}${TAB}${pin}${TAB}0${TAB}0${TAB}${PIN_TREE_NOTE_OUT}")
      return
    fi
    # Synced. Deliberately skip the dirty probe here: `git status` is the
    # expensive call (~0.1-0.2s per module) and local edits on a module that is
    # AT its pin are nobody's drift problem. Skipping keeps the all-synced case
    # — the overwhelmingly common one — free of both `git status` and, since the
    # anchor probe hangs off `ahead > 0`, of any network call whatsoever.
    # A standalone clone can already hold every pinned byte while its parent
    # lacks `submodule init` records. Git then reports '-', and x.py refuses
    # the uninitialised closure. Ask Git rather than guessing a module's name
    # from its path or overlooking explicit activation settings.
    reg_output="$(git -C "$parent" submodule status -- "$rel" 2>/dev/null)"
    reg_rc=$?
    state="REGISTRATION-UNKNOWN"
    anote="git submodule status did not confirm the recorded pin and initialization"
    if [ "$reg_rc" -eq 0 ]; then
      case "${reg_output:0:1}" in
        ' ') state="SYNCED"; anote="-" ;;
        '-') state="UNREGISTERED"; anote="source is at pin; parent initialization is missing" ;;
      esac
    fi
    RECORDS+=("${display}${TAB}${parent}${TAB}${rel}${TAB}${state}${TAB}0${TAB}0${TAB}${ondisk}${TAB}${pin}${TAB}0${TAB}0${TAB}${anote}")
    return
  fi

  # Drifted. From here on accuracy outweighs speed.
  # Classification is a read: Git's optional stat-cache refresh must not rewrite
  # the owner's index while diagnosing or acquiring missing source objects.
  if ! dirty="$(GIT_OPTIONAL_LOCKS=0 git -C "$parent/$rel" status --porcelain 2>/dev/null | wc -l | tr -d ' ')"; then
    RECORDS+=("${display}${TAB}${parent}${TAB}${rel}${TAB}STATUS-UNREADABLE${TAB}0${TAB}0${TAB}${ondisk}${TAB}${pin}${TAB}0${TAB}0${TAB}worktree status could not be read")
    return
  fi

  if ! git -C "$parent/$rel" cat-file -e "${pin}^{commit}" 2>/dev/null \
     && ! { [ "$FETCH" -eq 1 ] && fetch_pin "$parent/$rel" "$pin" "$display"; }; then
    # The recorded pin is not in the local object store, so ancestry cannot be
    # computed at all and no restore can be attempted without a fetch (a write).
    RECORDS+=("${display}${TAB}${parent}${TAB}${rel}${TAB}PIN-MISSING${TAB}0${TAB}0${TAB}${ondisk}${TAB}${pin}${TAB}${dirty}${TAB}0${TAB}-")
    return
  fi

  if ! pin_root_tree_readable "$parent/$rel" "$pin" \
      && ! repair_incomplete_pin "$parent/$rel" "$pin" "$display"; then
    RECORDS+=("${display}${TAB}${parent}${TAB}${rel}${TAB}PIN-INCOMPLETE${TAB}0${TAB}0${TAB}${ondisk}${TAB}${pin}${TAB}${dirty}${TAB}0${TAB}${PIN_TREE_NOTE_OUT}")
    return
  fi

  while :; do
    if merge_err="$(git -C "$parent/$rel" merge-base "$ondisk" "$pin" 2>&1 >/dev/null)"; then
      merge_rc=0
    else
      merge_rc=$?
    fi
    # Exit 1 is "no common ancestor" only when git says nothing. Git 2.43.0
    # (measured; Ubuntu 24.04's) also exits 1 when it could not read an ancestor,
    # after `error: Could not read <sha>`, where newer git exits 128. Without
    # this an incomplete store was called UNRELATED there and never repaired.
    if [ "$merge_rc" -eq 1 ] && [ -n "$merge_err" ]; then
      merge_rc=128
    fi
    if [ "$merge_rc" -eq 1 ]; then
      # Git's no-common-ancestor result remains unrelated, never a reason to
      # acquire objects or auto-restore a different history.
      RECORDS+=("${display}${TAB}${parent}${TAB}${rel}${TAB}UNRELATED${TAB}0${TAB}0${TAB}${ondisk}${TAB}${pin}${TAB}${dirty}${TAB}0${TAB}-")
      return
    fi
    # left = worktree-only commits (AHEAD); right = pin-only (BEHIND).
    if [ "$merge_rc" -eq 0 ] &&
       counts="$(git -C "$parent/$rel" rev-list --left-right --count "${ondisk}...${pin}" 2>/dev/null)"; then
      break
    fi
    anote="ancestry counts could not be read"
    if [ "$merge_rc" -ne 0 ]; then
      anote="merge-base failed (exit $merge_rc); ancestry objects are incomplete or unreadable"
      if [ -n "$merge_err" ]; then
        # Keep Git's missing-object cause, without letting a diagnostic add
        # record delimiters, terminal controls or unbounded report text.
        merge_err="$(printf '%s' "$merge_err" | LC_ALL=C tr -c ' -~' ' ')"
        anote="$anote: ${merge_err:0:1024}"
        [ "${#merge_err}" -le 1024 ] || anote="$anote [truncated]"
      fi
    fi
    if [ "$repaired" -eq 0 ] && [ "$FETCH" -eq 1 ]; then
      repaired=1
      if fetch_pin "$parent/$rel" "$pin" "$display" refetch; then
        # Successful transport is not ancestry evidence. Classify the changed
        # object graph once through the same ordinary safety predicates.
        continue
      fi
    fi
    RECORDS+=("${display}${TAB}${parent}${TAB}${rel}${TAB}ANCESTRY-UNREADABLE${TAB}0${TAB}0${TAB}${ondisk}${TAB}${pin}${TAB}${dirty}${TAB}0${TAB}${anote}")
    return
  done
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

# The `path` entries of <parent>/.gitmodules, as `git config -z` prints them:
# "<key>\n<value>\0". A module's name and its path may each hold a space.
gitmodules_paths() { # <parent>
  git config -z --file "$1/.gitmodules" --get-regexp '^submodule\..*\.path$' 2>/dev/null
}

walk() {
  local parent="$1" prefix="$2"
  local entry rel display
  [ -f "$parent/.gitmodules" ] || return 0
  while IFS= read -r -d '' entry; do
    rel="${entry#*$'\n'}"
    [ -n "$rel" ] || continue
    if [ -n "$prefix" ]; then display="$prefix/$rel"; else display="$rel"; fi
    classify_one "$parent" "$rel" "$display"
    # Nothing under a checkout git cannot read can be classified; its nested
    # modules are scanned once it is reconnected.
    case "${RECORDS[${#RECORDS[@]}-1]}" in *"${TAB}DISCONNECTED${TAB}"*) continue ;; esac
    # Recurse so that a `--recursive` restore is never recommended blind: a
    # nested module that is itself AHEAD must not be swept up by a parent's
    # checkout. trust-cg carries three of these (third_party/*).
    if [ -e "$parent/$rel/.git" ]; then
      walk "$parent/$rel" "$display"
    fi
  done < <(gitmodules_paths "$parent")
}

# ---------------------------------------------------------------------------
# A second worktree's submodule checkouts
#
# A second worktree of the superproject (`git worktree add`) gets no private
# copy of a submodule's repository. --restore makes its ABSENT submodule a
# LINKED WORKTREE of the repository's own module store,
# <common git dir>/modules/<name>: the store the first checkout cloned, which no
# worktree removal touches. Objects, refs, stash and history are that store's.
# The second worktree adds a HEAD and an index under <store>/worktrees/<id>,
# where git itself records the checkout, so a gc in the store keeps its HEAD.
# No other worktree's git directory is ever a provider: a store there is
# removed with that worktree, and what borrowed from it breaks.
#
# A store is shared as it is: a shallow one stays shallow, with the roots it
# has, and a complete one stays complete. A pin the store lacks is fetched
# into it by sha, in a fetch that writes no ref and no FETCH_HEAD
# (shared_fetch). Nothing is deepened: no root the store has is ever moved
# down, so nothing under one arrives because a store is shared.
#
# A scan reads a shared store as it reads any clone, through the same
# merge-base and rev-list (classify_one), over the commits the store holds,
# and never guesses an ancestry it does not hold. So what a pin arrives with
# decides what the scan can say:
#  * a pin that shares history with the store arrives with it, by the plain
#    by-sha fetch a clone of the checkout's own makes (fetch_pin): the
#    commits between the pin and what the store reads. It reads BEHIND, AHEAD
#    or DIVERGENT exactly as it would in that clone, in every checkout of the
#    store.
#  * a pin that shares none (one older than the store's roots, or on a line
#    that left the history under them) arrives alone, as one more shallow
#    root. A move between it and another commit has no merge base and reads
#    UNRELATED (review). A clone of the checkout's own reads it the same way,
#    after downloading the pin's whole history: its roots hide the commit
#    the two share.
# Those two cases are a git transport's. A GitHub remote is read through Agh
# alone (agh_fetch_pin), into a shared store as into any clone: the pin
# arrives under a private refs/agh/trust-source-pins/<pin> ref with its full
# ancestry metadata and its checkout's files, so it is never a pin alone. The
# byte limit below is a git transport's; Agh's selected-checkout scope is its
# own bound.
#
# Sharing a store exists to save disk. A NEW checkout's pin may add at most
# SUBMODULE_SYNC_LINK_LIMIT_KB to a store; where its history is more than
# that, nothing enters the store and that one module gets a store of its
# own holding the pin alone (restore_module). A pin that MOVES in a checkout
# already linked is fetched as its own clone would fetch it, under the same
# time bound (SUBMODULE_SYNC_FETCH_TIMEOUT).
#
# The price is one shared config. `git submodule update` in the second
# worktree, even one that moves nothing, rewrites core.worktree in the store's
# config relative to the linked git directory, and the first checkout's git
# then fails in that submodule (`fatal: cannot chdir to ...`). --restore never
# runs it there. Plain git still can, so every scan of a second worktree also
# reads the first checkout's side of each store (main_disconnected), and
# --restore, in whichever worktree it runs, puts the value back
# (reconnect_children): the right value is the checkout whose .git file names
# that store, so nobody repairs a config by hand, and the worktree that did
# the damage is the one whose next scan reads drift.
#
# Plain git has a second way, which costs the second worktree alone. A
# recursive checkout there (`--recurse-submodules`, or submodule.recurse)
# points the linked checkout's .git file at <linked git dir>/modules/<name>,
# where git expects a private store, and git then fails in that checkout
# (`fatal: gitfile does not point to a valid repository`). The store still
# registers the checkout, with its HEAD and index, so --restore in the second
# worktree names that registration in the .git file again (the same pass).
# ---------------------------------------------------------------------------
STORE_OUT=""
NAME_OUT=""
REL_OUT=""
GITDIR_OUT=""
REG_OUT=""

module_name_for() { # <parent> <rel> -> NAME_OUT, the name .gitmodules gives that path
  local parent="$1" rel="$2" entry
  NAME_OUT=""
  [ -f "$parent/.gitmodules" ] || return 1
  while IFS= read -r -d '' entry; do
    if [ "${entry#*$'\n'}" = "$rel" ]; then
      NAME_OUT="${entry%%$'\n'*}"
      NAME_OUT="${NAME_OUT#submodule.}"
      NAME_OUT="${NAME_OUT%.path}"
      break
    fi
  done < <(gitmodules_paths "$parent")
  # Git refuses a module name that climbs out of modules/; so does this lookup.
  case "/$NAME_OUT/" in */../*) NAME_OUT="" ;; esac
  [ -n "$NAME_OUT" ]
}

physical_dir() { # <dir> [<relative or absolute dir, read from the first>] -> stdout
  if [ "$#" -eq 2 ]; then
    (CDPATH='' cd -- "$1" 2>/dev/null && CDPATH='' cd -- "$2" 2>/dev/null && pwd -P)
  else
    (CDPATH='' cd -- "$1" 2>/dev/null && pwd -P)
  fi
}

relative_path() { # <from dir> <to dir>, both absolute and physical -> REL_OUT
  local from="${1%/}" to="${2%/}" up=""
  while [ "$to" != "$from" ] && [ "${to#"$from"/}" = "$to" ]; do
    from="${from%/*}"
    up="../$up"
  done
  if [ "$to" = "$from" ]; then
    REL_OUT="${up%/}"
    [ -n "$REL_OUT" ] || REL_OUT="."
  else
    REL_OUT="${up}${to#"$from"/}"
  fi
}

# This script's own --restore line, as a report prints it.
restore_line() {
  printf 'scripts/submodule_sync.sh'
  [ -z "$ROOT_ARG" ] || printf ' --root %q' "$ROOT"
  [ "$OFFLINE" -eq 0 ] || printf ' --offline'
  printf ' --restore'
}

# The first checkout of this repository when ROOT is a second worktree of it,
# else empty. Its submodule checkouts are the main worktrees of the stores a
# second worktree shares.
MAIN_ROOT=""
main_root_of() { # <root> -> MAIN_ROOT
  local root="$1" gitdir common main
  MAIN_ROOT=""
  gitdir="$(git -C "$root" rev-parse --absolute-git-dir 2>/dev/null)" || return 0
  [ -f "$gitdir/commondir" ] || return 0
  common="$(git -C "$root" rev-parse --path-format=absolute --git-common-dir 2>/dev/null)" || return 0
  case "$common" in */.git) ;; *) return 0 ;; esac
  main="$(physical_dir "${common%/.git}")" || return 0
  [ "$main" = "$(physical_dir "$root")" ] || MAIN_ROOT="$main"
}

# The repository's own store for a submodule of a linked worktree, or nothing.
# `parent` is a second worktree of the superproject, or a linked submodule
# checkout that is the parent of a nested module. The provider is computed
# only as <common git dir>/modules/<name>: nothing under another worktree's
# git directory is read. A store that does not exist is not created. A store
# is not shared when it borrows objects itself (alternates, an objects
# symlink), is not a main repository (commondir), or has
# extensions.worktreeConfig: git then applies a core.worktree left in the
# store's own config to a linked checkout too, and a checkout there would
# write into the first checkout's directory.
shared_store_of() { # <parent> <rel> -> STORE_OUT, NAME_OUT, GITDIR_OUT (the parent's git dir)
  local parent="$1" rel="$2" common store
  STORE_OUT=""
  GITDIR_OUT="$(git -C "$parent" rev-parse --absolute-git-dir 2>/dev/null)" || return 1
  [ -f "$GITDIR_OUT/commondir" ] || return 1
  module_name_for "$parent" "$rel" || return 1
  common="$(git -C "$parent" rev-parse --path-format=absolute --git-common-dir 2>/dev/null)" || return 1
  store="$common/modules/$NAME_OUT"
  [ -f "$store/HEAD" ] || return 1
  [ ! -e "$store/commondir" ] && [ ! -L "$store/objects" ] \
    && [ ! -e "$store/objects/info/alternates" ] \
    && [ ! -e "$store/objects/info/http-alternates" ] || return 1
  [ "$(git config --file "$store/config" --type=bool --get extensions.worktreeConfig 2>/dev/null)" != true ] || return 1
  # Fails while the store's core.worktree resolves nowhere and no checkout is
  # left to say what it should be (reconnect_children repairs the rest first).
  git --git-dir="$store" rev-parse --git-dir >/dev/null 2>&1 || return 1
  STORE_OUT="$store"
}

store_is_shallow() { [ -s "$1/shallow" ]; } # <store>: it has shallow roots

# A checkout that is a linked worktree: other checkouts read its store.
shares_a_store() { # <moddir> [shallow]: ... and that store is shallow
  local gitdir
  gitdir="$(git -C "$1" rev-parse --absolute-git-dir 2>/dev/null)" || return 1
  [ -f "$gitdir/commondir" ] || return 1
  [ -z "${2:-}" ] || store_is_shallow "$(git -C "$1" rev-parse --path-format=absolute --git-common-dir 2>/dev/null)"
}

# The store an ABSENT submodule of a linked worktree is populated from. A
# worktree made before this shape existed keeps the private store it has.
module_store_for() { # <parent> <rel> -> STORE_OUT
  shared_store_of "$1" "$2" || return 1
  if [ -e "$GITDIR_OUT/modules/$NAME_OUT/HEAD" ]; then STORE_OUT=""; return 1; fi
}

child_is_its_own_toplevel() { # <child>: git, asked inside it, answers this directory
  local child="$1" top here
  top="$(git -C "$child" rev-parse --show-toplevel 2>/dev/null)" || return 1
  [ -n "$top" ] || return 1
  here="$(physical_dir "$child")" || return 1
  [ "$(physical_dir "$top")" = "$here" ]
}

# A pure read. True only for a submodule checkout that is the MAIN worktree of
# its parent's own store (its .git file names <parent git dir>/modules/<name>,
# and that directory has no commondir) while the store's core.worktree names
# some other directory, or none that exists. The right value is then known
# without inference: it is this checkout. A second worktree's linked checkout
# never passes, because its .git file names <store>/worktrees/<id>, which has a
# commondir. A copied checkout whose .git file still names the original's
# store does not pass either: that store is not under its parent's git
# directory.
own_store_names_another_worktree() { # <parent> <rel> -> STORE_OUT
  local parent="$1" rel="$2" child line="" target own value here there
  child="$parent/$rel"
  STORE_OUT=""
  [ -f "$child/.git" ] && [ ! -L "$child/.git" ] || return 1
  IFS= read -r line <"$child/.git" || [ -n "$line" ] || return 1
  case "$line" in 'gitdir: '*) ;; *) return 1 ;; esac
  here="$(physical_dir "$child")" || return 1
  target="$(physical_dir "$child" "${line#gitdir: }")" || return 1
  [ -f "$target/HEAD" ] && [ -f "$target/config" ] && [ ! -e "$target/commondir" ] || return 1
  module_name_for "$parent" "$rel" || return 1
  own="$(git -C "$parent" rev-parse --absolute-git-dir 2>/dev/null)" || return 1
  own="$(physical_dir "$own/modules/$NAME_OUT")" || return 1
  [ "$own" = "$target" ] || return 1
  value="$(git config --file "$target/config" --get core.worktree 2>/dev/null)" || return 1
  [ -n "$value" ] || return 1
  # A value that resolves nowhere is what git 2.54 and 2.56 leave (measured): it
  # is relative to the other worktree's linked git directory, not to the store.
  there="$(physical_dir "$target" "$value")" || there=""
  [ "$there" != "$here" ] || return 1
  STORE_OUT="$target"
}

# The registration of <store> whose checkout is the directory <here> (physical):
# <store>/worktrees/<id>, with a HEAD of its own.
registration_of() { # <store> <here> -> REG_OUT
  local store="$1" here="$2" reg admin back
  REG_OUT=""
  for reg in "$store"/worktrees/*/gitdir; do
    [ -f "$reg" ] || continue
    admin="${reg%/gitdir}"
    back=""
    IFS= read -r back <"$reg" || [ -n "$back" ] || continue
    case "$back" in */.git) ;; *) continue ;; esac
    [ "$(physical_dir "$admin" "${back%/.git}")" = "$here" ] || continue
    [ -f "$admin/HEAD" ] && [ -f "$admin/commondir" ] || continue
    REG_OUT="$admin"
    return 0
  done
  return 1
}

# A pure read. True only for a second worktree's submodule checkout whose .git
# file names no repository while the repository's own store still registers
# this very directory as one of its worktrees, with a HEAD. STORE_OUT is that
# registration. Only that one .git file is ever rewritten: `git worktree
# repair` would also re-point every other checkout the store registers, one
# that has since been given a private store included.
shared_store_registers_child() { # <parent> <rel> -> STORE_OUT
  local parent="$1" rel="$2" child line="" here target
  child="$parent/$rel"
  STORE_OUT=""
  [ -f "$child/.git" ] && [ ! -L "$child/.git" ] || return 1
  IFS= read -r line <"$child/.git" || [ -n "$line" ] || return 1
  case "$line" in 'gitdir: '*) ;; *) return 1 ;; esac
  here="$(physical_dir "$child")" || return 1
  target="$(physical_dir "$child" "${line#gitdir: }")" || target=""
  [ -z "$target" ] || [ ! -e "$target/HEAD" ] || return 1
  shared_store_of "$parent" "$rel" || return 1
  [ ! -e "$GITDIR_OUT/modules/$NAME_OUT/HEAD" ] || { STORE_OUT=""; return 1; }
  if registration_of "$STORE_OUT" "$here"; then STORE_OUT="$REG_OUT"; return 0; fi
  STORE_OUT=""
  return 1
}

# The one line of a .git file, whole or not at all: a kill between a truncation
# and a write would leave a file no predicate here reads.
write_gitfile() { # <child> <line>
  local child="$1" tmp="$1/.git.submodule_sync.$$"
  if printf '%s\n' "$2" >"$tmp" && mv -f "$tmp" "$child/.git"; then return 0; fi
  rm -f "$tmp"
  return 1
}

relink_child() { # <child> <display> <registration>
  local child="$1" display="$2" registration="$3" old=""
  IFS= read -r old <"$child/.git"
  # The line `git worktree add` wrote there.
  if write_gitfile "$child" "gitdir: $registration" && child_is_its_own_toplevel "$child"; then
    printf 'relinked %s: its .git file named no repository (%s -> %s)\n' \
      "$display" "${old#gitdir: }" "$registration"
  else
    write_gitfile "$child" "$old"
  fi
}

# --restore only. It writes one config value (a store's core.worktree, in the
# checkout that owns the store) or one .git file (a second worktree's), and
# never a source byte, so it runs whether or not a build does. It runs over
# ROOT and, from a second worktree, over the first checkout too.
reconnect_children() { # <parent> <display prefix>
  local parent="$1" prefix="$2" entry rel display child store old
  [ -f "$parent/.gitmodules" ] || return 0
  while IFS= read -r -d '' entry; do
    rel="${entry#*$'\n'}"
    [ -n "$rel" ] || continue
    child="$parent/$rel"
    [ -e "$child/.git" ] || continue
    if [ -n "$prefix" ]; then display="$prefix/$rel"; else display="$rel"; fi
    if child_is_its_own_toplevel "$child"; then
      :
    elif own_store_names_another_worktree "$parent" "$rel"; then
      store="$STORE_OUT"
      old="$(git config --file "$store/config" --get core.worktree 2>/dev/null)"
      # The path from the store to its checkout, as git writes it.
      relative_path "$store" "$(physical_dir "$child")"
      if git config --file "$store/config" core.worktree "$REL_OUT" 2>/dev/null \
         && child_is_its_own_toplevel "$child"; then
        printf 'reconnected %s: its git directory named another worktree (core.worktree %s -> %s)\n' \
          "$display" "$old" "$REL_OUT"
      else
        git config --file "$store/config" core.worktree "$old" 2>/dev/null
      fi
    elif shared_store_registers_child "$parent" "$rel"; then
      relink_child "$child" "$display" "$STORE_OUT"
    fi
    # A nested store is reached only through a parent git can read again.
    reconnect_children "$child" "$display"
  done < <(gitmodules_paths "$parent")
}

# The read that goes with it, for a scan of a second worktree: a checkout of
# the FIRST checkout that git cannot read because its store names another
# worktree. The usual cause is plain git run in the worktree being scanned,
# whose own checkouts all still read SYNCED, so this is where that drift
# becomes visible to the one who caused it. One `git config` a module where
# nothing is wrong; the row's path is absolute because it is outside ROOT.
main_disconnected() { # <parent, in the first checkout>
  local parent="$1" entry rel child line target value
  [ -f "$parent/.gitmodules" ] || return 0
  while IFS= read -r -d '' entry; do
    rel="${entry#*$'\n'}"
    child="$parent/$rel"
    [ -f "$child/.git" ] && [ ! -L "$child/.git" ] || continue
    line=""
    IFS= read -r line <"$child/.git" || [ -n "$line" ] || continue
    case "$line" in 'gitdir: '*) target="${line#gitdir: }" ;; *) continue ;; esac
    case "$target" in /*) ;; *) target="$child/$target" ;; esac
    value="$(git config --file "$target/config" --get core.worktree 2>/dev/null)"
    case "$value" in /*) ;; *) value="$target/$value" ;; esac
    if [ ! "$value" -ef "$child" ] && own_store_names_another_worktree "$parent" "$rel"; then
      RECORDS+=("${child}${TAB}${parent}${TAB}${rel}${TAB}DISCONNECTED${TAB}0${TAB}0${TAB}-${TAB}-${TAB}0${TAB}0${TAB}the first checkout's git fails here: its git directory names another worktree (core.worktree)")
    fi
    main_disconnected "$child"
  done < <(gitmodules_paths "$parent")
}

# ---------------------------------------------------------------------------
# A pin fetched into a store several checkouts read
# ---------------------------------------------------------------------------

# One sync at a time tests whether a git directory holds a pin and fetches it:
# the test and the fetch are one step. Without that, a sync that found the
# pin absent and fetches it alone (`--depth 1`) can come second to one that
# brought the pin with its history, and its `shallow` line then hides commits
# a checkout already reads. The lock is flock(2) on <git dir>/submodule_sync.lock
# through descriptor 9: the kernel drops it when this process ends, however it
# ends, so no lock is ever left behind and none is ever broken by a guess.
# A waiter says so after five seconds and waits LOCK_WAIT seconds at most
# (SUBMODULE_SYNC_LOCK_WAIT), longer than the holder's bounded steps take.
# Returns 1, with nothing held, where the machine offers no way to take the
# lock, and 2, with nothing held, where another sync held it all that time.
# NEGATIVE CONTROL (scripts/tests/submodule_sync_test.sh, fixture WL): with a
# blocking flock in place of the loop the waiter waits for as long as the
# holder lives.
lock_store() { # <git dir>
  local lock="$1/submodule_sync.lock" rc=1
  : >>"$lock" 2>/dev/null || return 1
  exec 9>>"$lock" || return 1
  if command -v perl >/dev/null 2>&1; then
    perl -e '
      use Fcntl qw(:flock);
      open(my $l, ">&=", 9) or exit 1;
      my ($wait, $dir) = @ARGV;
      my ($start, $said) = (time, 0);
      while (!flock($l, LOCK_EX | LOCK_NB)) {
        exit 1 unless $!{EWOULDBLOCK} || $!{EAGAIN};
        my $waited = time - $start;
        exit 2 if $waited >= $wait;
        if (!$said && $waited >= 5) {
          print STDERR "submodule_sync: waiting for another sync to finish with $dir (at most ${wait}s)\n";
          $said = 1;
        }
        select(undef, undef, undef, 0.25);
      }
      exit 0' "$LOCK_WAIT" "$1"
    rc=$?
  elif command -v python3 >/dev/null 2>&1; then
    python3 -c '
import errno, fcntl, sys, time
wait, where = int(sys.argv[1]), sys.argv[2]
start, said = time.monotonic(), False
while True:
    try:
        fcntl.flock(9, fcntl.LOCK_EX | fcntl.LOCK_NB)
        sys.exit(0)
    except OSError as error:
        if error.errno not in (errno.EWOULDBLOCK, errno.EAGAIN):
            sys.exit(1)
    waited = time.monotonic() - start
    if waited >= wait:
        sys.exit(2)
    if not said and waited >= 5:
        print(f"submodule_sync: waiting for another sync to finish with {where} (at most {wait}s)", file=sys.stderr)
        said = True
    time.sleep(0.25)
' "$LOCK_WAIT" "$1"
    rc=$?
  fi
  [ "$rc" -ne 0 ] || return 0
  exec 9>&-
  [ "$rc" -eq 2 ] || return 1
  printf 'submodule_sync: %s is busy: another sync held its lock for %ss (SUBMODULE_SYNC_LOCK_WAIT)\n' "$1" "$LOCK_WAIT" >&2
  return 2
}
unlock_store() { exec 9>&-; }

# The commit each checkout of <store> has checked out: the store's own HEAD and
# each registered worktree's. Git's gc keeps what they reach, as it keeps what
# a ref reaches, so they are commits the store holds whole.
store_head_commits() { # <store> -> stdout
  local store="$1" head
  git --git-dir="$store" rev-parse -q --verify 'HEAD^{commit}' 2>/dev/null
  for head in "$store"/worktrees/*/HEAD; do
    [ -f "$head" ] || continue
    git --git-dir="${head%/HEAD}" rev-parse -q --verify 'HEAD^{commit}' 2>/dev/null
  done
  return 0
}

# What a plain by-sha fetch of <pin> would bring into the shallow store
# <store>, read BEFORE anything is fetched into it. In a shallow repository
# git sends a wanted commit's history down to the commits the repository
# says it has and to its shallow roots, and nothing local says where a pin
# the store lacks sits: the commits between, when every line of the pin's
# history ends there, or a line's whole history down to the remote's first
# commit when one does not (a pin older than the roots, or on a line that
# left the history under them).
#
# So the probe asks the remote for the pin's COMMITS alone (`--filter=tree:0`,
# no tree and no file), cut at the store's own roots (a copy of its `shallow`
# file), into a repository of its own that is removed again. Nothing is
# written to the store. It then walks from the pin through the commits the
# store does not read (those no ref and no checkout's HEAD of the store
# reaches), and prints
#   alone    no line of the pin's history ends at a commit the store reads
#            or at one of its roots: the pin shares no history with the
#            store, a plain fetch would bring its whole history, and no
#            checkout could relate the pin to its HEAD afterwards anyway;
#   linked   a line does, followed by one line per commit the store reads
#            where a line ends: named as what the store has, they make the
#            fetch the commits between, plus the whole of any line that
#            ends nowhere in the store (a merge of one that left the
#            history under the roots), as in a clone of the checkout's own.
# It exits non-zero, with git's own exit where the fetch failed, when the
# ancestry could not be read; the caller then fetches nothing.
#
# Its cost is one negotiation and the pin's commit objects down to the
# store's roots, a few hundred bytes each. A remote that does not filter
# sends their trees and files too, so the probe may write PROBE_LIMIT_KB at
# most (SUBMODULE_SYNC_PROBE_LIMIT_KB): past that the transfer is ended and
# the ancestry is unread. The probe repository borrows no object from the
# store: a git that fetches from a promisor remote copies every local object
# the new commits reach into a pack of its own (measured, git 2.56.0), which
# with the store as an alternate was the store's whole history.
probe_pin() { # <store> <remote url> <pin> -> stdout
  local store="$1" rurl="$2" pin="$3"
  (
    probe="$(mktemp -d "${TMPDIR:-/tmp}/submodule_sync.probe.XXXXXX")" || exit 1
    trap 'rm -rf "$probe"' EXIT
    trap 'exit 1' HUP INT TERM
    git init -q --bare --template= "$probe/repo" >/dev/null 2>&1 || exit 1
    git --git-dir="$probe/repo" config remote.origin.url "$rurl" || exit 1
    cp "$store/shallow" "$probe/repo/shallow" || exit 1
    [ -z "${SUBMODULE_SYNC_TRACE_NET:-}" ] || echo "net: probe $rurl $pin" >&2
    # NEGATIVE CONTROL (scripts/tests/submodule_sync_test.sh, fixture W):
    # without `--filter=tree:0` the probe downloads each commit's files, and
    # where they pass the limit the pin is not shared at all.
    ( ulimit -c 0 2>/dev/null; ulimit -f "$PROBE_LIMIT_KB" &&
      net_git_within "$FETCH_TIMEOUT" --git-dir="$probe/repo" fetch -q --no-tags \
        --recurse-submodules=no --no-write-fetch-head --no-auto-maintenance \
        --filter=tree:0 origin "$pin" ) >/dev/null 2>&1 || exit $?
    # The store's refs and HEADs, and every commit they reach.
    { git --git-dir="$store" for-each-ref --format='%(objectname)' 2>/dev/null
      store_head_commits "$store"
    } | git --git-dir="$store" cat-file --batch-check='%(objectname) %(objecttype)' 2>/dev/null |
      awk '$2 == "commit" || $2 == "tag" { print $1 }' |
      git --git-dir="$store" rev-list --stdin >"$probe/read" 2>/dev/null || exit 1
    git --git-dir="$probe/repo" rev-list --parents "$pin" >"$probe/new" 2>/dev/null || exit 1
    { sed 's/^/R /' "$probe/read"
      sed 's/^/S /' "$probe/repo/shallow"
      sed 's/^/P /' "$probe/new"
    } | awk -v pin="$pin" '
      $1 == "R" { read[$2] = 1; next }
      $1 == "S" { root[$2] = 1; next }
      { known[$2] = 1; parents[$2] = ""; for (i = 3; i <= NF; i++) parents[$2] = parents[$2] " " $i }
      END {
        n = 0; queue[n++] = pin; seen[pin] = 1; related = 0
        for (h = 0; h < n; h++) {
          c = queue[h]
          if (read[c]) { end[c] = 1; related = 1; continue }
          if (!known[c]) exit 1
          if (parents[c] == "") { if (root[c]) related = 1; continue }
          m = split(parents[c], p, " ")
          for (i = 1; i <= m; i++) if (!seen[p[i]]) { seen[p[i]] = 1; queue[n++] = p[i] }
        }
        # NEGATIVE CONTROL (fixture W): without this test a pin older than
        # the roots of the store is fetched with the history under it.
        if (!related) { print "alone"; exit 0 }
        print "linked"
        for (c in end) print c
      }'
  )
}

# The one network step of the shared shape: bring <pin> into <store>, by sha,
# and leave what the store held as it was. No ref and no FETCH_HEAD is written
# and no maintenance starts, because other checkouts read this store (the
# rule scripts/hooks-pin/pre-push states for a store several worktrees share).
# The caller found the pin absent; that is tested again under the store's
# lock (lock_store), and the fetch is made under it.
#
# What is fetched follows from what the store is:
#  * complete: a plain fetch, so the store stays complete. A depth would give
#    it a `shallow` file, cutting history the first checkout reads, and
#    scripts/check_dependency_cycle_anchor.py refuses a shallow repository.
#    Git sends what the pin reaches and the store's refs and HEADs do not.
#  * shallow, the pin shares history with the store (probe_pin, `linked`): a
#    plain fetch that names the commits where the two meet as what the store
#    has, so the remote sends what lies between. The `shallow` file is not
#    written and the pin arrives with its ancestry. This is the fetch a clone
#    of the checkout's own makes for a moved pin (fetch_pin, above), so every
#    checkout of the store reads the move as that clone would.
#  * shallow, the pin shares none (`alone`): `--depth 1`, the pin's one
#    commit and its tree, never more than a clone of that pin. The pin
#    becomes one more line of the `shallow` file. The roots the store had
#    stay, and no commit a checkout could read is hidden: under the lock the
#    pin was not in the store, so nothing was read through it. Without the
#    lock it is not made.
# No store is deepened (`--unshallow`, `--deepen`, a depth above 1): each of
# those downloads history the first checkout did without, and a larger depth
# also cuts, at its own boundary, commits the store already reads (measured,
# git 2.56.0: `--depth 2` for a child of HEAD left a three-commit history one
# commit long).
#
# Every fetch is received beside the store, not in it: into
# <store>/submodule_sync.incoming.*, an object directory of its own that
# reads the store's objects as its alternate, whose packs are moved into the
# store once the fetch has ended well. A fetch that a bound ends, or that
# fails, leaves nothing in the store. `fetch.unpackLimit=1` keeps what
# arrives one pack, however little it is. The pin alone is received there
# too: git writes its `shallow` line into the store only once its pack is
# whole, and the pack is moved in after that, so a fetch killed between the
# two leaves a `shallow` line for a commit the store does not have (which
# `git prune` drops), never a pin whose parent is missing and is not a
# root. (NEGATIVE CONTROL, fixture W: fetched straight into the store, a
# fetch killed after its pack is installed leaves exactly that.)
#
# <limit>, in KiB, is the most a plain fetch may write (`ulimit -f`, which
# ends git's receiving process there, by a signal whose default action can
# write a core file: `ulimit -c 0`). Past it the fetch is dropped and 27 is
# returned: the caller, which has a cheaper way to give its checkout the pin,
# takes that. The fetch of a pin alone needs no limit.
#
# A checkout's HEAD is named to the remote beside the refs: git names only
# refs by default, and a fetch here moves none, so without that each fetch
# would be sent again what the last one brought (measured, git 2.56.0).
#
# <need> = history: the caller can use the pin only with its ancestry (a
# registration to take up again), so a pin that could only arrive alone is
# not fetched at all.
SHARED_FETCH_OUT=""
shared_fetch() { # <store> <remote name> <remote url> <pin> [history] [limit KiB] -> SHARED_FETCH_OUT
  local store="$1" rname="$2" rurl="$3" pin="$4" need="${5:-}" limit="${6:-}"
  local locked=0 plan="" tip rc how="" err="" why="" incoming="" f
  SHARED_FETCH_OUT=""
  lock_store "$store"
  case "$?" in
    0) ;;
    2) SHARED_FETCH_OUT="another sync held the store's lock"; return 1 ;;
    *) locked=1 ;;
  esac
  if pin_whole "$store" "$pin"; then
    unlock_store
    SHARED_FETCH_OUT="another sync brought it"
    return 0
  fi
  # What a sync that was killed left of a fetch it was receiving: under the
  # lock no other sync is receiving one.
  [ "$locked" -ne 0 ] || rm -rf "${store:?}"/submodule_sync.incoming.*
  set -- fetch -q --no-tags --recurse-submodules=no --no-write-fetch-head --no-auto-maintenance
  if store_is_shallow "$store"; then
    plan="$(probe_pin "$store" "$rurl" "$pin")"
    rc=$?
    if [ "$rc" -ne 0 ]; then
      unlock_store
      SHARED_FETCH_OUT="its ancestry could not be read from the remote, so nothing was fetched into the store"
      return "$rc"
    fi
  fi
  case "$plan" in
    linked*)
      how="with its history down to commits the store held"
      for tip in ${plan#linked}; do set -- "$@" "--negotiation-tip=$tip"; done
      ;;
    alone)
      if [ -n "$need" ] || [ "$locked" -ne 0 ]; then
        unlock_store
        SHARED_FETCH_OUT="it shares no history with the store, and the pin alone is no use here"
        [ -n "$need" ] || SHARED_FETCH_OUT="the store could not be locked for a fetch of the pin alone"
        return 1
      fi
      how="alone; the store stays shallow"
      # NEGATIVE CONTROLS (scripts/tests/submodule_sync_test.sh, fixture W):
      # without the depth the store gains the remote's history under a pin
      # that descends from none of its roots; with `--unshallow` in its
      # place the store is completed.
      set -- "$@" --depth 1
      ;;
  esac
  if [ "$plan" = alone ] || [ "$plan" = linked ] || [ -z "$plan" ]; then
    # Nothing narrower is known: every ref, and every checkout's HEAD.
    set -- "$@" '--negotiation-tip=refs/*'
    for tip in $(store_head_commits "$store"); do set -- "$@" "--negotiation-tip=$tip"; done
  fi
  [ -z "${SUBMODULE_SYNC_TRACE_NET:-}" ] || echo "net: store fetch $rurl $pin" >&2
  # The pin alone needs no byte limit: it is one commit and its tree.
  [ "$plan" != alone ] || limit=""
  if incoming="$(mktemp -d "$store/submodule_sync.incoming.XXXXXX" 2>/dev/null)" &&
       mkdir -p "$incoming/info" "$incoming/pack" "$store/objects/pack" 2>/dev/null &&
       printf '%s\n' "$store/objects" >"$incoming/info/alternates"; then
    # NEGATIVE CONTROL (fixture W): without the `ulimit` a pin brings a store
    # whatever its history weighs.
    err="$(
      ulimit -c 0 2>/dev/null
      [ -z "$limit" ] || ulimit -f "$limit" || exit 1
      export GIT_OBJECT_DIRECTORY="$incoming"
      net_git_within "$FETCH_TIMEOUT" -c fetch.unpackLimit=1 --git-dir="$store" "$@" "$rname" "$pin" 2>&1 >/dev/null
    )"
    rc=$?
    if [ "$rc" -eq 0 ]; then
      # A pack is read once its index is there, so the index goes last.
      for f in "$incoming"/pack/pack-*; do
        case "$f" in *.idx|*.keep) continue ;; esac
        [ ! -f "$f" ] || mv "$f" "$store/objects/pack/" || rc=1
      done
      for f in "$incoming"/pack/pack-*.idx; do
        [ ! -f "$f" ] || [ "$rc" -ne 0 ] || mv "$f" "$store/objects/pack/" || rc=1
      done
      [ "$rc" -eq 0 ] || why="what was fetched could not be moved into the store"
    elif [ -n "$limit" ] && [ -n "$(find "$incoming" -type f -size "+$((limit * 2 - 1))" 2>/dev/null)" ]; then
      # A file there is as large as the limit lets one be.
      rc=27
      why="what the store lacks of its history is more than the $limit KiB a new checkout may add to a store other checkouts read (SUBMODULE_SYNC_LINK_LIMIT_KB)"
    fi
    rm -rf "$incoming"
  else
    [ -z "$incoming" ] || rm -rf "$incoming"
    rc=1
    why="no directory beside the store could receive the fetch"
  fi
  unlock_store
  if [ "$rc" -eq 0 ] && git --git-dir="$store" cat-file -e "${pin}^{commit}" 2>/dev/null; then
    SHARED_FETCH_OUT="$how"
    return 0
  fi
  err="${err##*$'\n'}"
  SHARED_FETCH_OUT="${why:-git fetch exit $rc${err:+: $err}}"
  [ "$rc" -ne 0 ] || rc=1
  return "$rc"
}

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

scan_modules() {
  local rec state dirty
  RECORDS=()
  walk "$ROOT" ""
  [ -z "$MAIN_ROOT" ] || main_disconnected "$MAIN_ROOT"
  if [ "${#RECORDS[@]}" -eq 0 ]; then
    echo "submodule_sync: no submodules recorded in .gitmodules" >&2
    return 3
  fi

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
      ABSENT|UNREGISTERED)
        # Never checked out. Populating it is the intended repair (`--init`, or in
        # a second worktree a linked worktree of the repository's own module
        # store) and cannot lose work, because there is no worktree to lose.
        # UNREGISTERED is different: the worktree exists, so repair ONLY the
        # parent's init records, never bytes.
        N_DRIFT=$((N_DRIFT + 1)); DRIFT_ROWS+=("$rec")
        N_SAFE=$((N_SAFE + 1)); SAFE_ROWS+=("$rec")
        ;;
      DISCONNECTED)
        # Git cannot read a checkout because plain git, run in another worktree
        # of this repository, rewrote the one link the two share. The repair
        # writes that link and moves no HEAD, index or file.
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
}

main_root_of "$ROOT"
if [ "$MODE" = "restore" ]; then
  reconnect_children "$ROOT" ""
  # NEGATIVE CONTROL (scripts/tests/submodule_sync_test.sh, fixture W): without
  # this line plain git run in a second worktree leaves the first checkout
  # broken until someone runs --restore there.
  [ -z "$MAIN_ROOT" ] || reconnect_children "$MAIN_ROOT" "$MAIN_ROOT"
fi
scan_modules || exit $?

# A removed worktree leaves each of its checkouts' registrations in the stores,
# and `git worktree add` refuses a path a registration still names. A worktree
# made again at that path takes the registration up again when nothing only
# the registration holds would move: nothing is staged in its index, and its
# HEAD is the pin or an ancestor of it. Its reflog and its own refs stay where
# they are. Any other registration is left alone (the caller clones a private
# store): forcing `worktree add` would delete it, with the HEAD it holds.
#
# The first half needs no pin, so it is asked before one is fetched: a
# registration that will be refused brings nothing into the store.
registration_is_idle() { # <child> <registration>
  local child="$1" reg="$2"
  [ ! -e "$reg/locked" ] || return 1
  [ -z "$(ls -A "$child" 2>/dev/null)" ] || return 1
  git --git-dir="$reg" diff-index --cached --quiet HEAD -- 2>/dev/null
}
readopt_registration() { # <child> <pin> <registration>
  local child="$1" pin="$2" reg="$3"
  registration_is_idle "$child" "$reg" || return 1
  git --git-dir="$reg" merge-base --is-ancestor HEAD "$pin" 2>/dev/null || return 1
  write_gitfile "$child" "gitdir: $reg" || return 1
  if child_is_its_own_toplevel "$child" \
     && git -C "$child" -c submodule.recurse=false checkout -q -f --detach "$pin"; then
    return 0
  fi
  rm -f "$child/.git"
  return 1
}

# Plain `git submodule update` in a second worktree rewrites the store's
# core.worktree, in the config every checkout of the store reads, as the path
# from the linked checkout's git directory (<store>/worktrees/<id>) to that
# checkout, both resolved (measured, git 2.56.0). The first checkout's git
# reads the value from <store>, two directories nearer the root. Where the
# two paths share only `/`, or only a top-level directory, the extra `..`
# stop at `/` and the value names a directory that exists: the second
# worktree's own checkout (`~/trust` beside `$TMPDIR` on macOS, by way of the
# /var and /tmp links; `<home>/trust` beside `/mnt/...` on Linux). The first
# checkout's git then works in that directory with its own index, without
# an error, and x.py's `reset --hard` and `clean -dfx` there delete the
# second worktree's edits. Elsewhere the value names nothing, and the first
# checkout's git fails until --restore reconnects it (DISCONNECTED). True
# when the value would name a directory: that module is not linked.
link_would_alias() { # <store> <child>
  local store child there
  store="$(physical_dir "$1")" && child="$(physical_dir "$2")" || return 0
  relative_path "$store/worktrees/id" "$child"
  there="$(CDPATH='' cd -P -- "$store" 2>/dev/null && CDPATH='' cd -P -- "$REL_OUT" 2>/dev/null && pwd -P)"
  [ -n "$there" ]
}

restore_absent_from_store() { # <parent> <rel> <pin> <store>
  local parent="$1" rel="$2" pin="$3" store="$4" child here reg="" pair rc repository
  child="$parent/$rel"
  [ -d "$child" ] || mkdir -p "$child" || return 1
  here="$(physical_dir "$child")" || return 1
  # NEGATIVE CONTROL (scripts/tests/submodule_sync_test.sh, fixture WP):
  # without this test the checkout is linked, and the first checkout's git
  # reads it as its own after a `git submodule update` here.
  if link_would_alias "$store" "$child"; then
    printf 'submodule_sync --restore: %s: not linked to %s: they share only a top-level directory, so a `git submodule update` here would point the first checkout'"'"'s git at another directory\n' \
      "$rel" "$store" >&2
    return 1
  fi
  if registration_of "$store" "$here"; then
    reg="$REG_OUT"
    registration_is_idle "$child" "$reg" || return 1
  fi
  if ! pin_whole "$store" "$pin"; then
    [ "$OFFLINE" -eq 0 ] || return 1
    if ! pair="$(GIT_DIR="$store" module_remote "$store")"; then
      printf 'submodule_sync --restore: %s: the shared store %s has no remote to fetch pin %.8s from\n' \
        "$rel" "$store" "$pin" >&2
      return 1
    fi
    if repository="$(github_source repository "${pair#* }")"; then
      # A GitHub pin comes through Agh alone, never plain git (fetch_pin),
      # unfiltered and with its history (shared_agh_fetch): it is never a pin
      # alone, and a registration's HEAD reads as its ancestor. Under the
      # store's lock, as shared_fetch's fetch is.
      lock_store "$store"
      if [ "$?" -eq 2 ]; then
        rc=1
        SHARED_FETCH_OUT="another sync held the store's lock"
      elif pin_whole "$store" "$pin"; then
        rc=0
        SHARED_FETCH_OUT="another sync brought it"
      else
        shared_agh_fetch "$store" "https://github.com/$repository.git" "$pin" "$LINK_LIMIT_KB"
        rc=$?
      fi
      unlock_store
    elif [ "$?" -ne 1 ]; then
      return 1
    else
      # A registration is taken up again only where its HEAD is an ancestor
      # of the pin, which a pin fetched alone never shows.
      shared_fetch "$store" "${pair%% *}" "${pair#* }" "$pin" "${reg:+history}" "$LINK_LIMIT_KB"
      rc=$?
    fi
    if [ "$rc" -ne 0 ]; then
      printf 'submodule_sync --restore: %s: %s <%s> did not bring pin %.8s into the shared store %s (%s)\n' \
        "$rel" "${pair%% *}" "${pair#* }" "$pin" "$store" "$SHARED_FETCH_OUT" >&2
      # 27: over the limit. The caller clones the pin alone.
      [ "$rc" -ne 27 ] || return 27
      return 1
    fi
    printf 'submodule_sync --restore: %s: the shared store %s now holds pin %.8s%s\n' \
      "$rel" "$store" "$pin" "${SHARED_FETCH_OUT:+, $SHARED_FETCH_OUT}" >&2
  fi
  if [ -n "$reg" ]; then
    readopt_registration "$child" "$pin" "$reg"
    return $?
  fi
  # Git 2.48 and later can write extensions.relativeWorktrees into the store's
  # config; an older git ignores the key.
  git -c worktree.useRelativePaths=false --git-dir="$store" \
    worktree add --detach "$child" "$pin" || return 1
  # A checkout git reads as some other directory must not stay: the next
  # restore there would write that directory.
  child_is_its_own_toplevel "$child" && return 0
  git --git-dir="$store" worktree remove --force "$child" >/dev/null 2>&1
  return 1
}

materialize_source_witnesses() {
  # Explicit --fetch also restores tiny, indexed historical source witnesses.
  # The default diagnostic remains read-only; this owner imports object DATA,
  # never a ref/checkout or a substitute for the unchanged bridge validator.
  [ "$FETCH" -eq 1 ] || return 0
  [ -n "$(git -C "$ROOT" ls-files -- data/bridge-source-witnesses)" ] || return 0
  local python
  for python in python3.14 python3.13 python3.12 python3.11 python3; do
    if command -v "$python" >/dev/null 2>&1; then
      "$python" -B "$SCRIPT_DIR/recreate_bootstrap.py" materialize-source-witnesses --root "$ROOT" >&2
      return $?
    fi
  done
  echo "submodule_sync: Python unavailable for exact bridge source DATA restoration" >&2
  return 3
}

if [ "$RC" -eq 0 ]; then
  materialize_source_witnesses || exit $?
fi

restore_cmd_for() {
  # One explicit path per invocation, run from the module's own parent. No bare
  # repo-wide `git submodule update`, and no `--recursive`: both would sweep in
  # modules this script has not cleared, which is precisely the mistake the
  # BEHIND/AHEAD split exists to prevent.
  local rec="$1" parent rel pin state gitdir="" store=""
  parent="$(field "$rec" 2)"; rel="$(field "$rec" 3)"; pin="$(field "$rec" 8)"
  state="$(field "$rec" 4)"
  if [ "$state" = "UNREGISTERED" ]; then
    printf '    git -C %q submodule init -- %q\n' "$parent" "$rel"
    return
  fi
  if [ "$state" = "DISCONNECTED" ]; then
    # The one write reconnect_children makes for this row.
    if own_store_names_another_worktree "$parent" "$rel"; then
      store="$STORE_OUT"
      relative_path "$store" "$(physical_dir "$parent/$rel")"
      printf '    git config --file %q core.worktree %q\n' "$store/config" "$REL_OUT"
    elif shared_store_registers_child "$parent" "$rel"; then
      printf '    printf %s %q >%q\n' "'gitdir: %s\\n'" "$STORE_OUT" "$parent/$rel/.git"
    else
      printf '    %s\n' "$(restore_line)"
    fi
    return
  fi
  if [ -e "$parent/$rel/.git" ]; then
    gitdir="$(git -C "$parent/$rel" rev-parse --absolute-git-dir 2>/dev/null)"
  elif module_store_for "$parent" "$rel"; then
    # A second worktree: the steps restore_absent_from_store takes. Offline
    # with the pin absent nothing here can succeed, so that case keeps the
    # line below it.
    if [ -d "$parent/$rel" ] && registration_of "$STORE_OUT" "$(physical_dir "$parent/$rel")"; then
      # A removed worktree's registration names this path (readopt_registration).
      printf '    %s\n' "$(restore_line)"
      return
    fi
    if [ -d "$parent/$rel" ] && link_would_alias "$STORE_OUT" "$parent/$rel"; then
      # Not linked (restore_absent_from_store): a clone of its own, below.
      :
    elif pin_whole "$STORE_OUT" "$pin"; then
      store="$STORE_OUT"
    elif [ "$OFFLINE" -eq 0 ] && GIT_DIR="$STORE_OUT" module_remote "$STORE_OUT" >/dev/null; then
      # The store lacks the pin. What brings it is not one command: a shallow
      # store's fetch is chosen by what the pin's history ends at
      # (shared_fetch), under the store's lock.
      printf '    %s\n' "$(restore_line)"
      return
    fi
  fi
  printf '    '
  if [ "$OFFLINE" -eq 1 ]; then
    printf 'GIT_NO_LAZY_FETCH=1 GIT_ALLOW_PROTOCOL=%q ' "$GIT_ALLOW_PROTOCOL"
  fi
  if [ -n "$gitdir" ] && [ -f "$gitdir/commondir" ]; then
    printf 'git -C %q -c submodule.recurse=false checkout --detach %q\n' \
      "$parent/$rel" "$pin"
  elif [ -n "$gitdir" ]; then
    printf 'git -C %q submodule update --init --no-fetch -- %q\n' "$parent" "$rel"
  elif [ -n "$store" ]; then
    printf 'git -c worktree.useRelativePaths=false --git-dir=%q worktree add --detach %q %q\n' \
      "$store" "$parent/$rel" "$pin"
  elif [ "$OFFLINE" -eq 1 ]; then
    printf 'git -C %q submodule update --init --no-fetch -- %q\n' "$parent" "$rel"
  else
    printf 'git -C %q submodule update --init -- %q\n' "$parent" "$rel"
  fi
}

restore_module() {
  local parent="$1" rel="$2" pin="$3" state="${4:-}" gitdir reg_output rc alone=""
  if [ "$state" = "UNREGISTERED" ]; then
    git -C "$parent" submodule init -- "$rel" || return 1
    reg_output="$(git -C "$parent" submodule status -- "$rel" 2>/dev/null)" || return 1
    [ "${reg_output:0:1}" = ' ' ] && [ "$(git -C "$parent/$rel" rev-parse HEAD)" = "$pin" ]
    return $?
  fi
  if [ "$state" = "DISCONNECTED" ]; then
    # reconnect_children ran before this scan and the row is still here.
    printf 'submodule_sync --restore: %s could not be reconnected\n' "$parent/$rel" >&2
    return 1
  fi
  if [ ! -e "$parent/$rel/.git" ]; then
    # A second worktree's submodule is a linked worktree of the repository's
    # own store. Whatever that path cannot finish falls through to the command
    # below, so this restore never fails where it used to succeed.
    # NEGATIVE CONTROL (scripts/tests/submodule_sync_test.sh, fixture W):
    # without this block every store is cloned again under the worktree.
    if module_store_for "$parent" "$rel"; then
      restore_absent_from_store "$parent" "$rel" "$pin" "$STORE_OUT"
      rc=$?
      [ "$rc" -ne 0 ] || return 0
      if [ "$rc" -eq 27 ]; then
        # The pin's history is more than a new checkout may add to the store
        # (shared_fetch). A whole clone would download that history and the
        # rest, so this one module's own store holds the pin alone.
        # NEGATIVE CONTROL (fixture W): without the depth below it is a
        # whole clone.
        alone=1
        printf 'submodule_sync --restore: %s: not shared from %s; cloning a private store of pin %.8s alone\n' \
          "$rel" "$STORE_OUT" "$pin" >&2
      else
        printf 'submodule_sync --restore: %s: not shared from %s; cloning a private store\n' \
          "$rel" "$STORE_OUT" >&2
      fi
    fi
    # A refused `worktree add` removes what it made, and can take the empty
    # gitlink directory with it. Where it left a checkout instead, the command
    # below would be the plain-git trap: stop, and the next scan reads it.
    [ ! -e "$parent/$rel/.git" ] || return 1
    [ -d "$parent/$rel" ] || mkdir -p "$parent/$rel"
    if [ "$OFFLINE" -eq 1 ]; then
      git -C "$parent" submodule update --init --no-fetch -- "$rel"
    else
      git -C "$parent" submodule update --init ${alone:+--depth 1} -- "$rel"
    fi
    return $?
  fi
  gitdir="$(git -C "$parent/$rel" rev-parse --absolute-git-dir 2>/dev/null)" || return 1
  if [ -f "$gitdir/commondir" ]; then
    # `submodule update` rewrites core.worktree in the shared config relative
    # to this linked gitdir, breaking the primary submodule checkout. Move
    # only this worktree; ancestry, anchoring and dirty checks still apply.
    git -C "$parent/$rel" -c submodule.recurse=false checkout --detach "$pin"
  else
    # Classification already proved the pin is a local commit. Without
    # --no-fetch, a pin on no local ref (fetched by sha, or anchored-only)
    # sends `submodule update` to the network, --offline or not.
    git -C "$parent" submodule update --init --no-fetch -- "$rel"
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
  echo "  $N_DRIFT of $TOTAL submodule worktrees need pin or initialization repair."
  echo "  A build's source or Git initialization differs from the recorded closure;"
  echo "  resolve the reported states before diagnosing compiler errors."
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
      UNREGISTERED) delta="parent init missing" ;;
      DISCONNECTED) delta="git link broken" ;;
      PIN-MISSING) delta="pin not in object store" ;;
      PIN-INCOMPLETE) delta="pin object data missing" ;;
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
    echo "  ref, so moving HEAD to the pin destroys nothing. A checkout that was never"
    echo "  made, or one whose link to its git directory plain git broke from another"
    echo "  worktree (DISCONNECTED), has nothing to lose either."
    echo
    for rec in "${SAFE_ROWS[@]}"; do
      if [ "$(field "$rec" 10)" = "1" ]; then
        printf '    %s  [%s, ANCHORED]  — %s commit(s) the pin lacks, each held by:\n' \
          "$(field "$rec" 1)" "$(field "$rec" 4)" "$(field "$rec" 5)"
        anchor_lines "$rec" "        "
      elif [ "$(field "$rec" 4)" = "DISCONNECTED" ]; then
        printf '    %s  [DISCONNECTED]  — %s. This moves nothing:\n' \
          "$(field "$rec" 1)" "$(field "$rec" 11)"
      fi
      restore_cmd_for "$rec"
    done
    echo
    echo "  or let this script do exactly that set and nothing else:"
    echo
    printf '    scripts/submodule_sync.sh'
    [ -z "$ROOT_ARG" ] || printf ' --root %q' "$ROOT"
    [ "$OFFLINE" -eq 0 ] || printf ' --offline'
    printf ' --restore\n'
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
          if shares_a_store "$(field "$rec" 2)/$(field "$rec" 3)"; then
            # A plain `git fetch` in a checkout that shares its store has no
            # bound, writes that store's `shallow` file on stale knowledge
            # and starts maintenance in it. The bounded fetch is this
            # script's (shared_fetch).
            [ "$FETCH" -eq 1 ] || printf '      fetch it, bounded, into the store this checkout shares:  scripts/submodule_sync.sh --fetch --restore\n'
          else
            printf '      inspect:  git -C %s fetch origin %s\n' \
              "$(field "$rec" 2)/$(field "$rec" 3)" "$(field "$rec" 8)"
            printf '                # NOT `fetch --all`: it fetches branches, and an\n'
            printf '                # anchored pin (refs/pins/*) is on no branch.\n'
            [ "$FETCH" -eq 1 ] || printf '      or fetch every missing pin:  scripts/submodule_sync.sh --fetch --restore\n'
          fi
          ;;
        ANCESTRY-UNREADABLE)
          printf '      Unknown ancestry: %s\n' "$(field "$rec" 11)"
          printf '      No restore is safe until the object graph can be read.\n'
          if shares_a_store "$(field "$rec" 2)/$(field "$rec" 3)" shallow; then
            printf '      Its store is shallow and other checkouts read it: --fetch does not\n'
            printf '      refetch there, because a refetch has no bound in a shallow store.\n'
          else
            printf '      Explicit repair: scripts/submodule_sync.sh'
            [ -z "$ROOT_ARG" ] || printf ' --root %q' "$ROOT"
            printf ' --fetch --restore\n'
          fi
          ;;
        PIN-INCOMPLETE)
          printf '      %s\n' "$(field "$rec" 11)"
          printf '      Repair the selected pin\047s local object closure through Git before\n'
          printf '      restoring; preserve existing refs, index and worktree data.\n'
          printf '      inspect locally: GIT_NO_LAZY_FETCH=1 git -C %q cat-file -e %q\n' \
            "$(field "$rec" 2)/$(field "$rec" 3)" "$(field "$rec" 8)^{tree}"
          printf '      An ordinary exact-pin fetch can exit 0 without filling missing\n'
          printf '      objects for a commit already present. For canonical HTTPS GitHub\n'
          printf '      remotes, explicit --fetch --restore uses owner-routed Agh repair.\n'
          printf '      Other stores need an appropriate object repair; read-only checks never fetch.\n'
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

# Read `pid command...` lines (the `ps -o pid=,command=` shape) on stdin; print the
# pid of each line whose command names $ROOT as a whole path — the root itself or
# a path beneath it — never a sibling that merely shares the prefix
# (`$ROOT-wt-b`, `$ROOT-packs`, `$ROOT.old`). See `builds_running` for why.
# ROOT goes through the environment, not `awk -v`, which would expand backslash
# escapes in the path.
cmdlines_naming_root() {
  SUBMODULE_SYNC_ROOT_PATH="$ROOT" awk '
    function names_root(s, root,   n, i, after) {
      n = length(root)
      if (n == 0) return 0
      while ((i = index(s, root)) > 0) {
        after = substr(s, i + n, 1)
        # A name continues past the match: a different directory.
        if (after == "" || after !~ /[A-Za-z0-9._~+@%#-]/) return 1
        s = substr(s, i + 1)
      }
      return 0
    }
    { if (names_root($0, ENVIRON["SUBMODULE_SYNC_ROOT_PATH"])) print $1 }'
}

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
  # "Names it" means names the ROOT AS A PATH: the root itself, or something under
  # "$ROOT/". A plain substring test (`grep -F "$ROOT"`, the pre-2026-09-28 form)
  # also matched every SIBLING that shares the prefix — with ROOT=<home>/trust
  # a build in <home>/trust-packs/... or <home>/trust-wt-b/... counted
  # as a build in this repo, and --restore refused on a machine where worktrees
  # build constantly. The test is the character AFTER the match: end of the command
  # line, `/`, or anything that cannot continue a path-component name. No test is
  # made of the character BEFORE it: `/private/tmp/x` names the same directory as
  # `/tmp/x` on macOS, and over-refusing is the safe direction for this guard.
  #
  # `pgrep -x bootstrap` is a SEPARATE probe, not another alternative in the -f
  # pattern, and it is not optional: the python `x.py` wrapper can exit while its
  # bootstrap child keeps compiling (observed 2026-08-01, attempt 8), and matching
  # on `x.py` alone then sees nothing while the tree is being written. Matching the
  # executable NAME also assumes nothing about argument order — `bootstrap build`
  # as a -f pattern never matches, because `x.py --stage 1 build` produces
  # `.../bootstrap --stage 1 build` and the two words are not adjacent.
  #
  # A SHELL counts by its command line only, never by its cwd alone. An agent
  # harness starts every shell in the superproject (cwd <home>/trust) and
  # runs `bash -c '<script that mentions targo>'` from there while the build
  # itself runs in another tree: measured 2026-10-14 18:02, a 90-minute trust-vc
  # gate in a scratch directory refused the lander's --restore here. A real build
  # in this tree is still seen: its x.py, bootstrap, cargo, targo and rustc
  # processes are candidates themselves, with their own cwd and command line.
  #
  # An AGENT HARNESS executable (codex, claude, agy, muse, grok, kimi: the agents
  # aterm spawns, as atpkg installs them) is the same case one level up and counts
  # by its command line only too. Its argv carries the task prompt, which names
  # targo and rustc in prose, and it starts in the superproject: measured
  # 2026-10-31, a read-only codex prep task (pid 87525, started 00:28, no child
  # but its code-mode host) whose prompt said "installed genuine targo identity"
  # and "stock cargo/rustc builds" held this checkout's --restore at exit 4 for
  # over an hour. A build it runs is its own candidate. The executable's NAME is
  # read from the whole comm field: atpkg installs agents under "Application
  # Support", so the second whitespace field is "/Users/<u>/Library/Application".
  #
  # EVERY candidate is examined (2026-09-29). This used to keep only the 40 lowest
  # PIDs (`| head -40`). On this machine ~140 compiler processes run at once, so the
  # 40 lowest were other lanes' long-running builds, and a build started in THIS
  # checkout after them — a higher PID — was never looked at: the guard failed OPEN
  # exactly when the box was busiest.
  local cands pid_csv by_cmd by_cwd cmd_only
  cands="$( { pgrep -f 'x\.py|[/ ]cargo |[/ ]rustc |[/ ]targo ' 2>/dev/null
              pgrep -x bootstrap 2>/dev/null; } | sort -un)"
  [ -n "$cands" ] || return 0

  if ! command -v lsof >/dev/null 2>&1; then
    # No way to read cwd: fall back to the broad list. Over-refusing is the safe
    # direction for a guard whose failure mode is a corrupted build.
    printf '%s\n' "$cands"
    return 0
  fi

  pid_csv="$(printf '%s' "$cands" | tr '\n' ',' | sed 's/,$//')"
  by_cmd="$(ps -o pid=,command= -p $(printf '%s' "$cands" | tr '\n' ' ') 2>/dev/null \
            | cmdlines_naming_root)"
  cmd_only="$(ps -o pid=,comm= -p $(printf '%s' "$cands" | tr '\n' ' ') 2>/dev/null \
            | awk '{ n = $0; sub(/^ *[0-9]+ /, "", n); sub(/.*\//, "", n); sub(/^-/, "", n)
                     if (n ~ /^(sh|bash|zsh|dash|ksh|mksh|fish|codex|claude|agy|muse|grok|kimi)$/) printf " %s ", $1 }')"
  by_cwd="$(lsof -a -d cwd -p "$pid_csv" -Fpn 2>/dev/null \
            | awk -v root="$ROOT" -v cmd_only="$cmd_only" '
                /^p/ { pid = substr($0, 2) }
                /^n/ { path = substr($0, 2)
                       if (index(cmd_only, " " pid " ")) next
                       if (path == root || index(path, root "/") == 1) print pid }')"
  printf '%s\n%s\n' "$by_cmd" "$by_cwd" | grep -E '^[0-9]+$' | sort -un
}

do_restore() {
  if [ "${#SAFE_ROWS[@]}" -eq 0 ]; then
    echo "submodule_sync --restore: nothing is provably safe to restore."
    [ "$N_REVIEW" -gt 0 ] && echo "  $N_REVIEW module(s) need a human; see scripts/submodule_sync.sh"
    return
  fi

  local pids rec parent rel display restored_head key i restore_error restore_rc rc=0
  local restored_keys=()
  while [ "${#SAFE_ROWS[@]}" -gt 0 ]; do
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

    # A parent checkout may expose children or change their pins. Restore only
    # one row from a classification, then walk the resulting tree again before
    # trusting any more safety decisions. Never use a stale child's old pin.
    rec="${SAFE_ROWS[0]}"
    display="$(field "$rec" 1)"; parent="$(field "$rec" 2)"; rel="$(field "$rec" 3)"
    key="${parent}${TAB}${rel}${TAB}$(field "$rec" 8)"
    i=0
    while [ "$i" -lt "${#restored_keys[@]}" ]; do
      if [ "${restored_keys[$i]}" = "$key" ]; then
        echo "submodule_sync --restore: REFUSED — $display moved again after restoration." >&2
        exit 2
      fi
      i=$((i + 1))
    done
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
    # Keep native Git diagnostics: missing descendant objects, lock failures,
    # permissions and transport errors must not collapse to a bare FAILED.
    if restore_error="$(restore_module "$parent" "$rel" "$(field "$rec" 8)" "$(field "$rec" 4)" 2>&1 >/dev/null)"; then
      restored_head="$(git -C "$parent/$rel" rev-parse HEAD 2>/dev/null)"
      if [ "$restored_head" != "$(field "$rec" 8)" ]; then
        printf 'FAILED (checkout did not reach the selected pin)\n'
        rc=1
        break
      fi
      printf 'ok (%.8s)\n' "$restored_head"
      # What the shared store could not do, when the private clone then did.
      [ -z "$restore_error" ] || printf '%s\n' "$restore_error" | grep -e '^submodule_sync' -e '^net: ' >&2 || true
      restored_keys+=("$key")
    else
      restore_rc=$?
      printf 'FAILED (git exit %s)\n' "$restore_rc"
      [ -z "$restore_error" ] || printf '%s\n' "$restore_error" >&2
      rc=1
      break
    fi
    scan_modules || exit $?
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
  if [ "$rc" -eq 0 ]; then
    materialize_source_witnesses || exit $?
    emit_quiet
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
