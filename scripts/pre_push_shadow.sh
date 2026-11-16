#!/usr/bin/env bash
# pre_push_shadow.sh — D13 stage C in SHADOW mode: judge each pushed tree from a
# real (sparse) checkout of that tree, and log where that verdict differs from
# the live pre-push run. ADVISORY: it never blocks, never prints to the pushing
# terminal, and nothing reads its exit status.
#
# WHY (docs/DECISION_QUEUE.md D13, ruled 2026-09-28: C + A, staged). The
# pre-push hook runs every `push` row from the PUSHING CHECKOUT, but a push
# publishes the pushed commits' trees. A row that reads the working tree judges
# local state the push does not publish: it passes a bad push (the defect is in
# a non-HEAD ref) and refuses a good one (the defect is local WIP).
# docs/issues/2026-09-28-push-lanes-judge-the-checkout-not-the-push.md
# reproduces both directions. Option C runs those rows in a checkout of each
# pushed tree instead. The ruling stages it: this shadow first, promoted to
# enforcing only on measured evidence from real pushes (no false difference,
# and every difference a real one). This script produces that evidence.
#
# HOW IT IS STARTED. scripts/hooks/pre-push launches it fully detached (its own
# session, stdin = the pushed-ref lines, stdout/stderr = the log) just before
# the hook exits, after the live verdict is final, and never waits for it.
# It inherits no fd above 2 (git's transport pipes stay the push's). The hook
# passes --common (the common git dir, so a GIT_DIR/--work-tree push with no
# .git in the work tree is still found), --live (each lane's graded outcome,
# plus the dates the live run judged by), --in-dir (its own copies, removed on
# exit) and --remote. TRUST_PRE_PUSH_SHADOW=0 in the pushing environment skips
# the launch. It can also be run by hand:
#
#   printf 'refs/heads/main %s refs/heads/main %s\n' "$(git rev-parse HEAD)" \
#       "$(git rev-parse HEAD~1)" | bash scripts/pre_push_shadow.sh [--live FILE]
#
# (without --log it picks the default log path and also prints to stdout).
#
# WHAT IT DOES, per push:
#   1. takes a lock (mkdir; the holder is "<pid> <start time>", plus that start
#      time with no time zone or locale in `start_utc`, so a reused
#      pid is not mistaken for it; a live holder means this run is SKIPPED,
#      logged; a lock with no pid yet is a holder mid-take for one minute);
#   2. removes worktrees left by an earlier crashed run (only its own: admin
#      entries whose gitdir lies under <common-dir>/trust-shadow/, and only
#      when the pid in the path's name is no longer running);
#   3. for each DISTINCT non-deletion pushed tree (at most MAX_TREES; the rest
#      are logged as skipped): `git worktree add --detach --no-checkout` under
#      <common-dir>/trust-shadow/wt-<pid>-<n>, writes a sparse cone covering the
#      shadowed lanes' read roots, and checks it out;
#   4. reads the lane commands from THAT tree's `tests/run_trust_comprehensive_harness.sh
#      --list push`, so the command strings are the manifest's, never a copy;
#   5. runs each SHADOW lane there, in the hook's exec form, with
#      TRUST_PUSHED_REFS and TRUST_PUSH_REMOTE UNSET — the lane's standing
#      reading on a real clean checkout of the pushed tree, which is the
#      semantics the push rows are meant to have — under a per-lane timeout;
#   6. writes one line per (tree, lane), for diagnosis:
#        SHADOW <lane> tree=<sha12> live=<outcome/rc> shadow=<rc> AGREE|DIFFER|NOT-RUN|NO-LIVE
#      (TREE-AGREE|TREE-DIFFER when the push has more than one tree, see
#      below), then ONE line per lane for the push, which is the evidence:
#        SHADOW-PUSH <lane> live=<outcome/rc> shadow=<red|skipped|green|-> trees=<judged>/<pushed> AGREE|DIFFER|NOT-RUN|NO-LIVE
#      and a final `SHADOW-SUMMARY` line; keeps the newest KEEP_LOGS logs.
#   Worktrees are removed on every exit path (EXIT/TERM/INT trap), and a
#   SIGKILLed run's leftovers are removed by the next run's step 2.
#
# AGREE/DIFFER compares VERDICT CLASSES, not raw exit codes: green (exit 0),
# skipped (exit 0 with a `SKIPPED: ` line, as the hook grades it), red (any
# nonzero exit). The live class comes from the lane's own exit, not the hook's
# grade, so a QUARANTINED or optional (WARN) red lane is red, and a "GREEN but
# still quarantined" FAIL is green. NO-LIVE: the lane ran here but the live run
# has no row for it (a hand run, or a lane the checkout's manifest lacks).
# NOT-RUN: the pushed tree's manifest has no such row, its script is absent
# from the pushed tree, the checkout could not be made, the lane ran out of
# its per-lane budget (shadow=timeout/<rc>; also counted as `timeout=`), or —
# for a lane that judges by the date (ledger-expirations: UTC; help-surfaces:
# local) — the live run and this one ran on different dates, so a difference
# could be the calendar rather than the tree.
#
# PUSH LEVEL. The live run gives ONE verdict per lane for the whole push; the
# enforcing stage C would refuse the push when ANY pushed tree is red. So the
# push-level shadow verdict is the worst class over the pushed trees (red >
# skipped > green), and that is what is compared with the live one. A per-tree
# line on its own is not push evidence: a push of a green tree and a red tree
# that the live run refuses is an AGREE (both refuse), though the green tree's
# own line differs from the live verdict. Red dominates, so a red tree settles
# the push even when another tree reached no verdict; otherwise a tree without
# a verdict (NOT-RUN, timeout) or a tree over MAX_TREES leaves the push-level
# verdict unknown: NOT-RUN. SHADOW-SUMMARY's agree=, differ=, not-run= and
# no-live= count SHADOW-PUSH lines; timeout= and tree-differ= count (tree,
# lane) lines.
#
# SHADOW LANES and their read roots. Each root set was derived by reading the
# lane's script (re-verified at cb8406c0bf, 2026-09-29); where a script names its inputs in DATA, the
# cone is derived from the pushed tree's own copy of that data (cone_for below),
# so a manifest edit moves the cone with it. `scripts/` and
# `tests/trust-comprehensive/` are always in the cone (every lane's own script,
# and the harness, a top-level file of tests/).
#
#   fast.fixture-span-paths      the ROOTS tuple of scripts/check_fixture_span_paths.py
#                                (crates/trust-vcgen/tests/fixtures, crates/trust-vcgen/fixtures,
#                                targo-trust/src/fixtures), its `.allow` file in scripts/,
#                                and `git ls-files` (the worktree's index: a real one here)
#   fast.run-make-fixture-lex    tests/run-make (it globs tests/run-make/trust-*/**/*.rs)
#   fast.help-surfaces           data/help_surfaces.json and, from it: scan_roots,
#                                program_roots, extra_surfaces, every rostered/not_help
#                                path, every `describes` path, and every include_str!/
#                                include_bytes! target of a rostered .rs surface (R8)
#   fast.conversion-guide-paths  docs/TWO_LANGUAGE_CONVERSION_GUIDE.md and every path it
#                                names (the lane `-e` tests each one)
#   fast.trust-ir-tag-families   scripts/trust_ir_tag_families.json and its scan_roots
#   fast.trust-ir-seam-blockers  crates/trust-thir-lower/src/crate_module.rs
#                                (`_DECL_KIND_SOURCE` of trust_ir_producer_scorecard.py)
#   fast.ledger-expirations      every `REPO_ROOT / ... .toml` its script names: the seven
#                                ledgers under tests/upstream-rust, tests/trust-comprehensive,
#                                tests/trust-added, plus the exempt baseline.toml. Those three
#                                directories are ALSO always in the cone (0.2 MB): the lane
#                                reads a missing ledger as empty, so a parse that missed one
#                                would be a silent fail-open, not a visible NOT-RUN
#   fast.trust-ir-seam-blockers-selftest   the same file as seam-blockers (it ends by
#                                re-running that check); the rest is embedded cases
#   fast.two-language-wire-grader-selftest tests/two-language-programs (its own script)
#                                and tests/e2e_two_language_programs.sh, a top-level file
#                                of tests/, which every cone carries (below)
#
# Cone mode always carries the files directly inside every ancestor directory
# of a cone entry, so the harness (tests/*.sh) and each rostered surface's
# nearest Cargo.toml (help-surfaces' own_crate walk) are always present.
#
# A lane that reads OUTSIDE its cone sees a MISSING file. Some lanes treat a
# missing input as empty (the issue's fail-closed caveat), so a cone that has
# gone stale against its lane can read AGREE while judging less than the live
# run. That is the known weak point of this stage; any new input a shadow lane
# grows must be added to cone_for in the same commit.
#
# EXCLUDED, and why (these need stage-A per-tree reads, not a checkout):
#   fast.pin-coherence            reads submodule stores, worktree HEADs and dirt;
#                                 a checkout here has no submodules
#   fast.call-summary-labels      reads the trust-mc submodule worktree
#   fast.seed-freshness           reads bootstrap.toml / RUST_BOOTSTRAP_CONFIG and
#                                 build/*/stage0 (machine state, see D12)
#   fast.toolchain-coherence      `targo metadata` through submodule worktrees, build/, PATH
#   fast.audited-trust-spec-sources  NOT faithful even for its crates-only part: it is
#                                 one exit code over both halves, and in a checkout with
#                                 no submodules its first-party providers (ny) are
#                                 excused as UNRESOLVED, while the live run resolves
#                                 them from the local ny worktree. Its verdict here and
#                                 live would differ for reasons that are not the pushed
#                                 tree, which is exactly the false DIFFER this stage
#                                 must not produce. Its walk also spans compiler/,
#                                 library/, src/tools/ and all of crates/ (517 MB).
#   fast.call-summary-labels-selftest, fast.dependency-constellation-selftest
#                                 their controls read the trust-mc / ny submodule worktrees
#   fast.crates-tests-scoped-selftest  reads every crate's [features] table: a cone
#                                 of all of crates/ (517 MB) for a low-priority row
#   fast.revert-rationale-test    builds git fixtures against HEAD-relative state (11 s);
#                                 a detached shadow checkout is not the same subject, so
#                                 a DIFFER there would not be evidence about the push
#   fast.bridge-pin, fast.first-party-pin-lattice, fast.ledger-expirations' push
#   reading, fast.revert-rationale, fast.measurement-provenance(-test): fixed per
#   tree by stage A; ledger-expirations is still shadowed because its STANDING
#   reading on a checkout is the target this stage measures against.
#   The other `*-selftest`/`*-test` rows, the pushed-refs readers and scoped.* rows
#   are not worktree readers of the push (issue table: `n/a`, `none`, `pushed-refs`).
#
# IT NEVER MODIFIES the main worktree, its index, any ref, or any config. The
# sparse cone is written to the linked worktree's OWN info/sparse-checkout and
# enabled with `git -c core.sparseCheckout=true` for the one read-tree that
# needs it, never with `git sparse-checkout`, which would set
# extensions.worktreeConfig in the shared config. The only shared state it
# touches is <common-dir>/worktrees/<its own wt-*> (created and removed) and
# <common-dir>/trust-shadow/ (logs, lock, worktrees).
#
# Tunables (environment): TRUST_PRE_PUSH_SHADOW_TIMEOUT (seconds per lane,
# default 300, at most 600: MAX_TREES x 9 lanes x 600 s = 4.5 h stays inside
# the 6-hour window after which a lock or a leftover is stale whatever its pid).
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
set -uo pipefail

SHADOW_LANES="fast.fixture-span-paths fast.run-make-fixture-lex fast.help-surfaces fast.conversion-guide-paths fast.trust-ir-tag-families fast.trust-ir-seam-blockers fast.trust-ir-seam-blockers-selftest fast.two-language-wire-grader-selftest fast.ledger-expirations"
EXCLUDED_NOTE="fast.pin-coherence fast.call-summary-labels(-selftest) fast.seed-freshness fast.toolchain-coherence fast.audited-trust-spec-sources fast.dependency-constellation-selftest (submodules or machine state; see this script's header)"
MAX_TREES=3
KEEP_LOGS=50
# For the two git commands that WRITE (worktree add, read-tree): no hooks, no
# fsmonitor daemon, no submodule recursion, whatever the user's config says.
GIT_QUIET_CFG=(-c core.hooksPath=/dev/null -c core.fsmonitor=false -c submodule.recurse=false)
LANE_TIMEOUT="${TRUST_PRE_PUSH_SHADOW_TIMEOUT:-300}"
case "$LANE_TIMEOUT" in ''|*[!0-9]*) LANE_TIMEOUT=300 ;; esac
[ "$LANE_TIMEOUT" -gt 600 ] && LANE_TIMEOUT=600
[ "$LANE_TIMEOUT" -lt 1 ] && LANE_TIMEOUT=1
STALE_MIN=360

LOG="" LIVE="" IN_DIR="" REMOTE="" COMMON_ARG=""
while [ $# -gt 0 ]; do
  case "$1" in
    --log) LOG="${2:-}"; shift 2 ;;
    --live) LIVE="${2:-}"; shift 2 ;;
    --in-dir) IN_DIR="${2:-}"; shift 2 ;;
    --common) COMMON_ARG="${2:-}"; shift 2 ;;
    --remote) REMOTE="${2:-}"; shift 2 ;;
    -h|--help) sed -n '2,40p' "$0"; exit 0 ;;
    *) echo "pre_push_shadow: unknown argument: $1" >&2; exit 2 ;;
  esac
done
# Before the EXIT trap exists: an early refusal still removes the hook's input
# dir, which nothing else would.
early_exit() {
  echo "pre_push_shadow: $1; nothing was judged" >&2
  [ -n "$IN_DIR" ] && rm -rf "${IN_DIR:?}"
  exit 2
}

# The hook passes the remote URL; a log must not keep `user:token@` from it.
REMOTE="$(printf '%s' "$REMOTE" | sed -E 's#^([A-Za-z][A-Za-z0-9+.-]*://)[^/@]*@#\1#')"

# The push context is the LIVE run's reading; the shadow's is the standing one.
unset TRUST_PUSHED_REFS TRUST_PUSH_REMOTE
for git_local_var in $(git rev-parse --local-env-vars 2>/dev/null); do
  unset "$git_local_var"
done
# Lanes import sibling modules; do not leave __pycache__ in the checkout.
export PYTHONDONTWRITEBYTECODE=1

# The hook names the common dir: a `git --git-dir=X --work-tree=Y push` has no
# .git in Y, and GIT_DIR was unset above. Every git command below reads only
# the common dir (objects, worktree admin) or runs `-C` inside a shadow
# worktree, so running from the common dir itself is enough.
if [ -n "$COMMON_ARG" ]; then
  cd "$COMMON_ARG" 2>/dev/null || early_exit "cannot enter the common git dir $COMMON_ARG"
fi
COMMON="$(git rev-parse --path-format=absolute --git-common-dir 2>/dev/null)" \
  || early_exit "not inside a git repository ($PWD)"
mkdir -p "$COMMON/trust-shadow" || early_exit "cannot create $COMMON/trust-shadow"
SHADOW_ROOT="$(cd "$COMMON/trust-shadow" && pwd -P)" || early_exit "cannot enter $COMMON/trust-shadow"
COMMON="$(cd "$COMMON" && pwd -P)"

REFS="$(cat 2>/dev/null || true)"

first_sha12() {
  local _l sha _r _s
  while read -r _l sha _r _s; do
    case "$sha" in ''|*[!0]*) ;; *) continue ;; esac
    [ -n "$sha" ] && { printf '%s' "${sha:0:12}"; return; }
  done <<< "$REFS"
  printf '000000000000'
}

if [ -z "$LOG" ]; then
  LOG="$SHADOW_ROOT/$(date -u +%Y%m%dT%H%M%SZ)-$(first_sha12).log"
  [ -e "$LOG" ] && LOG="${LOG%.log}-$$.log"
  # By hand: to the log AND the terminal.
  exec > >(tee -a "$LOG") 2>&1
else
  exec >>"$LOG" 2>&1
fi

START_EPOCH="$(date +%s)"
echo "TRUST PRE-PUSH SHADOW (D13 stage C; advisory — never blocks a push)"
echo "started:  $(date -u +%Y-%m-%dT%H:%M:%SZ)  pid=$$"
echo "repo:     $COMMON${REMOTE:+  remote=$REMOTE}"
echo "live:     ${LIVE:-none (hand run: every row is NO-LIVE)}"
echo "lanes:    $SHADOW_LANES"
echo "excluded: $EXCLUDED_NOTE"
echo "timeout:  ${LANE_TIMEOUT}s per lane"
if [ -z "${REFS//[[:space:]]/}" ]; then
  echo "pushed:   (none)"
else
  while read -r l s r d; do
    [ -n "$l" ] || continue
    echo "pushed:   $l ${s:0:12} -> $r ${d:0:12}"
  done <<< "$REFS"
fi

N_AGREE=0 N_DIFFER=0 N_NOTRUN=0 N_NOLIVE=0 N_TIMEOUT=0 N_TREES=0 N_SKIPTREES=0 N_TREEDIFFER=0
summary() {
  echo "SHADOW-SUMMARY trees=$N_TREES skipped-trees=$N_SKIPTREES agree=$N_AGREE differ=$N_DIFFER not-run=$N_NOTRUN no-live=$N_NOLIVE timeout=$N_TIMEOUT tree-differ=$N_TREEDIFFER elapsed=$(( $(date +%s) - START_EPOCH ))s${1:+ $1}"
}

# ---- lock -----------------------------------------------------------------
LOCK="$SHADOW_ROOT/lock"
HAVE_LOCK=0
# A holder is "<pid> <start time>": a dead holder whose pid number an unrelated
# process has since taken is still recognised as dead.
#
# That start time is `ps -o lstart=`, whose text follows the caller's TZ and
# LC_TIME, so a live holder that took the lock in one zone or locale read as a
# reused pid in another, and its lock was removed under it (EW18-LOCKUTC-1,
# 2026-11-05). A holder therefore also writes `start_utc`: the same start time
# under LC_ALL=C TZ=UTC0, which reads the same in every caller's environment. It
# is a separate file so the `pid` line keeps its format for a copy of this script
# that predates it, and it is written BEFORE `pid`, so a reader that sees a pid
# line also sees it. A lock with `start_utc` is judged by it alone; a lock
# without it (taken by an older copy) by the `pid` line's start, as before. An
# empty `start_utc` cannot judge, so it leaves pid liveness alone to decide, as
# an empty start on the `pid` line does, and never falls back to that zoned text.
proc_start() { ps -o lstart= -p "$1" 2>/dev/null | sed 's/^ *//; s/ *$//'; }
proc_start_utc() { LC_ALL=C TZ=UTC0 ps -o lstart= -p "$1" 2>/dev/null | sed 's/^ *//; s/ *$//'; }
ME_START="$(proc_start $$)"
ME_START_UTC="$(proc_start_utc $$)"
take_lock() {
  if mkdir "$LOCK" 2>/dev/null; then
    printf '%s\n' "$ME_START_UTC" >"$LOCK/start_utc"
    echo "$$ $ME_START" >"$LOCK/pid"
    HAVE_LOCK=1
    return 0
  fi
  return 1
}
if ! take_lock; then
  # `pid` first: its writer wrote `start_utc` before it.
  holder_line="$(cat "$LOCK/pid" 2>/dev/null || true)"
  holder="${holder_line%% *}"
  holder_start=""
  case "$holder_line" in *" "*) holder_start="${holder_line#* }" ;; esac
  holder_has_utc=0 holder_start_utc=""
  if [ -f "$LOCK/start_utc" ]; then
    holder_has_utc=1
    holder_start_utc="$(cat "$LOCK/start_utc" 2>/dev/null || true)"
  fi
  stale=0
  case "$holder" in
    '')
      # A holder between its mkdir and its pid write looks empty: only an
      # empty lock older than a minute is abandoned.
      [ -n "$(find "$LOCK" -maxdepth 0 -mmin +1 2>/dev/null)" ] && stale=1 ;;
    *[!0-9]*) stale=1 ;;
    *)
      if ! kill -0 "$holder" 2>/dev/null; then stale=1
      elif [ "$holder_has_utc" -eq 1 ]; then
        if [ -n "$holder_start_utc" ] && [ "$(proc_start_utc "$holder")" != "$holder_start_utc" ]; then stale=1
        fi
      elif [ -n "$holder_start" ] && [ "$(proc_start "$holder")" != "$holder_start" ]; then stale=1
      fi ;;
  esac
  # A lock older than six hours is stale whoever holds its pid number now.
  [ -n "$(find "$LOCK" -maxdepth 0 -mmin +$STALE_MIN 2>/dev/null)" ] && stale=1
  if [ "$stale" -eq 1 ]; then
    echo "lock:     removing a stale lock (pid ${holder:-?} is not running)"
    # Only if it still names the holder judged stale: another run may have
    # taken the lock over in the meantime.
    if [ "$(cat "$LOCK/pid" 2>/dev/null || true)" = "$holder_line" ]; then
      rm -rf "${LOCK:?}"
    fi
    take_lock || true
  fi
  if [ "$HAVE_LOCK" -ne 1 ]; then
    echo "SHADOW-SKIPPED another shadow run holds $LOCK (pid ${holder:-?}); nothing was judged for this push"
    [ -n "$IN_DIR" ] && rm -rf "${IN_DIR:?}"
    summary "skipped=lock-held"
    exit 0
  fi
fi

# ---- cleanup --------------------------------------------------------------
WORK="$SHADOW_ROOT/run-$$"
mkdir -p "$WORK"
LANE_PID="" WATCH_PID=""

# Remove one shadow worktree and its admin entry. Only ever called on paths
# under $SHADOW_ROOT/wt-*.
drop_worktree() {
  local wt="$1" admin
  case "$wt" in "$SHADOW_ROOT"/wt-*) ;; *) return 0 ;; esac
  git worktree remove --force --force "$wt" >/dev/null 2>&1 || true
  # If git could not (a half-made worktree), remove the pieces by hand: the
  # directory, and the admin entry whose gitdir names it — nobody else's.
  for admin in "$COMMON"/worktrees/*; do
    [ -f "$admin/gitdir" ] || continue
    if [ "$(cat "$admin/gitdir" 2>/dev/null)" = "$wt/.git" ]; then
      rm -rf "${admin:?}"
    fi
  done
  rm -rf "${wt:?}"
}

kill_lane() {
  if [ -n "$LANE_PID" ]; then
    kill -TERM -- "-$LANE_PID" 2>/dev/null || kill -TERM "$LANE_PID" 2>/dev/null
  fi
  [ -n "$WATCH_PID" ] && kill -TERM "$WATCH_PID" 2>/dev/null
  return 0
}

cleanup() {
  kill_lane
  local wt
  for wt in "$SHADOW_ROOT"/wt-$$-*; do
    [ -e "$wt" ] || continue
    drop_worktree "$wt"
  done
  rm -rf "${WORK:?}"
  [ -n "$IN_DIR" ] && rm -rf "${IN_DIR:?}"
  if [ "$HAVE_LOCK" -eq 1 ] && [ "$(cat "$LOCK/pid" 2>/dev/null)" = "$$ $ME_START" ]; then
    rm -rf "${LOCK:?}"
  fi
  HAVE_LOCK=0
}
trap cleanup EXIT
trap 'echo "SHADOW-ABORTED by a signal; worktrees removed"; summary "aborted=signal"; exit 143' TERM
# Detached, it has no terminal; run by hand, Ctrl-C still ends it cleanly.
trap 'echo "SHADOW-ABORTED by SIGINT; worktrees removed"; summary "aborted=signal"; exit 130' INT
trap '' HUP

# ---- stale state from earlier crashed runs --------------------------------
# Every shadow path carries its run's pid (wt-<pid>-<n>, run-<pid>). A path
# whose pid is still running belongs to a live run and is left alone: the lock
# already keeps two runs apart, and this keeps even a lost stale-lock race
# (two runs both judging the same dead holder stale) from deleting a live
# run's checkout under it. A path older than STALE_MIN is stale whatever its
# pid, as the lock is: no run lasts that long (LANE_TIMEOUT's cap), and an
# unrelated process that reused a dead run's pid must not keep its leftovers
# forever.
owner_alive() {  # <path> -> 0 when the pid in its name is a running process other than us
  local base="${1##*/}" pid
  pid="${base#wt-}"; pid="${pid#run-}"; pid="${pid%%-*}"
  case "$pid" in ''|*[!0-9]*) return 1 ;; esac
  [ -n "$(find "$1" -maxdepth 0 -mmin +$STALE_MIN 2>/dev/null)" ] && return 1
  [ "$pid" != "$$" ] && kill -0 "$pid" 2>/dev/null
}
for admin in "$COMMON"/worktrees/*; do
  [ -f "$admin/gitdir" ] || continue
  gd="$(cat "$admin/gitdir" 2>/dev/null)"
  case "$gd" in
    "$SHADOW_ROOT"/wt-*/.git)
      owner_alive "${gd%/.git}" && continue
      echo "prune:    removing a stale shadow worktree ${gd%/.git}"
      drop_worktree "${gd%/.git}" ;;
  esac
done
for leftover in "$SHADOW_ROOT"/wt-* "$SHADOW_ROOT"/run-*; do
  [ -e "$leftover" ] || continue
  [ "$leftover" = "$WORK" ] && continue
  owner_alive "$leftover" && continue
  echo "prune:    removing leftover $leftover"
  rm -rf "${leftover:?}"
done
# Input dirs a SIGKILLed run could not remove (the hook makes one per push).
find "$SHADOW_ROOT" -maxdepth 1 -name '*.log.in' -type d -mmin +60 -exec rm -rf {} + 2>/dev/null

# ---- live results ---------------------------------------------------------
# One line per live lane: id <TAB> outcome <TAB> rc <TAB> command.
live_get() {
  # Sets live_outcome, live_rc, live_cmd for lane $1; returns 1 when absent.
  live_outcome="" live_rc="" live_cmd=""
  [ -n "$LIVE" ] && [ -f "$LIVE" ] || return 1
  local id o r c
  while IFS=$'\t' read -r id o r c; do
    if [ "$id" = "$1" ]; then
      live_outcome="$o" live_rc="$r" live_cmd="$c"
      return 0
    fi
  done <"$LIVE"
  return 1
}

class_of() {  # rc, output-file -> green|skipped|red
  if [ "$1" != "0" ]; then echo red
  elif [ -n "${2:-}" ] && grep -qE '^[[:space:]]*SKIPPED: ' "$2" 2>/dev/null; then echo skipped
  else echo green
  fi
}
live_class() {
  case "$live_outcome" in SKIPPED) echo skipped; return ;; esac
  if [ "$live_rc" = "0" ]; then echo green; else echo red; fi
}

# The dates the live lanes ran on (`# live-dates start|end <utc> <local>`,
# written by the hook when it starts and ends its lanes). Empty for a hand run.
LIVE_UTC="" LIVE_LOCAL=""
if [ -n "$LIVE" ] && [ -f "$LIVE" ]; then
  while read -r h k _w u l; do
    [ "$h $k" = "# live-dates" ] || continue
    case " $LIVE_UTC " in *" $u "*) ;; *) LIVE_UTC="${LIVE_UTC:+$LIVE_UTC }$u" ;; esac
    case " $LIVE_LOCAL " in *" $l "*) ;; *) LIVE_LOCAL="${LIVE_LOCAL:+$LIVE_LOCAL }$l" ;; esac
  done <"$LIVE"
fi
echo "live-dates: utc=${LIVE_UTC:-?} local=${LIVE_LOCAL:-?}"
# Which calendar a lane's verdict depends on (read from the scripts: the
# ledger's as_of is the UTC date; help-surfaces' R4 age is the local date).
date_clock_of() {
  case "$1" in
    fast.ledger-expirations) echo utc ;;
    fast.help-surfaces) echo local ;;
    *) echo none ;;
  esac
}
# straddled <clock> <date-before> <date-after>: 0 when the live run and this
# lane's run did not all fall on one date of that clock.
straddled() {
  local live d
  case "$1" in utc) live="$LIVE_UTC" ;; local) live="$LIVE_LOCAL" ;; *) return 1 ;; esac
  [ -n "$live" ] || return 1
  for d in $live "$2" "$3"; do
    [ "$d" = "${live%% *}" ] || return 0
  done
  return 1
}

# Per-lane tallies over the pushed trees, indexed by the lane's position in
# SHADOW_LANES: how many trees gave each class, and how many gave none.
P_RED=() P_SKIP=() P_GREEN=() P_UNK=()
li=0
for lane in $SHADOW_LANES; do
  P_RED[li]=0 P_SKIP[li]=0 P_GREEN[li]=0 P_UNK[li]=0
  li=$((li + 1))
done
tally() {  # tally <lane-index> <red|skipped|green|unknown>
  case "$2" in
    red) P_RED[$1]=$(( ${P_RED[$1]} + 1 )) ;;
    skipped) P_SKIP[$1]=$(( ${P_SKIP[$1]} + 1 )) ;;
    green) P_GREEN[$1]=$(( ${P_GREEN[$1]} + 1 )) ;;
    *) P_UNK[$1]=$(( ${P_UNK[$1]} + 1 )) ;;
  esac
}

# ---- cone -----------------------------------------------------------------
# Prints the cone-mode sparse-checkout patterns for tree $1 (a commit), then a
# `# recursive:` and a `# files-of:` comment. Every input is read from the
# pushed commit's objects, never from a checkout.
cone_for() {
  python3 - "$1" <<'PY'
import json
import posixpath
import re
import subprocess
import sys

sha = sys.argv[1]


def blob(path):
    p = subprocess.run(["git", "cat-file", "blob", f"{sha}:{path}"], capture_output=True)
    return p.stdout.decode("utf-8", "replace") if p.returncode == 0 else None


recursive = {"scripts", "tests/trust-comprehensive"}
files_of = set()
wanted = []  # paths whose kind (tree/blob) decides how they enter the cone


def want(path):
    path = posixpath.normpath(str(path).strip().strip("/"))
    if path and path != "." and not path.startswith(".."):
        wanted.append(path)


def strings(text):
    return re.findall(r'"([^"\n]+)"', text or "")


# fast.fixture-span-paths: the ROOTS tuple (its .allow sits in scripts/).
src = blob("scripts/check_fixture_span_paths.py") or ""
m = re.search(r"^ROOTS\s*=\s*\((.*?)\)", src, re.S | re.M)
for p in (strings(m.group(1)) if m else []) or [
        "crates/trust-vcgen/tests/fixtures", "crates/trust-vcgen/fixtures", "targo-trust/src/fixtures"]:
    want(p)

# fast.run-make-fixture-lex: tests/run-make/trust-*.
recursive.add("tests/run-make")

# fast.help-surfaces: the manifest and everything it names.
src = blob("scripts/check_help_surfaces.py") or ""
m = re.search(r'^MANIFEST\s*=\s*"([^"]+)"', src, re.M)
manifest = m.group(1) if m else "data/help_surfaces.json"
want(manifest)
try:
    man = json.loads(blob(manifest) or "{}")
except ValueError:
    man = {}
if isinstance(man, dict):
    for key in ("scan_roots", "program_roots", "extra_surfaces"):
        for p in man.get(key) or []:
            if isinstance(p, str):
                want(p)
    for key in ("surfaces", "not_help"):
        for row in man.get(key) or []:
            if not isinstance(row, dict):
                continue
            path = row.get("path")
            if isinstance(path, str):
                want(path)
                if path.endswith(".rs"):
                    # R8: an include_str!/include_bytes! target is read by path.
                    for t in re.findall(r'include_(?:str|bytes)!\s*\(\s*"([^"]+)"', blob(path) or ""):
                        want(posixpath.join(posixpath.dirname(path), t))
            for p in row.get("describes") or []:
                if isinstance(p, str):
                    want(p)

# fast.conversion-guide-paths: the guide and every path it names.
src = blob("scripts/check_conversion_guide_paths.sh") or ""
m = re.search(r'^GUIDE="\$ROOT/([^"]+)"', src, re.M)
guide = m.group(1) if m else "docs/TWO_LANGUAGE_CONVERSION_GUIDE.md"
want(guide)
# The lane's own extraction, run by the same tool (`grep -oE`, POSIX leftmost-
# longest), so the cone names exactly the paths the lane will `-e` test.
g = subprocess.run(
    ["grep", "-oE", r"(tests|docs|compiler|crates|scripts|src)/[A-Za-z0-9_./-]+\.(rs|lean|clean|md|py|sh|toml)"],
    input=(blob(guide) or "").encode(), capture_output=True)
for p in g.stdout.decode("utf-8", "replace").splitlines():
    want(p)

# fast.trust-ir-tag-families: the map's scan_roots.
try:
    spec = json.loads(blob("scripts/trust_ir_tag_families.json") or "{}")
except ValueError:
    spec = {}
for root in (spec.get("scan_roots") or []) if isinstance(spec, dict) else []:
    if isinstance(root, dict) and isinstance(root.get("path"), str):
        want(root["path"])

# fast.trust-ir-seam-blockers: _DECL_KIND_SOURCE.
src = blob("scripts/trust_ir_producer_scorecard.py") or ""
m = re.search(r"^_DECL_KIND_SOURCE\s*=\s*os\.path\.join\((.*?)\)", src, re.M)
want("/".join(strings(m.group(1))) if m else "crates/trust-thir-lower/src/crate_module.rs")

# fast.ledger-expirations: every `REPO_ROOT / "a" / "b.toml"` it names.
src = blob("scripts/check_ledger_expirations.py") or ""
for chain in re.findall(r'REPO_ROOT((?:\s*/\s*"[^"]+")+)', src):
    want("/".join(strings(chain)))
# ...and its three ledger directories whole, whatever the parse found: the
# lane reads a missing ledger as empty (a fail-open), never as an error.
recursive.update({"tests/upstream-rust", "tests/trust-comprehensive", "tests/trust-added"})

# fast.two-language-wire-grader-selftest: its own directory; the battery
# script it lints is a top-level file of tests/, which cone mode carries.
recursive.add("tests/two-language-programs")

# Classify every wanted path by its kind in the pushed tree, in one batch.
if wanted:
    p = subprocess.run(["git", "cat-file", "--batch-check=%(objecttype)"],
                       input="".join(f"{sha}:{w}\n" for w in wanted).encode(), capture_output=True)
    kinds = p.stdout.decode("utf-8", "replace").splitlines()
    for path, kind in zip(wanted, kinds):
        if kind == "tree":
            recursive.add(path)
        elif kind == "blob":
            files_of.add(posixpath.dirname(path))
        # absent from the pushed tree: nothing to check out; the lane sees the
        # absence exactly as a full checkout would.


def under(path, roots):
    return any(path == r or path.startswith(r + "/") for r in roots)


recursive = {r for r in recursive if not any(r != o and r.startswith(o + "/") for o in recursive)}
files_of = {d for d in files_of if d and not under(d, recursive)}
parents = set(files_of)
for d in list(recursive) + list(files_of):
    parts = d.split("/")
    for i in range(1, len(parts)):
        parents.add("/".join(parts[:i]))
parents -= recursive


def esc(path):
    return re.sub(r"([\\*?\[\]!#])", r"\\\1", path)


out = ["/*", "!/*/"]
for d in sorted(parents | recursive):
    if d in recursive:
        out.append(f"/{esc(d)}/")
    else:
        out += [f"/{esc(d)}/", f"!/{esc(d)}/*/"]
print("\n".join(out))
print("# recursive: " + " ".join(sorted(recursive)))
print("# files-of: " + " ".join(sorted(files_of)))
PY
}

# ---- one lane under a timeout ---------------------------------------------
# run_lane_timed <dir> <command> <outfile>; sets lane_rc, lane_timed_out.
run_lane_timed() {
  local dir="$1" cmd="$2" out="$3" marker="$WORK/timed-out"
  rm -f "$marker"
  lane_timed_out=0
  # Its own process group, so a timeout reaches every child it started.
  if command -v perl >/dev/null 2>&1; then
    ( cd "$dir" && exec perl -e 'setpgrp(0, 0); exec @ARGV or exit 127' \
        bash -o pipefail -c "$cmd" ) </dev/null >"$out" 2>&1 &
  else
    ( cd "$dir" && exec bash -o pipefail -c "$cmd" ) </dev/null >"$out" 2>&1 &
  fi
  LANE_PID=$!
  local me=$$
  (
    trap 'kill "$s" 2>/dev/null; exit 0' TERM
    sleep "$LANE_TIMEOUT" & s=$!
    wait "$s"
    # A SIGKILLed shadow cannot stop its watchdog; then the lane's group id
    # may belong to someone else by now, so kill nothing.
    kill -0 "$me" 2>/dev/null || exit 0
    : >"$marker"
    kill -TERM -- "-$LANE_PID" 2>/dev/null || kill -TERM "$LANE_PID" 2>/dev/null
    sleep 5
    kill -KILL -- "-$LANE_PID" 2>/dev/null || kill -KILL "$LANE_PID" 2>/dev/null
  ) >/dev/null 2>&1 &
  WATCH_PID=$!
  wait "$LANE_PID"
  lane_rc=$?
  kill -TERM "$WATCH_PID" 2>/dev/null
  wait "$WATCH_PID" 2>/dev/null
  LANE_PID="" WATCH_PID=""
  [ -f "$marker" ] && lane_timed_out=1
  return 0
}

# ---- trees ----------------------------------------------------------------
TREES=""      # "<commit> <tree>" per distinct tree
seen_trees=" "
bad_refs=0
while read -r lref lsha rref rsha; do
  [ -n "$lref" ] || continue
  case "$lsha" in
    *[!0-9a-f]*|'') echo "ref:      malformed pushed-ref line ignored: $lref $lsha $rref $rsha"; bad_refs=1; continue ;;
  esac
  case "$lsha" in *[!0]*) ;; *) continue ;; esac   # a deletion has no tree
  tree="$(git rev-parse --verify --quiet "$lsha^{tree}" 2>/dev/null)" || {
    echo "ref:      $lref ${lsha:0:12} is not a commit in this clone; not judged"
    continue
  }
  case "$seen_trees" in *" $tree "*) continue ;; esac
  seen_trees="$seen_trees$tree "
  N_TREES=$((N_TREES + 1))
  if [ "$N_TREES" -gt "$MAX_TREES" ]; then
    N_SKIPTREES=$((N_SKIPTREES + 1))
    echo "tree:     ${lsha:0:12} ($lref) SKIPPED — only the first $MAX_TREES distinct trees are shadowed"
    continue
  fi
  TREES="$TREES$lsha $tree"$'\n'
done <<< "$REFS"
N_TREES=$((N_TREES - N_SKIPTREES))
if [ -z "$TREES" ]; then
  echo "tree:     no non-deletion pushed tree to judge"
else
  echo "trees:    $(while read -r c t; do [ -n "$c" ] && printf '%s(tree %s) ' "${c:0:12}" "${t:0:12}"; done <<< "$TREES")"
fi

MULTI=0
[ $((N_TREES + N_SKIPTREES)) -gt 1 ] && MULTI=1
n=0
while read -r commit tree; do
  [ -n "$commit" ] || continue
  n=$((n + 1))
  sha12="${commit:0:12}"
  wt="$SHADOW_ROOT/wt-$$-$n"
  t0="$(date +%s)"
  echo
  echo "tree:     $sha12 (tree ${tree:0:12})"
  made=1
  # Absolute admin paths (worktree.useRelativePaths=false), so drop_worktree and
  # the next run's prune can recognise this entry whatever the user's config
  # says; no hooks, no fsmonitor, no submodule recursion.
  if ! git "${GIT_QUIET_CFG[@]}" -c worktree.useRelativePaths=false \
      worktree add --detach --no-checkout "$wt" "$commit" >"$WORK/wt.out" 2>&1; then
    sed 's/^/  | /' "$WORK/wt.out"
    made=0
  else
    wgd="$(git -C "$wt" rev-parse --absolute-git-dir 2>/dev/null)"
    mkdir -p "$wgd/info"
    cone_for "$commit" >"$WORK/cone" 2>"$WORK/cone.err" || made=0
    grep -v '^#' "$WORK/cone" >"$wgd/info/sparse-checkout"
    echo "cone:     $(grep '^# recursive:' "$WORK/cone" | sed 's/^# recursive: //')"
    echo "files-of: $(grep '^# files-of:' "$WORK/cone" | sed 's/^# files-of: //')"
    if [ "$made" -eq 1 ] && ! git -C "$wt" "${GIT_QUIET_CFG[@]}" -c core.sparseCheckout=true \
        -c core.sparseCheckoutCone=true read-tree -mu HEAD >"$WORK/wt.out" 2>&1; then
      sed 's/^/  | /' "$WORK/wt.out"
      made=0
    fi
    [ -s "$WORK/cone.err" ] && sed 's/^/  | cone: /' "$WORK/cone.err"
  fi
  if [ "$made" -eq 1 ]; then
    echo "checkout: $(du -sk "$wt" 2>/dev/null | cut -f1) KiB, $(( $(date +%s) - t0 ))s"
    if ! ( cd "$wt" && bash tests/run_trust_comprehensive_harness.sh --list push ) >"$WORK/manifest" 2>"$WORK/manifest.err"; then
      echo "manifest: \`tests/run_trust_comprehensive_harness.sh --list push\` failed in the pushed tree:"
      sed 's/^/  | /' "$WORK/manifest.err" | head -5
      : >"$WORK/manifest"
    fi
  fi

  li=-1
  for lane in $SHADOW_LANES; do
    li=$((li + 1))
    live="none"
    have_live=0
    if live_get "$lane"; then live="$live_outcome/$live_rc"; have_live=1; fi
    if [ "$made" -ne 1 ]; then
      echo "SHADOW $lane tree=$sha12 live=$live shadow=- NOT-RUN (no checkout)"
      tally "$li" unknown; continue
    fi
    cmd=""
    while IFS=$'\t' read -r gid _cat _req _lg c; do
      [ "$gid" = "$lane" ] && { cmd="$c"; break; }
    done <"$WORK/manifest"
    if [ -z "$cmd" ]; then
      echo "SHADOW $lane tree=$sha12 live=$live shadow=- NOT-RUN (no \`push\` row in the pushed tree's manifest)"
      tally "$li" unknown; continue
    fi
    script=""
    set -f
    for word in $cmd; do
      case "$word" in *.py|*.sh) script="$word"; break ;; esac
    done
    set +f
    if [ -n "$script" ] && [ ! -f "$wt/$script" ]; then
      echo "SHADOW $lane tree=$sha12 live=$live shadow=- NOT-RUN ($script is absent from the pushed tree)"
      tally "$li" unknown; continue
    fi
    out="$WORK/lane.out"
    l0="$(date +%s)"
    d0u="$(date -u +%F)" d0l="$(date +%F)"
    run_lane_timed "$wt" "$cmd" "$out"
    d1u="$(date -u +%F)" d1l="$(date +%F)"
    secs=$(( $(date +%s) - l0 ))
    note=""
    [ "$have_live" -eq 1 ] && [ -n "$live_cmd" ] && [ "$live_cmd" != "$cmd" ] && note=" (the pushed tree's command differs from the live run's)"
    clock="$(date_clock_of "$lane")"
    if [ "$clock" = utc ]; then ds="$d0u $d1u"; dlive="$LIVE_UTC"; else ds="$d0l $d1l"; dlive="$LIVE_LOCAL"; fi
    if [ "$lane_timed_out" -eq 1 ]; then
      N_TIMEOUT=$((N_TIMEOUT + 1))
      shadow="timeout/$lane_rc"
      sclass="timeout"
    else
      shadow="$lane_rc"
      sclass="$(class_of "$lane_rc" "$out")"
      [ "$sclass" = skipped ] && shadow="SKIPPED/$lane_rc"
    fi
    if [ "$sclass" = timeout ]; then
      # A lane cut off by the budget reached no verdict: counting it as a
      # DIFFER would put a false difference into the evidence this collects.
      verdict="NOT-RUN"; note="$note (timed out after ${LANE_TIMEOUT}s)"
      tally "$li" unknown
    elif [ "$have_live" -eq 1 ] && straddled "$clock" $ds; then
      # The calendar moved between the live run and this one: this lane's two
      # verdicts are about different days, not only different trees.
      verdict="NOT-RUN"; note="$note (dates straddled: live $clock ${dlive}, shadow ${ds% *}..${ds#* })"
      tally "$li" unknown
    else
      tally "$li" "$sclass"
      if [ "$have_live" -ne 1 ]; then
        verdict="NO-LIVE"
      elif [ "$sclass" = "$(live_class)" ]; then
        verdict="AGREE"
      else
        verdict="DIFFER"; N_TREEDIFFER=$((N_TREEDIFFER + 1))
      fi
      # With more than one pushed tree a tree's own line is diagnosis, not a
      # verdict about the push: the SHADOW-PUSH line below is.
      if [ "$MULTI" -eq 1 ]; then
        case "$verdict" in AGREE|DIFFER) verdict="TREE-$verdict" ;; esac
      fi
    fi
    echo "SHADOW $lane tree=$sha12 live=$live shadow=$shadow $verdict ${secs}s$note"
    case "$verdict" in *DIFFER) tail -n 15 "$out" | sed 's/^/  | /' ;; esac
    [ "$sclass" = timeout ] && tail -n 15 "$out" | sed 's/^/  | /'
  done
  [ -e "$wt" ] && drop_worktree "$wt"
done <<< "$TREES"

# ---- the push-level verdict, per lane --------------------------------------
# The worst class over the pushed trees (red > skipped > green) against the
# live run's one verdict for the push; see PUSH LEVEL in the header.
if [ -n "$TREES" ]; then
  echo
  li=-1
  for lane in $SHADOW_LANES; do
    li=$((li + 1))
    live="none" have_live=0
    if live_get "$lane"; then live="$live_outcome/$live_rc"; have_live=1; fi
    judged=$(( ${P_RED[li]} + ${P_SKIP[li]} + ${P_GREEN[li]} ))
    why=""
    if [ "${P_RED[li]}" -gt 0 ]; then worst=red
    elif [ "${P_UNK[li]}" -gt 0 ] || [ "$N_SKIPTREES" -gt 0 ]; then
      worst="-"
      [ "${P_UNK[li]}" -gt 0 ] && why=" (${P_UNK[li]} tree(s) reached no verdict)"
      [ "$N_SKIPTREES" -gt 0 ] && why="$why ($N_SKIPTREES tree(s) over the cap of $MAX_TREES were not judged)"
    elif [ "${P_SKIP[li]}" -gt 0 ]; then worst=skipped
    else worst=green
    fi
    if [ "$have_live" -ne 1 ]; then
      verdict="NO-LIVE"; N_NOLIVE=$((N_NOLIVE + 1))
    elif [ "$worst" = "-" ]; then
      verdict="NOT-RUN"; N_NOTRUN=$((N_NOTRUN + 1))
    elif [ "$worst" = "$(live_class)" ]; then
      verdict="AGREE"; N_AGREE=$((N_AGREE + 1))
    else
      verdict="DIFFER"; N_DIFFER=$((N_DIFFER + 1))
    fi
    echo "SHADOW-PUSH $lane live=$live shadow=$worst trees=$judged/$((N_TREES + N_SKIPTREES)) $verdict$why"
  done
fi

# ---- retention ------------------------------------------------------------
# Newest KEEP_LOGS logs stay; this run's log is the newest.
ls -1t "$SHADOW_ROOT"/*.log 2>/dev/null | tail -n +$((KEEP_LOGS + 1)) | while read -r old; do
  [ "$old" = "$LOG" ] && continue
  rm -f "$old"
  rm -rf "${old:?}.in"
done

echo
summary
exit 0
