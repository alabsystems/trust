#!/bin/sh
# THE BUILD-TREE MUTUAL EXCLUSION LOCK — one exclusive resource, both sides check.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
#
# WHY THIS EXISTS
# ---------------
# `build/` is a single exclusive resource that every lane shares, and until this
# script it had no lock. Measured cost in ONE session, 2026-08-20:
#
#   * a sweep died at 4m27s when a build started under it;
#   * another lost `stage1/bin/rustc` 37 seconds in (x.py deletes it at start);
#   * a third was voided by its own binary-invariance gate after a mid-run rebuild;
#   * a fourth was misdiagnosed as contaminated when it was actually fine.
#
# THE ASYMMETRY THAT CAUSED ALL FOUR. Every lane was told to check for a running
# BUILD before building. Nobody checked for a running MEASUREMENT before building.
# A wait is not a lock: a predicate stops you starting on top of somebody else and
# does nothing to stop somebody else starting on top of you. So the contract here
# is mutual — the same lock is taken by the sweep (`scripts/run_measurement_sweep.sh`)
# AND by the build (`x.py`), and either kind excludes the other.
#
# A PUSH IS A BUILD. `scripts/hooks/pre-push` runs `x.py check --stage 1`, which
# compiles into the same tree. It is covered because the lock lives in `x.py`, not
# in the hook, so there is no second place to remember.
#
# WHY `mkdir`, AND WHY NOT THE ALTERNATIVES
# -----------------------------------------
#   flock(1)   DOES NOT EXIST ON macOS. Verified 2026-08-20 on this machine:
#              no /usr/bin/flock, no /usr/local/bin/flock, `command -v flock`
#              finds nothing. Any design that reaches for it is dead on arrival.
#   shlock(1)  exists (/usr/bin/shlock) and is PID-aware, but it stores a bare pid
#              and nothing else — no purpose, no start time, no kind. Honest
#              diagnostics are requirement 3, so a bare pid is not enough.
#   lockf(1)   exists but wraps a COMMAND. It cannot express "hold this across a
#              37-minute python sweep whose exit code I still need", and it leaves
#              nothing readable behind for a second lane to inspect.
#   test-then-create
#              `[ -d "$D" ] || mkdir "$D"` is the race this file exists to avoid.
#              Two acquirers both see "absent" and both proceed. Never do this.
#
#   mkdir(2) is atomic on POSIX and its failure is observable: exactly one of N
#   concurrent `mkdir "$LOCKDIR"` calls returns 0 and the rest return EEXIST. That
#   single syscall IS the claim. Proven here by test T5, 400 contended acquisitions.
#
# STALENESS IS ALSO RACE-FREE. A crashed holder must not lock the tree forever, so
# a lock whose pid is gone is reclaimable — but two lanes can decide "stale" at the
# same instant, and if reclaiming were `rm -rf` + `mkdir` they would BOTH win. The
# reclaim is therefore a rename to a unique name (`mv LOCKDIR LOCKDIR.stale.<nonce>`,
# target guaranteed not to exist), which is rename(2): exactly one mv finds the
# source and the losers get ENOENT and go round the loop again.
#
# PID REUSE. A recorded pid alone is not identity — the OS recycles pids and a
# recycled one would read as "holder still alive" forever. The lock records the
# holder's process START TIME as well and requires BOTH to match. See T7.
#
# USAGE
#   trust_build_lock.sh acquire --kind build|measurement --purpose TEXT \
#                               [--pid N] [--wait SECONDS] [--break --reason TEXT]
#        -> prints the TOKEN on stdout; 0 acquired, 3 refused, 2 usage.
#           All diagnostics go to stderr so the token can be captured cleanly.
#   trust_build_lock.sh release TOKEN     -> 0 released/not-ours-so-nothing-done,
#                                            4 held by somebody else (untouched)
#   trust_build_lock.sh status            -> 0 free, 3 held (prints the holder)
#   trust_build_lock.sh break --reason TEXT
#        -> the loud human override. Prints a banner naming who is being displaced
#           and appends to .trust-build-lock.breaks. A reason is MANDATORY.
#   trust_build_lock.sh --selftest        -> see scripts/tests/trust_build_lock_test.sh
#
# ENVIRONMENT
#   TRUST_REPO              repo root (default: this script's parent)
#   TRUST_BUILD_LOCK_TOKEN  set by an acquirer and inherited by its children, so a
#                           nested x.py does not deadlock against its own parent.
#                           This is NOT an override: it names a lock already held.
#   TRUST_BUILD_LOCK_WAIT   seconds to block before refusing (default 0 = refuse now)
#   TRUST_BUILD_LOCK_BREAK  the reason text for a non-interactive break. Empty or
#                           unset means no break. There is deliberately no `=1`
#                           form and no config-file route: an override that can be
#                           set without typing a sentence is an override that gets
#                           set once and left on.
#
# THE HOLDER PID MUST OUTLIVE THE CRITICAL SECTION, AND THE DEFAULT USED NOT TO.
# ------------------------------------------------------------------------------
# `--pid` names the process whose liveness IS the lock's validity: when it dies the
# lock is stale and the next acquirer reclaims it automatically. The default was
# `$$` — this script's own pid — and this script exits the instant it prints the
# token. Measured 2026-08-29 in a scratch root, acquiring exactly the way
# `call_summary_census.sh` did before it was given `--pid $$`:
#
#     token recorded, holder pid 46945, `ps -p 46945` -> DEAD one instant later
#     a second acquirer with stderr suppressed: token issued, no wait, no message
#
# So the lock was BORN STALE and self-released, while `status` still printed HELD.
# That is the worst failure a guard can have: it reads as protection. It cost a
# measurement on 2026-08-29 (`E0463: can't find crate for 'core'` after a build
# took the tree out from under it) and it was the SECOND lock defect that day.
#
# The 2026-08-29 fix for the first one was applied at the CALL SITE (census gained
# `--pid $$`), which leaves every future caller one forgotten flag away from the
# same silent hole. The durable fix is here:
#
#   * the default holder is the lock script's PARENT — the process that invoked
#     acquire and normally spans the batch. Measured on this host, `$PPID` through
#     `TOK=$(bash lock.sh acquire ...)` resolves to the CALLER shell, not to a
#     transient command-substitution subshell, under both sh and bash;
#   * an unusable `$PPID` (absent, 0, 1, or already dead) REFUSES with the fix
#     rather than silently falling back to `$$` — a lock that cannot name a
#     durable holder must not be issued;
#   * a holder that is already dead at acquire time refuses for the same reason;
#   * and a stale-holder TAKEOVER is now appended to `.trust-build-lock.breaks`
#     as well as printed, because every acquiring caller in this tree redirects
#     the lock's stderr, so a stderr-only notice is invisible exactly when it
#     matters. Displacing somebody leaves a record whichever route it took.
#
# THE LOCK NAMES A PARENT; THE TREE IS WRITTEN BY ITS CHILD (2026-09-01)
# ---------------------------------------------------------------------
# `x.py` acquires with `--pid os.getpid()` and then spawns
# `build/bootstrap/debug/bootstrap`. The holder and the writer are therefore
# DIFFERENT PROCESSES, related by fork, and two defects followed from treating
# them as one. Both are fixed here; both have permanent cases in
# `scripts/tests/trust_build_lock_test.sh`.
#
#   1. A CORRECTLY-LOCKED BUILD WAS REPORTED AS UNLOCKED. Diagnosed at first as
#      "the scan matches the child, whose pid is in no lock". Measured, that is
#      not the mechanism: root scoping was a plain SUBSTRING test
#      (`ps ... | grep -F "$ROOT"`), and sibling checkouts share a prefix, so
#      Path-normalized: `/workspace/trust` matched every process under `/workspace/trust-t69`.
#      The refusal named another tree's build. In that normalized `/workspace/trust`
#      with that tree's own lock FREE, 2026-09-01:
#        trust-build-lock: FREE, but something is running outside the lock:
#          a bootstrap BUILD is running outside the lock: pid 1753
#          /workspace/trust-t69/build/bootstrap/debug/bootstrap build --stage 1 library
#      Fixed in `pids_scoped_to_root` by matching at a path boundary, which is
#      what the cwd half already did. The child-vs-holder relation is real too
#      and is now handled explicitly (`unwrapped_conflict` takes the holder pid
#      and excuses its descendants) — but it was a latent hole, not this one.
#      Do not "fix" the cross-tree part by making the lock machine-wide: whether
#      separate trees should interlock at all is a design question, not an
#      inference from this bug.
#
#   2. KILLING THE HOLDER LEFT A FREE LOCK OVER A LIVE, TREE-MUTATING BUILD.
#      `kill -TERM` on `x.py` runs its handler, the handler releases, and the
#      bootstrap child survives and keeps rewriting `build/`. Reproduced
#      deliberately; the tree then read
#        trust-build-lock: FREE, but something is running outside the lock:
#          a bootstrap BUILD is running outside the lock: pid 36141
#      This is the campaign's own failure class, not untidiness: a half-rewritten
#      `stage2/bin` makes every push gate fall back to cargo and die at
#      `-Ztrust-verify` flag-parse — a toolchain that compiles and cannot verify,
#      with no signal. `release` now HANDS THE LOCK OVER to the surviving writer
#      rather than dropping it, and `acquire` adopts an unwrapped writer instead
#      of deleting the lockdir on its way out. See `adopt_lock` for why the two
#      other candidate fixes (refuse-to-release, reap-the-process-group) do not
#      work.
set -u

# --------------------------------------------------------------------------
# Locations
# --------------------------------------------------------------------------
# Resolved PHYSICALLY. `lsof` reports a process cwd as its physical path, so a
# root carrying a symlink (`/var/...` vs `/private/var/...` on macOS, or any
# clone reached through one) would silently scope every cwd check to nothing.
_self_dir=$(cd -P "$(dirname "$0")" && pwd -P)
ROOT=$(cd -P "${TRUST_REPO:-$_self_dir/..}" 2>/dev/null && pwd -P) || ROOT=${TRUST_REPO:-$_self_dir/..}

LOCKDIR="$ROOT/.trust-build-lock"
INFO="$LOCKDIR/info"
BREAKS="$ROOT/.trust-build-lock.breaks"
# The pre-lock advisory artifact. Other lanes are reading this RIGHT NOW, and
# `run_measurement_sweep.sh` still publishes it, so the lock must understand it:
# an old copy of the sweep script publishes ONLY this and never takes the lock.
LEGACY_SENTINEL="$ROOT/.trust-measurement-in-flight"

err() { printf '%s\n' "$*" >&2; }

nonce() {
  if [ -r /dev/urandom ]; then
    od -An -N8 -tx1 /dev/urandom 2>/dev/null | tr -d ' \n' && return 0
  fi
  printf '%s%s' "$$" "$(date '+%s')"
}

# --------------------------------------------------------------------------
# Process identity
#
# `ps -o lstart=` is the holder's wall-clock start time. Together with the pid it
# is a usable process identity: a pid can be recycled, but the recycled process
# starts LATER, so the pair does not collide. Both `ps` fields are best-effort —
# if `ps` cannot answer we record the empty string and skip the comparison, which
# degrades to plain pid liveness rather than to a false "stale".
# --------------------------------------------------------------------------
pid_start() {
  ps -o lstart= -p "$1" 2>/dev/null | sed 's/^ *//; s/ *$//' | tr -d '\n'
}

pid_cmd() {
  ps -o command= -p "$1" 2>/dev/null | tr -d '\n' | cut -c1-200
}

pid_elapsed() {
  ps -o etime= -p "$1" 2>/dev/null | sed 's/^ *//; s/ *$//' | tr -d '\n'
}

pid_ppid() {
  ps -o ppid= -p "$1" 2>/dev/null | tr -d ' \n'
}

pid_pgid() {
  ps -o pgid= -p "$1" 2>/dev/null | tr -d ' \n'
}

# 0 = $1 is $2, or is reachable from $2 by following ppid links upward.
#
# THE PROCESS THAT WRITES THE TREE IS NOT THE PROCESS THAT HOLDS THE LOCK, and
# no consumer of this file should have to know that. `x.py` acquires with
# `--pid os.getpid()` and then spawns `build/bootstrap/debug/bootstrap`; the
# child appears in no lock under its own pid, so a scan that asks only "is this
# pid recorded anywhere" calls a correctly-locked build unlocked. Ancestry is
# the relation that answers it, and it cannot be forged: a pid's ppid is set by
# the kernel at fork.
#
# Bounded at 64 hops. A `ps` that answers inconsistently while processes exit
# under us must not be able to spin this loop — a guard that hangs is a guard
# that gets deleted.
pid_is_descendant_of() {
  _cand=${1:-}
  _anc=${2:-}
  case "$_anc" in ''|*[!0-9]*|0|1) return 1 ;; esac
  case "$_cand" in ''|*[!0-9]*) return 1 ;; esac
  _hops=0
  while [ "$_hops" -lt 64 ]; do
    [ "$_cand" = "$_anc" ] && return 0
    _cand=$(pid_ppid "$_cand")
    # Reaching init (1), the kernel (0) or an unreadable answer ends the chain.
    # Note that a REPARENTED process gets here: once its parent is gone the
    # chain can no longer prove anything, which is exactly right for the scan
    # (an orphan is not covered by anybody's lock) and is compensated for
    # separately in `holder_writers`.
    case "$_cand" in ''|0|1|*[!0-9]*) return 1 ;; esac
    _hops=$((_hops + 1))
  done
  return 1
}

# 0 = the process named by (pid, start) is still running.
#
# `kill -0` on a live process owned by ANOTHER user fails with EPERM. That is
# reported as ALIVE on purpose: over-refusing is the safe direction for a guard
# whose failure mode is a destroyed 37-minute measurement.
pid_is_live() {
  _p=${1:-}
  _want_start=${2:-}
  case "$_p" in ''|*[!0-9]*) return 1 ;; esac
  if kill -0 "$_p" 2>/dev/null; then
    :
  else
    # EPERM (foreign owner) vs ESRCH (gone). `ps` distinguishes them.
    ps -p "$_p" >/dev/null 2>&1 || return 1
  fi
  if [ -n "$_want_start" ]; then
    _now_start=$(pid_start "$_p")
    # An empty answer means `ps` would not say; do not manufacture a verdict.
    if [ -n "$_now_start" ] && [ "$_now_start" != "$_want_start" ]; then
      return 1   # pid recycled: same number, different process
    fi
  fi
  return 0
}

# --------------------------------------------------------------------------
# Reading the holder
#
# There is one narrow window in which the lockdir exists and `info` does not: the
# winner has returned from mkdir(2) and has not yet completed the rename(2) that
# puts `info` in place. It is a single syscall wide because the info file is
# written to a temp path BEFORE the claim and only moved afterwards. A reader that
# lands in it retries briefly rather than declaring the lock malformed.
# --------------------------------------------------------------------------
read_info() {
  _tries=0
  while [ "$_tries" -lt 30 ]; do
    [ -f "$INFO" ] && { cat "$INFO" 2>/dev/null; return 0; }
    [ -d "$LOCKDIR" ] || return 1        # released while we looked
    _tries=$((_tries + 1))
    sleep 0.1
  done
  return 1
}

info_field() {
  printf '%s\n' "$1" | sed -n "s/^$2=//p" | head -1
}

# Render a holder for a human. This is requirement 3 — a refusal that does not say
# WHO, SINCE WHEN and FOR WHAT is a refusal people learn to override reflexively.
describe_holder() {
  _info=$1
  _k=$(info_field "$_info" kind)
  _p=$(info_field "$_info" pid)
  _s=$(info_field "$_info" started)
  _u=$(info_field "$_info" purpose)
  _c=$(info_field "$_info" cmd)
  _n=$(info_field "$_info" contract)
  _e=$(pid_elapsed "$_p")
  _live=dead
  pid_is_live "$_p" "$(info_field "$_info" pstart)" && _live=alive
  err "    holder      ${_k:-?}  pid ${_p:-?}  ($_live)"
  err "    since       ${_s:-?}${_e:+   (running $_e)}"
  err "    purpose     ${_u:-unspecified}"
  [ -n "$_c" ] && err "    command     $_c"
  [ -n "$_n" ] && err "    contract    $_n"
}

# --------------------------------------------------------------------------
# Reclaim — rename to a unique name, then delete.
#
# `mv "$LOCKDIR" "$dest"` with a dest that provably does not exist is rename(2),
# so exactly one of N simultaneous reclaimers succeeds. It is NOT `rm -rf` + retry:
# that would let two lanes both conclude "stale" and both go on to claim.
# --------------------------------------------------------------------------
reclaim() {
  _dest="$ROOT/.trust-build-lock.stale.$$.$(nonce)"
  mv "$LOCKDIR" "$_dest" 2>/dev/null || return 1
  rm -rf "$_dest" 2>/dev/null
  return 0
}

# --------------------------------------------------------------------------
# Unwrapped conflicts — the belt-and-braces half.
#
# The lock only binds processes that take it. A raw `build/bootstrap/debug/bootstrap`
# or a hand-run `trust_ir_producer_scorecard.py` takes nothing, so after winning the
# claim we look for those directly. We already hold the lock at that point, so this
# scan cannot race another lock user; it only sees the ones that never played.
#
# TWO READINESS PATTERNS USED HERE WERE PREVIOUSLY WRITTEN WRONG, and each silently
# reported "clear" against a live process. Both root causes are recorded because the
# corrected forms look arbitrary without them:
#
#  (1) `pgrep -f "bootstrap (build|check)"`  matched NOTHING during a live build.
#      The alternation is NOT the problem — measured 2026-08-20, macOS pgrep(1)
#      compiles an EXTENDED regex and `pgrep -f 'bootstrap (25|check)'` matches a
#      process whose args are `bootstrap 25`. The defect is the ADJACENCY the
#      pattern assumes. `x.py --stage 1 build` is ordinary usage — x.py's own
#      preflight says so in a comment — and bootstrap.py builds its child argv as
#      `[bootstrap_binary] + sys.argv[1:]`, so the command line is
#      `build/bootstrap/debug/bootstrap --stage 1 build` and the words `bootstrap`
#      and `build` are NEVER adjacent. The pattern is a coin flip on argument order.
#      Correct form: `pgrep -x bootstrap`, which matches the executable NAME and
#      assumes nothing about arguments at all.
#
#  (2) `pgrep -f "python.*trust_ir_producer_scorecard"` matched NOTHING during a
#      live sweep at 400/2000. macOS CommandLineTools python3 is a symlink into a
#      framework and execs as
#        /Library/Developer/CommandLineTools/Library/Frameworks/Python3.framework/
#        Versions/3.9/Resources/Python.app/Contents/MacOS/Python <script>
#      — capital `P`. The lowercase string `python` never appears in the resolved
#      command line (`Python3.framework` and `Python.app` are both capitalised) and
#      `pgrep -f` is case-sensitive, so `python.*` cannot match. Verified by
#      `ps -eo args` on a live process, 2026-08-20.
#      Correct form: `pgrep -f 'trust_ir_producer_scorecar[d]\.py'` — it keys on the
#      lowercase SCRIPT name instead of the interpreter, and the `[d]` character
#      class makes it self-match-safe: the poller's own command line contains the
#      literal text `[d]`, which the regex (which requires the single char `d`
#      there) does not match.
#
# SCOPED TO THIS ROOT. There can be several trust clones on one machine, and a
# guard that fires for somebody else's build is a guard everyone learns to break.
# A pid counts only if its command line names $ROOT or its cwd is inside it.
#
# AND "NAMES $ROOT" MEANS AT A PATH BOUNDARY, NOT ANYWHERE IN THE STRING. This
# was `grep -F "$ROOT"`, a plain substring test, and sibling checkouts on this
# machine share a prefix (paths normalized): `/workspace/trust` is a substring of
# `/workspace/trust-t69`, `/workspace/trust-corpora`, `/workspace/
# trust-land`. Measured in `/workspace/trust` on 2026-09-01, with that tree's
# own lock FREE and a legitimate, correctly-locked stage-1 build running in
# `/workspace/trust-t69`:
#
#     trust-build-lock: FREE, but something is running outside the lock:
#       a bootstrap BUILD is running outside the lock: pid 1753
#       /workspace/trust-t69/build/bootstrap/debug/bootstrap build --stage 1 library
#
# `1753`'s cwd was `/workspace/trust-t69` and its ppid was 98180 — that tree's
# recorded lock holder. Nothing about it belonged to this root. The lock itself
# was never confused (LOCKDIR is per-tree); only this scan leaked, and a scan
# that refuses builds over another tree's work is worse than no scan, because
# the refusal is indistinguishable from a real one and teaches people to break.
#
# The cwd half below was already boundary-correct (`path == root ||
# index(path, root "/") == 1`); this makes the command-line half match it.
# --------------------------------------------------------------------------
pids_scoped_to_root() {
  _cands=$1
  [ -n "$_cands" ] || return 0
  _by_cmd=$(ps -o pid=,command= -p $(printf '%s' "$_cands" | tr '\n' ' ') 2>/dev/null \
            | awk -v root="$ROOT" '
                {
                  pid = $1
                  cmd = $0
                  sub(/^[ \t]*[0-9]+[ \t]+/, "", cmd)
                  n = length(root)
                  s = cmd
                  # Every occurrence of $ROOT is examined, not just the first:
                  # the root can appear in argv[0] AND in a later `--sysroot`.
                  # It counts only when the next character ends the path
                  # component — "/" (something inside the root), end of string,
                  # or a space (the root named as a bare argument).
                  while ((i = index(s, root)) > 0) {
                    nxt = substr(s, i + n, 1)
                    if (nxt == "" || nxt == "/" || nxt == " ") { print pid; break }
                    s = substr(s, i + 1)
                  }
                }')
  _by_cwd=''
  if command -v lsof >/dev/null 2>&1; then
    _csv=$(printf '%s' "$_cands" | tr '\n' ',' | sed 's/,$//')
    _by_cwd=$(lsof -a -d cwd -p "$_csv" -Fpn 2>/dev/null \
              | awk -v root="$ROOT" '
                  /^p/ { pid = substr($0, 2) }
                  /^n/ { path = substr($0, 2)
                         if (path == root || index(path, root "/") == 1) print pid }')
  else
    # No way to read cwd. Over-refuse rather than under-refuse.
    _by_cwd=$_cands
  fi
  printf '%s\n%s\n' "$_by_cmd" "$_by_cwd" | grep -E '^[0-9]+$' | sort -un
}

# EVERY tree-mutating process in $ROOT, whatever its relation to the lock. One
# row per process, three TAB-separated fields:
#
#     <pid> \t <kind> \t <human sentence>
#
# The machine-readable prefix is not decoration. Two callers need the pid and
# not just the sentence: `release` has to ask whether its OWN writer outlived
# it, and `acquire` has to be able to name a writer in the lock it leaves
# behind. A `-` in the pid column marks a row that must never be adopted.
scan_writers() {
  # A build in flight — the process that deletes stage1/bin/rustc.
  _boot=$(pgrep -x bootstrap 2>/dev/null | grep -v "^$$\$")
  for _p in $(pids_scoped_to_root "$_boot"); do
    printf '%s\tbuild\ta bootstrap BUILD is running outside the lock: pid %s  %s\n' \
      "$_p" "$_p" "$(pid_cmd "$_p")"
  done

  # A measurement in flight, run directly instead of through run_measurement_sweep.sh.
  _sc=$(pgrep -f 'trust_ir_producer_scorecar[d]\.py' 2>/dev/null | grep -v "^$$\$")
  for _p in $(pids_scoped_to_root "$_sc"); do
    printf '%s\tmeasurement\ta producer SCORECARD sweep is running outside the lock: pid %s  %s\n' \
      "$_p" "$_p" "$(pid_cmd "$_p")"
  done
}

# The rows from scan_writers that NOBODY'S LOCK COVERS. This is the belt-and-
# braces question, and its answer is a refusal, so it must be exact in both
# directions.
#
# $2 is the pid the lock names, or empty. A writer is COVERED when that holder
# is alive and the writer descends from it — see `pid_is_descendant_of`: the
# process rewriting the tree is the holder's CHILD, never the holder itself, so
# a scan that asks "does this pid appear in a lock" answers no about a perfectly
# locked build.
#
# THE HOLDER MUST BE ALIVE FOR THE EXCUSE TO APPLY, and that asymmetry is the
# whole safety argument. A dead holder protects nothing; its surviving children
# are precisely the orphans this scan exists to find, and excusing them by
# ancestry would convert a fail-closed check into a fail-open one — strictly
# worse than the false alarm it replaced. Ancestry is also the only relation
# used: process-GROUP membership would excuse an unrelated peer that merely
# shares a group with the holder (everything a non-interactive shell script
# starts shares one), which is the same fail-open direction.
unwrapped_conflict() {
  _kind=$1
  _holder=${2:-}
  if [ -n "$_holder" ] && ! pid_is_live "$_holder" ""; then
    _holder=''   # a dead holder excuses nothing
  fi

  scan_writers | while read -r _wp _wk _wt; do
    case "$_wp" in
      ''|*[!0-9]*) printf '%s\t%s\t%s\n' "$_wp" "$_wk" "$_wt"; continue ;;
    esac
    if [ -n "$_holder" ] && pid_is_descendant_of "$_wp" "$_holder"; then
      err "  note: pid $_wp descends from the lock holder (pid $_holder) — it IS the"
      err "        work the lock is protecting, so it is not a conflict."
      continue
    fi
    printf '%s\t%s\t%s\n' "$_wp" "$_wk" "$_wt"
  done

  # The pre-lock advisory sentinel, published by a copy of run_measurement_sweep.sh
  # that predates this lock. A LIVE one is a real conflict. A dead one is reported
  # and stepped over — it is another lane's artifact and `run_measurement_sweep.sh
  # --force` is its documented deleter, so this script does not delete it.
  #
  # Its pid column is `-`: the sentinel records a bare pid with no start time, so
  # it cannot be told apart from a RECYCLED pid, and adopting one would wedge the
  # tree until an unrelated process happened to exit.
  if [ -e "$LEGACY_SENTINEL" ]; then
    _lp=$(sed -n 's/^pid=//p' "$LEGACY_SENTINEL" 2>/dev/null | head -1)
    if pid_is_live "$_lp" ""; then
      printf -- '-\tmeasurement\ta legacy measurement sentinel is LIVE: %s pid %s\n' \
        "$LEGACY_SENTINEL" "$_lp"
    else
      err "  note: a stale $LEGACY_SENTINEL (pid ${_lp:-?}, gone) is present and ignored;"
      err "        scripts/run_measurement_sweep.sh --force removes it."
    fi
  fi
  : "$_kind"
}

# The exact inverse: the rows that DO belong to the holder named by $1 (whose
# process group at acquire time was $2). `release` asks this, and its answer
# decides whether the critical section is really over.
#
# The second arm exists because a child can be REPARENTED between the holder's
# death and this scan, which erases the ppid evidence. The process group is what
# survives that, and it is safe to use HERE — where the failure direction is
# reversed. Including a process that is not really ours means the lock stays
# HELD one build too long; missing one means the tree is left unlocked with a
# writer in it. The arm is still restricted to a reparented process (ppid 1) so
# an unrelated peer sharing the group is not swept in.
holder_writers() {
  _h=${1:-}
  _hg=${2:-}
  [ -n "$_h" ] || return 0
  scan_writers | while read -r _wp _wk _wt; do
    case "$_wp" in ''|*[!0-9]*) continue ;; esac
    if pid_is_descendant_of "$_wp" "$_h"; then
      printf '%s\t%s\t%s\n' "$_wp" "$_wk" "$_wt"
      continue
    fi
    if [ -n "$_hg" ] && [ "$(pid_ppid "$_wp")" = "1" ] && [ "$(pid_pgid "$_wp")" = "$_hg" ]; then
      printf '%s\t%s\t%s\n' "$_wp" "$_wk" "$_wt"
    fi
  done
}

# First adoptable row of a scan_writers-shaped list, or nothing.
first_adoptable() {
  printf '%s\n' "$1" | awk -F'\t' '$1 ~ /^[0-9]+$/ { print; exit }'
}

# The human half of a scan_writers-shaped list.
conflict_text() {
  printf '%s\n' "$1" | cut -f3-
}

# --------------------------------------------------------------------------
# The loud override
# --------------------------------------------------------------------------
loud_break() {
  _reason=$1
  _info=${2:-}
  err ""
  err "  ####################################################################"
  err "  ##  BUILD-TREE LOCK BROKEN BY HAND                                ##"
  err "  ####################################################################"
  if [ -n "$_info" ]; then
    err "  displacing:"
    describe_holder "$_info"
  else
    err "  displacing: (no readable holder info)"
  fi
  err "  broken by : pid $$  $(id -un 2>/dev/null)@$(hostname 2>/dev/null)"
  err "  reason    : $_reason"
  err "  recorded  : $BREAKS"
  err "  ####################################################################"
  err ""
  {
    printf 'when=%s pid=%s user=%s reason=%s\n' \
      "$(date '+%Y-%m-%d %H:%M:%S')" "$$" "$(id -un 2>/dev/null)" "$_reason"
    [ -n "$_info" ] && printf '%s\n' "$_info" | sed 's/^/    displaced: /'
    printf '\n'
  } >> "$BREAKS" 2>/dev/null
}

# --------------------------------------------------------------------------
# A takeover is a DISPLACEMENT, so it leaves the same durable trace a hand break
# does. Reclaiming a dead holder is correct — a crashed lane must not wedge the
# tree forever — but until 2026-08-29 it announced itself on stderr ONLY, and
# every acquiring caller in this tree redirects the lock's stderr (the census
# with `2>/dev/null`, x.py through a pipe). So the one event that says "the lock
# you thought you held is gone" was invisible precisely where it mattered, and a
# self-releasing lock looked identical to a lock nobody ever took.
#
# `.trust-build-lock.breaks` survives the redirect and is the file a post-mortem
# already reads. `reason=STALE-TAKEOVER` distinguishes it from a hand break: this
# one is legitimate, it just must not be silent.
# --------------------------------------------------------------------------
loud_takeover() {
  _why=$1
  _info=${2:-}
  err "  ------------------------------------------------------------------"
  err "  STALE-HOLDER TAKEOVER — $_why"
  err "  (this is the event scripts/tests/trust_build_lock_test.sh T2 pins)"
  if [ -n "$_info" ]; then
    describe_holder "$_info"
  else
    err "    holder      (no readable info: malformed, or killed inside the"
    err "                 one-syscall publish window)"
  fi
  err "    taken by    pid $$  ($(id -un 2>/dev/null))"
  err "    recorded    $BREAKS"
  err "  If that lane is in fact still running, it is now UNPROTECTED: stop this"
  err "  one, and give the survivor a --pid that outlives it."
  err "  ------------------------------------------------------------------"
  {
    printf 'when=%s pid=%s user=%s reason=STALE-TAKEOVER (%s)\n' \
      "$(date '+%Y-%m-%d %H:%M:%S')" "$$" "$(id -un 2>/dev/null)" "$_why"
    if [ -n "$_info" ]; then
      printf '%s\n' "$_info" | sed 's/^/    displaced: /'
    else
      printf '    displaced: (no readable holder info)\n'
    fi
    printf '\n'
  } >> "$BREAKS" 2>/dev/null
}

# --------------------------------------------------------------------------
# ADOPTION — re-point the lock at a process that is writing the tree and never
# took it.
#
# THE STATE THIS EXISTS TO MAKE UNREACHABLE is "the lock is free and something
# is rewriting `build/` anyway". Two routes produced it, and both are routine:
#
#   * `x.py` is signalled. Its SIGTERM handler runs `release`, the lock goes
#     away with the parent, and `build/bootstrap/debug/bootstrap` — which is a
#     CHILD, not the holder — survives and keeps rewriting the tree. Reproduced
#     deliberately with `kill -TERM`; the tree then reported
#         trust-build-lock: FREE, but something is running outside the lock
#     which is an accurate description of a state no lock should permit.
#   * `x.py` is hard-killed. Nothing runs, so the lockdir survives naming a dead
#     holder — fail-closed so far — until the NEXT acquirer reclaims it as
#     stale, finds the orphan, refuses, and (before this) DELETED the lockdir on
#     the way out. A reader turned a safe state into the unsafe one.
#
# WHY THIS AND NOT THE OTHER TWO CANDIDATES.
#   * "Refuse to release while a writer lives" does nothing: the lock would name
#     a dead holder, and the very next acquirer reclaims it as stale. The record
#     has to name something ALIVE or the reclaim rule erases it.
#   * "Reap the holder's process group on release" only narrows the window — a
#     hard-killed holder runs no cleanup at all, which is the case that matters —
#     and it makes a guard into a killer of other lanes' work.
#
# WHY IT IS SAFE. Adoption never makes the lock weaker: it is taken ONLY on a
# path that was already going to refuse, and it changes the outcome from
# "refused, tree unlocked" to "refused, tree locked and the holder named". The
# adopted holder never receives the token, so nothing can release on its behalf —
# it never agreed to hold anything. The lock clears the moment that process
# exits, by the ordinary stale-reclaim rule, so it cannot wedge the tree; and
# `break --reason` remains for a writer that never exits.
#
# WHAT IT BUYS THE CALLER. The refusal used to end with "That process never took
# the lock, so it cannot be waited on safely." After adoption it can:
# TRUST_BUILD_LOCK_WAIT blocks on a real recorded holder like any other.
#
# REQUIRES $LOCKDIR to already be ours.
adopt_lock() {
  _apid=$1
  _akind=$2
  _awhy=$3
  _atmp=$(mktemp "$ROOT/.trust-build-lock.tmp.XXXXXX" 2>/dev/null) || return 1
  {
    printf 'token=%s\n' "$(nonce)"
    printf 'kind=%s\n' "$_akind"
    printf 'pid=%s\n' "$_apid"
    printf 'pstart=%s\n' "$(pid_start "$_apid")"
    printf 'pgid=%s\n' "$(pid_pgid "$_apid")"
    printf 'started=%s\n' "$(date '+%Y-%m-%d %H:%M:%S')"
    printf 'purpose=%s\n' "ADOPTED (this process never took the lock): $_awhy"
    printf 'cmd=%s\n' "$(pid_cmd "$_apid")"
    printf 'host=%s\n' "$(hostname 2>/dev/null)"
    printf 'adopted=%s\n' "$_awhy"
    printf 'contract=%s\n' "an unwrapped writer is rewriting this tree; wait for it or break the lock"
  } > "$_atmp"
  mv "$_atmp" "$INFO" 2>/dev/null || { rm -f "$_atmp"; return 1; }
  return 0
}

# A handover is a DISPLACEMENT of the lock's meaning, so it leaves the same
# durable trace a break and a stale takeover do — and for the same measured
# reason: every acquiring caller in this tree redirects this script's stderr
# (x.py's `release` sends both streams to DEVNULL), so a stderr-only notice is
# invisible in exactly the runs where it matters.
loud_handover() {
  _old=$1
  _new=$2
  _what=$3
  err "  ------------------------------------------------------------------"
  err "  ORPHAN HANDOVER — the holder is finishing but its WRITER is not."
  err "    departing   holder pid $_old"
  err "    surviving   $_what"
  err "  The lock is NOT being released. It now names the surviving process, so"
  err "  the tree stays protected and the next lane can WAIT on it instead of"
  err "  finding a free lock over a live build. It clears when that pid exits."
  err "    recorded    $BREAKS"
  err "  ------------------------------------------------------------------"
  {
    printf 'when=%s pid=%s user=%s reason=ORPHAN-HANDOVER (holder %s exited, writer %s survives)\n' \
      "$(date '+%Y-%m-%d %H:%M:%S')" "$$" "$(id -un 2>/dev/null)" "$_old" "$_new"
    printf '    surviving: %s\n' "$_what"
    printf '\n'
  } >> "$BREAKS" 2>/dev/null
}

# --------------------------------------------------------------------------
# acquire
# --------------------------------------------------------------------------
cmd_acquire() {
  # HOLD_PID is deliberately left EMPTY here, not defaulted to `$$`. See the
  # "THE HOLDER PID MUST OUTLIVE THE CRITICAL SECTION" note in the header: `$$` is
  # this script, which exits milliseconds later, so that default minted a lock that
  # was stale from birth. It is resolved and validated below, after re-entrancy.
  KIND=''; PURPOSE='unspecified'; HOLD_PID=''; WAIT=${TRUST_BUILD_LOCK_WAIT:-0}
  BREAK_REASON=${TRUST_BUILD_LOCK_BREAK:-}
  CONTRACT='the build tree is exclusive: do not run x.py or a sweep against it'
  while [ $# -gt 0 ]; do
    case "$1" in
      --kind)    KIND=${2:?--kind needs a value}; shift 2 ;;
      --purpose) PURPOSE=${2:?--purpose needs a value}; shift 2 ;;
      --pid)     HOLD_PID=${2:?--pid needs a value}; shift 2 ;;
      --wait)    WAIT=${2:?--wait needs a value}; shift 2 ;;
      --contract) CONTRACT=${2:?--contract needs a value}; shift 2 ;;
      --break)   shift ;;
      --reason)  BREAK_REASON=${2:?--reason needs a value}; shift 2 ;;
      *) err "acquire: unknown argument '$1'"; return 2 ;;
    esac
  done
  case "$KIND" in
    build|measurement) ;;
    *) err "acquire: --kind must be build or measurement (got '${KIND}')"; return 2 ;;
  esac
  case "$WAIT" in ''|*[!0-9]*) err "acquire: --wait must be a whole number of seconds"; return 2 ;; esac

  # Re-entrancy. A nested x.py (bootstrap's own test suite shells out to one)
  # inherits TRUST_BUILD_LOCK_TOKEN and must NOT block on its own parent. This is
  # not an override — it names a lock that is genuinely held, and it is verified
  # against the lock on disk rather than believed.
  if [ -n "${TRUST_BUILD_LOCK_TOKEN:-}" ] && [ -f "$INFO" ]; then
    _held=$(sed -n 's/^token=//p' "$INFO" 2>/dev/null | head -1)
    if [ "$_held" = "$TRUST_BUILD_LOCK_TOKEN" ]; then
      printf '%s\n' "$TRUST_BUILD_LOCK_TOKEN"
      err "trust-build-lock: already held by this process tree (nested; not re-acquired)"
      return 0
    fi
  fi

  # ---- Resolve and VALIDATE the holder. A lock is only as good as this pid. ----
  #
  # Placed after the re-entrancy check on purpose: a nested acquire that is merely
  # naming a lock its parent already holds must not be refused over a pid it never
  # needed. Refusals here carry the fix and the options (design ruling v7/D3).
  if [ -z "$HOLD_PID" ]; then
    HOLD_PID=${PPID:-}
    case "$HOLD_PID" in
      ''|*[!0-9]*|0|1)
        err ""
        err "  TRUST-BUILD-LOCK: REFUSING to issue a lock with no durable holder."
        err ""
        err "    --pid was not given and this shell reports no usable parent"
        err "    (PPID='${PPID:-}'). Defaulting to this script's own pid is what"
        err "    made the lock self-release on 2026-08-29, so it is not done."
        err ""
        err "  Options:"
        err "    state it   acquire ... --pid \$\$    <- from the process that holds"
        err "               the tree for the whole batch (the sweep, x.py, the census)"
        err "    check      the caller must be a long-lived process; a pid that exits"
        err "               when acquire returns cannot protect anything"
        err ""
        return 2 ;;
    esac
    err "trust-build-lock: --pid not given; holder inferred as the caller (pid $HOLD_PID)."
    err "                  Pass --pid \$\$ explicitly from the process that spans the batch."
  fi
  if ! pid_is_live "$HOLD_PID" ""; then
    err ""
    err "  TRUST-BUILD-LOCK: REFUSING — the named holder pid $HOLD_PID is already dead."
    err ""
    err "    A lock whose holder is gone is reclaimed automatically by the next"
    err "    acquirer, so issuing this one would protect nothing while reading as"
    err "    protection. Refused at birth instead."
    err ""
    err "  Options:"
    err "    fix        pass --pid \$\$ from the live process that will hold the tree"
    err "    inspect    ps -p $HOLD_PID"
    err ""
    return 2
  fi

  TOKEN=$(nonce)
  HOLD_START=$(pid_start "$HOLD_PID")
  # Recorded so `release` can still recognise the holder's own writers after the
  # holder has died and they have been reparented away from it. See holder_writers.
  HOLD_PGID=$(pid_pgid "$HOLD_PID")
  _deadline=$(( $(date '+%s') + WAIT ))
  _rounds=0
  _said_waiting=0

  while :; do
    _rounds=$((_rounds + 1))
    if [ "$_rounds" -gt 10000 ]; then
      err "trust-build-lock: gave up after $_rounds acquire rounds (contended or looping)"
      return 3
    fi

    # Stage the metadata BEFORE the claim so the post-claim publish is one
    # rename(2), which is what keeps the reader window a single syscall wide.
    _tmp=$(mktemp "$ROOT/.trust-build-lock.tmp.XXXXXX" 2>/dev/null) || {
      err "trust-build-lock: cannot write to $ROOT"; return 2; }
    {
      printf 'token=%s\n' "$TOKEN"
      printf 'kind=%s\n' "$KIND"
      printf 'pid=%s\n' "$HOLD_PID"
      printf 'pstart=%s\n' "$HOLD_START"
      printf 'pgid=%s\n' "$HOLD_PGID"
      printf 'started=%s\n' "$(date '+%Y-%m-%d %H:%M:%S')"
      printf 'purpose=%s\n' "$(printf '%s' "$PURPOSE" | tr '\n' ' ')"
      printf 'cmd=%s\n' "$(pid_cmd "$HOLD_PID")"
      printf 'host=%s\n' "$(hostname 2>/dev/null)"
      printf 'contract=%s\n' "$(printf '%s' "$CONTRACT" | tr '\n' ' ')"
    } > "$_tmp"

    # ---- THE CLAIM. One atomic syscall; exactly one winner. ----
    if mkdir "$LOCKDIR" 2>/dev/null; then
      mv "$_tmp" "$INFO" 2>/dev/null || { rm -f "$_tmp"; rmdir "$LOCKDIR" 2>/dev/null; \
        err "trust-build-lock: could not publish holder info"; return 2; }

      # `$HOLD_PID` is passed so the holder's OWN build is not reported as
      # unlocked. It cannot normally have children yet at this instant, but the
      # argument is what makes the rule "a writer under the holder is covered"
      # true of every caller of this scan rather than true by accident of timing.
      _conf=$(unwrapped_conflict "$KIND" "$HOLD_PID")
      if [ -n "$_conf" ]; then
        if [ -n "$BREAK_REASON" ]; then
          err "trust-build-lock: proceeding past an unwrapped conflict because --reason was given:"
          conflict_text "$_conf" | sed 's/^/    /' >&2
          loud_break "$BREAK_REASON" ""
        else
          # DO NOT hand the tree back unlocked with a writer still in it. That
          # is the very state this file exists to prevent, and deleting the
          # lockdir here is how a reader used to create it out of a safe one.
          # See `adopt_lock`.
          _adopt=$(first_adoptable "$_conf")
          _apid=$(printf '%s' "$_adopt" | awk -F'\t' '{print $1}')
          _akind=$(printf '%s' "$_adopt" | awk -F'\t' '{print $2}')
          _adopted=0
          if [ -n "$_apid" ] && adopt_lock "$_apid" "$_akind" \
                "found rewriting $ROOT while the lock was free"; then
            _adopted=1
          else
            rm -f "$INFO"; rmdir "$LOCKDIR" 2>/dev/null
          fi
          err ""
          err "  TRUST-BUILD-LOCK: REFUSING to start a $KIND — the tree is busy."
          err ""
          conflict_text "$_conf" | sed 's/^/    /' >&2
          err ""
          if [ "$_adopted" -eq 1 ]; then
            err "  That process never took the lock. The lock now NAMES it (pid $_apid)"
            err "  so the tree is not left unprotected and it CAN be waited on; the"
            err "  lock clears by itself when that pid exits."
            err "  Options:"
            err "    wait     TRUST_BUILD_LOCK_WAIT=3600 <your command>   (blocks, then runs)"
            err "    watch    scripts/trust_build_lock.sh status"
            err "    break    scripts/trust_build_lock.sh break --reason \"...\"  (LOUD;"
            err "             logged to .trust-build-lock.breaks)"
          else
            err "  That process never took the lock, so it cannot be waited on safely."
            err "  Options:"
            err "    watch    scripts/trust_build_lock.sh status"
            err "    wait     re-run when it exits (pgrep -x bootstrap;"
            err "             pgrep -f 'trust_ir_producer_scorecar[d]\\.py')"
            err "    break    re-run with --break --reason \"...\"  (LOUD; logged to"
            err "             .trust-build-lock.breaks)"
          fi
          err ""
          return 3
        fi
      fi

      err "trust-build-lock: acquired ($KIND, pid $HOLD_PID) — $PURPOSE"
      printf '%s\n' "$TOKEN"
      return 0
    fi
    rm -f "$_tmp"

    # ---- Contended. Decide whether the holder is real. ----
    _info=$(read_info) || {
      # The lockdir exists but has no info even after retrying. Either the winner
      # died inside the one-syscall publish window, or somebody hand-made the
      # directory. Both are reclaimable; say so rather than deadlocking on it.
      if [ -d "$LOCKDIR" ]; then
        loud_takeover "the lock carries no holder info (malformed, or the winner was\
 killed inside the one-syscall publish window)" ""
        reclaim || :
      fi
      continue
    }

    _hp=$(info_field "$_info" pid)
    _hs=$(info_field "$_info" pstart)
    if ! pid_is_live "$_hp" "$_hs"; then
      loud_takeover "RECLAIMING a stale lock: holder pid $_hp is gone" "$_info"
      reclaim || err "trust-build-lock: another lane reclaimed it first; retrying"
      continue
    fi

    if [ -n "$BREAK_REASON" ]; then
      loud_break "$BREAK_REASON" "$_info"
      reclaim || :
      continue
    fi

    _now=$(date '+%s')
    if [ "$_now" -lt "$_deadline" ]; then
      if [ "$_said_waiting" -eq 0 ]; then
        _said_waiting=1
        err "trust-build-lock: held; waiting up to ${WAIT}s —"
        describe_holder "$_info"
      fi
      sleep 5
      continue
    fi

    # ---- Refuse, with the fix and the options (design ruling v7/D3). ----
    err ""
    err "  TRUST-BUILD-LOCK: REFUSING to start a $KIND — the build tree is held."
    err ""
    describe_holder "$_info"
    err ""
    err "  The build tree is one exclusive resource. Starting a $KIND now would"
    if [ "$(info_field "$_info" kind)" = measurement ]; then
      err "  delete stage1/bin/rustc under a running measurement and destroy it."
    else
      err "  race a compiler that is being rewritten underneath you."
    fi
    err ""
    err "  Options:"
    err "    wait     TRUST_BUILD_LOCK_WAIT=3600 <your command>   (blocks, then runs)"
    err "    watch    scripts/trust_build_lock.sh status"
    err "    break    scripts/trust_build_lock.sh break --reason \"...\""
    err "             (LOUD banner + a line in .trust-build-lock.breaks; use it only"
    err "              when you know the holder is wedged)"
    if [ "$KIND" = build ]; then
      err "    push     git push --no-verify   — the pre-push hook runs 'x.py check',"
      err "             which IS a build for interlock purposes."
    fi
    err ""
    return 3
  done
}

# --------------------------------------------------------------------------
# release — only the holder may release. Removing somebody else's lock is the
# same bug as not having one.
#
# AND A HOLDER MAY NOT RELEASE OUT FROM UNDER ITS OWN WRITER. `x.py` takes the
# lock, spawns `build/bootstrap/debug/bootstrap`, and releases from a SIGTERM
# handler / `atexit` / `finally` — none of which stop the child. Signalling the
# parent therefore used to free the lock while the child went on rewriting the
# tree, which is not untidiness: a half-rewritten `stage2/bin` makes every push
# gate fall back to cargo and die at `-Ztrust-verify`, i.e. a toolchain that
# compiles and cannot verify, reported as success. The release becomes a
# HANDOVER instead — see `adopt_lock` for why the two alternatives do not work.
# --------------------------------------------------------------------------
cmd_release() {
  _tok=${1:-}
  [ -n "$_tok" ] || { err "release: needs the token returned by acquire"; return 2; }
  [ -d "$LOCKDIR" ] || return 0                        # already gone; idempotent
  _info=$(read_info) || { reclaim || :; return 0; }     # malformed: clear it
  _held=$(info_field "$_info" token)
  if [ "$_held" != "$_tok" ]; then
    err "trust-build-lock: NOT releasing — the lock is held by somebody else"
    describe_holder "$_info"
    return 4
  fi

  _rhp=$(info_field "$_info" pid)
  _rhg=$(info_field "$_info" pgid)
  _surv=$(first_adoptable "$(holder_writers "$_rhp" "$_rhg")")
  if [ -n "$_surv" ]; then
    _spid=$(printf '%s' "$_surv" | awk -F'\t' '{print $1}')
    _skind=$(printf '%s' "$_surv" | awk -F'\t' '{print $2}')
    _stext=$(printf '%s' "$_surv" | cut -f3-)
    loud_handover "$_rhp" "$_spid" "$_stext" || :
    if adopt_lock "$_spid" "$_skind" \
         "orphaned by holder pid $_rhp, which released while this process was still writing"; then
      return 0
    fi
    err "trust-build-lock: could not publish the handover; keeping the lock as-is"
    return 0
  fi

  reclaim || :
  err "trust-build-lock: released ($(info_field "$_info" kind))"
  return 0
}

cmd_status() {
  if [ ! -d "$LOCKDIR" ]; then
    _conf=$(unwrapped_conflict any)
    if [ -n "$_conf" ]; then
      err "trust-build-lock: FREE, but something is running outside the lock:"
      conflict_text "$_conf" | sed 's/^/    /' >&2
      return 3
    fi
    printf 'trust-build-lock: free\n'
    return 0
  fi
  _info=$(read_info) || { err "trust-build-lock: held, holder info unreadable (reclaimable)"; return 3; }
  err "trust-build-lock: HELD"
  describe_holder "$_info"
  # A held lock does not mean everything in the tree is covered by it. The scan
  # is run here too — excusing the holder's own build, which is the normal and
  # overwhelmingly common case — so that a writer nobody's lock covers is
  # visible while the tree is held, not only once it is free.
  _conf=$(unwrapped_conflict any "$(info_field "$_info" pid)")
  if [ -n "$_conf" ]; then
    err ""
    err "  AND something ELSE is running that this lock does not cover:"
    conflict_text "$_conf" | sed 's/^/    /' >&2
  fi
  return 3
}

cmd_break() {
  _reason=''
  while [ $# -gt 0 ]; do
    case "$1" in
      --reason) _reason=${2:?--reason needs a value}; shift 2 ;;
      *) err "break: unknown argument '$1'"; return 2 ;;
    esac
  done
  [ -n "$_reason" ] || {
    err "break: --reason \"...\" is MANDATORY."
    err "       An override you can trigger without typing a sentence is an override"
    err "       that gets left on. Say what is wedged and why you are displacing it."
    return 2; }
  if [ ! -d "$LOCKDIR" ]; then
    err "trust-build-lock: nothing to break; the lock is free"
    return 0
  fi
  _info=$(read_info) || _info=''
  loud_break "$_reason" "$_info"
  reclaim || :
  return 0
}

# --------------------------------------------------------------------------
usage() {
  sed -n '/^# USAGE/,/^# ENVIRONMENT/p' "$0" | sed 's/^# \{0,1\}//' >&2
}

case "${1:-}" in
  acquire) shift; cmd_acquire "$@" ;;
  release) shift; cmd_release "$@" ;;
  status)  shift; cmd_status "$@" ;;
  break)   shift; cmd_break "$@" ;;
  --selftest)
    err "the mutation proof lives in scripts/tests/trust_build_lock_test.sh"
    err "run:  bash scripts/tests/trust_build_lock_test.sh"
    exit 2 ;;
  -h|--help|'') usage; exit 2 ;;
  *) err "unknown subcommand '${1:-}'"; usage; exit 2 ;;
esac
