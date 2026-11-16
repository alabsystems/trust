#!/bin/sh
# machine_preflight.sh — is this machine fit to build or measure on, and if not, what exactly is wrong?
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHY THIS EXISTS
# ---------------
# Native Targo build-tree ownership makes `build/` mutually exclusive between THIS repo's
# lanes. It cannot see the three things that actually stalled a session on
# 2026-09-21, because none of them is this repo's lock and two are not this repo
# at all:
#
#   * 18 ORPHANED `zsh` busy-loops (`while :; do :; done`, PPID 1, ~93% CPU
#     each, 7h old) left behind by a synthetic-load experiment whose `kill`
#     silently did nothing. All 18 cores pegged; an `x.py build` that normally
#     takes 25 min made no progress for 20.
#   * a 5-DAY-OLD runaway verification binary (`p3_loop_plus_rec`, 99.8% CPU) in
#     a scratch worktree — the leaked-non-terminating-test hazard, still burning
#     a core five days later.
#   * an ORPHANED, WEDGED `targo build` from an UNRELATED project holding
#     `~/.cargo/.package-cache`, 21 min at 0% CPU with 19 children in
#     UNINTERRUPTIBLE WAIT. Every cargo invocation on the machine — including
#     two of this repo's submodule checks and another live build — sat behind it
#     printing "Blocking waiting for file lock on package cache".
#
# Each looked like "the build is slow". None is. The signature that separates a
# wedge from slowness is cheap to read and is what this script reads.
#
# READ-ONLY by default. `--fix` touches ONLY the provably-lossless subset (see
# THE FIX SET). It never kills a process: killing someone else's build is a
# judgement call, so the kill line is PRINTED, correct and ready to paste.
#
# TWO ZSH TRAPS ARE BAKED INTO EVERY COMMAND THIS PRINTS, because both silently
# no-op'd during the incident above and a failed kill is indistinguishable from
# a successful one:
#
#   1. `ps -o comm` prints `/bin/zsh`, NOT `zsh`. An `awk '$n=="zsh"'` filter
#      matches nothing and reports a clean machine. Match `/\/zsh$/`.
#   2. `kill $list` does NOT word-split in zsh. The whole newline-joined list
#      arrives as ONE argument and kill fails — even `kill -9`. Pipe through
#      `xargs -n1 kill`, and always re-`ps` to confirm.
#
# A ZERO HERE IS A FACT ABOUT THE INSTRUMENT until it has produced a non-zero.
# `--self-test` spawns one short-lived orphan and proves each detector fires.
#
# Usage:
#   scripts/machine_preflight.sh              # report; exit 0 clean, 1 problems
#   scripts/machine_preflight.sh --fix        # + revert submodule Cargo.lock drift,
#                                             #   reclaim an over-threshold crates/
#                                             #   incremental cache
#   scripts/machine_preflight.sh --self-test  # prove the detectors can fire
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
FIX=0
SELFTEST=0
for a in "$@"; do
  case "$a" in
    --fix) FIX=1 ;;
    --self-test) SELFTEST=1 ;;
    -h|--help) sed -n '2,45p' "$0"; exit 0 ;;
    *) printf 'machine_preflight: unknown argument: %s\n' "$a" >&2; exit 2 ;;
  esac
done

PROBLEMS=0
# A lock holder idling below this is presumed healthy (a cargo parent waiting on
# its children). Above it, idle means wedged. The override exists so the
# self-tests can exercise the verdict without waiting five minutes.
WEDGE_MIN_SECS=${MACHINE_PREFLIGHT_WEDGE_MIN_SECS:-300}
case "$WEDGE_MIN_SECS" in
  ''|*[!0-9]*) printf 'machine_preflight: MACHINE_PREFLIGHT_WEDGE_MIN_SECS must be a whole number of seconds\n' >&2; exit 2 ;;
esac

# What "burning CPU" means depends on how many runnable processes share the
# cores. `ps` pcpu is the process's SHARE: on an oversubscribed machine a pure
# busy-loop cannot reach a fixed bar (measured 2026-09-24 at load 50 on 18
# cores: a spinner read 21-37%, so a fixed >40% missed it and the self-test
# reported a working detector as broken). The bar is therefore 40% of a core,
# scaled down by the fair share a runnable process can get when load exceeds
# the core count, and never below 10% so idle daemons stay out of it.
NCPU=$(getconf _NPROCESSORS_ONLN 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || true)
LOAD1=$(sysctl -n vm.loadavg 2>/dev/null | awk '{print $2}')
[ -n "$LOAD1" ] || LOAD1=$(awk '{print $1}' /proc/loadavg 2>/dev/null || true)
HOG_MIN_PCPU=$(awk -v n="${NCPU:-0}" -v l="${LOAD1:-0}" 'BEGIN {
  t = 40
  if (n + 0 > 0 && l + 0 > n + 0) t = 40 * n / l
  if (t < 10) t = 10
  printf "%.1f", t }')

# `ps` etime is [[D-]HH:]MM:SS. Convert to seconds so "old" is a number, not a
# regex over colons -- the colon-counting form cannot tell 2m from 2h.
etime_secs() {
  printf '%s' "${1:-}" | awk -F'[-:]' '
    { n = NF
      s = (n >= 1 ? $(n) : 0) + (n >= 2 ? $(n-1) * 60 : 0) \
        + (n >= 3 ? $(n-2) * 3600 : 0) + (n >= 4 ? $(n-3) * 86400 : 0)
      print int(s) }'
}

note() { printf '  %s\n' "$*"; }
bad()  { PROBLEMS=$((PROBLEMS + 1)); printf 'PROBLEM  %s\n' "$*"; }
ok()   { printf 'ok       %s\n' "$*"; }

# Orphaned (PPID 1) processes burning CPU for longer than a build should.
# ELAPSED containing two colons is >= 1 hour; that plus PPID 1 is never
# legitimate work, and is the busy-loop / runaway-binary signature.
# SYSTEM DAEMONS ARE PPID 1 BY DESIGN and some legitimately burn CPU
# (`syspolicyd`, `mds_stores`, `kernel_task`). This script printed a `kill -9`
# for `/usr/libexec/syspolicyd` on its first run; killing an OS daemon to speed
# up a build is exactly the wrong advice, and this repo already carries the
# scar of the same confusion (`/usr/libexec/trustd` is a macOS daemon, NOT the
# Trust solver daemon). Restrict to processes outside the system prefixes.
orphan_hogs() {
  ps -eo pid,ppid,pcpu,etime,comm 2>/dev/null | awk -v min="$HOG_MIN_PCPU" '
    NR > 1 && $2 == 1 && $3 > min + 0 && $4 ~ /:.*:/ \
      && $5 !~ /^\/usr\/(libexec|sbin|bin)\// \
      && $5 !~ /^\/System\// \
      && $5 !~ /^\/Library\// \
      && $5 != "kernel_task" { print $1, $3, $4, $5 }'
}

# Uninterruptible wait (state U*) is the WEDGE signature: the process is not
# slow, it is blocked in the kernel and will not make progress on its own.
wedged() {
  ps -eo pid,ppid,pcpu,etime,stat,comm 2>/dev/null | awk '
    NR > 1 && $5 ~ /^U/ { print $1, $3, $4, $6 }'
}

printf '== orphaned CPU hogs (PPID 1, >%s%% CPU, >=1h; ncpu=%s load1=%s) ==\n' \
  "$HOG_MIN_PCPU" "${NCPU:-?}" "${LOAD1:-?}"
HOGS=$(orphan_hogs || true)
if [ -n "$HOGS" ]; then
  printf '%s\n' "$HOGS" | sed 's/^/  /'
  bad "$(printf '%s\n' "$HOGS" | wc -l | tr -d ' ') orphaned hog(s) are stealing the machine."
  note 'Kill them (xargs forces the word-split zsh will not do):'
  note "  ps -eo pid,ppid,pcpu,etime,comm | awk 'NR>1 && \$2==1 && \$3>$HOG_MIN_PCPU && \$4~/:.*:/ {print \$1}' | xargs -n1 kill -9"
  note 'Then RE-RUN this script: a kill that silently failed looks exactly like one that worked.'
else
  ok 'none'
fi

printf '== wedged processes (uninterruptible wait) ==\n'
WEDGED=$(wedged || true)
if [ -n "$WEDGED" ]; then
  printf '%s\n' "$WEDGED" | sed 's/^/  /'
  bad "$(printf '%s\n' "$WEDGED" | wc -l | tr -d ' ') process(es) in uninterruptible wait — blocked, not slow."
  note 'If one holds a shared lock (see below), everything else queues behind it forever.'
else
  ok 'none'
fi

printf '== cargo package-cache lock ==\n'
# Cargo's cache has TWO lock files, and having one OPEN is not holding it:
#   .package-cache         EXCLUSIVE while a build resolves/downloads; while it
#                          is held every other cargo/targo prints "Blocking
#                          waiting for file lock on package cache".
#   .package-cache-mutate  held SHARED by every running build for its whole
#                          life (it fences out cache mutation only), EXCLUSIVE
#                          only while the cache itself is being mutated.
# A process WAITING for a lock has the file open exactly like the holder, and a
# SHARED holder blocks no build. This section used to flag every process with
# either file open and idle past WEDGE_MIN_SECS as a wedged holder "blocking
# every cargo/targo" — six at once on 2026-09-24, and on 2026-09-27 ten
# concurrent builds holding -mutate SHARED while .package-cache was FREE, i.e.
# nothing was blocked at all. The verdict now comes from the LOCK STATE: only an
# exclusive lock blocks, and only an idle, old holder of one is a wedge.
CACHE_LOCK="${CARGO_HOME:-$HOME/.cargo}"

# proc_lock_rows FILE -> "READ|WRITE PID" for each flock HELD on FILE (Linux).
# /proc/locks prints waiters on `->` lines; those are skipped, so every row is a
# holder.
proc_lock_rows() {
  ino=$(stat -c %i "$1" 2>/dev/null) || return 1
  awk -v ino="$ino" '$2 == "FLOCK" { n = split($6, a, ":"); if (a[n] == ino) print $4, $5 }' /proc/locks
}

# lock_state FILE -> free | shared | exclusive | unknown
# Linux names holders in /proc/locks. Darwin's F_GETLK sees flock locks but
# reports pid -1 for them (no holder identity): a WRITE probe conflicts with
# any lock, a READ probe only with an exclusive one. F_GETLK does NOT see flock
# locks on Linux, hence two paths. Both only LOOK; nothing is ever acquired.
lock_state() {
  if [ -r /proc/locks ]; then
    rows=$(proc_lock_rows "$1") || { echo unknown; return 0; }
    if [ -z "$rows" ]; then echo free
    elif printf '%s\n' "$rows" | grep -q '^WRITE '; then echo exclusive
    else echo shared; fi
    return 0
  fi
  if [ "$(uname -s)" = Darwin ] && command -v perl >/dev/null 2>&1; then
    perl -MFcntl -e '
      open(my $f, "<", $ARGV[0]) or do { print "unknown\n"; exit 0 };
      sub probe {                       # Darwin struct flock: start len pid type whence
        my $b = pack("q q l s s", 0, 0, 0, $_[0], 0);
        fcntl($f, F_GETLK, $b) or return -1;
        return (unpack("q q l s s", $b))[3];
      }
      my ($w, $r) = (probe(F_WRLCK), probe(F_RDLCK));
      print $w < 0 || $r < 0 ? "unknown\n"
          : $w == F_UNLCK    ? "free\n"
          : $r == F_UNLCK    ? "shared\n"
          :                    "exclusive\n";' "$1" 2>/dev/null || echo unknown
    return 0
  fi
  echo unknown
}

CACHE_SEEN=0
for LF in "$CACHE_LOCK/.package-cache" "$CACHE_LOCK/.package-cache-mutate"; do
  [ -e "$LF" ] || continue
  CACHE_SEEN=1
  NAME=${LF##*/}
  OPENERS=$(lsof -t -- "$LF" 2>/dev/null | sort -un || true)
  NOPEN=$(printf '%s' "$OPENERS" | grep -c . || true)
  STATE=$(lock_state "$LF")
  case "$STATE" in
    free)
      ok "$NAME: unlocked — $NOPEN process(es) have it open and none holds it" ;;
    shared)
      ok "$NAME: held SHARED ($NOPEN process(es) have it open) — running builds; this blocks no build" ;;
    unknown)
      note "$NAME: $NOPEN process(es) have it open; this platform does not say who HOLDS it"
      note '  An open file is not a held lock (a waiter has it open too), so no wedge verdict is given.' ;;
    exclusive)
      # Who holds it: exact on Linux; on Darwin, one of the openers.
      HOLDERS=$OPENERS
      EXACT=0
      if [ -r /proc/locks ]; then
        HOLDERS=$(proc_lock_rows "$LF" | awk '$1 == "WRITE" {print $2}' | sort -un)
        EXACT=1
      fi
      [ "$(printf '%s' "$HOLDERS" | grep -c .)" -eq 1 ] && EXACT=1
      ALL_IDLE_OLD=1
      NCAND=0
      for p in $OPENERS; do
        INFO=$(ps -o pid=,ppid=,pcpu=,etime= -p "$p" 2>/dev/null || true)
        [ -n "$INFO" ] || continue
        PPID_=$(printf '%s' "$INFO" | awk '{print $2}')
        CPU=$(printf '%s' "$INFO" | awk '{print $3}')
        ET=$(printf '%s' "$INFO" | awk '{print $4}')
        ROLE=waiter
        case " $(printf '%s' "$HOLDERS" | tr '\n' ' ') " in *" $p "*)
          if [ "$EXACT" -eq 1 ]; then ROLE=holder; else ROLE=holder-or-waiter; fi ;;
        esac
        printf '  %s pid=%s ppid=%s cpu=%s elapsed=%s %s\n' "$NAME" "$p" "$PPID_" "$CPU" "$ET" "$ROLE"
        [ "$ROLE" = waiter ] && continue
        NCAND=$((NCAND + 1))
        # 0% CPU alone is NOT a wedge: a cargo parent legitimately sits at 0%
        # while its children compile (this script's first run flagged a healthy
        # 1m26s build). A wedge is idle AND OLD, so require both — of EVERY
        # process that could be the holder, since one of them is.
        case "$CPU" in 0.0|0) ;; *) ALL_IDLE_OLD=0 ;; esac
        [ "$(etime_secs "$ET")" -ge "$WEDGE_MIN_SECS" ] || ALL_IDLE_OLD=0
      done
      if [ "$NCAND" -gt 0 ] && [ "$ALL_IDLE_OLD" -eq 1 ]; then
        H=$(printf '%s' "$HOLDERS" | tr '\n' ' ' | sed 's/ $//')
        if [ "$EXACT" -eq 1 ]; then
          bad "pid $H holds $LF EXCLUSIVE at 0% CPU for over ${WEDGE_MIN_SECS}s — wedged, blocking every cargo/targo that uses $CACHE_LOCK."
          note "  kill -9 $H   # and its children: ps -eo pid,ppid | awk '\$2==$H {print \$1}' | xargs -n1 kill -9"
        else
          bad "$LF is held EXCLUSIVE and every process that has it open ($H) has sat at 0% CPU for over ${WEDGE_MIN_SECS}s — its holder is wedged, blocking every cargo/targo that uses $CACHE_LOCK."
          note '  The holder is the ONE of these not blocked in flock (`sample <pid> 1` shows flock on a waiter'"'"'s main thread); kill that one, not the queue.'
        fi
      else
        ok "$NAME: held EXCLUSIVE and a process that could be its holder is making progress"
      fi ;;
  esac
done
[ "$CACHE_SEEN" -eq 1 ] || ok "no package-cache lock files under $CACHE_LOCK"

printf '== build/ lock ==\n'
if [ -d "$ROOT/.trust-build-lock" ]; then
  note "held: $(cat "$ROOT/.trust-build-lock/info" 2>/dev/null | head -1)"
  note 'A build under a measurement destroys it, and vice versa (CLAUDE.md).'
else
  ok 'free'
fi

printf '== disk and the two unbounded caches ==\n'
AVAIL=$(df -g "$ROOT" 2>/dev/null | awk 'NR==2 {print $4}')
case "${AVAIL:-}" in
  ''|*[!0-9]*) note 'could not read free space' ;;
  *) if [ "$AVAIL" -lt 50 ]; then
       bad "only ${AVAIL}Gi free — at zero bytes NOTHING works."
       note '  rm -rf crates/target/debug/incremental   # pure rebuildable state'
       note '  targo --unverified resource fixed -- repo-prune --tool-target-trees'
     else ok "${AVAIL}Gi free"; fi ;;
esac
# HOST-02: incremental-cache policy belongs to the native Trust toolchain
# (thresholds, cargo-lock aware, crates/target*/debug/incremental only). The
# build lock runs it on every acquisition; here it reports, and --fix applies.
native_incremental_preflight() {
  for native in "${TRUST_BUILD_TREE_BOOTSTRAP:-}" \
      "$ROOT/build/bootstrap/debug/bootstrap" "$ROOT/build/bootstrap/release/bootstrap"; do
    [ -n "$native" ] && [ -x "$native" ] || continue
    if [ "$("$native" --trust-build-tree-lock reclaim-incremental --protocol 2>/dev/null)" = trust-incremental-reclamation-v1 ]; then
      "$native" --trust-build-tree-lock reclaim-incremental --repo-root "$ROOT" "$@"
      return $?
    fi
  done
  # The default inspection is read-only: PATH's Targo shim may install a
  # selected SDK, so only an already available native provider is invoked.
  note 'native incremental reclaimer unavailable; build a current Bootstrap or select TRUST_BUILD_TREE_BOOTSTRAP'
  return 2
}
if [ "$FIX" -eq 1 ]; then
  native_incremental_preflight --apply 2>&1 | sed 's/^/  /'
else
  native_incremental_preflight 2>&1 | sed 's/^/  /'
fi
if [ -s "$ROOT/.trust-build-lock.reclaim.log" ]; then
  note "last automatic reclaim: $(tail -1 "$ROOT/.trust-build-lock.reclaim.log")"
fi

printf '== submodule Cargo.lock drift ==\n'
DRIFTED=''
for d in "$ROOT"/first-party/*/; do
  [ -e "$d/Cargo.lock" ] || continue
  m=$(basename "$d")
  if ! git -C "$d" diff --quiet -- Cargo.lock 2>/dev/null; then
    DRIFTED="$DRIFTED $m"
  fi
done
if [ -n "$DRIFTED" ]; then
  # Merely RUNNING targo in a submodule re-resolves git-rev deps and rewrites
  # its lock — silently DOWNGRADING a pinned dependency. The superproject builds
  # these as path members of ITS workspace and never reads these locks, so the
  # drift is pure noise that must never ride along in a commit.
  # `check_submodule_lock_coherence.sh` documents the recorded incoherence this
  # drift is "fixing"; reverting is the correct action, not re-recording it.
  bad "Cargo.lock drift in:$DRIFTED (a targo run in a submodule rewrote it)"
  if [ "$FIX" -eq 1 ]; then
    for m in $DRIFTED; do
      git -C "$ROOT/first-party/$m" checkout -- Cargo.lock
      note "reverted first-party/$m/Cargo.lock"
    done
    PROBLEMS=$((PROBLEMS - 1))
  else
    note 'Revert (never commit it):'
    for m in $DRIFTED; do note "  git -C first-party/$m checkout -- Cargo.lock"; done
  fi
else
  ok 'none'
fi

# A first-party pin that moved AHEAD of the consumers compiled against it is the
# single most expensive failure this repo has: main stops building for everyone,
# and `x.py build` reveals only ONE offending crate per ~25-minute round.
printf '== first-party pin vs. its consumers ==\n'
MOVED=''
for d in "$ROOT"/first-party/*/; do
  m=$(basename "$d")
  # A pin whose gitlink moved in the last few commits is the suspect. Cheap
  # proxy: did HEAD change this gitlink relative to its parent?
  if git -C "$ROOT" diff --quiet HEAD~1 HEAD -- "first-party/$m" 2>/dev/null; then :; else
    MOVED="$MOVED $m"
  fi
done
if [ -n "$MOVED" ]; then
  note "gitlink(s) moved in HEAD:$MOVED"
  note 'A pin move can break consumers in TWO ways that a grep will not find:'
  note '  * a new enum variant -> every exhaustive `match` over it fails (E0004)'
  note '  * a new struct field -> every struct literal fails (E0063)'
  note 'ENUMERATE THEM ALL IN ONE PASS -- do NOT use `x.py build`, which reveals'
  note 'one crate per round at ~25 min each:'
  note '  ./x.py check --stage 1 2>&1 | tee /tmp/check.log'
  note "  grep -E '^error' /tmp/check.log | sed 's/ due to.*//' | sort -u"
  note 'Measured 2026-09-21: one trust-ir pin move broke 17 sites across 6 crates'
  note '(8x E0004 from `Inst::MakeAggregate`, 9x E0063 from `ScopeData.inlined_at`).'
  note 'FIX SHAPE: each sibling rev-pins trust-ir for STANDALONE builds while the'
  note 'superproject `[patch]`es it to `first-party/trust-ir`. So naming a new'
  note 'variant explicitly compiles in the workspace and BREAKS standalone. Use a'
  note 'catch-all -- but make it FAIL CLOSED (refuse / delegate to the upstream'
  note 'walk), never `=> {}` or `=> vec![]`, which silently drops real work.'
else
  ok 'no first-party gitlink moved in HEAD'
fi

if [ "$SELFTEST" -eq 1 ]; then
  printf '== self-test: can the orphan detector fire? ==\n'
  # A detector that has never produced a non-zero is not evidence of a clean
  # machine. This proves the ps/awk pipeline sees a real orphaned spinner.
  ( while : ; do : ; done ) >/dev/null 2>&1 &
  SPIN=$!
  sleep 3
  # The SAME load-scaled bar orphan_hogs uses: a self-test with its own fixed
  # bar tests a different detector from the one it vouches for.
  SEEN=$(ps -eo pid,ppid,pcpu,comm 2>/dev/null | awk -v s="$SPIN" -v min="$HOG_MIN_PCPU" 'NR>1 && $1==s && $3>min+0 {print $1}')
  kill -9 "$SPIN" 2>/dev/null || true
  if [ -n "$SEEN" ]; then
    ok "detector fired on a live spinner (pid $SPIN) — a zero above is meaningful"
  else
    bad 'detector did NOT fire on a known spinner — the ps/awk filter is broken, so every zero above is a lie'
  fi
fi

printf '\n'
if [ "$PROBLEMS" -eq 0 ]; then
  printf 'machine-preflight: OK — fit to build and measure.\n'
  exit 0
fi
printf 'machine-preflight: %s problem(s). Fix these BEFORE blaming a slow build.\n' "$PROBLEMS"
exit 1
