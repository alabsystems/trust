#!/usr/bin/env bash
# MUTATION PROOF for scripts/trust_build_lock.sh.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
#
# A lock that cannot fail is not a lock. This runs a behaviour suite against the
# real script (every case must pass), then re-runs it against SIX deliberately
# broken copies. Each mutant must make a DIFFERENT set of cases fail — a mutation
# nothing notices means the case that was supposed to cover it does not.
#
# The mutants are the six ways this lock could plausibly have been written wrong,
# and five of them are ways locks in this repo HAVE been written wrong:
#
#   M1  test-then-create instead of atomic mkdir   (the classic acquire race)
#   M2  a holder is always assumed alive           (a crash locks the tree forever)
#   M3  release does not check the token           (anyone can free anyone's lock)
#   M4  only same-kind holders conflict            (THE ASYMMETRY THAT COST FOUR RUNS:
#                                                   a build could start under a sweep)
#   M5  no pid-reuse guard                         (a recycled pid reads as alive)
#   M6  the two pgrep patterns that reported "clear" against a live process
#
# House style follows scripts/trust_ir_tag_families.py --selftest: name each
# mutation in prose, print one line per mutation saying whether the gate FIRED,
# and fail loudly if a mutation slipped through.
set -uo pipefail

REPO_ROOT=$(cd -P "${BASH_SOURCE[0]%/*}/../.." && pwd -P)
PRISTINE="$REPO_ROOT/scripts/trust_build_lock.sh"
WORK=$(mktemp -d)
WORK=$(cd -P "$WORK" && pwd -P)
KEEPALIVES=()

cleanup_all() {
  for p in "${KEEPALIVES[@]:-}"; do [ -n "$p" ] && kill -9 "$p" 2>/dev/null; done
  rm -rf "$WORK"
}
trap cleanup_all EXIT

fail_hard() { printf 'trust_build_lock_test: %s\n' "$*" >&2; exit 2; }
[ -f "$PRISTINE" ] || fail_hard "missing $PRISTINE"

# A process we can point --pid at that outlives the check. Returns its pid.
#
# The redirections are load-bearing. This runs inside `$( )`, and a background job
# that inherits the substitution's stdout keeps that pipe open, so the substitution
# blocks for the child's whole lifetime instead of returning its pid. Measured
# while writing this file: a 600-second hang on the first case.
spawn_keepalive() {
  sleep 300 >/dev/null 2>&1 &
  local p=$!
  KEEPALIVES+=("$p")
  printf '%s' "$p"
}

fresh_root() {
  local r
  r=$(mktemp -d "$WORK/root.XXXXXX")
  (cd -P "$r" && pwd -P)
}

# ---------------------------------------------------------------------------
# Behaviour cases. Each prints nothing on success and returns non-zero on
# failure. $1 = the lock script under test (pristine or a mutant).
# ---------------------------------------------------------------------------

# T1 — a live holder is named and the second acquirer refuses.
t_refuse_while_held() {
  local lock=$1 root out rc holder
  root=$(fresh_root); holder=$(spawn_keepalive)
  TRUST_REPO="$root" sh "$lock" acquire --kind build --purpose "T1 holder" \
      --pid "$holder" >/dev/null 2>&1 || return 1
  out=$(TRUST_REPO="$root" sh "$lock" acquire --kind build --purpose "T1 second" \
        --pid "$holder" 2>&1); rc=$?
  kill -9 "$holder" 2>/dev/null
  [ "$rc" -eq 3 ] || return 1
  # "naming the holder" is the requirement, not merely refusing.
  grep -q "REFUSING" <<<"$out" || return 1
  grep -q "pid $holder" <<<"$out" || return 1
  grep -q "T1 holder" <<<"$out" || return 1
}

# T2 — a holder killed -9 is stale; the next acquirer reclaims AND says so.
t_reclaim_stale() {
  local lock=$1 root out rc holder
  root=$(fresh_root); holder=$(spawn_keepalive)
  TRUST_REPO="$root" sh "$lock" acquire --kind measurement --purpose "T2 doomed" \
      --pid "$holder" >/dev/null 2>&1 || return 1
  kill -9 "$holder" 2>/dev/null; wait "$holder" 2>/dev/null
  out=$(TRUST_REPO="$root" sh "$lock" acquire --kind build --purpose "T2 heir" \
        --pid $$ 2>&1); rc=$?
  [ "$rc" -eq 0 ] || return 1
  grep -q "RECLAIMING a stale lock" <<<"$out" || return 1
}

# T3a — a BUILD in flight blocks a measurement.
t_build_blocks_sweep() {
  local lock=$1 root rc holder
  root=$(fresh_root); holder=$(spawn_keepalive)
  TRUST_REPO="$root" sh "$lock" acquire --kind build --purpose "T3a build" \
      --pid "$holder" >/dev/null 2>&1 || return 1
  TRUST_REPO="$root" sh "$lock" acquire --kind measurement --purpose "T3a sweep" \
      --pid "$holder" >/dev/null 2>&1; rc=$?
  kill -9 "$holder" 2>/dev/null
  [ "$rc" -eq 3 ]
}

# T3b — a MEASUREMENT in flight blocks a build. This is the direction that did
# not exist before the lock, and the direction that destroyed four runs.
t_sweep_blocks_build() {
  local lock=$1 root rc holder
  root=$(fresh_root); holder=$(spawn_keepalive)
  TRUST_REPO="$root" sh "$lock" acquire --kind measurement --purpose "T3b sweep" \
      --pid "$holder" >/dev/null 2>&1 || return 1
  TRUST_REPO="$root" sh "$lock" acquire --kind build --purpose "T3b build" \
      --pid "$holder" >/dev/null 2>&1; rc=$?
  kill -9 "$holder" 2>/dev/null
  [ "$rc" -eq 3 ]
}

# T4 — the holder's trap releases on EXIT, INT and TERM alike. A sentinel that
# outlives its holder blocks every other lane indefinitely, which is worse than
# the collision it prevents.
t_trap_releases() {
  local lock=$1 root harness sig
  root=$(fresh_root)
  harness="$root/hold.sh"
  cat > "$harness" <<EOF
#!/bin/sh
set -u
TOK=\$(TRUST_REPO="$root" sh "$lock" acquire --kind measurement \\
        --purpose "T4 trap harness" --pid \$\$ 2>/dev/null)
[ -n "\$TOK" ] || exit 9
cleanup() { TRUST_REPO="$root" sh "$lock" release "\$TOK" >/dev/null 2>&1; }
trap 'cleanup; exit 130' INT
trap 'cleanup; exit 143' TERM
trap cleanup EXIT
: > "$root/ready"
# BACKGROUND + wait, never a foreground sleep. A caught signal that arrives while
# the shell is running a foreground external command is not delivered until that
# command RETURNS; the \`wait\` builtin is interruptible. Measured 2026-08-20:
# 20s trap latency foreground vs 0s through \`wait\`. run_measurement_sweep.sh
# holds the real lock the same way for the same reason.
sleep "\${1:-60}" & wait \$!
EOF
  chmod +x "$harness"

  # (a) normal EXIT
  rm -f "$root/ready"
  sh "$harness" 1 >/dev/null 2>&1
  [ -d "$root/.trust-build-lock" ] && return 1

  # (b) INT and (c) TERM
  #
  # `set -m` is load-bearing for the INT case and for that case only. POSIX says a
  # command started ASYNCHRONOUSLY by a non-interactive shell has SIGINT and SIGQUIT
  # set to ignore, and a shell may not un-ignore a signal it inherited ignored — so
  # `trap ... INT` inside the harness silently becomes a no-op and the signal is
  # dropped. Measured 2026-08-20: 30s (i.e. never; the sleep simply ran out) without
  # job control, 0s with it. Job control gives the child its own process group and
  # the default dispositions, which is what a human pressing Ctrl-C actually
  # produces. SIGTERM is never ignored this way, but it is tested through the same
  # path so both arms are exercised identically.
  local had_m=1; [[ $- == *m* ]] || had_m=0
  set -m
  for sig in INT TERM; do
    rm -f "$root/ready"
    sh "$harness" 60 >/dev/null 2>&1 &
    local hp=$!
    local waited=0
    while [ ! -e "$root/ready" ] && [ "$waited" -lt 100 ]; do
      sleep 0.1; waited=$((waited + 1))
    done
    [ -e "$root/ready" ] || { kill -9 "$hp" 2>/dev/null; [ "$had_m" -eq 0 ] && set +m; return 1; }
    [ -d "$root/.trust-build-lock" ] || { kill -9 "$hp" 2>/dev/null; [ "$had_m" -eq 0 ] && set +m; return 1; }
    kill -"$sig" "$hp" 2>/dev/null
    wait "$hp" 2>/dev/null
    if [ -d "$root/.trust-build-lock" ]; then
      [ "$had_m" -eq 0 ] && set +m
      printf '      %s left the lock behind\n' "$sig" >&2
      return 1
    fi
  done
  [ "$had_m" -eq 0 ] && set +m
  return 0
}

# T5 — the acquire race. N acquirers released together; exactly one may win.
# This is the case that distinguishes an atomic primitive from a check.
T5_ROUNDS=25
T5_RACERS=16
t_race_one_winner() {
  local lock=$1 root racer holder round wins
  root=$(fresh_root); holder=$(spawn_keepalive)
  racer="$root/racer.sh"
  cat > "$racer" <<EOF
#!/bin/sh
# Spin on the barrier so all racers reach mkdir(2) inside the same microseconds.
until [ -e "\$1" ]; do :; done
TRUST_REPO="$root" sh "$lock" acquire --kind build --purpose "racer \$\$" \\
    --pid "$holder" >/dev/null 2>&1
echo \$? > "\$2/\$\$"
EOF
  chmod +x "$racer"

  for ((round = 0; round < T5_ROUNDS; round++)); do
    local go="$root/go.$round" results="$root/res.$round"
    mkdir -p "$results"
    rm -rf "$root/.trust-build-lock"
    local i pids=()
    for ((i = 0; i < T5_RACERS; i++)); do sh "$racer" "$go" "$results" & pids+=("$!"); done
    : > "$go"
    # Wait for the RACERS specifically. A bare `wait` also blocks on the
    # long-lived keepalive whose pid the racers are recording, which hangs the
    # suite for the keepalive's full lifetime.
    wait "${pids[@]}" 2>/dev/null
    wins=$(grep -lx 0 "$results"/* 2>/dev/null | wc -l | tr -d ' ')
    if [ "$wins" != "1" ]; then
      kill -9 "$holder" 2>/dev/null
      printf '      round %d: %s winners out of %d racers (must be exactly 1)\n' \
        "$round" "$wins" "$T5_RACERS" >&2
      return 1
    fi
  done
  kill -9 "$holder" 2>/dev/null
  return 0
}

# T6 — a foreign token must not free somebody else's lock.
t_foreign_release_refused() {
  local lock=$1 root rc holder
  root=$(fresh_root); holder=$(spawn_keepalive)
  TRUST_REPO="$root" sh "$lock" acquire --kind measurement --purpose "T6 holder" \
      --pid "$holder" >/dev/null 2>&1 || return 1
  TRUST_REPO="$root" sh "$lock" release "not-the-token" >/dev/null 2>&1; rc=$?
  local still_held=1
  [ -d "$root/.trust-build-lock" ] || still_held=0
  kill -9 "$holder" 2>/dev/null
  [ "$rc" -eq 4 ] && [ "$still_held" -eq 1 ]
}

# T7 — pid reuse. The recorded pid is ALIVE but is a different process than the
# one that took the lock. Without a start-time comparison the lock is immortal.
t_pid_reuse_detected() {
  local lock=$1 root out rc holder
  root=$(fresh_root); holder=$(spawn_keepalive)
  TRUST_REPO="$root" sh "$lock" acquire --kind build --purpose "T7 original" \
      --pid "$holder" >/dev/null 2>&1 || return 1
  # Same pid, different process: rewrite the recorded start time.
  sed -i.bak 's/^pstart=.*/pstart=Thu Jan  1 00:00:00 1970/' \
      "$root/.trust-build-lock/info" || return 1
  rm -f "$root/.trust-build-lock/info.bak"
  out=$(TRUST_REPO="$root" sh "$lock" acquire --kind build --purpose "T7 heir" \
        --pid $$ 2>&1); rc=$?
  kill -9 "$holder" 2>/dev/null
  [ "$rc" -eq 0 ] || return 1
  grep -q "RECLAIMING a stale lock" <<<"$out"
}

# T9 — the belt-and-braces scan for processes that never took the lock, and with
# it the correctness of the two pgrep predicates that used to report "clear"
# against something live.
#
# T9a: a scorecard sweep run directly (not via run_measurement_sweep.sh) blocks
#      a build. The fake's argv is `/bin/sh <root>/trust_ir_producer_scorecard.py`
#      — no lowercase "python" anywhere, exactly like the real CommandLineTools
#      interpreter, which execs as .../Python.app/Contents/MacOS/Python.
# T9b: a raw bootstrap binary blocks a sweep. The fake's argv is `./bootstrap 600`
#      — the subcommand is NOT adjacent to the word "bootstrap", exactly like
#      `x.py --stage 1 build`, whose child argv is
#      `build/bootstrap/debug/bootstrap --stage 1 build`.

# Kill a fake process AND its children. The fake scorecard is a shell whose child
# is a `sleep`; killing only the shell orphans the sleep, and an orphan that
# inherited this suite's stdout holds the `$(run_suite ...)` pipe open for its
# whole lifetime. Measured while writing this file: the suite sat for 600s after
# every case had already passed.
reap_tree() {
  local p=$1 c
  for c in $(pgrep -P "$p" 2>/dev/null); do kill -9 "$c" 2>/dev/null; done
  kill -9 "$p" 2>/dev/null
  wait "$p" 2>/dev/null
}

t_unwrapped_conflicts_seen() {
  local lock=$1 root rc out sc_pid bs_pid
  root=$(fresh_root)

  printf '#!/bin/sh\nsleep 600\n' > "$root/trust_ir_producer_scorecard.py"
  chmod +x "$root/trust_ir_producer_scorecard.py"
  (cd "$root" && exec /bin/sh "$root/trust_ir_producer_scorecard.py") >/dev/null 2>&1 &
  sc_pid=$!; KEEPALIVES+=("$sc_pid")
  sleep 0.7
  out=$(TRUST_REPO="$root" sh "$lock" acquire --kind build --purpose "T9a build" \
        --pid $$ 2>&1); rc=$?
  reap_tree "$sc_pid"
  if [ "$rc" -ne 3 ] || ! grep -q "SCORECARD" <<<"$out"; then
    rm -rf "$root/.trust-build-lock"; return 1
  fi
  [ -d "$root/.trust-build-lock" ] && { rm -rf "$root/.trust-build-lock"; return 1; }

  ln -sf /bin/sleep "$root/bootstrap"
  (cd "$root" && exec ./bootstrap 600) >/dev/null 2>&1 &
  bs_pid=$!; KEEPALIVES+=("$bs_pid")
  sleep 0.7
  out=$(TRUST_REPO="$root" sh "$lock" acquire --kind measurement --purpose "T9b sweep" \
        --pid $$ 2>&1); rc=$?
  reap_tree "$bs_pid"
  rm -rf "$root/.trust-build-lock"
  [ "$rc" -eq 3 ] && grep -q "BUILD" <<<"$out"
}

# T10 — THE DEFAULT HOLDER MUST OUTLIVE `acquire`. Deliberately the one case that
# does NOT pass `--pid`: every other case supplies it, which is exactly why this
# hole survived. Until 2026-08-29 `acquire` defaulted the holder to `$$` — the
# lock script's own pid — and the script exits the instant it prints the token, so
# the lock was stale from birth and the next acquirer walked through it without
# waiting. Measured in a scratch root that day: holder pid DEAD one instant after
# acquire, second acquirer issued a token immediately. It cost a measurement
# (`E0463: can't find crate for 'core'`) when a build took the tree.
#
# The assertion is in two halves because either alone is satisfiable by accident:
# the recorded holder must still be ALIVE after acquire returns, AND a second
# acquirer must still be REFUSED.
t_default_holder_durable() {
  local lock=$1 root rc hp
  root=$(fresh_root)
  TRUST_REPO="$root" sh "$lock" acquire --kind measurement \
      --purpose "T10 batch with no --pid" >/dev/null 2>&1 || return 1
  hp=$(sed -n 's/^pid=//p' "$root/.trust-build-lock/info" 2>/dev/null | head -1)
  [ -n "$hp" ] || return 1
  ps -p "$hp" >/dev/null 2>&1 || return 1        # born stale
  TRUST_REPO="$root" sh "$lock" acquire --kind build --purpose "T10 heir" \
      --pid $$ >/dev/null 2>&1; rc=$?
  rm -rf "$root/.trust-build-lock"
  [ "$rc" -eq 3 ]                                 # self-released if 0
}

# T11 — A STALE-HOLDER TAKEOVER MUST LEAVE A DURABLE RECORD, not just a line on
# stderr. Reclaiming a dead holder is correct, but every acquiring caller in the
# tree redirects this script's stderr (`call_summary_census.sh` with
# `2>/dev/null`, x.py through a pipe), so a stderr-only notice is invisible in
# exactly the runs where a lane discovers its lock was taken. The heir here
# suppresses stderr on purpose — that is the shape that hid it.
t_takeover_recorded() {
  local lock=$1 root rc holder
  root=$(fresh_root); holder=$(spawn_keepalive)
  TRUST_REPO="$root" sh "$lock" acquire --kind measurement --purpose "T11 crashed lane" \
      --pid "$holder" >/dev/null 2>&1 || return 1
  kill -9 "$holder" 2>/dev/null; wait "$holder" 2>/dev/null
  TRUST_REPO="$root" sh "$lock" acquire --kind build --purpose "T11 heir" \
      --pid $$ >/dev/null 2>/dev/null; rc=$?
  rm -rf "$root/.trust-build-lock"
  [ "$rc" -eq 0 ] || return 1
  [ -f "$root/.trust-build-lock.breaks" ] || return 1
  grep -q "STALE-TAKEOVER" "$root/.trust-build-lock.breaks" || return 1
  # and it must name WHO was displaced, not merely that something was.
  grep -q "T11 crashed lane" "$root/.trust-build-lock.breaks"
}

CASES=(refuse_while_held reclaim_stale build_blocks_sweep sweep_blocks_build
       trap_releases race_one_winner foreign_release_refused pid_reuse_detected
       unwrapped_conflicts_seen default_holder_durable takeover_recorded)

# Runs every case against $1; echoes the space-separated names that FAILED.
# Progress goes to stderr as it happens: a suite that prints nothing for minutes
# is indistinguishable from a hang, and this one legitimately takes tens of
# seconds because several cases are timing-sensitive by construction.
run_suite() {
  local lock=$1 c failed=()
  for c in "${CASES[@]}"; do
    printf '      %-26s' "$c" >&2
    local t0=$SECONDS
    if "t_$c" "$lock"; then
      printf 'ok   %2ds\n' "$((SECONDS - t0))" >&2
    else
      failed+=("$c")
      printf 'FAIL %2ds\n' "$((SECONDS - t0))" >&2
    fi
  done
  printf '%s' "${failed[*]:-}"
}

# ---------------------------------------------------------------------------
# Baseline
# ---------------------------------------------------------------------------
printf '=== baseline: the real scripts/trust_build_lock.sh\n'
BASE_FAIL=$(run_suite "$PRISTINE")
if [ -n "$BASE_FAIL" ]; then
  printf 'BUILD-LOCK SELFTEST: FAIL — the unmutated lock does not pass its own suite: %s\n' \
    "$BASE_FAIL" >&2
  exit 1
fi
printf '    all %d cases pass (race: %d rounds x %d racers = %d contended acquisitions)\n' \
  "${#CASES[@]}" "$T5_ROUNDS" "$T5_RACERS" "$((T5_ROUNDS * T5_RACERS))"

# ---------------------------------------------------------------------------
# Mutations. `mutate <name> <awk-program>` writes a mutant and REFUSES to
# continue if the program changed nothing — a mutation proof whose mutations
# silently stopped applying (a renamed variable, a reflowed line) is a green
# light that tests nothing.
# ---------------------------------------------------------------------------
MUT_DIR="$WORK/mutants"; mkdir -p "$MUT_DIR"
declare -a M_NAME M_DESC M_PATH

# NOT a command substitution. `fail_hard` must be able to abort the run, and
# `$(...)` would put it in a subshell where `exit` only ends the substitution —
# the suite would then sail on with an empty mutant path and report nine
# "failures" that are really one missing file.
#
# Each `local` is its own statement on purpose: bash 3.2 (what macOS ships, and
# what runs this) expands every word of a `local` command BEFORE performing any
# of its assignments, so `local name=$1 path="$MUT_DIR/$name.sh"` reads `name`
# while it is still unset — fatal under `set -u`. Measured here, 2026-08-20.
add_mutant() {
  local name=$1
  local desc=$2
  local prog=$3
  local path="$MUT_DIR/$name.sh"
  awk "$prog" "$PRISTINE" > "$path" || fail_hard "awk failed for $name"
  if cmp -s "$PRISTINE" "$path"; then
    fail_hard "mutation '$name' changed nothing — its anchor no longer matches, so it proves nothing"
  fi
  # A mutant that does not PARSE fails every case for a reason that has nothing to
  # do with the defect it is supposed to model, and reads as a pass. That is not
  # hypothetical: `\x27` inside an awk replacement is a greedy hex escape, so
  # `\x27bootstrap` became one stray character and M6 was silently proving nothing
  # while printing [ok]. Caught 2026-08-20 only because "fails all nine" looked odd.
  bash -n "$path" 2>/dev/null || fail_hard "mutant '$name' does not parse — it would fail every case for the wrong reason"
  M_NAME+=("$name"); M_DESC+=("$desc"); M_PATH+=("$path")
}

add_mutant M1 "test-then-create instead of the atomic mkdir claim" '
  /if mkdir "\$LOCKDIR" 2>\/dev\/null; then/ {
    print "    if [ ! -d \"$LOCKDIR\" ] && { sleep 0.05; mkdir -p \"$LOCKDIR\"; }; then"
    next }
  { print }'

add_mutant M2 "a recorded holder is always assumed alive" '
  { print }
  /^pid_is_live\(\) \{$/ { print "  return 0   # MUTANT M2" }'

add_mutant M3 "release removes the lock without checking the token" '
  /^  if \[ "\$_held" != "\$_tok" \]; then$/ { print "  if false; then"; next }
  { print }'

add_mutant M4 "only a same-kind holder conflicts (a build may start under a sweep)" '
  /^    _hp=\$\(info_field "\$_info" pid\)$/ {
    print "    [ \"$(info_field \"$_info\" kind)\" = \"$KIND\" ] || { reclaim || :; continue; }" }
  { print }'

add_mutant M5 "no pid-reuse guard: the recorded start time is not compared" '
  /if \[ -n "\$_now_start" \] && \[ "\$_now_start" != "\$_want_start" \]; then/ {
    print "    if false; then"; next }
  { print }'

# The single quotes are built with sprintf, not written as \x27: awk reads \x
# escapes greedily, so "\x27bootstrap" is parsed as the hex digits 27b and the
# replacement silently loses its opening quote. The search sides use `.` for the
# quote so nothing has to be escaped there either.
add_mutant M6 "the two pgrep predicates that reported clear against a live process" '
  BEGIN { q = sprintf("%c", 39) }
  { sub(/pgrep -x bootstrap 2>\/dev\/null/,
        "pgrep -f " q "bootstrap (build|check)" q " 2>/dev/null")
    sub(/pgrep -f .trust_ir_producer_scorecar\[d\]\\\.py. 2>\/dev\/null/,
        "pgrep -f " q "python.*trust_ir_producer_scorecard" q " 2>/dev/null")
    print }'

# M7/M8 model the TWO defects measured on 2026-08-29, the day after this suite's
# first six were written. Both had to be added by hand: the suite was green
# throughout, because every existing case supplies `--pid` and every existing case
# reads stderr.
add_mutant M7 "the pre-2026-08-29 default: the holder pid is the lock script itself" '
  /^  KIND=..; PURPOSE=.unspecified.; HOLD_PID=..; WAIT=/ {
    print "  KIND=\"\"; PURPOSE=\"unspecified\"; HOLD_PID=$$; WAIT=${TRUST_BUILD_LOCK_WAIT:-0}"
    next }
  { print }'

add_mutant M8 "a stale takeover announces itself on stderr only, leaving no record" '
  /^loud_takeover\(\) \{$/ { intake = 1 }
  intake && /^  \} >> "\$BREAKS" 2>\/dev\/null$/ {
    print "  } >> /dev/null 2>&1   # MUTANT M8"; intake = 0; next }
  { print }'

printf '\n=== mutation proof: each mutant must break a DIFFERENT set of cases\n'
ok=1
declare -a SIGNATURES
for i in "${!M_NAME[@]}"; do
  sig=$(run_suite "${M_PATH[$i]}")
  SIGNATURES+=("$sig")
  if [ -z "$sig" ]; then
    printf '  [BAD] %s %s: EVERY case still passes — nothing covers this\n' \
      "${M_NAME[$i]}" "${M_DESC[$i]}"
    ok=0
  elif [ "$(wc -w <<<"$sig")" -eq "${#CASES[@]}" ]; then
    # Every case failing is almost never a faithful model of one defect; it is
    # what a mutant that cannot run looks like. Treated as a failure so it cannot
    # masquerade as thorough coverage.
    printf '  [BAD] %s %s: fails ALL %d cases — that is a broken mutant, not a caught defect\n' \
      "${M_NAME[$i]}" "${M_DESC[$i]}" "${#CASES[@]}"
    ok=0
  else
    printf '  [ok ] %s %s\n        -> newly FAILS: %s\n' \
      "${M_NAME[$i]}" "${M_DESC[$i]}" "$sig"
  fi
done

# Distinctness: two mutants with the same failure signature mean one of them is
# not actually being distinguished by the suite.
for i in "${!SIGNATURES[@]}"; do
  for ((j = i + 1; j < ${#SIGNATURES[@]}; j++)); do
    if [ -n "${SIGNATURES[$i]}" ] && [ "${SIGNATURES[$i]}" = "${SIGNATURES[$j]}" ]; then
      printf '  [BAD] %s and %s are indistinguishable (both -> %s)\n' \
        "${M_NAME[$i]}" "${M_NAME[$j]}" "${SIGNATURES[$i]}"
      ok=0
    fi
  done
done

printf '\n'
if [ "$ok" -eq 1 ]; then
  printf 'BUILD-LOCK SELFTEST: OK — %d cases green, %d mutants each caught with a distinct signature\n' \
    "${#CASES[@]}" "${#M_NAME[@]}"
  exit 0
fi
printf 'BUILD-LOCK SELFTEST: FAIL\n' >&2
exit 1
