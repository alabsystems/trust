#!/usr/bin/env bash
# End-to-end test of scripts/hooks/pre-push's OVERLAPPED crates-tests build,
# through real `git push`es to a bare remote.
#
# Where the host can hold it (or TRUST_PRE_PUSH_SCOPED=overlap), the hook starts
# the scoped lane that runs scripts/check_crates_tests_scoped.py early, so its
# BUILD overlaps the scoped lanes before it, and releases its barrier (`run`)
# only after all of them have finished; its TEST binaries never start before
# that (the hook header, "CRATES-TESTS' BUILD OVERLAPS THE LANES BEFORE IT").
# This test holds that contract:
#   * the build really overlaps the lane before it, and in line it does not;
#   * no test of the overlapped lane starts before every earlier scoped lane
#     has FINISHED, and a lane after it starts only once it has finished;
#   * each lane's output sits under its own header, in manifest order, graded
#     PASS / FAIL / SKIPPED as in line; a red lane anywhere is still RED, and
#     an earlier red lane still lets the overlapped lane's tests run;
#   * the STALE stop is asked before the scoped lanes start, between them, and
#     before the barrier: a push stopped while the overlapped lane builds stops
#     it before any of its tests ran, and ends STALE (or RED after a FAIL);
#   * an interrupted hook, whether the overlapped lane is building or testing,
#     leaves no lane running;
#   * serial mode passes no barrier and runs the lanes one after another; the
#     mode and its reason are printed, a bogus mode runs in line;
#   * the shared worktree target default reaches the crates child in either
#     mode, while an explicit native target remains caller-owned;
#   * only a lane whose WHOLE command runs the script overlaps (a step before
#     it would run unbarriered), and a submodule x.py would check out (not at
#     its gitlink, or not checked out) puts the lanes in line;
#   * a barrier the hook cannot write stops the lane and the push at once
#     (never a wait on each other); a STALE stop's verdict stays the last
#     thing the hook says; QUIT interrupts like INT/TERM/HUP; a lane gets ONE
#     SIGINT per interrupt.
#
# The fixture repo carries a COPY of the real hook, a stand-in harness whose
# `--list push` names two fast lanes and four scoped lanes, and a stand-in
# scripts/check_crates_tests_scoped.py (bash, run as `bash <path>`) that speaks
# the lane's side of the barrier: it "builds" (sleeps FIXTURE_BUILD_S), then,
# when TRUST_CRATES_TESTS_RUN_AFTER is set, waits for that file and "tests"
# only if it says `run`. scoped.a and scoped.b (the compiler-check and
# completion-gate stand-ins) record when they start and end and sleep
# FIXTURE_SLEEP; scoped.after follows the overlapped lane in manifest order.
# `mover` plays another machine landing on the destination (FIXTURE_MOVE_IN
# names where), as in scripts/tests/pre_push_stale_destination_test.sh.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
HOOK="$REPO_ROOT/scripts/hooks/pre-push"
[ -f "$HOOK" ] || { echo "pre-push overlap tests: no $HOOK" >&2; exit 2; }
command -v perl >/dev/null 2>&1 || { echo "pre-push overlap tests: needs perl" >&2; exit 2; }

# A push hook running this test must not hand the fixtures its own push.
unset TRUST_PUSHED_REFS TRUST_PUSH_REMOTE TRUST_PRE_PUSH_SCOPED TRUST_CRATES_TESTS_RUN_AFTER \
  TRUST_CRATES_TESTS_RUN_AFTER_OWNER FIXTURE_MOVE_IN FIXTURE_A_RC FIXTURE_CRATES_RC \
  CARGO_TARGET_DIR TARGO_TARGET_DIR FIXTURE_CRATES_SKIP FIXTURE_SLEEP FIXTURE_BUILD_S FIXTURE_TEST_S \
  FIXTURE_PUBLISH_SCOPE FIXTURE_PUBLISH_POINT FIXTURE_PUBLISH_MUTANT
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@example.invalid
export GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@example.invalid
export TRUST_PRE_PUSH_SHADOW=0
# Fixtures exercise unmanaged scheduling first, even when the suite itself
# owns a machine-wide admission. Managed cases below set their own share.
unset BUILD_SLOT_HELD CARGO_BUILD_JOBS
unset GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE

TMP="$(mktemp -d)" || exit 2
trap 'chmod -R u+rwx "${TMP:?}" 2>/dev/null; rm -rf "${TMP:?}"' EXIT

FAILED=0
pass() { echo "  ok   $1"; }
fail() { echo "  FAIL $1"; FAILED=1; }

cat > "$TMP/mover.sh" <<'EOF'
#!/usr/bin/env bash
[ "${FIXTURE_MOVE_IN:-}" = "$1" ] || exit 0
other="$FIXTURE_OTHER"
git -C "$other" fetch -q origin 2>/dev/null
git -C "$other" checkout -q -B mover origin/main 2>/dev/null
echo "$1" >> "$other/landed-elsewhere.txt"
git -C "$other" add -A && git -C "$other" commit -qm "landed elsewhere during the hook"
git -C "$other" push -q --no-verify origin mover:refs/heads/main
EOF

# now: seconds since the epoch, to the millisecond.
cat > "$TMP/now.sh" <<'EOF'
perl -MTime::HiRes=time -e 'printf "%.3f\n", time'
EOF

# lane.sh <name> <exit>: record pid and start, print, maybe move the
# destination (mover <name>), sleep FIXTURE_SLEEP (default 3), record the end.
# Starts and ends are appended, and `mark` reads the first: a lane run twice
# is judged by its earliest run.
# FIXTURE_LOCK_IN=<name>: that lane makes the overlapped lane's scratch dir
# unwritable (a full disk, as far as the barrier's write can tell).
# FIXTURE_COUNT_INTS: the lane counts each SIGINT it gets (one line in
# <name>.ints), waits to be interrupted, and takes 2 s to clean up after the
# first, as x.py handing over its build lock does.
cat > "$TMP/lane.sh" <<'EOF'
#!/usr/bin/env bash
echo "$$" > "$FIXTURE_MARKS/$1.pid"
bash "$FIXTURE_TMP/now.sh" >> "$FIXTURE_MARKS/$1.start"
echo "lane $1 output"
bash "$FIXTURE_TMP/mover.sh" "$1"
if [ "${FIXTURE_LOCK_IN:-}" = "$1" ]; then
  chmod a-w "$(dirname "$(cat "$FIXTURE_MARKS/crates.barrier-env")")"
fi
if [ -n "${FIXTURE_COUNT_INTS:-}" ]; then
  got=""
  trap 'echo int >> "$FIXTURE_MARKS/$1.ints"; got=1' INT
  echo ready > "$FIXTURE_MARKS/$1.ready"
  n=0; while [ -z "$got" ] && [ "$n" -lt 600 ]; do sleep 0.1; n=$((n + 1)); done
  for _ in 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20; do sleep 0.1; done
  exit 130
fi
sleep "${FIXTURE_SLEEP:-3}"
bash "$FIXTURE_TMP/now.sh" >> "$FIXTURE_MARKS/$1.end"
exit "$2"
EOF

T="$TMP/template"
mkdir -p "$T/scripts/hooks" "$T/tests/trust-comprehensive"
cp "$HOOK" "$T/scripts/hooks/pre-push" && chmod +x "$T/scripts/hooks/pre-push"
mkdir -p "$T/scripts/lib" && cp "$REPO_ROOT/scripts/lib/host_budget.py" "$T/scripts/lib/host_budget.py"
printf '# quarantine ledger (fixture)\n' > "$T/tests/trust-comprehensive/divergences.toml"
# The crates-tests stand-in: the barrier protocol of the real lane, nothing else.
cat > "$T/scripts/check_crates_tests_scoped.py" <<'EOF'
m="$FIXTURE_MARKS"; now() { bash "$FIXTURE_TMP/now.sh"; }
# Interrupted: record what the barrier said at that moment (a stop must never
# be preceded by `run`, however quickly the kill follows it).
trap 'cat "${TRUST_CRATES_TESTS_RUN_AFTER:-/nonexistent}" > "$m/crates.barrier-at-interrupt" 2>/dev/null; exit 130' INT
echo "$$" > "$m/crates.pid"
echo "${TRUST_CRATES_TESTS_RUN_AFTER:-unset}" > "$m/crates.barrier-env"
printf '%s\n' "${CARGO_TARGET_DIR+x}" > "$m/crates.cargo-target-set"
printf '%s\n' "${CARGO_TARGET_DIR-}" > "$m/crates.cargo-target"
printf '%s\n' "${TARGO_TARGET_DIR+x}" > "$m/crates.targo-target-set"
printf '%s\n' "${TARGO_TARGET_DIR-}" > "$m/crates.targo-target"
now > "$m/crates.build_start"
echo "crates build output"
[ -z "${FIXTURE_CRATES_SKIP:-}" ] || { echo "SKIPPED: no crates/ change"; exit 0; }
sleep "${FIXTURE_BUILD_S:-2}"
now > "$m/crates.build_end"
if [ -n "${TRUST_CRATES_TESTS_RUN_AFTER:-}" ]; then
  while [ ! -f "$TRUST_CRATES_TESTS_RUN_AFTER" ]; do sleep 0.05; done
  if [ "$(cat "$TRUST_CRATES_TESTS_RUN_AFTER")" != run ]; then
    echo "NOT JUDGED: the barrier said stop"; now > "$m/crates.stopped"; exit 3
  fi
fi
now > "$m/crates.tests_start"
echo "crates test output"
sleep "${FIXTURE_TEST_S:-1}"
now > "$m/crates.tests_end"
exit "${FIXTURE_CRATES_RC:-0}"
EOF
cat > "$T/tests/run_trust_comprehensive_harness.sh" <<EOF
#!/usr/bin/env bash
[ "\${1:-}" = "--list" ] || exit 0
printf '%s\t%s\t%s\t%s\t%s\n' fast.ok fixture true 2026-09-30 'true'
printf '%s\t%s\t%s\t%s\t%s\n' fast.mover fixture true 2026-09-30 'bash "$TMP/mover.sh" fast'
printf '%s\t%s\t%s\t%s\t%s\n' scoped.a fixture true 2026-09-30 'bash "$TMP/lane.sh" a "\${FIXTURE_A_RC:-0}"'
printf '%s\t%s\t%s\t%s\t%s\n' scoped.b fixture true 2026-09-30 'bash "$TMP/lane.sh" b 0'
if [ -n "\${FIXTURE_PREFIXED:-}" ]; then
  printf '%s\t%s\t%s\t%s\t%s\n' scoped.crates-tests fixture true 2026-09-30 'bash "$TMP/lane.sh" pre 0; bash scripts/check_crates_tests_scoped.py --push-context'
else
  printf '%s\t%s\t%s\t%s\t%s\n' scoped.crates-tests fixture true 2026-09-30 'bash scripts/check_crates_tests_scoped.py --push-context'
fi
printf '%s\t%s\t%s\t%s\t%s\n' scoped.after fixture true 2026-09-30 'FIXTURE_SLEEP=0 bash "$TMP/lane.sh" after 0'
EOF
git -C "$T" init -q -b main
git -C "$T" config core.hooksPath scripts/hooks
git -C "$T" add -A && git -C "$T" commit -qm template
export FIXTURE_TMP="$TMP"

new_case() {
  echo "-- $1"
  W="$TMP/$1"; R="$TMP/$1.git"
  cp -R "$T" "$W"
  git init -q --bare "$R"
  git -C "$W" remote add origin "$R"
  git -C "$W" push -q --no-verify origin main >/dev/null 2>&1 || fail "$1: base push"
  git clone -q "$R" "$TMP/$1.other" 2>/dev/null
  export FIXTURE_OTHER="$TMP/$1.other" FIXTURE_MARKS="$TMP/$1.marks"
  mkdir -p "$FIXTURE_MARKS"
  echo "work" > "$W/work.txt" && git -C "$W" add -A && git -C "$W" commit -qm work
}

attempt() {
  local label="$1" want="$2"; shift 2
  OUT="$(git -C "$W" push origin "$@" 2>&1)"
  local rc=$?
  if [ "$want" = pushed ] && [ "$rc" -ne 0 ]; then
    fail "$label: push refused (exit $rc), expected it to land"; printf '%s\n' "$OUT" | sed 's/^/        /' | tail -30; return 1
  fi
  if [ "$want" = refused ] && [ "$rc" -eq 0 ]; then
    fail "$label: push LANDED, expected a refusal"; printf '%s\n' "$OUT" | sed 's/^/        /' | tail -30; return 1
  fi
  return 0
}
# A here-string, not `printf | grep -q`: under pipefail, grep -q exiting at its
# first match can fail the printf still writing the rest of a long $OUT (EPIPE,
# or SIGPIPE), so saw read a present line as missing and not_saw passed it.
saw() {
  if grep -qE -- "$2" <<<"$OUT"; then pass "$1"; else
    fail "$1: output lacks /$2/"; printf '%s\n' "$OUT" | sed 's/^/        /' | tail -30
  fi
}
not_saw() {
  if grep -qE -- "$2" <<<"$OUT"; then
    fail "$1: output has /$2/"; printf '%s\n' "$OUT" | sed 's/^/        /' | tail -30
  else pass "$1"; fi
}
# in_order <label> <fixed string>...: each string's first line comes after the previous one's.
in_order() {
  local label="$1" prev=0 n; shift
  for want in "$@"; do
    n="$(printf '%s\n' "$OUT" | grep -nF -- "$want" | head -1 | cut -d: -f1)"
    if [ -z "$n" ] || [ "$n" -le "$prev" ]; then
      fail "$label: '$want' is missing or out of order"; printf '%s\n' "$OUT" | sed 's/^/        /' | tail -30; return
    fi
    prev="$n"
  done
  pass "$label"
}
mark() { head -1 "$FIXTURE_MARKS/$1" 2>/dev/null; }
# before <label> <mark x> <mark y>: x happened strictly before y (both recorded).
before() {
  local x y; x="$(mark "$2")"; y="$(mark "$3")"
  if [ -n "$x" ] && [ -n "$y" ] && awk -v x="$x" -v y="$y" 'BEGIN { exit !(x < y) }'; then pass "$1"
  else fail "$1 ($2=${x:-none}, $3=${y:-none})"; fi
}
absent() { if [ -e "$FIXTURE_MARKS/$2" ]; then fail "$1"; else pass "$1"; fi; }
# said_stop <label>: when the overlapped lane was interrupted the barrier said
# exactly `stop` (the hook writes it BEFORE it signals the lane; a missing
# barrier is a failure too: then only the signal stopped the lane), never
# `run`; or the lane read `stop` itself first (crates.stopped), a race the
# kill usually wins.
said_stop() {
  local said; said="$(mark crates.barrier-at-interrupt)"
  if [ -e "$FIXTURE_MARKS/crates.barrier-at-interrupt" ]; then
    if [ "$said" = stop ]; then pass "$1"; else fail "$1: the barrier said '${said}', not stop"; fi
  elif [ -e "$FIXTURE_MARKS/crates.stopped" ]; then pass "$1 (the lane read it before the kill)"
  else fail "$1: the lane was neither interrupted nor stopped by the barrier"; fi
}
alive_none() {  # alive_none <label> <mark.pid>...: none of those processes still runs
  local label="$1" alive="" p; shift
  for p in "$@"; do
    [ -s "$FIXTURE_MARKS/$p" ] && kill -0 "$(mark "$p")" 2>/dev/null && alive="$alive $p"
  done
  if [ -z "$alive" ]; then pass "$label"; else
    fail "$label: still running:$alive"
    for p in "$@"; do kill "$(mark "$p")" 2>/dev/null; done
  fi
}

# last_word <label> <verdict regex>: nothing the hook prints after its verdict
# block (a lander may read the last line): no `pre-push:` line follows it.
last_word() {
  if printf '%s\n' "$OUT" | awk -v v="$2" '$0 ~ v { s = 1; next } s && /^pre-push: / { bad = 1 } END { exit !(s && !bad) }'
  then pass "$1"; else
    fail "$1"; printf '%s\n' "$OUT" | sed 's/^/        /' | tail -30
  fi
}

echo "== one build-slot admission cannot be spent by two overlapping builds"
new_case managed-serial
BUILD_SLOT_HELD=1 CARGO_BUILD_JOBS=6 TRUST_PRE_PUSH_SCOPED=overlap FIXTURE_SLEEP=0 \
  FIXTURE_BUILD_S=0 FIXTURE_TEST_S=0 attempt "managed overlap preference is serialized" pushed main && {
  saw "the admission owns one heavy lane" "^scoped lanes: in line \(build-slot CPU share belongs to one heavy lane at a time\)$"
  not_saw "no lane starts early" "started:  scoped\."
}
before "both preceding lanes finish before crates build" b.end crates.build_start
for share in '' 0 -1 six 1.5; do
  new_case "managed-invalid-${share:-missing}"
  BUILD_SLOT_HELD=1 CARGO_BUILD_JOBS="$share" TRUST_PRE_PUSH_SCOPED=overlap FIXTURE_SLEEP=0 \
    attempt "invalid admission is refused before any lane" refused main && {
    saw "the missing CPU share is explicit" "requires positive integer CARGO_BUILD_JOBS"
    not_saw "no fast or heavy lane was judged" "^=== |^PRE-PUSH: GREEN"
  }
  absent "the compiler stand-in never starts" a.start
  absent "the crates stand-in never starts" crates.build_start
done

# Instrument only the fixture's COPY of the real hook. The launch, signal and
# wait owners still execute; checkpoints expose their publication/readiness
# boundaries without a replacement executable, production flag or sleep race.
instrument_publication() {
  perl - "$W/scripts/hooks/pre-push" <<'PERL'
use strict;
use warnings;
my $file = shift;
open(my $in, "<", $file) or die $!;
local $/; my $source = <$in>; close($in) or die $!;
sub replace_once {
    my ($from, $to) = @_;
    my $at = index($source, $from);
    die "missing/ambiguous hook instrumentation anchor: $from\n"
        if $at < 0 || index($source, $from, $at + length($from)) >= 0;
    substr($source, $at, length($from), $to);
}
my $checkpoint = <<'CHECKPOINT';
  my $id = $path =~ m{/([0-9]+)\.pgid$} ? "fast$1"
    : $path =~ m{/inline\.pgid$} ? "inline" : "overlap";
  my $selected = $ENV{FIXTURE_PUBLISH_SCOPE} eq "fast" ? $id =~ m{^fast}
    : $id eq "inline" || $id eq "overlap";
  my $checkpoint = sub {
    my ($point) = @_;
    return unless $selected && ($ENV{FIXTURE_PUBLISH_POINT} eq $point
      || ($ENV{FIXTURE_PUBLISH_POINT} eq "atomic"
        && ($point eq "before_print" || $point eq "before_exec")));
    my $prefix = "$ENV{FIXTURE_MARKS}/publisher.$id";
    open(my $p, ">", "$prefix.path") or die $!;
    print $p "$path\n" or die $!; close($p) or die $!;
    open(my $pid, ">", "$prefix.pid") or die $!;
    print $pid "$$\n" or die $!; close($pid) or die $!;
    open(my $ready, ">", "$prefix.$point") or die $!;
    print $ready "ready\n" or die $!; close($ready) or die $!;
    while (!-e "$ENV{FIXTURE_MARKS}/release.$point") {
      exit 130 if -e "$ENV{FIXTURE_MARKS}/publisher.cancel";
      select(undef, undef, undef, 0.01);
    }
  };
  $checkpoint->("before_open");
CHECKPOINT
replace_once('  my $path = shift; my $part = "$path.part.$$";',
    '  my $path = shift; my $part = "$path.part.$$";' . "\n" . $checkpoint);
replace_once('  print $f "$$\n" or exit 2;',
    '  $checkpoint->("before_print");' . "\n" . '  print $f "$$\n" or exit 2;');
replace_once('  exec @ARGV or exit 127',
    '  $checkpoint->("before_exec");' . "\n" . '  exec @ARGV or exit 127');
replace_once('signal_group() {', 'fixture_signal_group() {');
my $observer = <<'OBSERVER';
signal_group() {
  local result id
  fixture_signal_group "$@"; result=$?
  case "$1" in */inline.pgid) id=inline ;; */pgid) id=overlap ;; *) id=other ;; esac
  printf '%s\n' "$result" >> "$FIXTURE_MARKS/$id.signal-attempts"
  return "$result"
}

OBSERVER
replace_once("# The running lane's output, streamed AND kept, so run_lane can read the",
    $observer . "# The running lane's output, streamed AND kept, so run_lane can read the");
replace_once("  wait\n  OVERLAP_ENDED=1\n  exit 130",
    '  cat "$OVERLAP_DIR/barrier" > "$FIXTURE_MARKS/barrier.before-wait"' . "\n" .
    '  : > "$FIXTURE_MARKS/handler.wait"' . "\n  wait\n  OVERLAP_ENDED=1\n  exit 130");
my $root_line = "\n" . 'cd "$REPO_ROOT"' . "\n";
replace_once($root_line, $root_line .
    'printf "%s\n" "$$" > "$FIXTURE_MARKS/hook.pid"' . "\n");
if (($ENV{FIXTURE_PUBLISH_MUTANT} // "") eq "final-open") {
    replace_once('  open(my $f, ">", $part) or exit 2;',
        '  open(my $f, ">", $path) or exit 2;');
}
if (($ENV{FIXTURE_PUBLISH_POINT} // "") eq "before_inline") {
    replace_once('      start_overlap_lane "$o_command"',
        '      start_overlap_lane "$o_command"' . "\n" . <<'BEFORE_INLINE');
      printf "ready\n" > "$FIXTURE_MARKS/before.inline"
      while [ ! -e "$FIXTURE_MARKS/release.inline" ]; do sleep 0.01; done
BEFORE_INLINE
}
open(my $out, ">", $file) or die $!;
print $out $source or die $!; close($out) or die $!;
PERL
}

publication_wait() {
  local path="$1" deadline=$((SECONDS + 20))
  while [ ! -s "$path" ] && kill -0 "$publication_push" 2>/dev/null && [ "$SECONDS" -lt "$deadline" ]; do sleep 0.05; done
  [ -s "$path" ] || { fail "publication checkpoint missing: $path"; return 1; }
}

publication_drain() {
  local want="$1" deadline=$((SECONDS + 20)) rc id pid
  while kill -0 "$publication_push" 2>/dev/null && [ "$SECONDS" -lt "$deadline" ]; do sleep 0.05; done
  if kill -0 "$publication_push" 2>/dev/null; then
    fail "publication fixture did not drain within the unchanged twenty-second bound"
    : > "$FIXTURE_MARKS/publisher.cancel"
    [ ! -s "$FIXTURE_MARKS/hook.pid" ] || kill -TERM "$(mark hook.pid)" 2>/dev/null
    for id in $publication_ids; do
      pid="$(mark "publisher.$id.pid")"
      case "$pid" in "" | *[!0-9]*) ;; *) [ "$pid" -le 1 ] || kill -TERM -- "-$pid" 2>/dev/null ;; esac
    done
    kill -TERM "$publication_push" 2>/dev/null
  fi
  wait "$publication_push"; rc=$?
  if { [ "$want" = green ] && [ "$rc" -eq 0 ]; } || { [ "$want" = refused ] && [ "$rc" -ne 0 ]; }; then
    pass "the actual publication fixture exits $want"
  else fail "publication fixture exit $rc, expected $want"; tail -30 "$TMP/publication.out"; fi
  for id in $publication_ids; do
    pid="$(mark "publisher.$id.pid")"
    if [ -n "$pid" ] && kill -0 "$pid" 2>/dev/null; then fail "publisher $id outlived the fixture"; fi
  done
}

atomic_publication() {
  local scope="$1" mutant="${2:-}" id path expected broken="" ready=1
  new_case "publication-$scope${mutant:+-$mutant}"
  instrument_publication || { fail "publication fixture instrumentation"; return; }
  if [ "$scope" = fast ]; then publication_ids="fast0 fast1"; else publication_ids="inline overlap"; fi
  ( cd "$W" && FIXTURE_SLEEP=0 FIXTURE_BUILD_S=0 FIXTURE_TEST_S=0 \
      TRUST_PRE_PUSH_FAST_JOBS=2 TRUST_PRE_PUSH_SCOPED=overlap git push origin main ) >"$TMP/publication.out" 2>&1 &
  publication_push=$!
  for id in $publication_ids; do publication_wait "$FIXTURE_MARKS/publisher.$id.before_print" || ready=""; done
  for id in $publication_ids; do
    path="$(mark "publisher.$id.path")"
    [ -n "$path" ] || { ready=""; continue; }
    [ ! -e "$path" ] || broken=1
  done
  if [ -z "$ready" ] || [ -n "$broken" ]; then
    if [ -n "$ready" ] && [ "$mutant" = final-open ] && [ -n "$broken" ]; then
      pass "the final-open mutant is caught before an incomplete ID can be consumed"
    else fail "the final process-group path became visible before print/close"; fi
    : > "$FIXTURE_MARKS/publisher.cancel"
    publication_drain refused
    return
  fi
  [ -z "$mutant" ] || { fail "the publication control missed its final-open mutant"; }
  pass "$scope publication keeps incomplete records private"
  : > "$FIXTURE_MARKS/release.before_print"
  for id in $publication_ids; do
    publication_wait "$FIXTURE_MARKS/publisher.$id.before_exec" || ready=""
    path="$(mark "publisher.$id.path")"; expected="$(mark "publisher.$id.pid")"
    if [ -n "$path" ] && [ -n "$expected" ] && [ "$(cat "$path" 2>/dev/null)" = "$expected" ]; then
      pass "$scope $id publishes its complete group ID before exec"
    else fail "$scope $id has no complete group record"; fi
  done
  if [ -n "$ready" ]; then : > "$FIXTURE_MARKS/release.before_exec"; else : > "$FIXTURE_MARKS/publisher.cancel"; fi
  publication_drain green
}

late_publication() {
  local kind="$1" id path inline_calls overlap_calls deadline stopped_at="" ready=1
  new_case "publication-late-$kind"
  instrument_publication || { fail "late publication fixture instrumentation"; return; }
  publication_ids="inline overlap"
  ( cd "$W" && FIXTURE_SLEEP=60 FIXTURE_BUILD_S=60 \
      TRUST_PRE_PUSH_FAST_JOBS=2 TRUST_PRE_PUSH_SCOPED=overlap \
      perl -e '$SIG{INT} = $SIG{QUIT} = "DEFAULT"; exec @ARGV' git push origin main ) >"$TMP/publication.out" 2>&1 &
  publication_push=$!
  for id in $publication_ids; do publication_wait "$FIXTURE_MARKS/publisher.$id.before_open" || ready=""; done
  if [ "$kind" = empty ]; then
    for id in $publication_ids; do path="$(mark "publisher.$id.path")"; [ -z "$path" ] || : > "$path"; done
  fi
  if [ -n "$ready" ]; then
    stopped_at=$SECONDS
    kill -TERM "$(mark hook.pid)"
    deadline=$((SECONDS + 20))
    while [ "$SECONDS" -lt "$deadline" ]; do
      if [ -e "$FIXTURE_MARKS/handler.wait" ]; then
        fail "cleanup reached wait while $kind process-group IDs were still unready"; ready=""; break
      fi
      inline_calls="$(grep -c '^[^0]' "$FIXTURE_MARKS/inline.signal-attempts" 2>/dev/null)"
      overlap_calls="$(grep -c '^[^0]' "$FIXTURE_MARKS/overlap.signal-attempts" 2>/dev/null)"
      [ "${inline_calls:-0}" -ge 2 ] && [ "${overlap_calls:-0}" -ge 2 ] && break
      sleep 0.05
    done
    if [ "${inline_calls:-0}" -lt 2 ] || [ "${overlap_calls:-0}" -lt 2 ]; then
      fail "each $kind process-group ID must remain pending over repeated readiness passes"; ready=""
    fi
  fi
  if [ -n "$ready" ]; then
    pass "both $kind group records stay pending across repeated failed delivery attempts"
    : > "$FIXTURE_MARKS/release.before_open"
  else : > "$FIXTURE_MARKS/publisher.cancel"; fi
  publication_drain refused
  if [ -n "$ready" ]; then
    if [ $((SECONDS - stopped_at)) -lt 20 ]; then pass "late publication cleanup ends within twenty seconds"
    else fail "late publication cleanup exceeded the unchanged twenty-second bound"; fi
    for id in $publication_ids; do
      if [ "$(grep -c '^0$' "$FIXTURE_MARKS/$id.signal-attempts" 2>/dev/null)" = 1 ]; then
        pass "$id receives exactly one successfully delivered signal after publication"
      else fail "$id did not receive exactly one successfully delivered signal"; fi
    done
  fi
  absent "late publication starts no crates test" crates.tests_start
  if [ "$(mark barrier.before-wait)" = stop ]; then pass "late publication keeps the actual barrier stopped"
  else fail "late publication lost the stop barrier"; fi
}

before_inline_publication() {
  new_case publication-before-inline
  instrument_publication || { fail "before-inline fixture instrumentation"; return; }
  publication_ids=""
  ( cd "$W" && FIXTURE_BUILD_S=60 TRUST_PRE_PUSH_FAST_JOBS=2 TRUST_PRE_PUSH_SCOPED=overlap \
      perl -e '$SIG{INT} = $SIG{QUIT} = "DEFAULT"; exec @ARGV' git push origin main ) >"$TMP/publication.out" 2>&1 &
  publication_push=$!
  if publication_wait "$FIXTURE_MARKS/before.inline"; then
    kill -TERM "$(mark hook.pid)"
  else : > "$FIXTURE_MARKS/release.inline"; fi
  publication_drain refused
  absent "interrupt before inline launch starts no inline workload" a.pid
  absent "interrupt before inline launch starts no crates test" crates.tests_start
  if [ "$(mark barrier.before-wait)" = stop ]; then pass "before-inline cleanup keeps the barrier stopped"
  else fail "before-inline cleanup lost its stop barrier"; fi
  alive_none "before-inline cleanup leaves no crates child" crates.pid
}

echo "== process-group publication is atomic and late readiness stays owned"
FIXTURE_PUBLISH_SCOPE=fast FIXTURE_PUBLISH_POINT=atomic atomic_publication fast
FIXTURE_PUBLISH_SCOPE=scoped FIXTURE_PUBLISH_POINT=atomic atomic_publication scoped
FIXTURE_PUBLISH_SCOPE=scoped FIXTURE_PUBLISH_POINT=atomic FIXTURE_PUBLISH_MUTANT=final-open \
  atomic_publication scoped final-open
FIXTURE_PUBLISH_SCOPE=scoped FIXTURE_PUBLISH_POINT=before_open late_publication missing
FIXTURE_PUBLISH_SCOPE=scoped FIXTURE_PUBLISH_POINT=before_open late_publication empty
FIXTURE_PUBLISH_SCOPE=scoped FIXTURE_PUBLISH_POINT=before_inline before_inline_publication

echo "== overlap: the build overlaps the lanes before it; its tests wait for them"
new_case green
TRUST_PRE_PUSH_SCOPED=overlap attempt "green" pushed main && {
  saw "the mode and its reason are printed" \
    "^scoped lanes: overlap \(TRUST_PRE_PUSH_SCOPED=overlap\) — scoped\.crates-tests builds while the lanes before it run;$"
  saw "the early start is printed" "^  started:  scoped\.crates-tests \(its build only"
  saw "the release is printed" "^released: scoped\.crates-tests may run its test binaries"
  saw "its end is printed" "^  finished: scoped\.crates-tests \(exit 0\) after 0 min [0-9]+ s$"
  saw "the overlapped execution records elapsed and actual exit" \
    '^TIMING: phase=lane lane=scoped\.crates-tests elapsed_s=[0-9]+ exit=0 '
  saw "the whole scoped phase records elapsed separately" \
    '^TIMING: phase=scoped-lanes lane=- elapsed_s=[0-9]+ exit=- '
  in_order "each lane's output sits under its own header, in manifest order" \
    "=== scoped.a ===" "lane a output" "PASS: scoped.a" \
    "=== scoped.b ===" "lane b output" "PASS: scoped.b" \
    "=== scoped.crates-tests ===" "crates build output" "crates test output" "PASS: scoped.crates-tests" \
    "=== scoped.after ===" "lane after output" "PASS: scoped.after" "PRE-PUSH: GREEN"
}
before "the crates build started before scoped.a ended (overlap)" crates.build_start a.end
before "no crates test started before scoped.a finished" a.end crates.tests_start
before "no crates test started before scoped.b finished" b.end crates.tests_start
before "scoped.after started only after the crates tests ended" crates.tests_end after.start
if [ "$(mark crates.barrier-env)" != unset ]; then pass "the lane was given a barrier"; else fail "no barrier was passed"; fi
if [ "$(mark crates.cargo-target-set)" = x ] && [ "$(mark crates.cargo-target)" = "$(cd "$W" && pwd -P)/crates/target" ]; then
  pass "the overlapped crates child receives its worktree target default"
else fail "the overlapped crates child lost its worktree target default"; fi

new_case red-crates
FIXTURE_CRATES_RC=1 TRUST_PRE_PUSH_SCOPED=overlap attempt "the overlapped lane red" refused main && {
  saw "overlapped red timing preserves exit 1" \
    '^TIMING: phase=lane lane=scoped\.crates-tests elapsed_s=[0-9]+ exit=1 '
  saw "it is FAIL" "^FAIL: scoped\.crates-tests$"
  saw "the lanes beside it are still PASS" "^PASS: scoped\.b$"
  saw "the verdict is RED" "^PRE-PUSH: RED"
}

new_case red-earlier
FIXTURE_A_RC=1 TRUST_PRE_PUSH_SCOPED=overlap attempt "an earlier lane red" refused main && {
  saw "the earlier lane is FAIL" "^FAIL: scoped\.a$"
  saw "the overlapped lane still ran its tests, and passed" "^PASS: scoped\.crates-tests$"
  saw "the verdict is RED" "^PRE-PUSH: RED"
}
before "and its tests still waited for the red lane" a.end crates.tests_start

new_case skipped
FIXTURE_CRATES_SKIP=1 TRUST_PRE_PUSH_SCOPED=overlap attempt "the overlapped lane ran nothing" pushed main && {
  saw "it is graded SKIPPED, not PASS" "^SKIPPED: scoped\.crates-tests ran nothing"
  not_saw "never PASS" "^PASS: scoped\.crates-tests$"
}

echo "== in line: nothing overlaps and no barrier is passed"
new_case serial
TRUST_PRE_PUSH_SCOPED=serial attempt "serial" pushed main && {
  saw "the mode is printed" "^scoped lanes: in line \(TRUST_PRE_PUSH_SCOPED=serial\)$"
  not_saw "nothing starts early" "started:  scoped\."
  in_order "the lanes print in manifest order" \
    "=== scoped.a ===" "=== scoped.b ===" "=== scoped.crates-tests ===" "crates build output" \
    "PASS: scoped.crates-tests" "=== scoped.after ===" "PRE-PUSH: GREEN"
}
before "the crates build started after scoped.b ended" b.end crates.build_start
if [ "$(mark crates.barrier-env)" = unset ]; then pass "no barrier was passed"; else fail "serial mode passed a barrier"; fi
if [ "$(mark crates.cargo-target-set)" = x ] && [ "$(mark crates.cargo-target)" = "$(cd "$W" && pwd -P)/crates/target" ]; then
  pass "the serial crates child receives its worktree target default"
else fail "the serial crates child lost its worktree target default"; fi

new_case native-target
TARGO_TARGET_DIR="$TMP/native target" FIXTURE_SLEEP=0 FIXTURE_BUILD_S=0 FIXTURE_TEST_S=0 \
  TRUST_PRE_PUSH_SCOPED=overlap attempt "native target in overlap" pushed main
if [ "$(mark crates.cargo-target-set)" = "" ] && [ "$(mark crates.targo-target-set)" = x ] \
    && [ "$(mark crates.targo-target)" = "$(cd "$TMP" && pwd -P)/native target" ]; then
  pass "the overlapped crates child retains native Targo target selection, by its real path"
else fail "the overlapped crates child changed native Targo target selection"; fi

new_case bogus
TRUST_PRE_PUSH_SCOPED=sometimes FIXTURE_SLEEP=0 attempt "a bogus mode" pushed main \
  && saw "runs in line and says why" "^scoped lanes: in line \(TRUST_PRE_PUSH_SCOPED=sometimes is neither serial nor overlap\)$"

new_case auto
FIXTURE_SLEEP=0 attempt "the host decides" pushed main \
  && saw "and says what it measured" "^scoped lanes: (overlap \(host budget: room [0-9.]+ GiB >= .*\) — |in line \(host budget: (room [0-9.]+ GiB < .*|not even one .*|cannot measure this host)\)$)"

echo "== the destination moves"
new_case moved-before
FIXTURE_MOVE_IN=fast TRUST_PRE_PUSH_SCOPED=overlap attempt "moved during a fast lane" refused main && {
  saw "the stop before the scoped lanes is STALE" "^PRE-PUSH: STALE"
  not_saw "no scoped lane started" "started:  scoped\.|^=== scoped\."
}
absent "the overlapped lane never started" crates.pid

new_case moved-during-build
t0=$SECONDS
FIXTURE_MOVE_IN=a FIXTURE_BUILD_S=60 TRUST_PRE_PUSH_SCOPED=overlap attempt "moved while the crates lane builds" refused main && {
  saw "the stop before scoped.b is STALE" "^PRE-PUSH: STALE"
  saw "the overlapped lane is stopped in its build" "stopped scoped\.crates-tests in its build, before any of its test binaries ran"
  not_saw "no verdict" "^PRE-PUSH: (GREEN|RED)"
  not_saw "scoped.b never ran" "^=== scoped\.b ==="
  last_word "the STALE verdict is the hook's last word" "^PRE-PUSH: STALE"
}
if [ $((SECONDS - t0)) -lt 40 ]; then pass "the hook did not wait out the build"; else fail "the hook waited out the 60 s build"; fi
absent "no crates test ran" crates.tests_start
said_stop "the barrier said stop when the lane was interrupted"
alive_none "the stopped lane is gone" crates.pid

new_case moved-at-barrier
FIXTURE_MOVE_IN=b TRUST_PRE_PUSH_SCOPED=overlap attempt "moved during the last lane before the barrier" refused main && {
  saw "the check before the barrier is STALE" "^PRE-PUSH: STALE"
  not_saw "the barrier was never released" "^released: "
}
absent "no crates test ran" crates.tests_start
said_stop "the barrier said stop when the lane was interrupted"
alive_none "the stopped lane is gone" crates.pid

new_case moved-after-red
FIXTURE_A_RC=1 FIXTURE_MOVE_IN=a FIXTURE_BUILD_S=60 TRUST_PRE_PUSH_SCOPED=overlap attempt "moved after a red lane" refused main && {
  saw "the red lane is not hidden" "^FAIL: scoped\.a$"
  saw "the verdict is RED, not STALE" "^PRE-PUSH: RED"
  saw "the overlapped lane is stopped" "stopped scoped\.crates-tests in its build"
  last_word "the RED verdict is the hook's last word" "^PRE-PUSH: RED"
}
absent "no crates test ran" crates.tests_start

echo "== which lane overlaps, and when the tree forbids it"
new_case prefixed
FIXTURE_PREFIXED=1 TRUST_PRE_PUSH_SCOPED=overlap attempt "a step before the script" pushed main && {
  saw "the lanes run in line, saying why" \
    "^scoped lanes: in line \(no scoped lane's whole command runs scripts/check_crates_tests_scoped\.py"
  not_saw "nothing starts early" "started:  scoped\."
}
before "the step before the script waited for scoped.b" b.end pre.start
if [ "$(mark crates.barrier-env)" = unset ]; then pass "no barrier was passed"; else fail "a prefixed command was overlapped"; fi

new_case submodule
git init -q -b main "$TMP/subsrc"
echo one > "$TMP/subsrc/f" && git -C "$TMP/subsrc" add -A && git -C "$TMP/subsrc" commit -qm one
echo two > "$TMP/subsrc/f" && git -C "$TMP/subsrc" commit -qam two
git -C "$W" -c protocol.file.allow=always submodule -q add "$TMP/subsrc" sub >/dev/null 2>&1
git -C "$W" commit -qm "add sub"
FIXTURE_SLEEP=0 TRUST_PRE_PUSH_SCOPED=overlap attempt "a submodule at its gitlink" pushed main \
  && saw "still overlaps" "^scoped lanes: overlap \(TRUST_PRE_PUSH_SCOPED=overlap\)"
git -C "$W/sub" checkout -q HEAD~1
# Commit work.txt alone: `commit -a` would stage the drifted gitlink itself.
echo more >> "$W/work.txt" && git -C "$W" add work.txt && git -C "$W" commit -qm "more work"
rm -rf "$FIXTURE_MARKS" && mkdir -p "$FIXTURE_MARKS"
TRUST_PRE_PUSH_SCOPED=overlap attempt "a submodule off its gitlink" pushed main && {
  saw "runs in line and names it" \
    "^scoped lanes: in line \(submodule sub is checked out at [0-9a-f]{12}, not its gitlink [0-9a-f]{12}"
  not_saw "nothing starts early" "started:  scoped\."
}
before "the crates build waited for scoped.b" b.end crates.build_start
git -C "$W/sub" checkout -q main
git -C "$W" submodule -q deinit -f sub
echo more >> "$W/work.txt" && git -C "$W" add work.txt && git -C "$W" commit -qm "more work"
FIXTURE_SLEEP=0 TRUST_PRE_PUSH_SCOPED=overlap attempt "a submodule not checked out" pushed main \
  && saw "runs in line and names it" "^scoped lanes: in line \(submodule sub is not checked out"

echo "== a barrier the hook cannot write"
new_case barrier-unwritable
# The hook's scratch dir goes under $TMP, whose cleanup restores write access.
mkdir -p "$TMP/unwritable-tmp"
( cd "$W" && FIXTURE_LOCK_IN=b FIXTURE_BUILD_S=1 TRUST_PRE_PUSH_SCOPED=overlap TMPDIR="$TMP/unwritable-tmp" \
    git push origin main ) >"$TMP/unwritable.out" 2>&1 &
push_pid=$!
t0=$SECONDS
while kill -0 "$push_pid" 2>/dev/null && [ $((SECONDS - t0)) -lt 40 ]; do sleep 0.2; done
if kill -0 "$push_pid" 2>/dev/null; then
  fail "the hook and the lane waited on each other (still running after 40 s)"
  pkill -TERM -f "pre-push origin $R" 2>/dev/null; kill "$push_pid" 2>/dev/null
  [ -s "$FIXTURE_MARKS/crates.pid" ] && kill "$(mark crates.pid)" 2>/dev/null
  wait "$push_pid" 2>/dev/null
else
  wait "$push_pid"; rc=$?
  OUT="$(cat "$TMP/unwritable.out")"
  if [ "$rc" -ne 0 ]; then pass "the push is refused"; else fail "the push landed without its crates tests"; fi
  pass "the hook ended promptly"
  saw "it says why" "^pre-push: cannot write the barrier"
  not_saw "it never claims a release" "^released: "
fi
absent "no crates test ran" crates.tests_start
alive_none "the stopped lane is gone" crates.pid

echo "== an interrupted hook leaves no lane running"
# interrupt <case> <mark to wait for> [env...]: push in the background, TERM
# the hook once <mark> exists, and check what is left.
interrupt() {
  local name="$1" at="$2" push_pid hook_pid rc; shift 2
  new_case "$name"
  # perl puts INT and QUIT back to their defaults, which bash ignores in a
  # background job (and a hook that inherits a signal ignored cannot trap it).
  ( cd "$W" && env "$@" TRUST_PRE_PUSH_SCOPED=overlap \
      perl -e '$SIG{INT} = $SIG{QUIT} = "DEFAULT"; exec @ARGV' git push origin main ) >"$TMP/$name.out" 2>&1 &
  push_pid=$!
  for _ in $(seq 1 200); do [ -s "$FIXTURE_MARKS/$at" ] && break; sleep 0.1; done
  hook_pid="$(pgrep -f "pre-push origin $R" | head -1)"
  if [ -z "$hook_pid" ] || [ ! -s "$FIXTURE_MARKS/$at" ]; then
    fail "$name: never reached $at"; kill "$push_pid" 2>/dev/null; return
  fi
  local t0=$SECONDS
  kill "-${INTERRUPT_SIG:-TERM}" "$hook_pid"
  wait "$push_pid"; rc=$?
  OUT="$(cat "$TMP/$name.out")"
  if [ "$rc" -ne 0 ]; then pass "the push is refused"; else fail "the interrupted push landed"; fi
  # The lanes sleep 60 s: a hook that waited them out instead of interrupting
  # them would also leave nothing running, only a minute later.
  if [ $((SECONDS - t0)) -lt 20 ]; then pass "the hook ended promptly"; else fail "the hook waited out its lanes"; fi
  saw "the hook says what it did" "interrupting every running lane"
  sleep 0.5
  alive_none "no lane outlived the hook" a.pid crates.pid
}
interrupt interrupted-building a.pid FIXTURE_SLEEP=60 FIXTURE_BUILD_S=60
absent "no crates test ran" crates.tests_start
said_stop "the barrier said stop when the lane was interrupted"
interrupt interrupted-testing crates.tests_start FIXTURE_SLEEP=0 FIXTURE_TEST_S=60
INTERRUPT_SIG=QUIT interrupt interrupted-quit a.pid FIXTURE_SLEEP=60 FIXTURE_BUILD_S=60
absent "no crates test ran" crates.tests_start
interrupt interrupted-once a.ready FIXTURE_COUNT_INTS=1 FIXTURE_BUILD_S=60
n_ints="$(wc -l < "$FIXTURE_MARKS/a.ints" 2>/dev/null | tr -d ' ')"
if [ "${n_ints:-0}" = 1 ]; then pass "the lane got one SIGINT, not a second while it cleaned up"
else fail "the lane got ${n_ints:-0} SIGINTs"; fi

echo
if [ "$FAILED" -ne 0 ]; then
  echo "pre-push overlap tests: FAILED"
  exit 1
fi
echo "pre-push overlap tests: all passed"
