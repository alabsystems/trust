#!/usr/bin/env bash
# End-to-end test of scripts/hooks/pre-push's FAST-LANE POOL, through real
# `git push`es to a bare remote.
#
# The hook runs its fast lanes TRUST_PRE_PUSH_FAST_JOBS at a time and prints
# each one's output, under its own header and graded as in line, in MANIFEST
# order (the hook header, "THE FAST LANES RUN IN A POOL"). This test holds that
# contract:
#   * the lanes really overlap, and their output still reads in manifest order
#     even when a later lane finishes first;
#   * a red lane is still FAIL and the verdict RED, a SKIPPED lane is not PASS,
#     an optional lane's red is WARN, exactly as in line;
#   * a FAST_SOLO_RE lane runs alone, after every pooled lane has ended;
#   * TRUST_PRE_PUSH_FAST_JOBS=1 runs every lane in line, one after another;
#   * a lane runs from the repository root with stdin closed (it must not eat
#     the hook's ref list);
#   * the worktree target default reaches child lanes without overriding an
#     explicit Cargo or native Targo target choice, including empty values;
#   * an interrupted hook (TERM, INT) stops every pool lane, promptly, and
#     leaves none running.
#
# The fixture repo carries a COPY of the real hook and a stand-in harness whose
# `--list push` names the lanes; lane.sh records when each lane starts and ends.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
HOOK="$REPO_ROOT/scripts/hooks/pre-push"
[ -f "$HOOK" ] || { echo "pre-push fast-pool tests: no $HOOK" >&2; exit 2; }
command -v perl >/dev/null 2>&1 || { echo "pre-push fast-pool tests: needs perl" >&2; exit 2; }

# A push hook running this test must not hand the fixtures its own push.
unset TRUST_PUSHED_REFS TRUST_PUSH_REMOTE TRUST_PRE_PUSH_SCOPED TRUST_PRE_PUSH_FAST_JOBS \
  CARGO_TARGET_DIR TARGO_TARGET_DIR FIXTURE_SLOW_S FIXTURE_RED FIXTURE_HANG
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@example.invalid
export GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@example.invalid
export TRUST_PRE_PUSH_SHADOW=0
# Fixtures exercise unmanaged scheduling first, even when the suite itself
# owns a machine-wide admission. Managed cases below set their own share.
unset BUILD_SLOT_HELD CARGO_BUILD_JOBS
unset GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE

TMP="$(mktemp -d)" || exit 2
trap 'rm -rf "${TMP:?}"' EXIT

FAILED=0
pass() { echo "  ok   $1"; }
fail() { echo "  FAIL $1"; FAILED=1; }

# now: seconds since the epoch, to the millisecond.
cat > "$TMP/now.sh" <<'EOF'
perl -MTime::HiRes=time -e 'printf "%.3f\n", time'
EOF

# lane.sh <name> <exit> <sleep s>: record pid, cwd, stdin and start, print,
# sleep, record the end. FIXTURE_HANG=1: sleep 60 instead (an interrupt case).
cat > "$TMP/lane.sh" <<'EOF'
#!/usr/bin/env bash
echo "$$" > "$FIXTURE_MARKS/$1.pid"
pwd -P > "$FIXTURE_MARKS/$1.cwd"
printf '%s\n' "${CARGO_TARGET_DIR+x}" > "$FIXTURE_MARKS/$1.cargo-target-set"
printf '%s\n' "${CARGO_TARGET_DIR-}" > "$FIXTURE_MARKS/$1.cargo-target"
printf '%s\n' "${TARGO_TARGET_DIR+x}" > "$FIXTURE_MARKS/$1.targo-target-set"
printf '%s\n' "${TARGO_TARGET_DIR-}" > "$FIXTURE_MARKS/$1.targo-target"
if read -r line; then echo "read: $line" > "$FIXTURE_MARKS/$1.stdin"; else echo none > "$FIXTURE_MARKS/$1.stdin"; fi
bash "$FIXTURE_TMP/now.sh" >> "$FIXTURE_MARKS/$1.start"
echo "lane $1 output"
if [ -n "${FIXTURE_HANG:-}" ]; then sleep 60; else sleep "$3"; fi
bash "$FIXTURE_TMP/now.sh" >> "$FIXTURE_MARKS/$1.end"
echo "lane $1 done"
exit "$2"
EOF

T="$TMP/template"
mkdir -p "$T/scripts/hooks" "$T/tests/trust-comprehensive"
cp "$HOOK" "$T/scripts/hooks/pre-push" && chmod +x "$T/scripts/hooks/pre-push"
printf '# quarantine ledger (fixture)\n' > "$T/tests/trust-comprehensive/divergences.toml"
# fast.slow is first in the manifest and finishes last of the pooled lanes;
# fast.crates-tests-scoped-selftest is the FAST_SOLO_RE lane.
cat > "$T/tests/run_trust_comprehensive_harness.sh" <<EOF
#!/usr/bin/env bash
[ "\${1:-}" = "--list" ] || exit 0
row() { printf '%s\t%s\t%s\t%s\t%s\n' "\$1" fixture "\$2" 2026-10-14 "\$3"; }
row fast.slow true 'bash "$TMP/lane.sh" slow 0 "\${FIXTURE_SLOW_S:-2}"'
row fast.solo-before true 'bash "$TMP/lane.sh" solo-before 0 0'
row fast.crates-tests-scoped-selftest true 'bash "$TMP/lane.sh" solo 0 1'
row fast.quick true 'bash "$TMP/lane.sh" quick "\${FIXTURE_RED:-0}" 0'
row fast.skip true 'echo "SKIPPED: nothing to do"'
row fast.optional false 'bash "$TMP/lane.sh" optional 1 0'
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
  export FIXTURE_MARKS="$TMP/$1.marks"
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
# Here-strings, not `printf | grep -q` (a pipefail race: docs/KNOWN_HAZARDS.md).
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
  local label="$1" prev=0 n want; shift
  for want in "$@"; do
    n="$(grep -nF -- "$want" <<<"$OUT" | head -1 | cut -d: -f1)"
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

echo "== the pool: lanes overlap, output reads in manifest order"
new_case green
TRUST_PRE_PUSH_FAST_JOBS=4 attempt "green" pushed main && {
  saw "the pool is announced" "^fast lanes: 5 in a pool of 4, printed in manifest order; then 1 alone \(FAST_SOLO_RE\)$"
  in_order "each lane's output sits under its own header, in manifest order" \
    "=== fast.slow ===" "lane slow output" "lane slow done" "PASS: fast.slow" \
    "=== fast.solo-before ===" "PASS: fast.solo-before" \
    "=== fast.quick ===" "lane quick output" "PASS: fast.quick" \
    "=== fast.skip ===" "SKIPPED: fast.skip ran nothing" \
    "=== fast.optional ===" "WARN: fast.optional FAILED exit=1" \
    "=== fast.crates-tests-scoped-selftest ===" "lane solo output" "PASS: fast.crates-tests-scoped-selftest" \
    "PRE-PUSH: GREEN"
  not_saw "a SKIPPED lane is never PASS" "^PASS: fast\.skip$"
}
before "fast.quick started before fast.slow ended (the lanes overlap)" quick.start slow.end
before "fast.quick ended before fast.slow (a later lane finished first)" quick.end slow.end
before "the solo lane started only after fast.slow ended" slow.end solo.start
before "the solo lane started only after fast.optional ended" optional.end solo.start
# Timing must end at the child's completion, rather than at manifest-order
# grading after fast.slow. Both runs have genuine independently recorded ends.
slow_elapsed="$(sed -nE 's/^TIMING: phase=lane lane=fast\.slow elapsed_s=([0-9]+) .*/\1/p' <<<"$OUT")"
quick_elapsed="$(sed -nE 's/^TIMING: phase=lane lane=fast\.quick elapsed_s=([0-9]+) .*/\1/p' <<<"$OUT")"
if [ -n "$slow_elapsed" ] && [ -n "$quick_elapsed" ] \
    && [ "$slow_elapsed" -ge 2 ] && [ "$quick_elapsed" -lt "$slow_elapsed" ]; then
  pass "pooled timing measures execution, not waiting for manifest-order printing"
else fail "pooled timing lost actual ends (slow=$slow_elapsed, quick=$quick_elapsed)"; fi
printf -v timing_refs '%q' "refs/heads/main $(git -C "$W" rev-parse HEAD) refs/heads/main $(git -C "$W" rev-parse HEAD^)"
if grep -qF -- "exit=0 clock=bash-seconds authority=none refs=$timing_refs" <<<"$OUT"; then
  pass "timing preserves the exact original pushed and destination SHAs"
else fail "timing lost the original pushed refs"; fi
saw "optional red timing preserves the actual exit" '^TIMING: phase=lane lane=fast\.optional elapsed_s=[0-9]+ exit=1 '
saw "skipped execution has timing without becoming PASS" '^TIMING: phase=lane lane=fast\.skip elapsed_s=[0-9]+ exit=0 '
saw "the fast phase has elapsed timing" '^TIMING: phase=fast-lanes lane=- elapsed_s=[0-9]+ exit=- '
saw "the inherited comparison phase is distinguished" '^TIMING: phase=inherited-comparison lane=- elapsed_s=[0-9]+ exit=- '
if [ "$(mark slow.cwd)" = "$(cd "$W" && pwd -P)" ]; then pass "a lane runs from the repository root"
else fail "a lane runs from $(mark slow.cwd), not $W"; fi
if [ "$(mark slow.stdin)" = none ]; then pass "a lane's stdin is closed"
else fail "a lane read the hook's stdin: $(mark slow.stdin)"; fi
if [ "$(mark slow.cargo-target-set)" = x ] && [ "$(mark slow.cargo-target)" = "$(cd "$W" && pwd -P)/crates/target" ]; then
  pass "the default target belongs to the pushing worktree"
else fail "the default target is missing or names another worktree"; fi
if [ ! -e "$W/crates/target" ]; then pass "selecting a target does not create it"
else fail "the hook created a target without a build"; fi

echo "== target directory: caller choices retain native precedence"
target_case() {
  local label="$1" cargo_set="$2" cargo="$3" targo_set="$4" targo="$5"; shift 5
  new_case "$label"
  OUT="$(env "$@" TRUST_PRE_PUSH_FAST_JOBS=4 FIXTURE_SLOW_S=0 git -C "$W" push origin main 2>&1)"
  local rc=$?
  if [ "$rc" -ne 0 ]; then
    fail "$label: push refused (exit $rc)"; printf '%s\n' "$OUT" | tail -30; return
  fi
  if [ "$(mark slow.cargo-target-set)" = "$cargo_set" ] && [ "$(mark slow.cargo-target)" = "$cargo" ] \
      && [ "$(mark slow.targo-target-set)" = "$targo_set" ] && [ "$(mark slow.targo-target)" = "$targo" ]; then
    pass "$label: the child receives the caller's target choices"
  else fail "$label: target choices changed in the hook"; fi
}
target_case "default target with spaces" x "$(cd "$TMP" && pwd -P)/default target with spaces/crates/target" "" ""
# A caller's target is named by its real path too (EW-24 review): a relative
# one against the repository root, a missing one through its parent.
target_case "Cargo target with spaces" x "$(cd "$TMP" && pwd -P)/Cargo target with spaces/caller target" "" "" "CARGO_TARGET_DIR=caller target"
target_case "native Targo target" "" "" x "$(cd "$TMP" && pwd -P)/native target" "TARGO_TARGET_DIR=$TMP/native target"
target_case "both target spellings" x "$(cd "$TMP" && pwd -P)/cargo" x "$(cd "$TMP" && pwd -P)/native" \
  "CARGO_TARGET_DIR=$TMP/cargo" "TARGO_TARGET_DIR=$TMP/native"
mkdir -p "$TMP/caller real target" && ln -s "caller real target" "$TMP/caller link"
target_case "symlinked Cargo target" x "$(cd "$TMP" && pwd -P)/caller real target" "" "" \
  "CARGO_TARGET_DIR=$TMP/caller link"
target_case "symlinked native Targo target" "" "" x "$(cd "$TMP" && pwd -P)/caller real target" \
  "TARGO_TARGET_DIR=$TMP/caller link"
target_case "empty Cargo target" x "" "" "" CARGO_TARGET_DIR=
target_case "empty native Targo target" "" "" x "" TARGO_TARGET_DIR=

# EW-24: a pre-2026-09-10 Mac's crates/target is a symlink to
# crates/target.noindex; atpkg refuses a target named through a symlink, so
# the hook's default names the real directory.
new_case "symlinked default target"
mkdir -p "$W/crates/target.noindex" && ln -s target.noindex "$W/crates/target"
OUT="$(env TRUST_PRE_PUSH_FAST_JOBS=4 FIXTURE_SLOW_S=0 git -C "$W" push origin main 2>&1)"
if [ $? -ne 0 ]; then fail "symlinked default target: push refused"; printf '%s\n' "$OUT" | tail -30
elif [ "$(mark slow.cargo-target-set)" = x ] \
    && [ "$(mark slow.cargo-target)" = "$(cd "$W" && pwd -P)/crates/target.noindex" ]; then
  pass "a symlinked default target reaches the child by its real path"
else fail "a symlinked default target reached the child as $(mark slow.cargo-target)"; fi
new_case "dangling symlinked default target"
ln -s target.noindex "$W/crates/target" 2>/dev/null || { mkdir -p "$W/crates" && ln -s target.noindex "$W/crates/target"; }
OUT="$(env TRUST_PRE_PUSH_FAST_JOBS=4 FIXTURE_SLOW_S=0 git -C "$W" push origin main 2>&1)"
if [ $? -ne 0 ]; then fail "dangling symlinked default target: push refused"; printf '%s\n' "$OUT" | tail -30
elif [ "$(mark slow.cargo-target)" = "$(cd "$W" && pwd -P)/crates/target.noindex" ] && [ ! -e "$W/crates/target.noindex" ]; then
  pass "a dangling symlinked default target is named by where it points, and not created"
else fail "a dangling symlinked default target reached the child as $(mark slow.cargo-target)"; fi

new_case red
TRUST_PRE_PUSH_FAST_JOBS=4 FIXTURE_RED=1 attempt "a red lane" refused main && {
  saw "a red execution's timing retains exit 1" '^TIMING: phase=lane lane=fast\.quick elapsed_s=[0-9]+ exit=1 '
  saw "it is FAIL" "^FAIL: fast\.quick$"
  saw "the lanes beside it are still PASS" "^PASS: fast\.slow$"
  saw "the verdict is RED" "^PRE-PUSH: RED"
  not_saw "never GREEN" "^PRE-PUSH: GREEN"
}

echo "== diagnostic timing storage is never judgement authority"
new_case no-timing
# Drop only this fixture's elapsed files before grading. The real child,
# publication status and grader still execute; failed timing reads are real.
perl - "$W/scripts/hooks/pre-push" <<'PERL'
use strict; use warnings;
my $path = shift;
open my $in, '<', $path or die $!; local $/; my $text = <$in>; close $in;
my $needle = '  timing_file lane "$gate_id" "$FAST_DIR/$1.elapsed" "$status"';
my $injected = '  rm -f "$FAST_DIR/$1.elapsed"' . "\n" . $needle;
my $count = $text =~ s/\Q$needle\E/$injected/g;
die "expected one pooled timing reader, found $count" unless $count == 1;
open my $out, '>', $path or die $!; print {$out} $text; close $out or die $!;
PERL
TRUST_PRE_PUSH_FAST_JOBS=4 FIXTURE_SLOW_S=0 attempt "missing timing does not refuse a green lane" pushed main && {
  saw "missing timing is explicit" '^TIMING: phase=lane lane=fast\.quick elapsed_s=unavailable exit=0 '
  saw "the actual green lane still passes" '^PASS: fast\.quick$'
  saw "the actual optional red remains a warning" '^WARN: fast\.optional FAILED exit=1 '
}

echo "== TRUST_PRE_PUSH_FAST_JOBS=1: in line, as before the pool"
new_case serial
TRUST_PRE_PUSH_FAST_JOBS=1 FIXTURE_SLOW_S=1 attempt "serial" pushed main && {
  saw "serial execution also records actual elapsed and exit" '^TIMING: phase=lane lane=fast\.slow elapsed_s=[1-9][0-9]* exit=0 '
  not_saw "no pool is announced" "^fast lanes: "
  in_order "the lanes print in manifest order" \
    "=== fast.slow ===" "=== fast.solo-before ===" "=== fast.crates-tests-scoped-selftest ===" \
    "=== fast.quick ===" "=== fast.skip ===" "=== fast.optional ===" "PRE-PUSH: GREEN"
}
before "fast.quick started only after fast.slow ended" slow.end quick.start
before "the solo lane ran in its manifest place, before fast.quick" solo.end quick.start
if [ "$(mark slow.cargo-target-set)" = x ] && [ "$(mark slow.cargo-target)" = "$(cd "$W" && pwd -P)/crates/target" ]; then
  pass "serial lanes receive the same worktree target default"
else fail "serial lanes lost the worktree target default"; fi

echo "== TRUST_PRE_PUSH_FAST_JOBS unset: the host helper sizes the pool"
new_case helper
mkdir -p "$W/scripts/lib" && cp "$REPO_ROOT/scripts/lib/host_budget.py" "$W/scripts/lib/" \
  && git -C "$W" add -A && git -C "$W" commit -qm helper
# A lane that wants more than any host has: the helper's plan is ONE lane, so the
# hook runs them in line. Without the helper it would be the CPU count.
TRUST_HOST_FAST_LANE_WANT_GIB=100000 FIXTURE_SLOW_S=1 attempt "helper sizes to one" pushed main && {
  not_saw "one lane fits: no pool is announced" "^fast lanes: "
  saw "still GREEN" "^PRE-PUSH: GREEN"
}
rm -rf "${W:?}/scripts/lib"; git -C "$W" add -A; git -C "$W" commit -qm "no helper"
FIXTURE_SLOW_S=1 attempt "no helper: the CPU count" pushed main && {
  saw "a pool of the CPU count (at most 16)" "^fast lanes: [0-9]+ in a pool of ([2-9]|1[0-6])"
}

echo "== an explicit pool cannot exceed a build-slot admission"
new_case managed-pool
BUILD_SLOT_HELD=1 CARGO_BUILD_JOBS=2 TRUST_PRE_PUSH_FAST_JOBS=16 FIXTURE_SLOW_S=1 \
  attempt "managed fast pool" pushed main && {
  saw "the admitted two-child ceiling wins" "^fast lanes: 5 in a pool of 2, printed in manifest order"
  saw "all rows still pass" "^PRE-PUSH: GREEN"
}

echo "== an interrupted hook leaves no pool lane running"
# interrupt <case> <signal>: push in the background, signal the hook once two
# lanes are running, and check what is left.
interrupt() {
  local name="$1" sig="$2" push_pid hook_pid rc t0 p alive=""
  new_case "$name"
  # perl puts INT and QUIT back to their defaults, which bash ignores in a
  # background job (and a hook that inherits a signal ignored cannot trap it).
  ( cd "$W" && TRUST_PRE_PUSH_FAST_JOBS=4 FIXTURE_HANG=1 \
      perl -e '$SIG{INT} = $SIG{QUIT} = "DEFAULT"; exec @ARGV' git push origin main ) >"$TMP/$name.out" 2>&1 &
  push_pid=$!
  for _ in $(seq 1 300); do
    [ -s "$FIXTURE_MARKS/slow.start" ] && [ -s "$FIXTURE_MARKS/quick.start" ] && break; sleep 0.1
  done
  hook_pid="$(pgrep -f "pre-push origin $R" | head -1)"
  if [ -z "$hook_pid" ] || [ ! -s "$FIXTURE_MARKS/quick.start" ]; then
    fail "$name: the lanes never started"; kill "$push_pid" 2>/dev/null; return
  fi
  t0=$SECONDS
  kill "-$sig" "$hook_pid"
  wait "$push_pid"; rc=$?
  OUT="$(cat "$TMP/$name.out")"
  if [ "$rc" -ne 0 ]; then pass "the push is refused"; else fail "the interrupted push landed"; fi
  # The lanes sleep 60 s: a hook that waited them out would also leave nothing
  # running, only a minute later.
  if [ $((SECONDS - t0)) -lt 20 ]; then pass "the hook ended promptly"; else fail "the hook waited out its lanes"; fi
  saw "the hook says what it did" "^pre-push: interrupted — stopping the fast lanes$"
  not_saw "no verdict" "^PRE-PUSH: (GREEN|RED)"
  sleep 0.5
  for p in slow solo-before quick optional; do
    [ -s "$FIXTURE_MARKS/$p.pid" ] && kill -0 "$(mark "$p.pid")" 2>/dev/null && alive="$alive $p"
  done
  if [ -z "$alive" ]; then pass "no lane outlived the hook"; else
    fail "still running:$alive"
    for p in slow solo-before quick optional; do kill "$(mark "$p.pid")" 2>/dev/null; done
  fi
  [ -e "$FIXTURE_MARKS/solo.start" ] && fail "the solo lane started after the interrupt" || pass "the solo lane never started"
}
interrupt interrupted-term TERM
interrupt interrupted-int INT

echo
if [ "$FAILED" -ne 0 ]; then
  echo "pre-push fast-pool tests: FAILED"
  exit 1
fi
echo "pre-push fast-pool tests: all passed"
