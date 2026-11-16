#!/usr/bin/env bash
# End-to-end test of scripts/hooks/pre-push's INHERITED-RED grading (the hook's
# header, "INHERITED-RED"; docs/DECISION_QUEUE.md INHERITED-RED).
#
# A red fast lane that reads the push is graded INHERITED, and the push lands,
# only when every destination tip is red on that lane with every finding key
# the push's run printed; anything else is FAIL, exactly as before.
#
# The fixture repo carries a COPY of the real hook, a stand-in harness and a
# stand-in reader derivation (scripts/check_gate_lane_coverage.py). Its lanes
# read each pushed tree's `findings.txt` from git objects, as a tree-whole lane
# does: no file means green; each line is a finding key; a line `UNKEYED` is a
# red cause without a key (no `FINDINGS: complete`); `EXIT2` means the lane
# could not judge that tree; `EXIT2KEYED` makes it exit 2 after printing the
# keys and `FINDINGS: complete` (only exit 1 is a red that can be inherited). `fast.keyed` is a pushed-refs reader;
# `fast.worktree` prints the same findings but is not one (it reads the
# working tree), so it is never inherited.
#
# Real `git push`es to a bare remote prove what lands; direct hook runs with
# crafted stdin cover the destinations a real push cannot produce here.
# Cancellation cases block only a destination replay, after its real child
# and descendant have started; TERM/INT and the launch handoff must drain them.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
HOOK="$REPO_ROOT/scripts/hooks/pre-push"
[ -f "$HOOK" ] || { echo "pre-push inherited-red tests: no $HOOK" >&2; exit 2; }
command -v perl >/dev/null 2>&1 || { echo "pre-push inherited-red tests: needs perl" >&2; exit 2; }

# A push hook running this test must not hand the fixtures its own push.
unset TRUST_PUSHED_REFS TRUST_PUSH_REMOTE
unset FIXTURE_REPLAY_MARKS FIXTURE_REPLAY_CHILD FIXTURE_REPLAY_DEST
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@example.invalid
export GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@example.invalid
export TRUST_PRE_PUSH_SHADOW=0 TRUST_PRE_PUSH_FAST_JOBS=1
unset GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE

TMP="$(mktemp -d)" || exit 2
REPLAY_HOOK_PID="" REPLAY_MARKS_DIR=""
terminate_fixture_pid() {
  local observed
  observed="$(ps -p "$1" -o command= 2>/dev/null)" || return 0
  case "$observed" in *"${TMP:?}/"*) kill -TERM "$1" 2>/dev/null || true ;; esac
}
cleanup_replay_case() {
  local path pid
  if [ -n "$REPLAY_MARKS_DIR" ]; then
    : >"$REPLAY_MARKS_DIR/release-handle"
    # Only fixture-owned PIDs, leaf first so its parents can reap normally.
    for path in descendant child lane; do
      if [ -s "$REPLAY_MARKS_DIR/$path.pid" ]; then
        read -r pid <"$REPLAY_MARKS_DIR/$path.pid"
        terminate_fixture_pid "$pid"
      fi
    done
  fi
  if [ -n "$REPLAY_HOOK_PID" ]; then
    terminate_fixture_pid "$REPLAY_HOOK_PID"
    wait "$REPLAY_HOOK_PID" 2>/dev/null || true
  fi
  REPLAY_HOOK_PID="" REPLAY_MARKS_DIR=""
}
cleanup() { cleanup_replay_case; rm -rf "${TMP:?}"; }
trap cleanup EXIT

FAILED=0
pass() { echo "  ok   $1"; }
fail() { echo "  FAIL $1"; FAILED=1; }

# The lane: judge every pushed local sha's findings.txt (a tree-whole reader).
cat > "$TMP/lane.sh" <<'EOF'
#!/usr/bin/env bash
if [ -n "${FIXTURE_REPLAY_MARKS:-}" ]; then
  replay=0
  while read -r _l local_sha _r remote_sha; do
    if [ -n "$local_sha" ] && [ "$local_sha" = "$remote_sha" ] \
        && { [ -z "${FIXTURE_REPLAY_DEST:-}" ] || [ "$local_sha" = "$FIXTURE_REPLAY_DEST" ]; }; then
      replay=1
    fi
  done <<<"${TRUST_PUSHED_REFS:-}"
  if [ "$replay" -eq 1 ]; then
    echo "$$" >"$FIXTURE_REPLAY_MARKS/lane.pid"
    bash "$FIXTURE_REPLAY_CHILD" &
    wait $!
    exit 2
  fi
fi
rc=0 keys="" unkeyed=0 exit2k=0
while read -r _l sha _r _s; do
  [ -n "${sha:-}" ] || continue
  case "$sha" in *[!0]*) ;; *) continue ;; esac
  text="$(git show "$sha:findings.txt" 2>/dev/null)" || continue
  while IFS= read -r line; do
    case "$line" in
      "") ;;
      EXIT2) echo "cannot judge $sha"; exit 2 ;;
      UNKEYED) unkeyed=1; rc=1 ;;
      EXIT2KEYED) exit2k=1 ;;
      *) keys="$keys$line"$'\n'; rc=1 ;;
    esac
  done <<<"$text"
done <<<"${TRUST_PUSHED_REFS:-}"
if [ "$rc" -ne 0 ]; then
  printf '%s' "$keys" | sort -u | sed 's/^/FINDING: /'
  [ "$unkeyed" -eq 1 ] || echo "FINDINGS: complete"
fi
[ "$exit2k" -eq 0 ] || exit 2
exit "$rc"
EOF
cat > "$TMP/replay-child.sh" <<'EOF'
#!/usr/bin/env bash
echo "$$" >"$FIXTURE_REPLAY_MARKS/child.pid"
perl -e 'sleep 60' "$FIXTURE_REPLAY_MARKS" &
echo "$!" >"$FIXTURE_REPLAY_MARKS/descendant.pid"
wait $!
EOF

# Declared object-lookup fixture: two synthetic commit names with a common
# 12-hex prefix resolve to distinct, real fixture commits. Only object queries
# used by quarantine/replay may translate those exact names; every other Git
# command and argument reaches genuine Git unchanged. This avoids searching
# for an actual SHA collision and leaves the existing real-push controls intact.
REAL_GIT="$(command -v git)"
mkdir -p "$TMP/collision-bin"
cat > "$TMP/collision-bin/git" <<'EOF'
#!/usr/bin/env bash
args=()
for arg in "$@"; do
  mapped="$arg"
  case "${1:-}" in
    cat-file | show | rev-parse)
      case "$arg" in
        "$FIXTURE_COLLIDE_A" | "$FIXTURE_COLLIDE_A:"* | "$FIXTURE_COLLIDE_A^"*)
          mapped="$FIXTURE_COLLIDE_REAL_A${arg#"$FIXTURE_COLLIDE_A"}" ;;
        "$FIXTURE_COLLIDE_B" | "$FIXTURE_COLLIDE_B:"* | "$FIXTURE_COLLIDE_B^"*)
          mapped="$FIXTURE_COLLIDE_REAL_B${arg#"$FIXTURE_COLLIDE_B"}" ;;
      esac
      ;;
  esac
  if [ "$arg" != "$mapped" ]; then
    printf '%s %s -> %s\n' "$1" "$arg" "$mapped" >>"$FIXTURE_COLLIDE_TRACE"
  fi
  args+=("$mapped")
done
exec "$FIXTURE_REAL_GIT" "${args[@]}"
EOF
chmod +x "$TMP/collision-bin/git"

T="$TMP/template"
mkdir -p "$T/scripts/hooks" "$T/tests/trust-comprehensive"
cp "$HOOK" "$T/scripts/hooks/pre-push" && chmod +x "$T/scripts/hooks/pre-push"
printf '# quarantine ledger (fixture)\n' > "$T/tests/trust-comprehensive/divergences.toml"
cat > "$T/scripts/check_gate_lane_coverage.py" <<'EOF'
import sys
if sys.argv[1:] == ["--push-refs-readers"]:
    print("fast.keyed")
EOF
cat > "$T/tests/run_trust_comprehensive_harness.sh" <<EOF
#!/usr/bin/env bash
[ "\${1:-}" = "--list" ] || exit 0
printf '%s\t%s\t%s\t%s\t%s\n' fast.keyed fixture true 2026-10-24 'bash "$TMP/lane.sh"'
printf '%s\t%s\t%s\t%s\t%s\n' fast.worktree fixture true 2026-10-24 '[ -z "\${FIXTURE_WORKTREE_RED:-}" ] || { echo "FINDING: K"; echo "FINDINGS: complete"; exit 1; }'
EOF
git -C "$T" init -q -b main
git -C "$T" config core.hooksPath scripts/hooks
git -C "$T" add -A && git -C "$T" commit -qm template

# new_case <name> <findings on the destination main, or "">: W a copy of the
# template, R a bare origin whose main carries those findings (pushed with
# --no-verify: the base is not under test).
new_case() {
  echo "-- $1"
  W="$TMP/$1"; R="$TMP/$1.git"
  cp -R "$T" "$W"
  git init -q --bare "$R"
  git -C "$W" remote add origin "$R"
  set_findings "$2" "main's red"
  git -C "$W" push -q --no-verify origin main >/dev/null 2>&1 || fail "$1: base push"
  BASE="$(git -C "$W" rev-parse HEAD)"
}
# set_findings <lines or ""> <message>: one commit setting findings.txt.
set_findings() {
  if [ -n "$1" ]; then printf '%s\n' "$1" > "$W/findings.txt"; else rm -f "$W/findings.txt"; fi
  echo "$2" >> "$W/work.txt"
  git -C "$W" add -A && git -C "$W" commit -qm "$2"
}
attempt() {  # attempt <label> <pushed|refused> <refspec...>
  local label="$1" want="$2"; shift 2
  OUT="$(git -C "$W" push origin "$@" 2>&1)"
  local rc=$?
  if [ "$want" = pushed ] && [ "$rc" -ne 0 ]; then
    fail "$label: refused (exit $rc), expected it to land"; printf '%s\n' "$OUT" | sed 's/^/        /' | tail -30; return 1
  fi
  if [ "$want" = refused ] && [ "$rc" -eq 0 ]; then
    fail "$label: LANDED, expected a refusal"; printf '%s\n' "$OUT" | sed 's/^/        /' | tail -30; return 1
  fi
  pass "$label"
}
direct() {  # direct <label> <want rc> <stdin>: the hook alone, nothing pushed
  local label="$1" want="$2"
  OUT="$(cd "$W" && printf '%s\n' "$3" | bash scripts/hooks/pre-push origin "$R" 2>&1)"
  local rc=$?
  if [ "$rc" -ne "$want" ]; then
    fail "$label: hook exit $rc, expected $want"; printf '%s\n' "$OUT" | sed 's/^/        /' | tail -30; return 1
  fi
  pass "$label"
}
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
Z=0000000000000000000000000000000000000000

echo "== the destination's red, unchanged by the push"
new_case same "MOVED a.rs pin blob1"
set_findings "MOVED a.rs pin blob1" "unrelated work"
attempt "a push carrying main's red unchanged lands" pushed main
saw "  ... graded INHERITED, naming the key" '^INHERITED: fast\.keyed'
saw "  ... the key is listed" 'MOVED a\.rs pin blob1'
saw "  ... the verdict names the inherited lane" 'INHERITED, above\): fast\.keyed'
not_saw "  ... no FAIL line" '^FAIL: fast\.keyed'
printf -v timing_dest_refs '%q' "refs/heads/main $BASE refs/heads/main $BASE"
if grep -qF -- "TIMING: phase=inherited-replay lane=fast.keyed elapsed_s=" <<<"$OUT" \
    && grep -qF -- "exit=1 clock=bash-seconds authority=none refs=$timing_dest_refs" <<<"$OUT"; then
  pass "replay timing names its actual exit and exact destination subject"
else fail "replay timing lost its exit or destination subject"; fi
saw "comparison timing is distinct from original and replay executions" \
  '^TIMING: phase=inherited-comparison lane=- elapsed_s=[0-9]+ exit=- '

echo "== a push that adds a finding"
new_case adds "MOVED a.rs pin blob1"
set_findings "MOVED a.rs pin blob1
MOVED b.rs pin blob9" "adds a second move"
attempt "a push adding a key is refused" refused main
saw "  ... naming the key the destination lacks" 'not on the destination tip .*: MOVED b\.rs pin blob9'

echo "== a push that moves main's red again"
new_case changes "MOVED a.rs pin blob1"
set_findings "MOVED a.rs pin blob2" "edits the frozen file again"
attempt "a push changing the key (the file moved again) is refused" refused main
saw "  ... naming the new key" 'not on the destination tip .*: MOVED a\.rs pin blob2'

echo "== a red only the push has"
new_case only ""
set_findings "MOVED a.rs pin blob1" "moves a frozen file"
attempt "a red on a green destination is refused" refused main
saw "  ... the destination is green on the lane" 'is GREEN on this lane'

echo "== a red with an unkeyed cause"
new_case unkeyed "MOVED a.rs pin blob1"
set_findings "MOVED a.rs pin blob1
UNKEYED" "breaks a citation"
attempt "a red whose causes are not all keyed is refused" refused main
saw "  ... a plain FAIL, never provisional" '^FAIL: fast\.keyed$'

echo "== a lane that could not judge the push (exit 2), keyed or not"
new_case exit2 "MOVED a.rs pin blob1"
set_findings "MOVED a.rs pin blob1
EXIT2KEYED" "a tree the lane judges with exit 2"
attempt "a push the lane exits 2 on is refused, even with complete keys" refused main
not_saw "  ... never inherited" '^INHERITED: fast\.keyed'

echo "== a lane that reads the working tree"
new_case worktree ""
set_findings "" "work"
export FIXTURE_WORKTREE_RED=1
attempt "a worktree reader's red is never inherited" refused main
unset FIXTURE_WORKTREE_RED
saw "  ... a plain FAIL" '^FAIL: fast\.worktree$'

echo "== a push that fixes main's red"
new_case fixes "MOVED a.rs pin blob1"
set_findings "" "writes the waiver"
attempt "a push that fixes the red lands GREEN" pushed main
saw "  ... the lane passes" '^PASS: fast\.keyed'
not_saw "  ... nothing inherited" 'INHERITED'

echo "== destinations a real push here cannot produce (the hook alone)"
new_case edges "MOVED a.rs pin blob1"
set_findings "MOVED a.rs pin blob1" "unrelated work"
HEAD_SHA="$(git -C "$W" rev-parse HEAD)"
direct "control: the same push, by hand, is green" 0 "refs/heads/main $HEAD_SHA refs/heads/main $BASE"
saw "  ... inherited" '^INHERITED: fast\.keyed'
direct "a destination tip this clone does not hold is refused" 1 \
  "refs/heads/main $HEAD_SHA refs/heads/main 1111111111111111111111111111111111111111"
saw "  ... saying so" 'not inherited: the destination tip 111111111111 of refs/heads/main is not a commit in this clone'
direct "a create (no destination tip) is refused" 1 "refs/heads/topic $HEAD_SHA refs/heads/topic $Z"
saw "  ... saying so" 'not inherited: refs/heads/topic is created by this push'
# A destination the lane cannot judge (exit 2).
git -C "$W" checkout -q -b cannot "$BASE"
set_findings "MOVED a.rs pin blob1
EXIT2" "a tree the lane cannot read"
CANNOT="$(git -C "$W" rev-parse HEAD)"
git -C "$W" checkout -q main
direct "a destination the lane cannot judge (exit 2) is refused" 1 "refs/heads/main $HEAD_SHA refs/heads/main $CANNOT"
saw "  ... saying so" 'could not judge the destination tip'
saw "a destination refusal retains exit 2 in timing" \
  '^TIMING: phase=inherited-replay lane=fast\.keyed elapsed_s=[0-9]+ exit=2 '
# Two refs: main's tip has the red, the other ref's tip does not.
git -C "$W" checkout -q -b clean-topic "$BASE"
set_findings "" "a branch without the red"
CLEAN_TIP="$(git -C "$W" rev-parse HEAD)"
git -C "$W" checkout -q main
direct "a multi-ref push where one destination lacks the key is refused" 1 \
  "refs/heads/main $HEAD_SHA refs/heads/main $BASE
refs/heads/topic $HEAD_SHA refs/heads/topic $CLEAN_TIP"
saw "  ... naming the green destination" "destination tip ${CLEAN_TIP:0:12} is GREEN"
direct "the same two refs, both destinations red with the key, are green" 0 \
  "refs/heads/main $HEAD_SHA refs/heads/main $BASE
refs/heads/topic $HEAD_SHA refs/heads/topic $BASE"

echo "== cancellation owns the destination replay and its descendants"
interrupt_replay() {  # <case> <signal> [deferred-handoff] [colliding-destinations]
  local name="$1" sig="$2" handoff="${3:-}" collision="${4:-}" deadline rc pid path alive
  local second_tip="" alias_a=cccccccccccc1111111111111111111111111111
  local alias_b=cccccccccccc2222222222222222222222222222 head_sha
  new_case "$name" "MOVED a.rs pin blob1"
  if [ -n "$collision" ]; then
    set_findings "MOVED a.rs pin blob1" "a distinct destination with the same finding"
    second_tip="$(git -C "$W" rev-parse HEAD)"
    [ "$BASE" != "$second_tip" ] && pass "$name: underlying destinations are distinct real commits" \
      || fail "$name: fixture destinations were identical"
    [ "$alias_a" != "$alias_b" ] && [ "${alias_a:0:12}" = "${alias_b:0:12}" ] \
      && pass "$name: distinct destination names share their first 12 hex digits" \
      || fail "$name: fixture destination names did not collide"
  fi
  set_findings "MOVED a.rs pin blob1" "unrelated work"
  head_sha="$(git -C "$W" rev-parse HEAD)"
  REPLAY_MARKS_DIR="$TMP/$name.marks"
  mkdir -p "$REPLAY_MARKS_DIR"
  if [ -n "$collision" ]; then
    printf 'refs/heads/main %s refs/heads/main %s\nrefs/heads/topic %s refs/heads/topic %s\n' \
      "$head_sha" "$alias_a" "$head_sha" "$alias_b" >"$REPLAY_MARKS_DIR/refs"
  else
    printf 'refs/heads/main %s refs/heads/main %s\n' "$head_sha" "$BASE" >"$REPLAY_MARKS_DIR/refs"
  fi
  if [ -n "$handoff" ]; then
    # Instrument only this fixture's copy, after the real asynchronous launch
    # and before $! ownership. The production owner and workload still run.
    perl - "$W/scripts/hooks/pre-push" <<'PERL'
use strict; use warnings;
my $path = shift;
open my $in, '<', $path or die $!; local $/; my $text = <$in>; close $in;
my $needle = '  INHERIT_REPLAY_PID=$!';
my $checkpoint = '  : > "$FIXTURE_REPLAY_MARKS/before-handle"' . "\n" .
  '  while [ ! -e "$FIXTURE_REPLAY_MARKS/release-handle" ]; do sleep 0.01; done' . "\n";
my $count = $text =~ s/\Q$needle\E/$checkpoint$needle/g;
die "expected one inherited replay handle, found $count" unless $count == 1;
open my $out, '>', $path or die $!; print {$out} $text; close $out or die $!;
PERL
  fi
  ( cd "$W" || exit 2
    export FIXTURE_REPLAY_MARKS="$REPLAY_MARKS_DIR" FIXTURE_REPLAY_CHILD="$TMP/replay-child.sh"
    if [ -n "$collision" ]; then
      export FIXTURE_REPLAY_DEST="$alias_b" FIXTURE_REAL_GIT="$REAL_GIT"
      export FIXTURE_COLLIDE_A="$alias_a" FIXTURE_COLLIDE_B="$alias_b"
      export FIXTURE_COLLIDE_REAL_A="$BASE" FIXTURE_COLLIDE_REAL_B="$second_tip"
      export FIXTURE_COLLIDE_TRACE="$REPLAY_MARKS_DIR/git-lookups"
      export PATH="$TMP/collision-bin:$PATH"
    fi
    # A background Bash inherits INT ignored; restore it before the real hook.
    exec perl -e '$SIG{INT} = $SIG{QUIT} = "DEFAULT"; exec @ARGV' \
      bash scripts/hooks/pre-push origin "$R" ) \
      <"$REPLAY_MARKS_DIR/refs" >"$TMP/$name.out" 2>&1 &
  REPLAY_HOOK_PID=$!
  deadline=$((SECONDS + 30))
  while kill -0 "$REPLAY_HOOK_PID" 2>/dev/null && [ "$SECONDS" -lt "$deadline" ]; do
    [ -s "$REPLAY_MARKS_DIR/descendant.pid" ] \
      && { [ -z "$handoff" ] || [ -e "$REPLAY_MARKS_DIR/before-handle" ]; } && break
    sleep 0.05
  done
  if [ ! -s "$REPLAY_MARKS_DIR/descendant.pid" ] \
      || { [ -n "$handoff" ] && [ ! -e "$REPLAY_MARKS_DIR/before-handle" ]; }; then
    fail "$name: actual destination replay descendants never started"
    cleanup_replay_case; return
  fi
  for path in lane child descendant; do
    read -r pid <"$REPLAY_MARKS_DIR/$path.pid"
    if kill -0 "$pid" 2>/dev/null; then pass "$name: actual $path is running"
    else fail "$name: $path marker did not name a live process"; fi
  done
  if [ -n "$collision" ]; then
    if grep -qxF "show $alias_a:findings.txt -> $BASE:findings.txt" "$REPLAY_MARKS_DIR/git-lookups"; then
      pass "$name: first replay read the real destination's findings before the second blocked"
    else fail "$name: first destination replay did not read its actual findings"; fi
    if grep -qxF "cat-file $alias_b^{commit} -> $second_tip^{commit}" "$REPLAY_MARKS_DIR/git-lookups"; then
      pass "$name: second destination resolved to its distinct real commit"
    else fail "$name: second destination was not resolved through genuine Git"; fi
  fi
  kill "-$sig" "$REPLAY_HOOK_PID"
  if [ -n "$handoff" ]; then
    sleep 0.1
    if kill -0 "$REPLAY_HOOK_PID" 2>/dev/null; then pass "$name: cancellation awaits handle ownership"
    else fail "$name: hook exited before owning its launched replay"; fi
    : >"$REPLAY_MARKS_DIR/release-handle"
  fi
  deadline=$((SECONDS + 20))
  while kill -0 "$REPLAY_HOOK_PID" 2>/dev/null && [ "$SECONDS" -lt "$deadline" ]; do sleep 0.05; done
  if kill -0 "$REPLAY_HOOK_PID" 2>/dev/null; then
    fail "$name: interrupted hook did not finish promptly"
    cleanup_replay_case; return
  fi
  wait "$REPLAY_HOOK_PID"; rc=$?
  REPLAY_HOOK_PID=""
  [ "$rc" -eq 130 ] && pass "$name: interrupted exit 130" || fail "$name: hook exited $rc"
  OUT="$(cat "$TMP/$name.out")"
  saw "$name: cancellation is disclosed" '^pre-push: interrupted — stopping the inherited replay$'
  not_saw "$name: no final or inherited verdict" '^(PRE-PUSH: (GREEN|RED)|INHERITED:)'
  deadline=$((SECONDS + 5))
  while :; do
    alive=""
    for path in lane child descendant; do
      read -r pid <"$REPLAY_MARKS_DIR/$path.pid"
      kill -0 "$pid" 2>/dev/null && alive="$alive $path"
    done
    if [ -z "$alive" ] || [ "$SECONDS" -ge "$deadline" ]; then break; fi
    sleep 0.05
  done
  if [ -z "$alive" ]; then pass "$name: no replay descendant outlived the hook"
  else fail "$name: replay descendants still running:$alive"; fi
  cleanup_replay_case
}
interrupt_replay replay-term TERM
interrupt_replay replay-int INT
interrupt_replay replay-deferred-term TERM deferred-handoff
interrupt_replay replay-colliding-term TERM "" colliding-destinations

echo
if [ "$FAILED" -eq 0 ]; then
  echo "pre-push inherited-red tests: all passed"
  exit 0
fi
echo "pre-push inherited-red tests: FAILED"
exit 1
