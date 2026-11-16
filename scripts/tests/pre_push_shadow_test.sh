#!/usr/bin/env bash
# Hermetic proof for the D13 stage-C SHADOW (scripts/pre_push_shadow.sh) and
# the hook side of it (scripts/hooks/pre-push: record each lane's graded
# outcome, launch the shadow detached, one extra output line).
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# Every case runs in a throwaway superproject with a bare `origin`, holding a
# copy of the REAL hook and the REAL shadow script, a fake harness whose
# `--list push` names three rows, and fake lanes:
#
#   fast.conversion-guide-paths  reads docs/TWO_LANGUAGE_CONVERSION_GUIDE.md,
#                                `-e`-tests every path it names (two of them
#                                outside every static cone root, so the cone
#                                must be derived from the pushed tree), and is
#                                red when the guide carries `BAD`
#   fast.help-surfaces           green; sleeps $SHADOW_TEST_SLEEP seconds, but
#                                only when it runs inside a shadow checkout,
#                                where it is red (exit 7) if TRUST_PUSHED_REFS or
#                                TRUST_PUSH_REMOTE is set at all
#   fast.other                   green; not a shadow lane
#
# Cases (each asserts on the log the hook announced):
#   agree        push of the checked-out ref -> AGREE, worktrees and lock gone,
#                cone derived from the pushed tree
#   differ       push of a non-HEAD ref whose guide is BAD -> DIFFER logged, the
#                push still lands (live verdict unchanged)
#   output       direct hook runs, GREEN and RED: output with the shadow on is
#                the kill-switch output plus exactly one line; exit codes equal
#   kill-switch  TRUST_PRE_PUSH_SHADOW=0 -> no line, no log, no input dir
#   live-red     an uncommitted BAD guide makes the live lane red: the push is
#                refused (exit 1, remote unchanged) and the shadow still logs
#                DIFFER for the clean pushed tree
#   not-run      a pushed tree without the lane's script -> NOT-RUN; deletion
#                only -> no tree judged
#   max-trees    four distinct trees in one push -> three judged, one skipped;
#                per-tree lines are TREE-*, the push level is NOT-RUN
#   multi-tree   a green and a red tree: under a live FAIL the push level is
#                AGREE with differ=0 (the reviewer's false-DIFFER reproducer);
#                under a live PASS it is a real DIFFER; the detached shadow's
#                lanes do not inherit the hook's fds above 2
#   lock         a live holder -> SKIPPED; a dead holder's lock, and a live
#                pid whose start time is not the holder's, are taken over; a
#                live holder from another time zone and locale is respected
#                (its zone-free start_utc decides), a wrong start_utc is taken
#                over, an empty one leaves a live holder alone; a fresh lock
#                with no pid yet is respected
#   timeout      a lane over TRUST_PRE_PUSH_SHADOW_TIMEOUT is killed (with its
#                child), logged as timeout and graded NOT-RUN (no verdict, so
#                never a DIFFER), worktree removed; the push itself does not
#                wait for the shadow
#   killed       SIGTERM mid-lane -> worktree, lock and lane removed; SIGKILL
#                mid-lane -> the next run prunes the stale worktree
#   lock-zones   a real run's lock, taken under TZ=Asia/Tokyo, carries its
#                zone-free start_utc, and a real run in another zone and locale
#                skips it as live and leaves it alone
#   prune        a live pid's leftovers survive another run's prune, a dead
#                pid's do not; a user's worktree.useRelativePaths=true still
#                gets an absolute (recognisable, prunable) admin entry
#   dates        a live run on another date -> the date-reading lane is
#                NOT-RUN, not a DIFFER; the same date -> AGREE
#   early-exit   a refusal before the trap exists still removes the input dir
#   git-dir      GIT_DIR/GIT_WORK_TREE with no .git in the work tree: judged
#                via --common; without it, exit 2 and the input dir removed
#   untouched    a hand run leaves the main index, refs, config and worktree
#                byte-identical
#   retention    only the newest 50 logs remain
set -uo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
HOOK="$REPO/scripts/hooks/pre-push"
SHADOW="$REPO/scripts/pre_push_shadow.sh"
for f in "$HOOK" "$SHADOW"; do
  [ -f "$f" ] || { echo "pre_push_shadow_test: missing $f" >&2; exit 2; }
done

T="$(mktemp -d -t pre-push-shadow-test.XXXXXX)" || exit 2
T="$(cd "$T" && pwd -P)"
# Every sleep a case may orphan carries a token unique to THIS run (a fraction
# for the lanes' sleeps, a timeout for the watchdog's), so the pkills below can
# never reach another concurrent run's processes.
SUF=$(( RANDOM % 9000 + 1000 ))
TO_UNIQ=$(( RANDOM % 299 + 301 ))   # a valid per-lane timeout (<= 600), never the default
cleanup() {
  # Any lane a case left sleeping (the SIGKILL case orphans one on purpose).
  pkill -f "^sleep 4[0-9]\.$SUF\$" 2>/dev/null
  pkill -f "^sleep $TO_UNIQ\$" 2>/dev/null
  rm -rf "${T:?}"
}
trap cleanup EXIT

unset TRUST_PRE_PUSH_SHADOW TRUST_PRE_PUSH_SHADOW_TIMEOUT TRUST_PUSHED_REFS TRUST_PUSH_REMOTE SHADOW_TEST_SLEEP
export GIT_CONFIG_NOSYSTEM=1
export GIT_CONFIG_GLOBAL="$T/gitconfig"
cat >"$GIT_CONFIG_GLOBAL" <<'EOF'
[user]
	name = Shadow Test
	email = shadow@test.invalid
[init]
	defaultBranch = main
[advice]
	detachedHead = false
EOF

PASS=0
FAIL=0
ok() { PASS=$((PASS + 1)); echo "  ok   $1"; }
bad() { FAIL=$((FAIL + 1)); echo "  FAIL $1"; [ -n "${2:-}" ] && sed 's/^/       | /' "$2" | tail -40; }
check() {  # check <name> <condition...>; the log to show on failure is $SHOW
  local name="$1"; shift
  if "$@"; then ok "$name"; else bad "$name" "${SHOW:-}"; fi
}

# ---- the fixture ------------------------------------------------------------
W="$T/src"
BARE="$T/origin.git"
git init -q --bare "$BARE"
git init -q "$W"
mkdir -p "$W/scripts/hooks" "$W/tests/trust-comprehensive" "$W/docs" \
  "$W/crates/foo/src" "$W/crates/foo/big" "$W/compiler/bar/deep" "$W/data"
cp "$HOOK" "$W/scripts/hooks/pre-push"
cp "$SHADOW" "$W/scripts/pre_push_shadow.sh"
chmod +x "$W/scripts/hooks/pre-push"
printf '# no quarantine rows\n' >"$W/tests/trust-comprehensive/divergences.toml"
cat >"$W/tests/run_trust_comprehensive_harness.sh" <<'EOF'
#!/bin/bash
[ "${1:-}" = "--list" ] && [ "${2:-}" = "push" ] || exit 2
printf 'fast.conversion-guide-paths\tdocs\ttrue\t-\tbash scripts/check_conversion_guide_paths.sh\n'
printf 'fast.help-surfaces\tdocs\ttrue\t-\tbash scripts/check_help_surfaces.sh\n'
printf 'fast.other\tdocs\ttrue\t-\tbash scripts/check_other.sh\n'
EOF
cat >"$W/scripts/check_conversion_guide_paths.sh" <<'EOF'
#!/bin/bash
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
GUIDE="$ROOT/docs/TWO_LANGUAGE_CONVERSION_GUIDE.md"
[ -f "$GUIDE" ] || { echo "ERROR: guide missing: $GUIDE" >&2; exit 2; }
fails=0
while read -r p; do
  [ -e "$ROOT/$p" ] || { echo "MISSING PATH: $p" >&2; fails=$((fails + 1)); }
done < <(grep -oE '(tests|docs|compiler|crates|scripts|src)/[A-Za-z0-9_./-]+\.(rs|lean|clean|md|py|sh|toml)' "$GUIDE" | sort -u)
grep -q BAD "$GUIDE" && { echo "BAD marker in the guide" >&2; fails=$((fails + 1)); }
[ "$fails" = 0 ] || { echo "check_conversion_guide_paths: $fails problem(s)" >&2; exit 1; }
echo "check_conversion_guide_paths: OK"
EOF
cat >"$W/scripts/check_help_surfaces.sh" <<'EOF'
#!/bin/bash
case "$PWD" in
  */trust-shadow/wt-*)
    # The shadow's reading is the STANDING one: no push context may reach it.
    if [ -n "${TRUST_PUSHED_REFS+set}${TRUST_PUSH_REMOTE+set}" ]; then echo "push context leaked into the shadow"; exit 7; fi
    [ -n "${SHADOW_TEST_FDLOG:-}" ] && { [ -e /dev/fd/7 ] && echo "shadow: fd7 open" || echo "shadow: fd7 closed"; } >>"$SHADOW_TEST_FDLOG"
    [ -n "${SHADOW_TEST_SLEEP:-}" ] && sleep "$SHADOW_TEST_SLEEP" ;;
  *)
    [ -n "${SHADOW_TEST_FDLOG:-}" ] && { [ -e /dev/fd/7 ] && echo "live: fd7 open" || echo "live: fd7 closed"; } >>"$SHADOW_TEST_FDLOG" ;;
esac
echo "help surfaces: ok"
EOF
printf '#!/bin/bash\necho other: ok\n' >"$W/scripts/check_other.sh"
cat >"$W/docs/TWO_LANGUAGE_CONVERSION_GUIDE.md" <<'EOF'
# Guide
Example: crates/foo/src/lib.rs and compiler/bar/deep/x.rs.
EOF
echo 'pub fn f() {}' >"$W/crates/foo/src/lib.rs"
echo 'fn x() {}' >"$W/compiler/bar/deep/x.rs"
echo 'not needed by any lane' >"$W/crates/foo/big/blob.txt"
git -C "$W" add -A
git -C "$W" commit -qm "fixture"
git -C "$W" remote add origin "$BARE"
git -C "$W" config core.hooksPath scripts/hooks
git -C "$W" push -q --no-verify origin main
SROOT="$W/.git/trust-shadow"

# ---- helpers ----------------------------------------------------------------
log_of() { sed -n 's/^pre-push: shadow re-judge.* logs to //p' "$1" | tail -1; }
# Waits for a run to finish: its summary is written and its lock and input dir
# are gone (the EXIT trap removes the worktrees before either).
wait_done() {
  local log="$1" keep_lock="${2:-0}" i=0
  while [ "$i" -lt 600 ]; do
    if grep -q '^SHADOW-SUMMARY' "$log" 2>/dev/null && [ ! -d "$log.in" ] \
      && { [ "$keep_lock" = 1 ] || [ ! -d "$SROOT/lock" ]; }; then
      return 0
    fi
    sleep 0.1
    i=$((i + 1))
  done
  echo "  (timed out waiting for $log)"
  return 1
}
no_worktrees() {
  [ "$(git -C "$W" worktree list | wc -l | tr -d ' ')" = 1 ] \
    && [ -z "$(ls -d "$SROOT"/wt-* "$SROOT"/run-* 2>/dev/null)" ] \
    && [ -z "$(ls "$W/.git/worktrees" 2>/dev/null)" ]
}
has() { grep -qE "$2" "$1"; }
lacks() { ! grep -qE "$2" "$1"; }
one_added_line() {  # a `diff old new` with one `>` line, the shadow notice, and no `<`
  [ "$(grep -c '^>' "$1")" = 1 ] && [ "$(grep -c '^<' "$1")" = 0 ] \
    && grep -q '^> pre-push: shadow re-judge of the pushed trees .* logs to ' "$1"
}
n_logs() { ls "$SROOT"/*.log 2>/dev/null | wc -l | tr -d ' '; }
commit_file() {  # commit_file <branch-or-HEAD> <path> <content> <msg>
  printf '%s\n' "$3" >"$W/$2"
  git -C "$W" add -A && git -C "$W" commit -qm "$4"
}

# ---- agree ------------------------------------------------------------------
echo "case agree: push of the checked-out ref"
commit_file HEAD notes.txt "one" "c1"
H=$(git -C "$W" rev-parse HEAD)
git -C "$W" push origin main >"$T/agree.out" 2>&1; rc=$?
LOG=$(log_of "$T/agree.out"); SHOW="$T/agree.out"
check "push exits 0" [ "$rc" -eq 0 ]
check "the hook names the shadow log" [ -n "$LOG" ]
wait_done "$LOG"; SHOW="$LOG"
check "conversion-guide AGREE (live PASS, shadow 0)" has "$LOG" "^SHADOW fast.conversion-guide-paths tree=${H:0:12} live=PASS/0 shadow=0 AGREE"
check "help-surfaces AGREE" has "$LOG" "^SHADOW fast.help-surfaces tree=${H:0:12} live=PASS/0 shadow=0 AGREE"
check "a non-shadow lane is not shadowed" lacks "$LOG" "^SHADOW fast.other "
check "the cone reaches the guide's paths" has "$LOG" "^files-of: .*compiler/bar/deep.*crates/foo/src"
check "the cone leaves unrelated dirs out" lacks "$LOG" "crates/foo/big"
check "push-level AGREE for each lane" [ "$(grep -cE "^SHADOW-PUSH fast\.[a-z.-]+ live=PASS/0 shadow=green trees=1/1 AGREE$" "$LOG")" = 2 ]
check "summary: 2 agree, 0 differ" has "$LOG" "^SHADOW-SUMMARY trees=1 skipped-trees=0 agree=2 differ=0 "
check "worktrees removed" no_worktrees
check "lock released" [ ! -d "$SROOT/lock" ]

# ---- differ -----------------------------------------------------------------
echo "case differ: a non-HEAD ref whose tree differs in the lane's input"
git -C "$W" branch bad
git -C "$W" checkout -q bad
commit_file bad docs/TWO_LANGUAGE_CONVERSION_GUIDE.md "BAD guide: crates/foo/src/lib.rs" "bad guide"
B=$(git -C "$W" rev-parse bad)
git -C "$W" checkout -q main
git -C "$W" push origin bad >"$T/differ.out" 2>&1; rc=$?
LOG=$(log_of "$T/differ.out"); SHOW="$T/differ.out"
check "push of the bad ref still lands (live judged the checkout)" [ "$rc" -eq 0 ]
check "the remote holds it" [ "$(git -C "$BARE" rev-parse refs/heads/bad 2>/dev/null)" = "$B" ]
check "the hook stayed GREEN" has "$T/differ.out" "^PRE-PUSH: GREEN"
wait_done "$LOG"; SHOW="$LOG"
check "DIFFER logged (live PASS, shadow red)" has "$LOG" "^SHADOW fast.conversion-guide-paths tree=${B:0:12} live=PASS/0 shadow=1 DIFFER"
check "the DIFFER carries the lane's own words" has "$LOG" "^  \| BAD marker in the guide"
check "push-level DIFFER (live PASS, shadow red)" has "$LOG" "^SHADOW-PUSH fast.conversion-guide-paths live=PASS/0 shadow=red trees=1/1 DIFFER$"
check "summary counts it" has "$LOG" "^SHADOW-SUMMARY .* agree=1 differ=1 .* tree-differ=1 "
check "worktrees removed" no_worktrees

# ---- output (byte-identical but one line) -----------------------------------
echo "case output: the hook's output and exit are today's plus one line"
run_hook() {  # run_hook <refs-line> <out> [env...]; prints the exit code
  local refs="$1" out="$2"; shift 2
  ( cd "$W" && printf '%s\n' "$refs" | env "$@" bash scripts/hooks/pre-push origin "$BARE" ) >"$out" 2>&1
  echo $?
}
R=$(git -C "$BARE" rev-parse refs/heads/main)
refs="refs/heads/main $H refs/heads/main $R"
rc_off=$(run_hook "$refs" "$T/g.off" TRUST_PRE_PUSH_SHADOW=0)
rc_on=$(run_hook "$refs" "$T/g.on" TRUST_PRE_PUSH_SHADOW=1)
diff "$T/g.off" "$T/g.on" >"$T/g.diff"; SHOW="$T/g.diff"
check "GREEN: same exit code ($rc_off, $rc_on)" [ "$rc_off.$rc_on" = 0.0 ]
check "GREEN: exactly one added line, the shadow notice" one_added_line "$T/g.diff"
wait_done "$(log_of "$T/g.on")"
printf 'WIP BAD\n' >>"$W/docs/TWO_LANGUAGE_CONVERSION_GUIDE.md"
rc_off=$(run_hook "$refs" "$T/r.off" TRUST_PRE_PUSH_SHADOW=0)
rc_on=$(run_hook "$refs" "$T/r.on")
git -C "$W" checkout -q -- docs/TWO_LANGUAGE_CONVERSION_GUIDE.md
diff "$T/r.off" "$T/r.on" >"$T/r.diff"; SHOW="$T/r.diff"
check "RED: same exit code ($rc_off, $rc_on)" [ "$rc_off.$rc_on" = 1.1 ]
check "RED: exactly one added line, the shadow notice" one_added_line "$T/r.diff"
wait_done "$(log_of "$T/r.on")"

# ---- kill switch ------------------------------------------------------------
echo "case kill-switch: TRUST_PRE_PUSH_SHADOW=0"
commit_file HEAD notes.txt "two" "c2"
before=$(n_logs)
TRUST_PRE_PUSH_SHADOW=0 git -C "$W" push origin main >"$T/ks.out" 2>&1; rc=$?
SHOW="$T/ks.out"
check "push exits 0" [ "$rc" -eq 0 ]
check "no shadow line" lacks "$T/ks.out" "shadow re-judge"
check "no new log" [ "$(n_logs)" = "$before" ]
check "no input dir" [ -z "$(ls -d "$SROOT"/*.in 2>/dev/null)" ]

# ---- live red ---------------------------------------------------------------
echo "case live-red: a failing live lane"
commit_file HEAD notes.txt "three" "c3"
H=$(git -C "$W" rev-parse HEAD)
R=$(git -C "$BARE" rev-parse refs/heads/main)
printf 'WIP BAD\n' >>"$W/docs/TWO_LANGUAGE_CONVERSION_GUIDE.md"
git -C "$W" push origin main >"$T/red.out" 2>&1; rc=$?
git -C "$W" checkout -q -- docs/TWO_LANGUAGE_CONVERSION_GUIDE.md
LOG=$(log_of "$T/red.out"); SHOW="$T/red.out"
check "push refused" [ "$rc" -ne 0 ]
check "the hook said RED" has "$T/red.out" "^PRE-PUSH: RED"
check "remote unchanged" [ "$(git -C "$BARE" rev-parse refs/heads/main)" = "$R" ]
check "the shadow was still launched" [ -n "$LOG" ]
wait_done "$LOG"; SHOW="$LOG"
check "DIFFER logged (live FAIL/1, pushed tree green)" has "$LOG" "^SHADOW fast.conversion-guide-paths tree=${H:0:12} live=FAIL/1 shadow=0 DIFFER"
check "push-level DIFFER (the refusal was the WIP's, not the push's)" has "$LOG" "^SHADOW-PUSH fast.conversion-guide-paths live=FAIL/1 shadow=green trees=1/1 DIFFER$"
git -C "$W" push -q --no-verify origin main

# ---- not run ----------------------------------------------------------------
echo "case not-run: the lane's script is absent from the pushed tree; deletion only"
git -C "$W" checkout -q -b noscript
git -C "$W" rm -q scripts/check_help_surfaces.sh
git -C "$W" commit -qm "drop a lane script"
N=$(git -C "$W" rev-parse HEAD)
git -C "$W" checkout -q main
git -C "$W" push origin noscript >"$T/nr.out" 2>&1
LOG=$(log_of "$T/nr.out"); wait_done "$LOG"; SHOW="$LOG"
check "NOT-RUN for the absent script" has "$LOG" "^SHADOW fast.help-surfaces tree=${N:0:12} live=PASS/0 shadow=- NOT-RUN \(scripts/check_help_surfaces.sh is absent"
check "the other lane still ran" has "$LOG" "^SHADOW fast.conversion-guide-paths tree=${N:0:12} .* AGREE"
git -C "$W" push origin :noscript >"$T/del.out" 2>&1
LOG=$(log_of "$T/del.out"); wait_done "$LOG"; SHOW="$LOG"
check "deletion only: no tree judged" has "$LOG" "^tree: +no non-deletion pushed tree"
check "deletion only: summary trees=0" has "$LOG" "^SHADOW-SUMMARY trees=0 "

# ---- max trees --------------------------------------------------------------
echo "case max-trees: four distinct trees in one push"
for i in 1 2 3 4; do
  git -C "$W" checkout -q -b "t$i" main
  commit_file "t$i" "notes-$i.txt" "$i" "t$i"
done
git -C "$W" checkout -q main
git -C "$W" push origin t1 t2 t3 t4 >"$T/mt.out" 2>&1
LOG=$(log_of "$T/mt.out"); wait_done "$LOG"; SHOW="$LOG"
check "three trees judged, one skipped" has "$LOG" "^SHADOW-SUMMARY trees=3 skipped-trees=1 "
check "the skip is logged" has "$LOG" "SKIPPED — only the first 3 distinct trees"
check "six judged lane lines, labelled per tree" [ "$(grep -cE "^SHADOW fast\.[a-z.-]+ tree=.* TREE-AGREE " "$LOG")" = 6 ]
check "no per-tree line claims a push verdict" lacks "$LOG" "^SHADOW fast\.[a-z.-]+ tree=.* (AGREE|DIFFER) "
check "an unjudged tree leaves the push-level verdict unknown" [ "$(grep -cE "^SHADOW-PUSH fast\.[a-z.-]+ live=PASS/0 shadow=- trees=3/4 NOT-RUN .*over the cap of 3" "$LOG")" = 2 ]
check "summary: nothing counted as agree or differ" has "$LOG" "^SHADOW-SUMMARY .* agree=0 differ=0 not-run=2 "
check "worktrees removed" no_worktrees

# ---- multi-tree: the verdict is the push's, not each tree's -------------------
echo "case multi-tree: one green and one red tree, graded at push level"
git -C "$W" checkout -q -b topicbad main
commit_file topicbad docs/TWO_LANGUAGE_CONVERSION_GUIDE.md "BAD topic guide: crates/foo/src/lib.rs" "topic bad guide"
TB=$(git -C "$W" rev-parse topicbad)
git -C "$W" checkout -q main
commit_file HEAD notes.txt "multi" "c-multi"
M=$(git -C "$W" rev-parse main)
R=$(git -C "$BARE" rev-parse refs/heads/main)
# (a) the reviewer's reproducer: a WIP-red checkout refuses the push live; the
# enforcing stage C would refuse it too (topicbad is red), so this is an AGREE
# at push level although main's own tree is green.
printf 'WIP BAD\n' >>"$W/docs/TWO_LANGUAGE_CONVERSION_GUIDE.md"
git -C "$W" push origin main topicbad >"$T/mr.out" 2>&1; rc=$?
git -C "$W" checkout -q -- docs/TWO_LANGUAGE_CONVERSION_GUIDE.md
LOG=$(log_of "$T/mr.out"); SHOW="$T/mr.out"
check "live refuses the push (WIP red)" [ "$rc" -ne 0 ]
check "remote unchanged" [ "$(git -C "$BARE" rev-parse refs/heads/main)" = "$R" ]
wait_done "$LOG"; SHOW="$LOG"
check "main's own line: TREE-DIFFER (diagnosis only)" has "$LOG" "^SHADOW fast.conversion-guide-paths tree=${M:0:12} live=FAIL/1 shadow=0 TREE-DIFFER "
check "topicbad's own line: TREE-AGREE" has "$LOG" "^SHADOW fast.conversion-guide-paths tree=${TB:0:12} live=FAIL/1 shadow=1 TREE-AGREE "
check "push level: red over the trees, AGREE with the live refusal" has "$LOG" "^SHADOW-PUSH fast.conversion-guide-paths live=FAIL/1 shadow=red trees=2/2 AGREE$"
check "summary: differ=0 (the tree mismatch is not push evidence)" has "$LOG" "^SHADOW-SUMMARY trees=2 skipped-trees=0 agree=2 differ=0 .* tree-differ=1 "
# (b) the same two trees from a clean checkout: live passes the push, the
# enforcing stage would refuse it (topicbad is red) — a real DIFFER. The
# shadow must not hold the hook's inherited descriptors (fd 7 here stands in
# for git's pipes to receive-pack): the live lane sees it, the shadow's not.
: >"$T/fd.log"
( exec 7>"$T/fd7.marker"; SHADOW_TEST_FDLOG="$T/fd.log" git -C "$W" push origin main topicbad ) >"$T/mg.out" 2>&1; rc=$?
LOG=$(log_of "$T/mg.out"); SHOW="$T/mg.out"
check "live passes the push" [ "$rc" -eq 0 ]
wait_done "$LOG"; SHOW="$LOG"
check "push level: DIFFER (live PASS, a pushed tree red)" has "$LOG" "^SHADOW-PUSH fast.conversion-guide-paths live=PASS/0 shadow=red trees=2/2 DIFFER$"
check "summary: differ=1, agree=1" has "$LOG" "^SHADOW-SUMMARY trees=2 skipped-trees=0 agree=1 differ=1 "
SHOW="$T/fd.log"
check "fd probe: the live lane inherited fd 7 (control)" has "$T/fd.log" "^live: fd7 open$"
check "fd probe: no shadow lane holds fd 7" [ "$(grep -c '^shadow: fd7 closed$' "$T/fd.log")" = 2 ]
check "fd probe: and none saw it open" lacks "$T/fd.log" "^shadow: fd7 open"

# ---- lock -------------------------------------------------------------------
echo "case lock: held by a live run, then by a dead one"
mkdir -p "$SROOT/lock"; echo "$$" >"$SROOT/lock/pid"
commit_file HEAD notes.txt "four" "c4"
git -C "$W" push origin main >"$T/lk.out" 2>&1
LOG=$(log_of "$T/lk.out"); wait_done "$LOG" 1; SHOW="$LOG"
check "skipped with a log line" has "$LOG" "^SHADOW-SKIPPED another shadow run holds .*\(pid $$\)"
check "nothing judged" lacks "$LOG" "^SHADOW fast\."
check "the holder's lock is left alone" [ "$(cat "$SROOT/lock/pid")" = "$$" ]
check "no worktree" no_worktrees
echo 999999 >"$SROOT/lock/pid"
commit_file HEAD notes.txt "five" "c5"
git -C "$W" push origin main >"$T/lk2.out" 2>&1
LOG=$(log_of "$T/lk2.out"); wait_done "$LOG"; SHOW="$LOG"
check "a dead holder's lock is taken over" has "$LOG" "^lock: +removing a stale lock \(pid 999999"
check "and the run judged" has "$LOG" "^SHADOW fast.conversion-guide-paths .* AGREE"
# A live pid whose start time is not the holder's: the pid number was reused.
mkdir -p "$SROOT/lock"; echo "$$ Thu Jan  1 00:00:00 1970" >"$SROOT/lock/pid"
commit_file HEAD notes.txt "five-b" "c5b"
git -C "$W" push origin main >"$T/lk3.out" 2>&1
LOG=$(log_of "$T/lk3.out"); wait_done "$LOG"; SHOW="$LOG"
check "a reused pid's lock is taken over" has "$LOG" "^lock: +removing a stale lock \(pid $$"
check "and the run judged" has "$LOG" "^SHADOW-PUSH fast.conversion-guide-paths .* AGREE$"
# EW18-LOCKUTC-1: `ps -o lstart=` follows the caller's TZ and locale. A live
# holder that took the lock in Tokyo, read by a push in Los Angeles (and in
# French, where this machine has that locale), is still the same process: its
# `start_utc` says so, and the zoned text on its `pid` line does not decide.
lstart_in() { env "$@" ps -o lstart= -p $$ | sed 's/^ *//; s/ *$//'; }
lstart_of() { local p="$1"; shift; env "$@" ps -o lstart= -p "$p" | sed 's/^ *//; s/ *$//'; }
TOKYO_START="$(lstart_in TZ=Asia/Tokyo)"
READER_ENV=(TZ=America/Los_Angeles)
# Not `grep -q`: it exits at the first match, `locale -a` dies of SIGPIPE, and under
# `pipefail` the French reader silently never ran (EW18-LOCKUTC-1, final review).
locale -a 2>/dev/null | grep -x 'fr_FR.UTF-8' >/dev/null && READER_ENV+=(LC_ALL=fr_FR.UTF-8)
check "the zoned starts differ (the next case's premise)" \
  [ "$TOKYO_START" != "$(lstart_in "${READER_ENV[@]}")" ]
mkdir -p "$SROOT/lock"; lstart_in LC_ALL=C TZ=UTC0 >"$SROOT/lock/start_utc"
echo "$$ $TOKYO_START" >"$SROOT/lock/pid"
commit_file HEAD notes.txt "five-d" "c5d"
env "${READER_ENV[@]}" git -C "$W" push origin main >"$T/lk5.out" 2>&1
LOG=$(log_of "$T/lk5.out"); wait_done "$LOG" 1; SHOW="$LOG"
check "a live holder from another time zone is respected (SKIPPED)" has "$LOG" "^SHADOW-SKIPPED another shadow run holds .*\(pid $$\)"
check "and its lock is left alone" [ "$(cat "$SROOT/lock/pid")" = "$$ $TOKYO_START" ]
# Present, `start_utc` alone decides: a wrong one is a reused pid even though
# the `pid` line's start matches.
echo 'Thu Jan  1 00:00:00 1970' >"$SROOT/lock/start_utc"
echo "$$ $(lstart_in)" >"$SROOT/lock/pid"
commit_file HEAD notes.txt "five-e" "c5e"
git -C "$W" push origin main >"$T/lk6.out" 2>&1
LOG=$(log_of "$T/lk6.out"); wait_done "$LOG"; SHOW="$LOG"
check "a wrong start_utc is a reused pid's lock, taken over" has "$LOG" "^lock: +removing a stale lock \(pid $$"
# Present but empty, `start_utc` cannot judge: pid liveness decides, as an empty
# start on the `pid` line does, and the zoned start (wrong here) is not consulted.
mkdir -p "$SROOT/lock"; : >"$SROOT/lock/start_utc"
echo "$$ Thu Jan  1 00:00:00 1970" >"$SROOT/lock/pid"
commit_file HEAD notes.txt "five-f" "c5f"
git -C "$W" push origin main >"$T/lk7.out" 2>&1
LOG=$(log_of "$T/lk7.out"); wait_done "$LOG" 1; SHOW="$LOG"
check "an empty start_utc leaves a live holder alone (SKIPPED)" has "$LOG" "^SHADOW-SKIPPED "
check "and in place" [ -d "$SROOT/lock" ]
rm -rf "${SROOT:?}/lock"
# A fresh lock with no pid yet: a holder between its mkdir and its pid write.
mkdir -p "$SROOT/lock"; : >"$SROOT/lock/pid"
commit_file HEAD notes.txt "five-c" "c5c"
git -C "$W" push origin main >"$T/lk4.out" 2>&1
LOG=$(log_of "$T/lk4.out"); wait_done "$LOG" 1; SHOW="$LOG"
check "a fresh empty lock is respected (SKIPPED)" has "$LOG" "^SHADOW-SKIPPED "
check "and left in place" [ -d "$SROOT/lock" ]
rm -rf "${SROOT:?}/lock"

# ---- timeout ----------------------------------------------------------------
echo "case timeout: a lane over the per-lane budget; the push does not wait"
commit_file HEAD notes.txt "six" "c6"
t0=$(date +%s)
SHADOW_TEST_SLEEP=40.$SUF TRUST_PRE_PUSH_SHADOW_TIMEOUT=2 git -C "$W" push origin main >"$T/to.out" 2>&1; rc=$?
took=$(( $(date +%s) - t0 ))
LOG=$(log_of "$T/to.out"); SHOW="$T/to.out"
check "push exits 0" [ "$rc" -eq 0 ]
check "the push did not wait for the shadow (${took}s)" [ "$took" -lt 15 ]
wait_done "$LOG"; SHOW="$LOG"
check "timeout logged" has "$LOG" "^SHADOW fast.help-surfaces tree=.* shadow=timeout/"
check "a timeout is NOT-RUN, never a DIFFER" has "$LOG" "^SHADOW fast.help-surfaces tree=.* shadow=timeout/[0-9]+ NOT-RUN .*timed out after 2s"
check "no DIFFER counted" has "$LOG" "^SHADOW-SUMMARY .* differ=0 "
check "the timeout is counted" has "$LOG" "^SHADOW-SUMMARY .* timeout=1 "
check "the lane after it still ran" has "$LOG" "^SHADOW fast.conversion-guide-paths .* AGREE"
check "worktrees removed" no_worktrees
check "the lane's child was killed" [ -z "$(pgrep -f "^sleep 40\.$SUF\$")" ]

echo "case no-wait: a shadow lane that would run for a minute does not hold the push"
commit_file HEAD notes.txt "six-b" "c6b"
t0=$(date +%s)
SHADOW_TEST_SLEEP=43.$SUF TRUST_PRE_PUSH_SHADOW_TIMEOUT=$TO_UNIQ git -C "$W" push origin main >"$T/nw.out" 2>&1; rc=$?
took=$(( $(date +%s) - t0 ))
LOG=$(log_of "$T/nw.out"); SHOW="$T/nw.out"
check "push exits 0" [ "$rc" -eq 0 ]
check "the push returned while the shadow runs (${took}s)" [ "$took" -lt 20 ]
i=0; while [ "$i" -lt 300 ] && ! pgrep -f "^sleep 43\.$SUF\$" >/dev/null; do sleep 0.1; i=$((i + 1)); done
check "the shadow is still running after the push returned" [ -n "$(pgrep -f "^sleep 43\.$SUF\$")" ]
kill -TERM "$(cut -d' ' -f1 "$SROOT/lock/pid" 2>/dev/null)" 2>/dev/null
wait_done "$LOG"; SHOW="$LOG"
check "stopped by SIGTERM, cleanly" has "$LOG" "^SHADOW-ABORTED"
check "worktrees removed" no_worktrees

# ---- killed -----------------------------------------------------------------
echo "case killed: SIGTERM and SIGKILL mid-lane"
hand_run() {  # hand_run <log> <lane-sleep>; the shadow in the background on HEAD
  printf 'refs/heads/main %s refs/heads/main %s\n' "$(git -C "$W" rev-parse HEAD)" \
    "$(git -C "$W" rev-parse HEAD~1)" >"$T/hand.refs"
  # exec: $SPID is the shadow itself. A unique timeout, so the SIGKILL case can
  # reap the watchdog's sleep it orphans.
  ( cd "$W" && SHADOW_TEST_SLEEP="$2" TRUST_PRE_PUSH_SHADOW_TIMEOUT=$TO_UNIQ \
      exec bash scripts/pre_push_shadow.sh --log "$1" <"$T/hand.refs" ) &
  SPID=$!
  local i=0
  while [ "$i" -lt 300 ] && ! pgrep -f "^sleep $2\$" >/dev/null; do sleep 0.1; i=$((i + 1)); done
}
hand_run "$T/term.log" 41.$SUF
check "a worktree exists mid-lane" [ -n "$(ls -d "$SROOT"/wt-* 2>/dev/null)" ]
kill -TERM "$SPID"; wait "$SPID" 2>/dev/null
SHOW="$T/term.log"
check "SIGTERM: aborted and logged" has "$T/term.log" "^SHADOW-ABORTED"
check "SIGTERM: worktrees removed" no_worktrees
check "SIGTERM: lock released" [ ! -d "$SROOT/lock" ]
i=0; while [ "$i" -lt 50 ] && pgrep -f "^sleep 41\.$SUF\$" >/dev/null; do sleep 0.1; i=$((i + 1)); done
check "SIGTERM: the lane was killed" [ -z "$(pgrep -f "^sleep 41\.$SUF\$")" ]
hand_run "$T/kill.log" 42.$SUF
kill -KILL "$SPID"; wait "$SPID" 2>/dev/null
pkill -f "^sleep 42\.$SUF\$"
pkill -f "^sleep $TO_UNIQ\$"
check "SIGKILL: the worktree is left behind" [ -n "$(ls -d "$SROOT"/wt-* 2>/dev/null)" ]
( cd "$W" && printf 'refs/heads/main %s refs/heads/main %s\n' "$(git rev-parse HEAD)" "$(git rev-parse HEAD~1)" \
    | bash scripts/pre_push_shadow.sh --log "$T/after.log" )
SHOW="$T/after.log"
check "the next run prunes it" has "$T/after.log" "^prune: +removing a stale shadow worktree"
check "the next run takes the dead run's lock" has "$T/after.log" "^lock: +removing a stale lock"
check "and judges normally (no live file: NO-LIVE)" has "$T/after.log" "^SHADOW fast.conversion-guide-paths .* shadow=0 NO-LIVE"
check "worktrees removed" no_worktrees

# ---- lock-zones: a real run's lock, read by a real run in another zone ----------
# EW18-LOCKUTC-1, review follow-up. The lock cases above write `start_utc` by hand,
# so they prove the reader only: deleting the line of take_lock that writes it left
# every check green, and every real lock would then fall back to the zoned start.
# Here a real run takes the lock under TZ=Asia/Tokyo and stays in its lane; a second
# real run under the lock case's READER_ENV (Los Angeles, and French where this
# machine has that locale) must find a live holder, skip, and leave its lock alone.
echo "case lock-zones: a real run's lock, taken in Tokyo, read in Los Angeles"
# A prefix assignment to a function call is exported to the function's children.
TZ=Asia/Tokyo hand_run "$T/zone-holder.log" 45.$SUF
ZH="$(cat "$SROOT/lock/pid" 2>/dev/null)"
SHOW="$T/zone-holder.log"
check "the Tokyo run holds the lock" [ "${ZH%% *}" = "$SPID" ]
check "and wrote its zone-free start_utc" \
  [ "$(cat "$SROOT/lock/start_utc" 2>/dev/null)" = "$(lstart_of "$SPID" LC_ALL=C TZ=UTC0)" ]
check "its zoned start is not what the reader's ps prints (the premise)" \
  [ "${ZH#* }" != "$(lstart_of "$SPID" "${READER_ENV[@]}")" ]
( cd "$W" && printf 'refs/heads/main %s refs/heads/main %s\n' "$(git rev-parse HEAD)" "$(git rev-parse HEAD~1)" \
    | env "${READER_ENV[@]}" bash scripts/pre_push_shadow.sh --log "$T/zone-reader.log" )
SHOW="$T/zone-reader.log"
check "the run in Los Angeles skips: its holder is live" has "$T/zone-reader.log" "^SHADOW-SKIPPED another shadow run holds .*\(pid $SPID\)"
check "and leaves the holder's lock alone" [ "$(cat "$SROOT/lock/pid" 2>/dev/null)" = "$ZH" ]
kill -TERM "$SPID"; wait "$SPID" 2>/dev/null
SHOW="$T/zone-holder.log"
check "the Tokyo run then stops and releases its lock" [ ! -d "$SROOT/lock" ]
i=0; while [ "$i" -lt 50 ] && pgrep -f "^sleep 45\.$SUF\$" >/dev/null; do sleep 0.1; i=$((i + 1)); done
check "and its lane was killed" [ -z "$(pgrep -f "^sleep 45\.$SUF\$")" ]
check "worktrees removed" no_worktrees

# ---- prune: pid-aware, and indifferent to worktree.useRelativePaths --------------
echo "case prune: only dead runs' leftovers; absolute admin paths under any config"
mkdir -p "$SROOT/wt-$$-9" "$SROOT/run-$$" "$SROOT/wt-999999-1" "$SROOT/run-999999"
( cd "$W" && printf 'refs/heads/main %s refs/heads/main %s\n' "$(git rev-parse HEAD)" "$(git rev-parse HEAD~1)" \
    | bash scripts/pre_push_shadow.sh --log "$T/prune.log" )
SHOW="$T/prune.log"
check "a live pid's worktree dir is left alone" [ -d "$SROOT/wt-$$-9" ]
check "a live pid's run dir is left alone" [ -d "$SROOT/run-$$" ]
check "a dead pid's worktree dir is removed" [ ! -e "$SROOT/wt-999999-1" ]
check "a dead pid's run dir is removed" [ ! -e "$SROOT/run-999999" ]
rm -rf "${SROOT:?}/wt-$$-9" "${SROOT:?}/run-$$"
git -C "$W" config worktree.useRelativePaths true
hand_run "$T/rel.log" 44.$SUF
gd_file="$(ls "$W"/.git/worktrees/*/gitdir 2>/dev/null | head -1)"
check "the admin entry is absolute under useRelativePaths=true" [ "$(cut -c1 "$gd_file" 2>/dev/null)" = / ]
kill -KILL "$SPID"; wait "$SPID" 2>/dev/null
pkill -f "^sleep 44\.$SUF\$"
pkill -f "^sleep $TO_UNIQ\$"
( cd "$W" && printf 'refs/heads/main %s refs/heads/main %s\n' "$(git rev-parse HEAD)" "$(git rev-parse HEAD~1)" \
    | bash scripts/pre_push_shadow.sh --log "$T/rel-after.log" )
SHOW="$T/rel-after.log"
check "and a SIGKILLed run's entry is still pruned" has "$T/rel-after.log" "^prune: +removing a stale shadow worktree"
check "worktrees removed" no_worktrees
git -C "$W" config --unset worktree.useRelativePaths

# ---- dates ------------------------------------------------------------------
echo "case dates: a live run on another date is no evidence for a date-reading lane"
live_file() {  # live_file <out> <utc-date> <local-date>
  {
    printf '# live-dates start %s %s\n' "$2" "$3"
    printf 'fast.conversion-guide-paths\tPASS\t0\tbash scripts/check_conversion_guide_paths.sh\n'
    printf 'fast.help-surfaces\tPASS\t0\tbash scripts/check_help_surfaces.sh\n'
    printf '# live-dates end %s %s\n' "$2" "$3"
  } >"$1"
}
hand_refs() { printf 'refs/heads/main %s refs/heads/main %s\n' "$(git -C "$W" rev-parse HEAD)" "$(git -C "$W" rev-parse HEAD~1)"; }
live_file "$T/live-old.tsv" 2000-01-01 2000-01-01
hand_refs | ( cd "$W" && bash scripts/pre_push_shadow.sh --log "$T/dates.log" --live "$T/live-old.tsv" )
SHOW="$T/dates.log"
check "help-surfaces (local calendar): NOT-RUN, dates straddled" has "$T/dates.log" "^SHADOW fast.help-surfaces tree=.* shadow=0 NOT-RUN .*dates straddled: live local 2000-01-01"
check "and NOT-RUN at push level" has "$T/dates.log" "^SHADOW-PUSH fast.help-surfaces live=PASS/0 shadow=- trees=0/1 NOT-RUN"
check "a lane with no calendar still AGREEs" has "$T/dates.log" "^SHADOW-PUSH fast.conversion-guide-paths live=PASS/0 shadow=green trees=1/1 AGREE$"
live_file "$T/live-now.tsv" "$(date -u +%F)" "$(date +%F)"
hand_refs | ( cd "$W" && bash scripts/pre_push_shadow.sh --log "$T/dates2.log" --live "$T/live-now.tsv" )
SHOW="$T/dates2.log"
check "the same dates: help-surfaces AGREEs" has "$T/dates2.log" "^SHADOW-PUSH fast.help-surfaces live=PASS/0 shadow=green trees=1/1 AGREE$"

# ---- early exit and a separate git dir -------------------------------------
echo "case early-exit: an early refusal still removes the hook's input dir"
mkdir -p "$T/indir"
( cd "$T" && bash "$W/scripts/pre_push_shadow.sh" --common "$T/no-such-dir" --in-dir "$T/indir" \
    --log "$T/early.log" </dev/null ) 2>"$T/early.err"; rc=$?
SHOW="$T/early.err"
check "exit 2" [ "$rc" -eq 2 ]
check "the input dir is removed" [ ! -e "$T/indir" ]
echo "case git-dir: GIT_DIR/GIT_WORK_TREE with no .git in the work tree"
# The hook itself refuses such a push today (its quarantine read), so this runs
# the shadow as the hook launches it: from the work tree, git's variables set,
# --common naming the common dir.
mkdir -p "$T/wtcopy" "$T/indir2"
( cd "$W" && git ls-files -z | xargs -0 tar cf - ) | tar xf - -C "$T/wtcopy"
hand_refs | ( cd "$T/wtcopy" && GIT_DIR="$W/.git" GIT_WORK_TREE="$T/wtcopy" \
    bash scripts/pre_push_shadow.sh --common "$W/.git" --in-dir "$T/indir2" \
    --log "$T/gd.log" --live "$T/live-now.tsv" ); rc=$?
SHOW="$T/gd.log"
check "exit 0" [ "$rc" -eq 0 ]
check "it judged the pushed tree" has "$T/gd.log" "^SHADOW-PUSH fast.conversion-guide-paths live=PASS/0 shadow=green trees=1/1 AGREE$"
check "its input dir is removed" [ ! -e "$T/indir2" ]
check "worktrees removed" no_worktrees
mkdir -p "$T/indir3"
hand_refs | ( cd "$T/wtcopy" && GIT_DIR="$W/.git" GIT_WORK_TREE="$T/wtcopy" \
    bash scripts/pre_push_shadow.sh --in-dir "$T/indir3" --log "$T/gd2.log" ) 2>/dev/null; rc=$?
check "without --common: exit 2, and the input dir is still removed" [ "$rc.$([ -e "$T/indir3" ] && echo left || echo gone)" = 2.gone ]
rm -rf "${T:?}/wtcopy"

# ---- untouched --------------------------------------------------------------
echo "case untouched: a hand run leaves the main checkout's state alone"
printf 'WIP\n' >>"$W/notes.txt"
# `git status` may rewrite the index while refreshing stat data, so settle it
# first and read the state afterwards only with commands that never write it.
git -C "$W" status >/dev/null; sleep 1; git -C "$W" status >/dev/null
snap() {
  ( cd "$W" && shasum .git/index && cat .git/config && git for-each-ref && git ls-files -s \
      && git diff --name-status && git diff --cached --name-status && git stash list \
      && cat notes.txt && ls -a .git/info )
}
snap >"$T/snap.before"
( cd "$W" && printf 'refs/heads/main %s refs/heads/main %s\n' "$(git rev-parse HEAD)" "$(git rev-parse HEAD~1)" \
    | bash scripts/pre_push_shadow.sh --log "$T/hand.log" )
snap >"$T/snap.after"
diff "$T/snap.before" "$T/snap.after" >"$T/snap.diff"; SHOW="$T/snap.diff"
check "config, refs, index, status and WIP byte-identical" [ ! -s "$T/snap.diff" ]
git -C "$W" checkout -q -- notes.txt

# ---- retention --------------------------------------------------------------
echo "case retention: the newest 50 logs"
for i in $(seq 1 55); do
  f="$SROOT/20200101T0000$(printf '%02d' "$i")Z-000000000000.log"
  echo "old" >"$f"; touch -t "202001010000.$(printf '%02d' "$i")" "$f"
done
commit_file HEAD notes.txt "seven" "c7"
git -C "$W" push origin main >"$T/rt.out" 2>&1
LOG=$(log_of "$T/rt.out"); wait_done "$LOG"; SHOW="$LOG"
check "50 logs remain" [ "$(n_logs)" = 50 ]
check "the new log is among them" [ -f "$LOG" ]
check "the oldest went first" [ ! -e "$SROOT/20200101T000001Z-000000000000.log" ]

echo
echo "pre_push_shadow_test: $PASS passed, $FAIL failed"
[ "$FAIL" -eq 0 ]
