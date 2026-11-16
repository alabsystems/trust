#!/usr/bin/env bash
# The mutation proof for `scripts/check_revert_rationale.sh`.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# Every case below is executed against a real throwaway repository with real
# `git revert` output, because the thing being asserted is a property of git's
# generated message, not of a string this test invents. A gate that cannot be
# shown to FAIL is not a gate, so the negative controls come first and the
# accept controls sit beside each of them.
set -euo pipefail

REPO_ROOT=$(cd -P "${BASH_SOURCE[0]%/*}/../.." && pwd -P)
CHECKER="$REPO_ROOT/scripts/check_revert_rationale.sh"
# The destination reader the checker sources for a push with a destination; a
# copy of the checker finds it beside itself, so every copy below carries it.
DESTINATION_LIB="$REPO_ROOT/scripts/lib/push_destination.sh"
LEDGER="$REPO_ROOT/scripts/revert-rationale-grandfathered.txt"
LEDGER_REL="scripts/revert-rationale-grandfathered.txt"
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

# PUSH CONTEXT is this lane's, not the fixtures'. scripts/hooks/pre-push exports
# TRUST_PUSHED_REFS (and TRUST_PUSH_REMOTE) to every row; the fixture arms below
# drive the checker on throwaway repositories and must not inherit a real
# push's refs (with them set, the checker reads its waivers the anchored way).
# Captured here for S1, then removed from the environment; every arm that wants
# push context sets it on its own command line.
LANE_PUSH_READING=0
[ -z "${TRUST_PUSHED_REFS+x}" ] || LANE_PUSH_READING=1
LANE_PUSHED_REFS="${TRUST_PUSHED_REFS-}"
LANE_PUSH_REMOTE="${TRUST_PUSH_REMOTE-}"
unset TRUST_PUSHED_REFS TRUST_PUSH_REMOTE

PASSED=0
fail() { printf 'check_revert_rationale_test: %s\n' "$*" >&2; exit 1; }
ok()   { PASSED=$((PASSED + 1)); printf '  ok  %s\n' "$*"; }

[ -x "$CHECKER" ] || fail "checker is missing or not executable: $CHECKER"

R="$TMP/repo"
git init -q "$R"
git -C "$R" config user.name test
git -C "$R" config user.email test@example.invalid
git -C "$R" config commit.gpgsign false
mkdir -p "$R/scripts/lib" "$R/crates/trust-thir-lower/src"
cp "$CHECKER" "$R/scripts/check_revert_rationale.sh"
cp "$DESTINATION_LIB" "$R/scripts/lib/push_destination.sh"
cp "$REPO_ROOT/scripts/lib/remote_tips.py" "$REPO_ROOT/scripts/lib/landing_targo.py" "$REPO_ROOT/scripts/lib/remote_operation.py" "$R/scripts/lib/"
chmod +x "$R/scripts/check_revert_rationale.sh"
printf 'fn main() {}\n' >"$R/crates/trust-thir-lower/src/lib.rs"
git -C "$R" add -A
git -C "$R" commit -qm 'fixture: the checker and a soundness-gate path'
BASE=$(git -C "$R" rev-parse HEAD)

# The subject commit stands in for wave-SG: it touches a soundness-gate path.
printf 'fn main() { gate(); }\n' >"$R/crates/trust-thir-lower/src/lib.rs"
git -C "$R" commit -qam 'feat(thir-lower): the STRUCT-INTERIOR offset class is GATED'
SUBJECT=$(git -C "$R" rev-parse HEAD)

run() { ( cd "$R" && bash scripts/check_revert_rationale.sh "$@" 2>&1 ); }

# --------------------------------------------------------------- NEGATIVE: bare
# Exactly the shape of 31814afa35: `git revert --no-edit`, nothing added.
git -C "$R" revert --no-edit "$SUBJECT"
BARE=$(git -C "$R" rev-parse HEAD)
body=$(git -C "$R" log -1 --format=%b "$BARE")
case "$body" in
  *"This reverts commit ${SUBJECT}."*) ;;
  *) fail "git did not produce the generated revert line this test is about" ;;
esac
if out=$(run "${SUBJECT}..${BARE}"); then
  printf '%s\n' "$out" >&2
  fail 'M1: a BARE revert passed the gate'
fi
case "$out" in
  *"a revert that does not say WHY"*) ;;
  *) fail 'M1: the refusal did not name the defect' ;;
esac
case "$out" in
  *"$BARE"*) ;;
  *) fail 'M1: the refusal did not name the offending sha' ;;
esac
case "$out" in
  *'SOUNDNESS-GATE paths'*'crates/trust-thir-lower/src/lib.rs'*) ;;
  *) fail 'M1: the refusal did not report the reverted soundness-gate path' ;;
esac
ok 'M1  a bare `git revert --no-edit` is REFUSED, by sha, with the gate path named'

# ------------------------------------------------------ NEGATIVE: trailer only
# A `Co-Authored-By:` line is attribution. Without trailer stripping every
# agent-authored bare revert would walk straight through this gate.
git -C "$R" commit -q --amend -m "$(git -C "$R" log -1 --format=%s "$BARE")
This reverts commit ${SUBJECT}.

Co-Authored-By: Claude Opus 5 <noreply@anthropic.com>
Signed-off-by: A Machine <machine@example.invalid>"
TRAILER=$(git -C "$R" rev-parse HEAD)
if out=$(run "${SUBJECT}..${TRAILER}"); then
  printf '%s\n' "$out" >&2
  fail 'M2: a revert whose only body was trailers passed the gate'
fi
ok 'M2  trailers alone are NOT a reason'

# ------------------------------------------------------- NEGATIVE: token reason
git -C "$R" commit -q --amend -m "$(git -C "$R" log -1 --format=%s "$BARE")
This reverts commit ${SUBJECT}.

broke stuff"
TOKEN=$(git -C "$R" rev-parse HEAD)
if out=$(run "${SUBJECT}..${TOKEN}"); then
  printf '%s\n' "$out" >&2
  fail 'M3: an 11-character non-reason passed the gate'
fi
ok 'M3  a token gesture at a reason is REFUSED'

# -------------------------------------------------------- ACCEPT: stated reason
git -C "$R" commit -q --amend -m "$(git -C "$R" log -1 --format=%s "$BARE")
This reverts commit ${SUBJECT}.

trust-thir-lower --lib is RED at that commit: zero_displacement_tests::
test_the_zero_displacement_guard_runs_after_the_offset_query panics on
\"the accessor lane's offset query must exist\". The gate itself looks
correct; re-land it once the needle follows the widened binding."
REASON=$(git -C "$R" rev-parse HEAD)
out=$(run "${SUBJECT}..${REASON}") || { printf '%s\n' "$out" >&2; fail 'A1: a stated reason was refused'; }
case "$out" in
  *'REVERT RATIONALE: GREEN'*) ;;
  *) fail 'A1: the accept did not reach the green verdict' ;;
esac
ok 'A1  a revert that states its reason PASSES'

# ------------------------------------------- ACCEPT: ordinary commits untouched
# The falsifier for "the gate just fails everything": the subject commit has an
# empty body and a non-revert subject, and must not be judged at all.
out=$(run "${BASE}..${SUBJECT}") || { printf '%s\n' "$out" >&2; fail 'A2: a non-revert commit with an empty body was refused'; }
case "$out" in
  *'0 revert(s)'*) ;;
  *) fail 'A2: a non-revert commit was counted as a revert' ;;
esac
ok 'A2  a non-revert commit with an empty body is not judged'

# --------------------------------------- NEGATIVE + ACCEPT: the RE-LAND subject
# git >= 2.42 spells a revert-of-a-revert `Reapply "<original subject>"`, not
# `Revert "Revert "`. That is exactly the re-land case — the one where the
# reason matters MOST, because it is the commit that puts a reverted gate back
# — so it must be judged by the same rule. This test found the hole by running
# real `git revert` rather than assuming the subject.
git -C "$R" revert --no-edit "$REASON"
RERE=$(git -C "$R" rev-parse HEAD)
case "$(git -C "$R" log -1 --format=%s "$RERE")" in
  'Reapply "'*|'Revert "Revert "'*) ;;
  *) fail "A3: neither re-land subject shape was produced: $(git -C "$R" log -1 --format=%s "$RERE")" ;;
esac
if out=$(run "${REASON}..${RERE}"); then
  printf '%s\n' "$out" >&2
  fail 'M4: a BARE re-land (Reapply/Revert-of-a-Revert) passed the gate'
fi
ok 'M4  a bare re-land is REFUSED under whichever subject git generates'

git -C "$R" commit -q --amend -m "$(git -C "$R" log -1 --format=%s "$RERE")
This reverts commit ${REASON}.

Re-lands the gate: the needle now matches the widened binding, so the
--lib suite is green at this tree and the refusal that motivated the
first revert no longer reproduces."
RERE=$(git -C "$R" rev-parse HEAD)
out=$(run "${REASON}..${RERE}") || { printf '%s\n' "$out" >&2; fail 'A3: an explained re-land was refused'; }
ok 'A3  an explained re-land PASSES'

# ------------------------------------------------------ the grandfather ledger
# A listed sha is stepped over, and ONLY that sha: the ledger must not be a
# blanket amnesty, and a sha that is merely a prefix of a listed one must not
# match.
git -C "$R" checkout -q "$TRAILER" -- . 2>/dev/null || true
git -C "$R" reset -q --hard "$SUBJECT"
git -C "$R" revert --no-edit "$SUBJECT"
G1=$(git -C "$R" rev-parse HEAD)
printf 'fn main() { gate2(); }\n' >"$R/crates/trust-thir-lower/src/lib.rs"
git -C "$R" commit -qam 'feat: a second gate'
G2SUB=$(git -C "$R" rev-parse HEAD)
git -C "$R" revert --no-edit "$G2SUB"
G2=$(git -C "$R" rev-parse HEAD)

printf '# fixture ledger\n%s\n' "$G1" >"$R/scripts/revert-rationale-grandfathered.txt"
if out=$(run "${SUBJECT}..${G2}"); then
  printf '%s\n' "$out" >&2
  fail 'L1: the ledger amnestied a revert it does not list'
fi
case "$out" in
  *"$G2"*) ;;
  *) fail 'L1: the unlisted revert was not the one reported' ;;
esac
case "$out" in
  *"$G1"*) fail 'L1: a LISTED revert was still reported' ;;
  *) ;;
esac
case "$out" in
  *'1 grandfathered'*) ;;
  *) fail 'L1: the grandfathered count was not reported' ;;
esac
ok 'L1  the ledger steps over exactly the shas it lists, and no others'

# A truncated sha in the ledger must NOT match the full sha: `grep -qx` is the
# whole reason, and a regression to `grep -q` would silently widen the amnesty.
printf '# fixture ledger\n%s\n' "${G2:0:12}" >"$R/scripts/revert-rationale-grandfathered.txt"
if out=$(run "${G2SUB}..${G2}"); then
  printf '%s\n' "$out" >&2
  fail 'L2: an abbreviated ledger row amnestied a full sha'
fi
ok 'L2  an abbreviated ledger row does not amnesty anything'
rm -f "$R/scripts/revert-rationale-grandfathered.txt"

# ------------------------------------------------------------- --pre-push mode
# The shape git actually feeds the hook, including the deletion line that must
# be stepped over rather than crashed on.
ZERO=0000000000000000000000000000000000000000
if out=$(printf 'refs/heads/main %s refs/heads/main %s\n' "$G2" "$G2SUB" | ( cd "$R" && bash scripts/check_revert_rationale.sh --pre-push 2>&1 )); then
  printf '%s\n' "$out" >&2
  fail 'P1: --pre-push passed a range containing a bare revert'
fi
case "$out" in
  *"$G2"*) ;;
  *) fail 'P1: --pre-push did not name the offending sha' ;;
esac
ok 'P1  --pre-push refuses the pushed range that introduces a bare revert'

out=$(printf 'refs/heads/gone %s refs/heads/gone %s\n' "$ZERO" "$G2" | ( cd "$R" && bash scripts/check_revert_rationale.sh --pre-push 2>&1 )) \
  || { printf '%s\n' "$out" >&2; fail 'P2: a branch DELETION was judged'; }
ok 'P2  --pre-push steps over a branch deletion'

out=$( ( cd "$R" && bash scripts/check_revert_rationale.sh --pre-push </dev/null 2>&1 ) ) \
  || { printf '%s\n' "$out" >&2; fail 'P3: an empty stdin was treated as a failure'; }
case "$out" in
  *'nothing to judge'*) ;;
  *) fail 'P3: empty stdin did not say so' ;;
esac
ok 'P3  --pre-push with no updated refs says so instead of guessing'

# New branches must retain positive tips throughout a multi-ref push. Remote
# tracking refs are local state and cannot authorize an unexplained revert.
if out=$(printf 'refs/heads/new %s refs/heads/new %s\n' "$G2" "$ZERO" | ( cd "$R" && bash scripts/check_revert_rationale.sh --pre-push 2>&1 )); then
  printf '%s\n' "$out" >&2
  fail 'P4: a new branch carrying a bare revert passed'
fi
case "$out" in *"$G2"*) ;; *) fail 'P4: the new-branch refusal did not name the revert' ;; esac
ok 'P4  a new branch cannot introduce an unexplained revert'

git -C "$R" update-ref refs/remotes/forged/main "$G2"
if out=$(printf 'refs/heads/new %s refs/heads/new %s\n' "$G2" "$ZERO" | ( cd "$R" && bash scripts/check_revert_rationale.sh --pre-push 2>&1 )); then
  printf '%s\n' "$out" >&2
  fail 'P5: a local tracking ref hid an unexplained revert on a new branch'
fi
case "$out" in *"$G2"*) ;; *) fail 'P5: the tracking-ref refusal did not name the revert' ;; esac
git -C "$R" update-ref -d refs/remotes/forged/main "$G2"
ok 'P5  a forged local tracking ref cannot hide the pushed revert'

if out=$(printf 'refs/heads/clean %s refs/heads/clean %s\nrefs/heads/main %s refs/heads/main %s\n' "$BASE" "$ZERO" "$G2" "$G2SUB" | ( cd "$R" && bash scripts/check_revert_rationale.sh --pre-push 2>&1 )); then
  printf '%s\n' "$out" >&2
  fail 'P6: an earlier new branch hid a later bare revert in the same push'
fi
case "$out" in *"$G2"*) ;; *) fail 'P6: the multi-ref refusal did not name the revert' ;; esac
ok 'P6  an earlier new branch cannot negate a later pushed range'

out=$(printf 'refs/heads/clean %s refs/heads/clean %s\nrefs/heads/main %s refs/heads/main %s\n' "$BASE" "$ZERO" "$REASON" "$SUBJECT" | ( cd "$R" && bash scripts/check_revert_rationale.sh --pre-push 2>&1 )) \
  || { printf '%s\n' "$out" >&2; fail 'P7: a clean new branch and explained revert were refused'; }
case "$out" in *'1 revert(s)'*) ;; *) fail 'P7: the explained revert was not actually examined' ;; esac
ok 'P7  a multi-ref push actually examines and accepts the explained revert'

DESTINATION="$TMP/published.git"
git init -q --bare -b main "$DESTINATION"
# This fixture remote deliberately contains an old unexplained revert, as a
# clone can inherit history from machines that did not install the hook.
git -C "$R" push -q "$DESTINATION" "$G2:refs/heads/main"
out=$(printf 'refs/heads/new %s refs/heads/new %s\n' "$G2" "$ZERO" | ( cd "$R" && bash scripts/check_revert_rationale.sh --pre-push --remote "$DESTINATION" 2>&1 )) \
  || { printf '%s\n' "$out" >&2; fail 'P8: destination-published ancestry blocked a new branch'; }
case "$out" in *'0 commit(s)'*) ;; *) fail 'P8: published ancestry was not excluded' ;; esac
out=$( ( cd "$R" && TRUST_PUSH_REMOTE="$DESTINATION" TRUST_PUSHED_REFS="refs/heads/new $G2 refs/heads/new $ZERO" bash scripts/check_revert_rationale.sh --push-context 2>&1 ) ) \
  || { printf '%s\n' "$out" >&2; fail 'P8: push-context did not forward the destination'; }
if out=$(run "${G2SUB}..${G2}"); then
  fail 'P8: an explicit audit excused an already-published unexplained revert'
fi
ok 'P8  actual destination ancestry is preserved while explicit history audits still refuse'

EMPTY_DESTINATION="$TMP/empty.git"
git init -q --bare -b main "$EMPTY_DESTINATION"
git -C "$R" update-ref refs/remotes/forged/main "$G2"
if out=$(printf 'refs/heads/new %s refs/heads/new %s\n' "$G2" "$ZERO" | ( cd "$R" && bash scripts/check_revert_rationale.sh --pre-push --remote "$EMPTY_DESTINATION" 2>&1 )); then
  fail 'P9: another remote or local tracking ref excused this destination push'
fi
case "$out" in *"$G2"*) ;; *) fail 'P9: destination refusal did not identify the revert' ;; esac
git -C "$R" update-ref -d refs/remotes/forged/main "$G2"
ok 'P9  publication elsewhere and forged tracking refs do not authorize a new destination'

if out=$(printf 'refs/heads/new %s refs/heads/new %s\n' "$G2" "$ZERO" | ( cd "$R" && bash scripts/check_revert_rationale.sh --pre-push --remote "$TMP/missing.git" 2>&1 )); then
  fail 'P10: an unavailable destination reported success'
else
  rc=$?
fi
[ "$rc" -eq 2 ] || fail "P10: expected unavailable-destination exit 2, got $rc"
out=$(printf 'refs/heads/gone %s refs/heads/gone %s\n' "$ZERO" "$G2" | ( cd "$R" && bash scripts/check_revert_rationale.sh --pre-push --remote "$TMP/missing.git" 2>&1 )) \
  || fail 'P10: a deletion unnecessarily required remote history'
ok 'P10  unavailable destination history fails closed; deletions need no history query'

# ----------------------------------------- UPDATE pushes: introduced commits only
# An update is judged on what it INTRODUCES to the destination, exactly as a new
# branch is. The case that forced this: a lane branch updated to a head that
# merges main carried main's own already-published bare revert in `old..new`,
# and was refused over a commit the push did not introduce — while the SAME
# update beside a throwaway new ref was judged on its own commits, because the
# destination exclusions are global to one `git log`. Each accept arm below
# carries its own non-vacuity control: the same range WITHOUT a destination
# must still be refused, so the revert is demonstrably inside the range.
UPD_DEST="$TMP/update-dest.git"
git init -q --bare -b main "$UPD_DEST"
ucommit() {  # <file> <message>
  mkdir -p "$R/u"
  printf '%s\n' "$1" >"$R/u/$1"
  git -C "$R" add "u/$1"
  git -C "$R" commit -qm "$2"
}
upd() {  # <old> <new> [--remote DEST | -] [extra ref line]
  local dest="${3:-$UPD_DEST}"
  local args=(--pre-push)
  [ "$dest" = - ] || args+=(--remote "$dest")
  printf 'refs/heads/lane %s refs/heads/lane %s\n%s' "$2" "$1" "${4:-}" \
    | ( cd "$R" && bash scripts/check_revert_rationale.sh "${args[@]}" 2>&1 )
}
header() { printf '%s\n' "$1" | grep -m1 '^=== revert-rationale' || true; }

# Published main: a change and its BARE revert, already on the destination.
git -C "$R" checkout -q -b u-main "$BASE"
ucommit pub.txt 'feat: a change main later reverts'
git -C "$R" revert --no-edit HEAD >/dev/null
U_PUBREV=$(git -C "$R" rev-parse HEAD)
git -C "$R" push -q "$UPD_DEST" "$U_PUBREV:refs/heads/main"
# A published branch that is NOT main, carrying its own bare revert.
git -C "$R" checkout -q -b u-other "$BASE"
ucommit other.txt 'feat: a change another published branch reverts'
git -C "$R" revert --no-edit HEAD >/dev/null
U_OTHREV=$(git -C "$R" rev-parse HEAD)
git -C "$R" push -q "$UPD_DEST" "$U_OTHREV:refs/heads/other"
# The lane: published once, then updated to a head that merges main.
git -C "$R" checkout -q -b u-lane "$BASE"
ucommit lane.txt 'feat: the lane'
U_OLD=$(git -C "$R" rev-parse HEAD)
git -C "$R" push -q "$UPD_DEST" "$U_OLD:refs/heads/lane"
git -C "$R" merge -q --no-edit u-main
U_MERGED=$(git -C "$R" rev-parse HEAD)
git -C "$R" merge-base --is-ancestor "$U_PUBREV" "$U_MERGED" \
  && ! git -C "$R" merge-base --is-ancestor "$U_PUBREV" "$U_OLD" \
  || fail 'U1-fixture: the published revert is not inside old..new, so U1 would prove nothing'

if out=$(upd "$U_OLD" "$U_MERGED" -); then
  printf '%s\n' "$out" >&2
  fail 'U1-control: with no destination the merged-in bare revert passed; the arm is vacuous'
fi
case "$out" in *"$U_PUBREV"*) ;; *) fail 'U1-control: the no-destination refusal did not name the published revert' ;; esac
out=$(upd "$U_OLD" "$U_MERGED") \
  || { printf '%s\n' "$out" >&2; fail 'U1: an update was refused over a bare revert already on the destination main'; }
case "$out" in *"$U_PUBREV"*) fail 'U1: the published revert was still judged' ;; *) ;; esac
case "$(header "$out")" in *'1 commit(s), 0 revert(s)'*) ;; *) printf '%s\n' "$out" >&2; fail 'U1: the subject was not exactly the one introduced merge commit' ;; esac
U1_ALONE="$(header "$out")"
out=$(upd "$U_OLD" "$U_MERGED" "$UPD_DEST" "refs/heads/tmp $U_OLD refs/heads/tmp $ZERO
") || { printf '%s\n' "$out" >&2; fail 'U1: the update beside a new ref was refused'; }
[ "$(header "$out")" = "$U1_ALONE" ] \
  || fail "U1: one update, two subjects — alone: $U1_ALONE; beside a new ref: $(header "$out")"
out=$( ( cd "$R" && TRUST_PUSH_REMOTE="$UPD_DEST" TRUST_PUSHED_REFS="refs/heads/lane $U_MERGED refs/heads/lane $U_OLD" \
  bash scripts/check_revert_rationale.sh --push-context 2>&1 ) ) \
  || { printf '%s\n' "$out" >&2; fail 'U1: --push-context (the full hook path) refused the update'; }
if run "${U_OLD}..${U_MERGED}" >/dev/null; then
  fail 'U1: an explicit range audit excused the published bare revert'
fi
ok 'U1  an update whose range merges a bare revert already on destination main PASSES, judged on the one commit it introduces — alone, beside a new ref, and via --push-context; without a destination, and as an explicit audit, it is still refused'

# RED: an update that introduces a NEW bare revert is refused, and names it —
# not the published one it also carries.
git -C "$R" revert --no-edit "$U_OLD" >/dev/null
U_NEWREV=$(git -C "$R" rev-parse HEAD)
if out=$(upd "$U_OLD" "$U_NEWREV"); then
  printf '%s\n' "$out" >&2
  fail 'U2: an update introducing a NEW bare revert passed'
fi
case "$out" in *"$U_NEWREV"*) ;; *) fail 'U2: the refusal did not name the new revert' ;; esac
case "$out" in *"$U_PUBREV"*) fail 'U2: the refusal blamed the already-published revert' ;; *) ;; esac
if out=$(upd "$U_OLD" "$U_NEWREV" "$UPD_DEST" "refs/heads/tmp $U_OLD refs/heads/tmp $ZERO
"); then
  printf '%s\n' "$out" >&2
  fail 'U2: a throwaway new ref beside the update hid the new bare revert'
fi
case "$out" in *"$U_NEWREV"*) ;; *) fail 'U2: the throwaway-ref refusal did not name the new revert' ;; esac
ok 'U2  an update introducing a NEW bare revert is REFUSED by sha, alone and beside a throwaway new ref'

# GREEN half of the control: a bare revert on another destination branch that is
# not main is published history too, and an update merging it is not refused.
git -C "$R" checkout -q -b u-lane-other "$U_OLD"
git -C "$R" merge -q --no-edit u-other
U_MERGED_OTHER=$(git -C "$R" rev-parse HEAD)
if out=$(upd "$U_OLD" "$U_MERGED_OTHER" -); then
  fail 'U3-control: with no destination the other-branch bare revert passed; the arm is vacuous'
fi
case "$out" in *"$U_OTHREV"*) ;; *) fail 'U3-control: the no-destination refusal did not name the other-branch revert' ;; esac
out=$(upd "$U_OLD" "$U_MERGED_OTHER") \
  || { printf '%s\n' "$out" >&2; fail 'U3: a bare revert published on a non-main destination branch was not treated as known'; }
ok 'U3  a bare revert published on a destination branch other than main counts as known'

# RED half of the control: a bare revert created LOCALLY and merged into the
# pushed branch is refused however many LOCAL refs name it — a local branch, a
# remote-tracking ref for `origin`, and a remote configured AT the destination
# whose tracking ref is forged. Only what the destination advertises excludes.
git -C "$R" checkout -q -b u-local "$BASE"
ucommit local.txt 'feat: a change reverted only locally'
git -C "$R" revert --no-edit HEAD >/dev/null
U_LOCREV=$(git -C "$R" rev-parse HEAD)
git -C "$R" remote add dest "$UPD_DEST"
git -C "$R" update-ref refs/remotes/dest/main "$U_LOCREV"
git -C "$R" update-ref refs/remotes/origin/main "$U_LOCREV"
git -C "$R" checkout -q -b u-lane-local "$U_OLD"
git -C "$R" merge -q --no-edit u-local
U_MERGED_LOCAL=$(git -C "$R" rev-parse HEAD)
for dest in "$UPD_DEST" dest; do
  if out=$(upd "$U_OLD" "$U_MERGED_LOCAL" "$dest"); then
    printf '%s\n' "$out" >&2
    fail "U4: a locally-created bare revert merged into the update passed (--remote $dest)"
  fi
  case "$out" in *"$U_LOCREV"*) ;; *) fail "U4: the refusal did not name the local revert (--remote $dest)" ;; esac
done
if out=$( ( cd "$R" && TRUST_PUSH_REMOTE="$UPD_DEST" TRUST_PUSHED_REFS="refs/heads/lane $U_MERGED_LOCAL refs/heads/lane $U_OLD" \
  bash scripts/check_revert_rationale.sh --push-context 2>&1 ) ); then
  fail 'U4: --push-context passed a locally-created bare revert'
fi
git -C "$R" update-ref -d refs/remotes/origin/main
git -C "$R" update-ref -d refs/remotes/dest/main
git -C "$R" remote remove dest
ok 'U4  a locally-created bare revert merged into an update is REFUSED; local branches and forged tracking refs exclude nothing'

if out=$(upd "$U_OLD" "$U_MERGED" "$TMP/missing.git"); then
  fail 'U5: an update to an unavailable destination reported success'
else
  rc=$?
fi
[ "$rc" -eq 2 ] || fail "U5: expected unavailable-destination exit 2 on an update, got $rc"
ok 'U5  an update whose destination cannot be read fails closed (exit 2), never green'

# The destination is read by the helper the caller-skew lane shares. Without it
# the checker must not fall back to judging less: it refuses, exit 2.
mv "$R/scripts/lib/push_destination.sh" "$TMP/push_destination.sh.away"
if out=$(upd "$U_OLD" "$U_MERGED"); then
  mv "$TMP/push_destination.sh.away" "$R/scripts/lib/push_destination.sh"
  fail 'U6: an update with its destination reader missing reported success'
else
  rc=$?
fi
mv "$TMP/push_destination.sh.away" "$R/scripts/lib/push_destination.sh"
[ "$rc" -eq 2 ] || fail "U6: expected exit 2 with the destination reader missing, got $rc"
out=$(upd "$U_OLD" "$U_MERGED") || fail 'U6: the restored destination reader did not restore the green update'
ok 'U6  an update whose shared destination reader is missing fails closed (exit 2); restored, it is green again'

# ------------------------------- FORCE pushes over an old tip this clone never had
# `git push --force` (or a `+refspec`, or `--mirror`) over a destination tip that
# someone else pushed and this clone never fetched hands the hook an update line
# whose remote sha is ABSENT from this object store. The subject — the commits
# the push introduces — is all local, so the absent tip is no evidence the lane
# needs; until 2026-09-27 the lane spelled the range `absent..new`, `git log`
# could not start, and every such push died exit 2 with no revert anywhere in
# it. An absent caller-supplied old tip supplies no exclusion evidence. The
# shared destination reader separately requires the actual advertised main's
# original object before it can authorize any inherited-history exclusions.
F_DEST="$TMP/force-dest.git"
git init -q --bare -b main "$F_DEST"
git -C "$R" push -q "$F_DEST" "$BASE:refs/heads/main" "$BASE:refs/heads/keep"
git clone -q "$F_DEST" "$TMP/force-other" 2>/dev/null
git -C "$TMP/force-other" config user.name other
git -C "$TMP/force-other" config user.email other@example.invalid
git -C "$TMP/force-other" config commit.gpgsign false
printf 'theirs\n' >"$TMP/force-other/theirs.txt"
git -C "$TMP/force-other" add theirs.txt
git -C "$TMP/force-other" commit -qm 'other: work this clone never fetched'
git -C "$TMP/force-other" push -q origin main
F_ABSENT=$(git -C "$TMP/force-other" rev-parse HEAD)
if git -C "$R" cat-file -e "${F_ABSENT}^{commit}" 2>/dev/null; then
  fail 'F-fixture: the destination tip is in this object store, so no F arm below proves anything'
fi
[ "$(git --git-dir="$F_DEST" rev-parse main)" = "$F_ABSENT" ] || fail 'F-fixture: the acquired tip is not the destination main'

git -C "$R" checkout -q -b f-lane "$BASE"
ucommit f-clean.txt 'feat: a rewritten line, no revert anywhere'
F_CLEAN=$(git -C "$R" rev-parse HEAD)
fpush() {  # <new> [--remote DEST | -]
  local dest="${2:-$F_DEST}"
  local args=(--pre-push)
  [ "$dest" = - ] || args+=(--remote "$dest")
  printf 'refs/heads/main %s refs/heads/main %s\n' "$1" "$F_ABSENT" \
    | ( cd "$R" && bash scripts/check_revert_rationale.sh "${args[@]}" 2>&1 )
}

# A fresh advertised main whose original object is unreadable is NOT JUDGED,
# even when another published branch could otherwise narrow the subject.
if out=$(fpush "$F_CLEAN"); then
  fail 'F0: an unreadable actual destination main reported green'
else
  rc=$?
fi
[ "$rc" -eq 2 ] || { printf '%s\n' "$out" >&2; fail "F0: expected NOT JUDGED (exit 2), got $rc"; }
case "$out" in *'main original commit is unavailable; NOT JUDGED'*) ;; *) fail 'F0: missing original main was not named' ;; esac
# Acquire actual original DATA through the literal local fixture transport;
# no ref or caller-provided push row stands in for that object.
git -C "$R" fetch -q --no-tags --no-write-fetch-head "$F_DEST" "$F_ABSENT"
ok 'F0  unavailable advertised main refuses; actual local object acquisition enables judgment'

out=$(fpush "$F_CLEAN") \
  || { printf '%s\n' "$out" >&2; fail 'F1: a clean force push over the acquired destination tip was refused'; }
# `keep` (= BASE) is advertised, so the widened walk narrows back to the one
# commit the push introduces: the widening costs nothing the destination knows.
case "$(header "$out")" in *'1 commit(s), 0 revert(s)'*) ;; *) printf '%s\n' "$out" >&2; fail 'F1: the subject was not exactly the one introduced commit' ;; esac
ok 'F1  a clean force push over a destination tip this clone has now acquired PASSES, judged on the one commit it introduces'

git -C "$R" revert --no-edit "$F_CLEAN" >/dev/null
F_REV=$(git -C "$R" rev-parse HEAD)
if out=$(fpush "$F_REV"); then
  printf '%s\n' "$out" >&2
  fail 'F2: a force push introducing a bare revert over the acquired tip passed'
else
  rc=$?
fi
[ "$rc" -eq 1 ] || { printf '%s\n' "$out" >&2; fail "F2: expected the rationale refusal (exit 1), got $rc"; }
case "$out" in *"$F_REV"*) ;; *) fail 'F2: the refusal did not name the bare revert' ;; esac
ok 'F2  the same force push carrying a bare revert is REFUSED (exit 1), by sha'

out=$( ( cd "$R" && TRUST_PUSH_REMOTE="$F_DEST" TRUST_PUSHED_REFS="refs/heads/main $F_CLEAN refs/heads/main $F_ABSENT" \
  bash scripts/check_revert_rationale.sh --push-context 2>&1 ) ) \
  || { printf '%s\n' "$out" >&2; fail 'F3: --push-context refused a clean force push over the acquired tip'; }
case "$out" in 'SUBJECT: push'*) ;; *) fail 'F3: --push-context did not take the push reading' ;; esac
if out=$( ( cd "$R" && TRUST_PUSH_REMOTE="$F_DEST" TRUST_PUSHED_REFS="refs/heads/main $F_REV refs/heads/main $F_ABSENT" \
  bash scripts/check_revert_rationale.sh --push-context 2>&1 ) ); then
  fail 'F3: --push-context passed a bare revert force-pushed over the acquired tip'
else
  rc=$?
fi
[ "$rc" -eq 1 ] || { printf '%s\n' "$out" >&2; fail "F3: expected exit 1 from --push-context, got $rc"; }
case "$out" in *"$F_REV"*) ;; *) fail 'F3: the --push-context refusal did not name the bare revert' ;; esac
ok 'F3  --push-context (the manifest row) passes the clean force push and refuses the bare revert, by sha'

# Without a destination nothing narrows the widened walk, so a bare revert
# DEEP in local history — not at the tip — must still be found.
ucommit f-after1.txt 'feat: a commit after the revert'
ucommit f-after2.txt 'feat: another commit after the revert'
F_DEEP=$(git -C "$R" rev-parse HEAD)
for dest in - "$F_DEST"; do
  if out=$(fpush "$F_DEEP" "$dest"); then
    printf '%s\n' "$out" >&2
    fail "F4: a bare revert below the pushed tip passed a force push over the acquired tip (--remote $dest)"
  else
    rc=$?
  fi
  [ "$rc" -eq 1 ] || { printf '%s\n' "$out" >&2; fail "F4: expected exit 1 (--remote $dest), got $rc"; }
  case "$out" in *"$F_REV"*) ;; *) fail "F4: the refusal did not name the deep bare revert (--remote $dest)" ;; esac
done
ok 'F4  a bare revert deep below the tip is REFUSED, with and without a destination to narrow the walk'

# A genuinely unreadable new object remains unjudged after main acquisition.
git -C "$TMP/force-other" commit -q --allow-empty -m 'another original not acquired here'
F_NEW_ABSENT=$(git -C "$TMP/force-other" rev-parse HEAD)
# The widening is for an unreadable OLD tip only. A NEW tip this clone cannot
# read is a subject the lane cannot judge at all: that stays exit 2.
if out=$(printf 'refs/heads/main %s refs/heads/main %s\n' "$F_NEW_ABSENT" "$F_CLEAN" | ( cd "$R" && bash scripts/check_revert_rationale.sh --pre-push 2>&1 )); then
  fail 'F5: an unreadable pushed tip reported green'
else
  rc=$?
fi
[ "$rc" -eq 2 ] || { printf '%s\n' "$out" >&2; fail "F5: expected exit 2 for an unreadable pushed tip, got $rc"; }
ok 'F5  a pushed tip this clone cannot read still fails closed (exit 2)'

# ------------------------------------ ANCHORED WAIVERS: the push context (case R)
# Under push context the rows that waive are rows(anchor) ∩ rows(pushed tip),
# the anchor being a tree this push cannot author: the destination's tip for an
# update, the merge-base with the destination's main for a new ref, none
# otherwise (docs/issues/2026-09-28-push-lanes-judge-the-checkout-not-the-push.md).
# Every refusal arm carries a STANDING control — the same line on stdin with no
# push context — that passes, so the row is demonstrably the one the checkout's
# ledger would have honoured.
A="$TMP/anchored"
A_DEST="$TMP/anchored-dest.git"
git init -q -b main "$A"
git init -q --bare -b main "$A_DEST"
git -C "$A" config user.name test
git -C "$A" config user.email test@example.invalid
git -C "$A" config commit.gpgsign false
mkdir -p "$A/scripts/lib" "$A/crates/trust-thir-lower/src"
cp "$CHECKER" "$A/scripts/check_revert_rationale.sh"
cp "$DESTINATION_LIB" "$A/scripts/lib/push_destination.sh"
cp "$REPO_ROOT/scripts/lib/remote_tips.py" "$REPO_ROOT/scripts/lib/landing_targo.py" "$REPO_ROOT/scripts/lib/remote_operation.py" "$A/scripts/lib/"
printf 'fn main() {}\n' >"$A/crates/trust-thir-lower/src/lib.rs"
git -C "$A" add -A
git -C "$A" commit -qm 'fixture: the checker and a soundness-gate path'
A_BASE=$(git -C "$A" rev-parse HEAD)
git -C "$A" push -q "$A_DEST" "$A_BASE:refs/heads/main"
# The offender, on a side branch: a change and its BARE revert.
git -C "$A" checkout -q -b side
printf 'fn main() { gate(); }\n' >"$A/crates/trust-thir-lower/src/lib.rs"
git -C "$A" commit -qam 'feat(thir-lower): a gate'
git -C "$A" revert --no-edit HEAD >/dev/null
A_X=$(git -C "$A" rev-parse HEAD)
aledger() {  # <message> <rows...>: commit the ledger holding exactly these rows
  local msg="$1" r; shift
  { printf '# fixture ledger\n'; for r in "$@"; do printf '%s\n' "$r"; done; } >"$A/$LEDGER_REL"
  git -C "$A" add "$LEDGER_REL"
  git -C "$A" commit -qm "$msg"
  git -C "$A" rev-parse HEAD
}
apush() {  # <refs> [destination | -]: --push-context, as scripts/hooks/pre-push runs the row
  local dest="${2:-$A_DEST}"
  if [ "$dest" = - ]; then
    ( cd "$A" && TRUST_PUSHED_REFS="$1" bash scripts/check_revert_rationale.sh --push-context 2>&1 )
  else
    ( cd "$A" && TRUST_PUSHED_REFS="$1" TRUST_PUSH_REMOTE="$dest" bash scripts/check_revert_rationale.sh --push-context 2>&1 )
  fi
}
astanding() {  # <refs>: the same lines with NO push context (the checkout's ledger)
  printf '%s\n' "$1" | ( cd "$A" && bash scripts/check_revert_rationale.sh --pre-push --remote "$A_DEST" 2>&1 )
}
arefused() {  # <label> <output> <rc>
  [ "$3" -eq 1 ] || { printf '%s\n' "$2" >&2; fail "$1: expected the rationale refusal (exit 1), got $3"; }
  case "$2" in *"$A_X"*) ;; *) printf '%s\n' "$2" >&2; fail "$1: the refusal did not name the bare revert" ;; esac
}

# AR1 — R (1a): an UNCOMMITTED row in the checkout's ledger.
{ printf '# fixture ledger\n%s\n' "$A_X"; } >"$A/$LEDGER_REL"
A_REFS="refs/heads/main $A_X refs/heads/main $A_BASE"
out=$(astanding "$A_REFS") || { printf '%s\n' "$out" >&2; fail 'AR1-control: the standing reading did not honour the checkout row, so AR1 proves nothing'; }
set +e; out=$(apush "$A_REFS"); rc=$?; set -e
arefused 'AR1: an uncommitted ledger row waived the pushed bare revert' "$out" "$rc"
case "$out" in *'0 grandfather row(s) apply'*) ;; *) fail 'AR1: the waiver report did not say that no row applies' ;; esac
rm -f "$A/$LEDGER_REL"
ok 'AR1  an UNCOMMITTED ledger row does not waive the pushed bare revert (standing control: it does)'

# AR2 — R (1b): the row committed on HEAD, in the same push.
A_SELF=$(aledger 'grandfather my own revert' "$A_X")
A_REFS="refs/heads/main $A_SELF refs/heads/main $A_BASE"
out=$(astanding "$A_REFS") || { printf '%s\n' "$out" >&2; fail 'AR2-control: the standing reading did not honour the committed row'; }
set +e; out=$(apush "$A_REFS"); rc=$?; set -e
arefused 'AR2: a row committed in the same push waived its own bare revert' "$out" "$rc"
# ...and pushed as a NEW ref, anchored at the merge-base with destination main.
set +e; out=$(apush "refs/heads/topic $A_SELF refs/heads/topic $ZERO"); rc=$?; set -e
arefused 'AR2: a new ref carrying its own ledger row waived its bare revert' "$out" "$rc"
case "$out" in *"anchor ${A_BASE:0:12} (merge-base with the destination's main)"*) ;; *) printf '%s\n' "$out" >&2; fail 'AR2: the new ref was not anchored at the merge-base' ;; esac
ok 'AR2  a row committed IN THE SAME PUSH (update, or new ref) does not waive its bare revert (standing control: it does)'

# AR3 — accept: the destination's tip already grandfathers the side-branch revert
# (the shape of f1987758f1, recorded on main while it sat on another branch);
# merging that branch is waived, as an update and as a new ref.
git -C "$A" checkout -q main
A_L=$(aledger 'grandfather the side branch revert' "$A_X")
git -C "$A" push -q "$A_DEST" "$A_L:refs/heads/main"
git -C "$A" merge -q --no-edit side
A_M=$(git -C "$A" rev-parse HEAD)
out=$(apush "refs/heads/main $A_M refs/heads/main $A_L") \
  || { printf '%s\n' "$out" >&2; fail 'AR3: a row at the anchor AND the tip did not waive'; }
case "$out" in *'1 grandfathered'*) ;; *) printf '%s\n' "$out" >&2; fail 'AR3: the revert was not counted as grandfathered' ;; esac
out=$(apush "refs/heads/topic $A_M refs/heads/topic $ZERO") \
  || { printf '%s\n' "$out" >&2; fail 'AR3: a new ref anchored at the merge-base with a grandfathering main was refused'; }
ok 'AR3  a row present at the anchor AND the pushed tip waives, for an update and for a new ref'

# AR4 — the tip dropping the row: the intersection waives nothing.
A_DROP=$(aledger 'retire the row')
set +e; out=$(apush "refs/heads/main $A_DROP refs/heads/main $A_L"); rc=$?; set -e
arefused 'AR4: a row the pushed tip no longer carries still waived' "$out" "$rc"
ok 'AR4  a row the pushed tip drops waives nothing, even though the anchor has it'

# AR5 — no anchor, no waiver: no destination named, or one with no main.
git -C "$A" checkout -q side
A_SELF_REFS="refs/heads/topic $A_M refs/heads/topic $ZERO"
set +e; out=$(apush "$A_SELF_REFS" -); rc=$?; set -e
arefused 'AR5: a new ref with no destination to anchor it was waived' "$out" "$rc"
case "$out" in *'NO ANCHOR'*) ;; *) fail 'AR5: the report did not say there is no anchor' ;; esac
A_EMPTY="$TMP/anchored-empty.git"
git init -q --bare -b main "$A_EMPTY"
set +e; out=$(apush "$A_SELF_REFS" "$A_EMPTY"); rc=$?; set -e
arefused 'AR5: a new ref to a destination with no main was waived' "$out" "$rc"
case "$out" in *'advertises no main'*) ;; *) fail 'AR5: the report did not say the destination has no main' ;; esac
ok 'AR5  with NO anchor (no destination, or one advertising no main) no row waives'

# AR6 — one unanchored line empties the whole set: the rows are global to the
# one sweep, so a waiver must hold for every pushed line.
git -C "$A" checkout -q --orphan island
git -C "$A" rm -rq --cached .
printf 'island\n' >"$A/island.txt"
git -C "$A" add island.txt
git -C "$A" commit -qm 'unrelated history'
A_ISLAND=$(git -C "$A" rev-parse HEAD)
git -C "$A" checkout -qf side
set +e; out=$(apush "refs/heads/main $A_M refs/heads/main $A_L
refs/heads/island $A_ISLAND refs/heads/island $ZERO"); rc=$?; set -e
arefused 'AR6: an unanchored new ref beside an anchored update left the waiver standing' "$out" "$rc"
case "$out" in *'no history in common'*) ;; *) printf '%s\n' "$out" >&2; fail 'AR6: the report did not say why the island has no anchor' ;; esac
ok 'AR6  one pushed line with no anchor empties the waiver set for the whole push'

# AR7 — a line that is not four fields with full shas is exit 2, never skipped;
# an unterminated last line is judged; a deletion-only push judges nothing.
for bad_line in 'garbage' "refs/heads/main ${A_X:0:12} refs/heads/main $A_BASE" \
                "refs/heads/main $A_X refs/heads/main" "refs/heads/main $A_X refs/heads/main $A_BASE extra"; do
  set +e; out=$(apush "$bad_line"); rc=$?; set -e
  [ "$rc" -eq 2 ] || { printf '%s\n' "$out" >&2; fail "AR7: malformed line '$bad_line' gave exit $rc, not 2"; }
  case "$out" in *'malformed pushed-ref line'*) ;; *) fail "AR7: malformed line '$bad_line' was not named" ;; esac
done
{ printf '# fixture ledger\n%s\n' "$A_X"; } >"$A/$LEDGER_REL"
set +e
out=$(printf 'refs/heads/main %s refs/heads/main %s' "$A_X" "$A_BASE" \
  | ( cd "$A" && TRUST_PUSHED_REFS= bash scripts/check_revert_rationale.sh --pre-push --remote "$A_DEST" 2>&1 )); rc=$?
set -e
rm -f "$A/$LEDGER_REL"
arefused 'AR7: an unterminated last ref line was not judged' "$out" "$rc"
out=$(apush "(delete) $ZERO refs/heads/gone $A_BASE") \
  || { printf '%s\n' "$out" >&2; fail 'AR7: a deletion-only push was refused'; }
case "$out" in *'nothing to judge'*) ;; *) fail 'AR7: the deletion-only push did not say it judged nothing' ;; esac
ok 'AR7  a malformed pushed-ref line is exit 2, an unterminated last line is judged, a deletion-only push judges nothing'

# AR8 — the anchors the tests' ratchet reads are the checker's own.
out=$(printf 'refs/heads/main %s refs/heads/main %s\nrefs/heads/topic %s refs/heads/topic %s\n(delete) %s refs/heads/gone %s\n' \
        "$A_M" "$A_L" "$A_M" "$ZERO" "$ZERO" "$A_BASE" \
      | ( cd "$A" && bash scripts/check_revert_rationale.sh --waiver-anchors --remote "$A_DEST" 2>&1 )) \
  || { printf '%s\n' "$out" >&2; fail 'AR8: --waiver-anchors failed'; }
[ "$(printf '%s\n' "$out" | grep -c '^ANCHOR ')" -eq 2 ] || { printf '%s\n' "$out" >&2; fail 'AR8: expected one anchor per non-deletion line'; }
case "$out" in *"ANCHOR $A_M $A_L the destination's tip"*"ANCHOR $A_M $A_L merge-base with the destination's main"*) ;;
  *) printf '%s\n' "$out" >&2; fail 'AR8: the anchors are not the destination tip and the merge-base' ;; esac
ok 'AR8  --waiver-anchors names the destination tip for an update and the merge-base for a new ref'

# ------------------------------------- THE LEDGER UNDER PUSH CONTEXT (S1 + ratchet)
# With TRUST_PUSHED_REFS set, the ledger that matters is each pushed tip's
# COMMITTED one, not the checkout's. Each tip must SHIP the ledger (a tip
# without it is refused, as the standing reading refuses a checkout without
# it), and it must be well-formed (S1). Every row a tip ADDS over its anchor is
# then classified by where the commit it names lives:
#   * reachable from a commit the destination holds (one it advertises, or the
#     old tip git names for an updated ref): it records published history
#     (174a75e124 recorded four reverts; three were already on main). Holds.
#   * reachable from a pushed tip and not from the destination: the push would
#     be grandfathering a commit it brings itself. REFUSED — the gate refuses
#     it too, through the anchored waivers, so this reading is never weaker.
#   * neither (a revert on a branch this destination does not carry, or a
#     commit this store does not hold): a WARN, not a refusal. Refusing it
#     blocked a plain fast-forward of main across 174a75e124 to any destination
#     that carries main but not origin/b62-merge-redo. The residue is named: a
#     later push that brings that commit is anchored at a tip carrying the row,
#     so the row would waive it (the two-push form of case R 1b).
# Stderr of the anchor lookup and the destination read goes to a FILE, printed
# only on failure: a transport's warning (an ssh known_hosts notice, git's
# `warning: redirecting to`) is not an anchor line and not an advertised ref.
# Prints its findings; returns 0 (holds), 1 (violated) or 2 (cannot judge).
revert_ledger_push_reading() {  # <repo> <checker> <pushed-ref lines> <destination or "">
  local repo="$1" checker="$2" refs="$3" remote="$4" anchors advertised tag lsha anchor why
  local entry _mode type oid rc=0 row junk added warned unreached tips tip in_push is_rc held rsha gentry aentry
  local args=(--waiver-anchors)
  [ -z "$remote" ] || args+=(--remote "$remote")
  if ! anchors="$( cd "$repo" && printf '%s\n' "$refs" | bash "$checker" "${args[@]}" 2>"$TMP/rr-anchors.err" )"; then
    printf '  x cannot resolve the waiver anchors: %s\n' "$(cat "$TMP/rr-anchors.err" 2>/dev/null) $anchors"
    return 2
  fi
  if [ -z "$anchors" ]; then
    echo "  -- deletion(s) only: no pushed tree carries a ledger to judge"
    return 0
  fi
  advertised=""
  if [ -n "$remote" ]; then
    advertised="$( cd "$repo" && bash "$DESTINATION_LIB" "$remote" 2>"$TMP/rr-dest.err" )" \
      || { printf '  x cannot read the destination: %s\n' "$(cat "$TMP/rr-dest.err" 2>/dev/null)"; return 2; }
  fi
  tips="$(printf '%s\n' "$anchors" | awk '$1 == "ANCHOR" { print $2 }')"
  # What the destination HOLDS: every commit it advertises, and every old tip
  # git named for a non-deletion line (the destination's own ref value, the
  # same fact the gate excludes its range by), when this store holds it.
  held="$(printf '%s\n' "$advertised" | awk 'NF { print $1 }')"
  while read -r _ lsha _ rsha; do
    [ -n "${rsha:-}" ] && [ -n "${lsha//0/}" ] && [ -n "${rsha//0/}" ] || continue
    if git -C "$repo" --no-replace-objects rev-parse --verify --quiet "${rsha}^{commit}" >/dev/null 2>&1; then
      held="$held
$rsha"
    fi
  done <<< "$refs"
  while read -r tag lsha anchor why; do
    [ -n "${tag:-}" ] || continue
    [ "$tag" = ANCHOR ] || { printf '  x unexpected anchor line: %s %s\n' "$tag" "$lsha"; return 2; }
    : >"$TMP/rr-raw"; : >"$TMP/rr-anchor"
    if ! entry="$(git -C "$repo" --no-replace-objects ls-tree "$lsha" -- "$LEDGER_REL" 2>/dev/null)"; then
      printf '  x cannot read the tree of %s\n' "$lsha"; return 2
    fi
    type=""
    [ -z "$entry" ] || read -r _mode type oid _ <<< "$entry"
    if [ "$type" != blob ]; then
      # A tip older than the gate (an archive/ or salvage/ ref) ships neither
      # the gate nor its ledger: its missing ledger waives nothing, and main's
      # lane has no gate to run on it. Refused only when the tip ships the gate,
      # or the anchor ships the ledger (the push REMOVES it), or there is no anchor.
      if ! gentry="$(git -C "$repo" --no-replace-objects ls-tree "$lsha" -- scripts/check_revert_rationale.sh 2>/dev/null)"; then
        printf '  x cannot read the tree of %s\n' "$lsha"; return 2
      fi
      aentry=""
      if [ "$anchor" != NONE ] && ! aentry="$(git -C "$repo" --no-replace-objects ls-tree "$anchor" -- "$LEDGER_REL" 2>/dev/null)"; then
        printf '  x cannot read the tree of anchor %s\n' "$anchor"; return 2
      fi
      if [ -z "$gentry" ] && [ "$anchor" != NONE ] && [ -z "$aentry" ]; then
        printf '  -- %.12s: ships neither the gate nor its ledger, and neither does its anchor %.12s: nothing to judge\n' "$lsha" "$anchor"
        continue
      fi
      printf '  x %.12s: the shipped grandfather ledger %s is missing at the pushed tip\n' "$lsha" "$LEDGER_REL"
      rc=1; continue
    fi
    git -C "$repo" --no-replace-objects cat-file blob "$oid" >"$TMP/rr-raw" 2>/dev/null \
      || { printf '  x cannot read %s at %s\n' "$LEDGER_REL" "$lsha"; return 2; }
    # S1, on the pushed tip: every row is a full 40-character sha.
    junk=""
    while IFS= read -r row || [ -n "$row" ]; do
      row="${row%%#*}"
      row="$(printf '%s' "$row" | tr -d '[:space:]')"
      [ -n "$row" ] || continue
      [[ "$row" =~ ^[0-9a-f]{40}$ ]] || junk="$junk $row"
    done <"$TMP/rr-raw"
    if [ -n "$junk" ]; then
      printf '  x %.12s: the grandfather ledger holds rows that are not a full sha:%s\n' "$lsha" "$junk"; rc=1
    fi
    awk '{ sub(/#.*/, ""); gsub(/[ \t\r\n]/, ""); if ($0 ~ /^[0-9a-f]{40}$/) print }' "$TMP/rr-raw" \
      | LC_ALL=C sort -u >"$TMP/rr-tip"
    if [ "$anchor" != NONE ]; then
      if ! entry="$(git -C "$repo" --no-replace-objects ls-tree "$anchor" -- "$LEDGER_REL" 2>/dev/null)"; then
        printf '  x cannot read the tree of anchor %s\n' "$anchor"; return 2
      fi
      # No ledger at the ANCHOR is zero rows: every tip row then counts as added.
      if [ -n "$entry" ]; then
        read -r _mode type oid _ <<< "$entry"
        if [ "$type" = blob ]; then
          { git -C "$repo" --no-replace-objects cat-file blob "$oid" 2>/dev/null \
              | awk '{ sub(/#.*/, ""); gsub(/[ \t\r\n]/, ""); if ($0 ~ /^[0-9a-f]{40}$/) print }' \
              | LC_ALL=C sort -u >"$TMP/rr-anchor"; } \
            || { printf '  x cannot read %s at anchor %s\n' "$LEDGER_REL" "$anchor"; return 2; }
        fi
      fi
    fi
    added=0; warned=0
    while IFS= read -r row; do
      [ -n "$row" ] || continue
      added=$((added + 1))
      if ! git -C "$repo" --no-replace-objects rev-parse --verify --quiet "${row}^{commit}" >/dev/null 2>&1; then
        printf '  WARN %.12s: adds row %s, which names no commit this store holds — neither this push nor the destination (as far as this store can show) carries it\n' "$lsha" "$row"
        warned=$((warned + 1)); continue
      fi
      # Published = reachable from a commit the destination holds.
      if [ -n "$(printf '%s' "$held" | tr -d '[:space:]')" ]; then
        unreached="$(printf '%s\n' "$held" | awk 'NF { print "^" $1 }' \
                     | git -C "$repo" --no-replace-objects rev-list --stdin -n1 "$row" 2>/dev/null)" \
          || { printf '  x cannot walk the destination history for row %s\n' "$row"; return 2; }
        [ -n "$unreached" ] || continue
      fi
      # Not published: does THIS push carry it?
      in_push=0
      while IFS= read -r tip; do
        [ -n "$tip" ] || continue
        if git -C "$repo" --no-replace-objects merge-base --is-ancestor "$row" "$tip" 2>/dev/null; then
          is_rc=0
        else
          is_rc=$?
        fi
        if [ "$is_rc" -eq 0 ]; then in_push=1; break; fi
        [ "$is_rc" -eq 1 ] || { printf '  x cannot tell whether pushed tip %s carries row %s\n' "$tip" "$row"; return 2; }
      done <<< "$tips"
      if [ "$in_push" -eq 1 ]; then
        printf '  x %.12s: adds row %s, a commit THIS push carries and the destination does not already hold (anchor: %s) — a row may record published history, never excuse a revert it brings\n' \
          "$lsha" "$row" "$([ "$anchor" = NONE ] && printf '%s' "$why" || printf '%.12s, %s' "$anchor" "$why")"
        rc=1
      else
        printf '  WARN %.12s: adds row %s, which neither this push nor the destination carries — a later push that brings it would be waived by this row\n' "$lsha" "$row"
        warned=$((warned + 1))
      fi
    done < <(LC_ALL=C comm -23 "$TMP/rr-tip" "$TMP/rr-anchor")
    [ "$rc" -ne 0 ] || printf '  -- %.12s: %s row(s), well-formed; %s added over the anchor, %s of them already on the destination, %s outside this push (WARN)\n' \
      "$lsha" "$(grep -c . "$TMP/rr-tip" || true)" "$added" "$((added - warned))" "$warned"
  done <<< "$anchors"
  return "$rc"
}
rrcheck() {  # <want-rc> <needle> <label> <refs> [destination]: the reason must be NAMED
  local want="$1" needle="$2" label="$3" refs="$4" dest="${5:-}" out rc
  set +e; out="$(revert_ledger_push_reading "$A" "$A/scripts/check_revert_rationale.sh" "$refs" "$dest")"; rc=$?; set -e
  [ "$rc" -eq "$want" ] || { printf '%s\n' "$out" >&2; fail "$label (want rc=$want, got $rc)"; }
  case "$out" in *"$needle"*) ;; *) printf '%s\n' "$out" >&2; fail "$label (the output does not say '$needle')" ;; esac
  ok "$label"
}
rrcheck 1 'does not already hold' 'RR1  a pushed tip ADDING a row for an unpublished revert THIS PUSH CARRIES is REFUSED' \
  "refs/heads/main $A_SELF refs/heads/main $A_BASE" "$A_DEST"
# RR1w — the F12 shape: main fast-forwarded across a commit that records a
# revert living on a branch this destination does not carry (174a75e124 names
# f1987758f1, which sits on origin/b62-merge-redo). The push does not bring the
# revert, so it cannot exploit the row now; the residue is a WARN, not a block.
rrcheck 0 'neither this push nor the destination carries' 'RR1w a row naming a revert NEITHER this push NOR the destination carries is a WARN, not a refusal (a plain fast-forward of main to a main-only destination)' \
  "refs/heads/main $A_L refs/heads/main $A_BASE" "$A_DEST"
# RR8 — a transport that writes to stderr (an ssh known_hosts notice) is not
# an advertised ref and not an anchor line: the RR1 refusal still refuses, and
# a clean new-branch push over the same transport still passes.
mkdir -p "$TMP/noisy-ssh"
cat >"$TMP/noisy-ssh/ssh" <<'NOISY'
#!/bin/sh
echo "Warning: Permanently added 'fakehost' (ED25519) to the list of known hosts." >&2
for last in "$@"; do :; done
exec sh -c "$last"
NOISY
chmod +x "$TMP/noisy-ssh/ssh"
rrnoisy() {  # <want-rc> <needle> <label> <refs>: rrcheck, over the noisy transport
  local want="$1" needle="$2" label="$3" refs="$4" out rc
  set +e
  out="$(GIT_SSH_COMMAND="$TMP/noisy-ssh/ssh" GIT_SSH_VARIANT=simple \
         revert_ledger_push_reading "$A" "$A/scripts/check_revert_rationale.sh" "$refs" "fakehost:$A_DEST")"; rc=$?
  set -e
  [ "$rc" -eq "$want" ] || { printf '%s\n' "$out" >&2; fail "$label (want rc=$want, got $rc)"; }
  case "$out" in *"$needle"*) ;; *) printf '%s\n' "$out" >&2; fail "$label (the output does not say '$needle')" ;; esac
  ok "$label"
}
rrnoisy 1 'does not already hold' 'RR8  over a transport that writes to STDERR, an added row for an unpublished revert is still REFUSED (no fail-open)' \
  "refs/heads/main $A_SELF refs/heads/main $A_BASE"
rrnoisy 0 '0 added over the anchor' 'RR8b over the same noisy transport, a clean NEW-branch push passes (stderr is not an anchor line)' \
  "refs/heads/topic $A_L refs/heads/topic $ZERO"
git -C "$A" push -q "$A_DEST" "$A_X:refs/heads/published-side"
rrcheck 0 '1 added over the anchor' 'RR2  a pushed tip adding a row for a revert the destination ALREADY holds passes (the 174a75e124 shape)' \
  "refs/heads/main $A_SELF refs/heads/main $A_BASE" "$A_DEST"
rrcheck 1 'does not already hold' 'RR3  with no destination named, a row for a revert this push carries cannot be shown published' \
  "refs/heads/main $A_SELF refs/heads/main $A_BASE" ""
rrcheck 0 'neither this push nor the destination carries' 'RR3w with no destination named, a row naming a commit outside the push is a WARN' \
  "refs/heads/main $A_L refs/heads/main $A_BASE" ""
# RR3h — the old tip git names for an updated ref IS the destination's: a row
# for a revert below it records published history even with no destination
# named (the real shape: main pushed across 174a75e124, whose three main-line
# reverts sit below the old tip).
rrcheck 0 '1 of them already on the destination' 'RR3h with no destination named, a row for a revert below the updated ref'"'"'s OLD TIP holds (the destination has it)' \
  "refs/heads/side $A_SELF refs/heads/side $A_X" ""
git -C "$A" checkout -qf main
A_JUNK=$(aledger 'a malformed row' "$A_X" "${A_X:0:12}")
rrcheck 1 'not a full sha' 'RR4  S1 on the pushed tip: an abbreviated row is REFUSED' \
  "refs/heads/main $A_JUNK refs/heads/main $A_L" "$A_DEST"
git -C "$A" checkout -q "$A_L"
printf 'not-a-sha\n' >>"$A/$LEDGER_REL"
rrcheck 0 '0 added over the anchor' 'RR5  a malformed row in the CHECKOUT does not refuse a clean pushed tip' \
  "refs/heads/main $A_L refs/heads/main $A_L" "$A_DEST"
git -C "$A" checkout -q -- "$LEDGER_REL"
rrcheck 0 'deletion(s) only' 'RR6  a deletion-only push judges no ledger' \
  "(delete) $ZERO refs/heads/gone $A_BASE" "$A_DEST"
rrcheck 2 'malformed pushed-ref line' 'RR7  a malformed pushed-ref line cannot be judged (exit 2), never green' \
  "refs/heads/main ${A_L:0:12} refs/heads/main $A_BASE" "$A_DEST"
# RR9 — a pushed tip that does not SHIP the ledger is refused, as the standing
# reading refuses a checkout without it (differential F10: `git rm` of the
# ledger, pushed as a fast-forward). A ledger path that is not a file is the
# same defect.
git -C "$A" rm -q "$LEDGER_REL"
git -C "$A" commit -qm 'drop the grandfather ledger'
A_NOLEDGER=$(git -C "$A" rev-parse HEAD)
rrcheck 1 'is missing at the pushed tip' 'RR9  a pushed tip WITHOUT the grandfather ledger is REFUSED (the standing reading refuses a checkout without it)' \
  "refs/heads/main $A_NOLEDGER refs/heads/main $A_L" "$A_DEST"
mkdir -p "$A/$LEDGER_REL"
printf '%s\n' "$A_X" >"$A/$LEDGER_REL/rows"
git -C "$A" add "$LEDGER_REL/rows"
git -C "$A" commit -qm 'the ledger path is a directory'
A_LEDGERDIR=$(git -C "$A" rev-parse HEAD)
rrcheck 1 'is missing at the pushed tip' 'RR9b a pushed tip whose ledger path is not a file is REFUSED' \
  "refs/heads/main $A_LEDGERDIR refs/heads/main $A_L" "$A_DEST"
git -C "$A" checkout -qf "$A_L"
rm -rf "$A/$LEDGER_REL"
git -C "$A" checkout -qf "$A_L" -- "$LEDGER_REL"
# RR9c-RR9f — an archive/ or salvage/ ref: a new ref at a commit OLDER than the
# gate ships neither the gate nor its ledger. Its missing ledger waives nothing
# and main's lane has no gate to run on a checkout of it, so it is not the RR9
# defect: nothing to judge. The missing ledger is still REFUSED when any one
# of these holds (each arm isolates one):
#   RR9d  there is no anchor;
#   RR9e  the anchor ships the ledger (the push REMOVES it);
#   RR9f  the tip ships the gate.
# The commits are built from objects alone, so the worktree is not disturbed.
aplumb() {  # <message> <parent | -> <path> <content> [<path> <content>]...: a commit of exactly these files
  local msg="$1" parent="$2" idx="$TMP/aplumb.idx" blob tree; shift 2
  rm -f "$idx"
  while [ "$#" -ge 2 ]; do
    blob=$(printf '%s\n' "$2" | git -C "$A" hash-object -w --stdin)
    GIT_INDEX_FILE="$idx" git -C "$A" update-index --add --cacheinfo 100644 "$blob" "$1"
    shift 2
  done
  tree=$(GIT_INDEX_FILE="$idx" git -C "$A" write-tree)
  if [ "$parent" = - ]; then
    git -C "$A" commit-tree "$tree" -m "$msg"
  else
    git -C "$A" commit-tree "$tree" -p "$parent" -m "$msg"
  fi
}
A_ARCH_DEST="$TMP/anchored-archive-dest.git"
git init -q --bare -b main "$A_ARCH_DEST"
A_PRE=$(aplumb 'prehistory: before the gate' - crates/trust-thir-lower/src/lib.rs 'fn main() {}')
A_PRE_GATE=$(aplumb 'the gate and its ledger land' "$A_PRE" crates/trust-thir-lower/src/lib.rs 'fn main() {}' \
  scripts/check_revert_rationale.sh '# the gate' "$LEDGER_REL" "# fixture ledger")
git -C "$A" push -q "$A_ARCH_DEST" "$A_PRE_GATE:refs/heads/main"
A_ARCHIVE=$(aplumb 'archive: work from before the gate' "$A_PRE" crates/trust-thir-lower/src/lib.rs 'fn main() { old(); }')
rrcheck 0 'nothing to judge' 'RR9c a NEW ref at a commit older than the gate (neither gate nor ledger), anchored at a merge-base without the ledger, passes (archive/salvage refs)' \
  "refs/heads/archive/old $A_ARCHIVE refs/heads/archive/old $ZERO" "$A_ARCH_DEST"
rrcheck 1 'is missing at the pushed tip' 'RR9d the same pre-gate tip with NO anchor is REFUSED' \
  "refs/heads/archive/old $A_ARCHIVE refs/heads/archive/old $ZERO" ""
A_DROPALL=$(aplumb 'drop the gate and its ledger' "$A_PRE_GATE" crates/trust-thir-lower/src/lib.rs 'fn main() {}')
rrcheck 1 'is missing at the pushed tip' 'RR9e a tip that deletes BOTH the gate and its ledger, anchored at a tree that ships the ledger, is REFUSED' \
  "refs/heads/main $A_DROPALL refs/heads/main $A_PRE_GATE" "$A_ARCH_DEST"
A_GATEONLY=$(aplumb 'the gate without its ledger' "$A_PRE" crates/trust-thir-lower/src/lib.rs 'fn main() {}' \
  scripts/check_revert_rationale.sh '# the gate')
rrcheck 1 'is missing at the pushed tip' 'RR9f a tip that ships the GATE without its ledger is REFUSED even at an anchor without the ledger' \
  "refs/heads/gate-only $A_GATEONLY refs/heads/gate-only $ZERO" "$A_ARCH_DEST"

# --------------------------------------------------- fails CLOSED, never green
out=$( ( cd "$TMP" && bash "$CHECKER" HEAD 2>&1 ) ) && fail 'C1: the checker reported success outside a repository'
rc=$?
[ "$rc" -eq 2 ] || fail "C1: expected exit 2 outside a repository, got $rc"
ok 'C1  outside a worktree the checker exits 2, not 0'

if out=$( ( cd "$R" && bash scripts/check_revert_rationale.sh no-such-rev-xyz..HEAD 2>&1 ) ); then
  printf '%s\n' "$out" >&2
  fail 'C2: an unresolvable range reported green'
fi
ok 'C2  an unresolvable range fails closed'

# ------------------------------------------- the shipped ledger is well-formed
if [ "$LANE_PUSH_READING" -eq 1 ]; then
  # Push context: what ships is each pushed tip's committed ledger (above).
  set +e
  s1_out="$(revert_ledger_push_reading "$REPO_ROOT" "$CHECKER" "$LANE_PUSHED_REFS" "$LANE_PUSH_REMOTE")"
  s1_rc=$?
  set -e
  printf '%s\n' "$s1_out"
  if [ "$s1_rc" -eq 2 ]; then
    printf 'check_revert_rationale_test: cannot judge the pushed grandfather ledgers\n' >&2; exit 2
  fi
  [ "$s1_rc" -eq 0 ] || fail 'S1: a pushed tip does not ship the grandfather ledger, holds a malformed row, or adds a row for a revert this push carries and the destination does not already hold'
  ok 'S1  every pushed tip ships a well-formed grandfather ledger and adds no row for a revert it carries unpublished (the checkout'"'"'s copy is not the push)'
else
[ -f "$LEDGER" ] || fail "the shipped grandfather ledger is missing: $LEDGER"
while IFS= read -r row; do
  row="${row%%#*}"
  row="$(printf '%s' "$row" | tr -d '[:space:]')"
  [ -n "$row" ] || continue
  case "$row" in
    [0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f]) ;;
    *) fail "the grandfather ledger holds a row that is not a full sha: $row" ;;
  esac
done <"$LEDGER"
ok 'S1  every shipped grandfather row is a full 40-character sha'
fi

# ------------------------------------------------ the WIRING, end to end
# A checker nothing calls is not a gate. This runs a real `git push` through
# `scripts/hooks-pin/pre-push` — the hook that is actually installed — with the
# PIN lane stubbed green, so the only thing that can decide the push is the
# lane under test.
HOOK="$REPO_ROOT/scripts/hooks-pin/pre-push"
[ -f "$HOOK" ] || fail "the installed pre-push hook is missing: $HOOK"

E="$TMP/e2e"
BARE_REMOTE="$TMP/e2e-remote.git"
# `-b main` is not decoration: every push and every remote read below names
# `main` literally, while a bare `git init` uses the MACHINE's
# `init.defaultBranch` — which git leaves at `master` when nobody sets it.
# On such a clone W0 died with `src refspec main does not match any`, and
# because W0 is the accept control, W1-W3 (the real bare-revert refusal, the
# explained-revert acceptance, and the remote-did-not-move assertion) never
# executed at all. Pin the branch here rather than depend on ambient config.
git init -q --bare -b main "$BARE_REMOTE"
git init -q -b main "$E"
git -C "$E" config user.name test
git -C "$E" config user.email test@example.invalid
git -C "$E" config commit.gpgsign false
mkdir -p "$E/scripts/hooks-pin" "$E/scripts/lib" "$E/crates/trust-thir-lower/src"
cp "$CHECKER" "$E/scripts/check_revert_rationale.sh"
cp "$DESTINATION_LIB" "$E/scripts/lib/push_destination.sh"
cp "$REPO_ROOT/scripts/lib/remote_tips.py" "$REPO_ROOT/scripts/lib/landing_targo.py" "$REPO_ROOT/scripts/lib/remote_operation.py" "$E/scripts/lib/"
# The e2e reverts are new commits no ledger row names, so this copy decides no
# verdict below. Under push context S1 above has already judged every pushed
# tip's ledger and REFUSED a tip that does not ship it (RR9), so the fallback
# is reached only when the pushed trees carry the ledger and only the checkout
# lacks it (an uncommitted deletion, which is not a property of the push).
if [ "$LANE_PUSH_READING" -eq 1 ]; then
  cp "$LEDGER" "$E/scripts/revert-rationale-grandfathered.txt" 2>/dev/null \
    || printf '# fixture ledger\n' >"$E/scripts/revert-rationale-grandfathered.txt"
else
cp "$LEDGER" "$E/scripts/revert-rationale-grandfathered.txt"
fi
cp "$HOOK" "$E/scripts/hooks-pin/pre-push"
printf '#!/usr/bin/env bash\necho "PIN COHERENCE OK (fixture stub)"\nexit 0\n' \
  >"$E/scripts/check_pin_coherence.sh"
# Every OTHER lane hooks-pin runs is stubbed green for the same reason the pin
# lane is: the only thing allowed to decide this push is the lane under test.
# Each of these is fail-closed on a missing file, so an unstubbed one turns W0
# RED for a reason that has nothing to do with reverts — which is exactly what
# happened between 2026-08-25 and 2026-08-27, when the freeze, provenance,
# bridge and cohort lanes were added to the hook and this fixture was not
# updated. W0 is the accept control; when it cannot pass, no later verdict here
# means anything, and W1-W3 never run at all.
printf '#!/usr/bin/env bash\necho "MEASUREMENT PROVENANCE OK (fixture stub)"\nexit 0\n' \
  >"$E/scripts/check_measurement_provenance.sh"
printf '#!/usr/bin/env bash\necho "FREEZE GATE: GREEN (fixture stub)"\nexit 0\n' \
  >"$E/scripts/check_frozen_files.sh"
printf '#!/usr/bin/env bash\necho "BRIDGE PIN OK (fixture stub)"\nexit 0\n' \
  >"$E/scripts/check_bridge_pin.sh"
printf '#!/usr/bin/env python3\nprint("IR COHORT OK (fixture stub)")\n' \
  >"$E/scripts/check_ir_cohort.py"
# Third occurrence of the same class, 2026-08-30 (0fa3d84645, reachability) and
# 2026-09-01 (e4898add77, cfg(test) skew): two more fail-closed lanes, this
# fixture not updated, and W0 read `PRE-PUSH: RED (... reach=1 skew=1)` for
# eleven days while the message this test printed said nothing about either.
printf '#!/usr/bin/env python3\nprint("SUBMODULE REACHABILITY OK (fixture stub)")\n' \
  >"$E/scripts/check_submodule_remote_reachability.py"
printf '#!/usr/bin/env python3\nprint("CFG-TEST SKEW OK (fixture stub)")\n' \
  >"$E/scripts/check_cfg_test_caller_skew.py"
printf '#!/usr/bin/env python3\nprint("RUN-MAKE LEX OK (fixture stub)")\n' \
  >"$E/scripts/check_run_make_fixture_lex.py"
# Fourth occurrence of the same class, 2026-11-11 (367380521e, pin regression):
# a tenth fail-closed lane joined hooks-pin and this fixture was not updated in
# the same change, so the comprehensive fast run's W0 read RED for a reason
# unrelated to reverts. The completeness guard below named the missing stub.
printf '#!/usr/bin/env bash\necho "PIN REGRESSION OK (fixture stub)"\nexit 0\n' \
  >"$E/scripts/check_pin_regression.sh"
: >"$E/scripts/hooks-pin/pin-waivers.txt"
: >"$E/scripts/hooks-pin/ir-cohort-waivers.txt"
chmod +x "$E"/scripts/*.sh "$E"/scripts/*.py "$E/scripts/hooks-pin/pre-push"
# FIXTURE COMPLETENESS, judged against the hook's OWN declarations rather than
# against this file's memory of them. Every lane hooks-pin runs is declared as
# `<NAME>_CHECKER="scripts/<path>"` (or `CHECKER=` for the pin lane), and every
# one of them fails closed on a missing file. So the set of paths the hook names
# minus the lane under test is exactly the set this fixture must stub, and a
# hook that names a path the fixture does not carry is a fixture that will
# refuse W0 for a reason unrelated to reverts. Naming that path HERE turns the
# third recurrence of this class into the last one that reads as a mystery: the
# failure says which stub to add instead of "the green control push was
# refused". This does not auto-stub — a lane added to the hook still has to be
# looked at by a person before this test steps over it.
# `|| true`: under `set -e` a hook with no such declaration would abort inside
# the substitution and never reach the guard below that says so by name.
HOOK_LANES="$(grep -Eo '^[A-Z_]*CHECKER="scripts/[^"]+"' "$HOOK" | sed -E 's/^[A-Z_]*CHECKER="([^"]+)"/\1/' || true)"
[ -n "$HOOK_LANES" ] || fail 'W0-fixture: hooks-pin/pre-push declares no `*_CHECKER="scripts/..."` lane at all; either the hook changed shape or this grep no longer reads it — the fixture cannot prove it stubs every lane'
case "$HOOK_LANES" in
  *'scripts/check_revert_rationale.sh'*) ;;
  *) fail 'W0-fixture: hooks-pin/pre-push no longer declares the lane under test as a checker path' ;;
esac
while IFS= read -r lane; do
  [ -n "$lane" ] || continue
  [ -f "$E/$lane" ] \
    || fail "W0-fixture: hooks-pin/pre-push runs $lane and this fixture does not carry it; that lane fails closed on a missing file, so W0 would be refused for a reason that has nothing to do with reverts — read the lane, then add a green stub for it beside the others above"
done <<<"$HOOK_LANES"
printf 'fn main() {}\n' >"$E/crates/trust-thir-lower/src/lib.rs"
git -C "$E" add -A
git -C "$E" commit -qm fixture
git -C "$E" config core.hooksPath scripts/hooks-pin
git -C "$E" remote add origin "$BARE_REMOTE"
# Keep the hook's output: when W0 is refused, the hook has already printed the
# lane-by-lane verdict that says WHY, and discarding it (as this line did until
# 2026-09-10) left the reader with a one-line refusal and a fixture to bisect.
if ! w0_out="$(git -C "$E" push -q origin main 2>&1)"; then
  printf '%s\n' "$w0_out" >&2
  fail 'W0: the green control push was refused (hook output above), so no later verdict means anything'
fi
ok 'W0  a clean push passes the hook (the accept control for the wiring)'

printf 'fn main() { gate(); }\n' >"$E/crates/trust-thir-lower/src/lib.rs"
git -C "$E" commit -qam 'feat(thir-lower): the STRUCT-INTERIOR offset class is GATED'
git -C "$E" push -q origin main >/dev/null 2>&1 || fail 'W0: the subject push was refused'
E_SUBJECT=$(git -C "$E" rev-parse HEAD)
git -C "$E" revert --no-edit "$E_SUBJECT" >/dev/null

if out=$(git -C "$E" push origin main 2>&1); then
  printf '%s\n' "$out" >&2
  fail 'W1: `git push` of a BARE revert was ACCEPTED by the installed hook'
fi
case "$out" in
  *'a revert that does not say WHY'*) ;;
  *) fail 'W1: the hook refused for some other reason than the missing rationale' ;;
esac
case "$out" in
  *'PIN GATE: GREEN'*) ;;
  *) fail 'W1: the pin lane was not green, so the refusal is not attributable' ;;
esac
remote_head=$(git --git-dir="$BARE_REMOTE" log -1 --format=%H main)
[ "$remote_head" = "$E_SUBJECT" ] || fail 'W1: the bare revert reached the remote anyway'
ok 'W1  a real `git push` of a bare revert is REFUSED and the remote does not move'

if out=$(git -C "$E" push --atomic origin "$E_SUBJECT:refs/heads/aaa-clean" main 2>&1); then
  printf '%s\n' "$out" >&2
  fail 'W1b: an atomic new-branch plus bare-revert push passed the hook'
fi
case "$out" in *'a revert that does not say WHY'*) ;; *) fail 'W1b: the refusal did not name the rationale defect' ;; esac
[ "$(git --git-dir="$BARE_REMOTE" rev-parse main)" = "$E_SUBJECT" ] \
  || fail 'W1b: the bare revert reached remote main'
if git --git-dir="$BARE_REMOTE" show-ref --verify --quiet refs/heads/aaa-clean; then
  fail 'W1b: the refused atomic push created the new branch'
fi
ok 'W1b  an atomic multi-ref push cannot hide a bare revert or change either remote ref'

git -C "$E" commit -q --amend -m "$(git -C "$E" log -1 --format=%s)
This reverts commit ${E_SUBJECT}.

trust-thir-lower --lib is RED at that commit: the zero-displacement ordering
test searches for a literal the widened binding invalidated. The gate itself
looks correct; re-land it once the needle follows the binding."
git -C "$E" push -q origin main >/dev/null 2>&1 \
  || fail 'W2: a revert that states its reason was still refused'
remote_head=$(git --git-dir="$BARE_REMOTE" log -1 --format=%H main)
[ "$remote_head" = "$(git -C "$E" rev-parse HEAD)" ] || fail 'W2: the explained revert did not reach the remote'
ok 'W2  the same revert, with a reason, PUSHES'

# The UPDATE subject through the installed hook. A topic branch is published,
# then main gains a bare revert that reached the remote WITHOUT this hook —
# written in by a fetch, which runs no pre-push, the shape of a bare revert
# already on a real main. Merging main into the topic and pushing the update
# must pass; adding a new bare revert on top must not, and the remote must not
# move.
git -C "$E" checkout -q -b topic
printf 'topic\n' >"$E/topic.txt"
git -C "$E" add topic.txt
git -C "$E" commit -qm 'feat: a topic branch'
E_TOPIC_OLD=$(git -C "$E" rev-parse HEAD)
git -C "$E" push -q origin topic >/dev/null 2>&1 || fail 'W4: the clean topic branch was refused'
git -C "$E" checkout -q main
printf 'pub\n' >"$E/pub.txt"
git -C "$E" add pub.txt
git -C "$E" commit -qm 'feat: a change main later reverts'
git -C "$E" revert --no-edit HEAD >/dev/null
E_PUBREV=$(git -C "$E" rev-parse HEAD)
git --git-dir="$BARE_REMOTE" fetch -q "$E" refs/heads/main:refs/heads/main
[ "$(git --git-dir="$BARE_REMOTE" rev-parse main)" = "$E_PUBREV" ] || fail 'W4-fixture: the published bare revert did not reach remote main'
git -C "$E" checkout -q topic
git -C "$E" merge -q --no-edit main
git -C "$E" merge-base --is-ancestor "$E_PUBREV" HEAD \
  && ! git -C "$E" merge-base --is-ancestor "$E_PUBREV" "$E_TOPIC_OLD" \
  || fail 'W4-fixture: the published revert is not inside the pushed range'
if ! out=$(git -C "$E" push origin topic 2>&1); then
  printf '%s\n' "$out" >&2
  fail 'W4: an update carrying a bare revert already on remote main was refused by the installed hook'
fi
[ "$(git --git-dir="$BARE_REMOTE" rev-parse topic)" = "$(git -C "$E" rev-parse HEAD)" ] \
  || fail 'W4: the accepted update did not reach the remote'
ok 'W4  a real `git push` updating a branch that merged main'"'"'s published bare revert PASSES'

E_TOPIC_MERGED=$(git -C "$E" rev-parse HEAD)
git -C "$E" revert --no-edit "$E_TOPIC_OLD" >/dev/null
if out=$(git -C "$E" push origin topic 2>&1); then
  printf '%s\n' "$out" >&2
  fail 'W5: an update introducing a NEW bare revert was ACCEPTED by the installed hook'
fi
case "$out" in *'a revert that does not say WHY'*) ;; *) fail 'W5: the hook refused for some other reason than the missing rationale' ;; esac
case "$out" in *"$E_PUBREV"*) fail 'W5: the hook blamed the already-published revert' ;; *) ;; esac
[ "$(git --git-dir="$BARE_REMOTE" rev-parse topic)" = "$E_TOPIC_MERGED" ] \
  || fail 'W5: the new bare revert reached the remote anyway'
ok 'W5  a real `git push` of an update introducing a NEW bare revert is REFUSED and the remote does not move'

# A REAL `git push --force` over a destination tip this clone never fetched: git
# itself hands the hook an update line whose remote sha is absent here (F1-F4
# drive the same line by hand). Another clone moves remote main; this one
# rewrites main without fetching and force-pushes.
E_OTHER="$TMP/e2e-other"
git clone -q "$BARE_REMOTE" "$E_OTHER" 2>/dev/null
git -C "$E_OTHER" config user.name other
git -C "$E_OTHER" config user.email other@example.invalid
git -C "$E_OTHER" config commit.gpgsign false
eother() {  # <file>: commit on the other clone's main and publish it
  git -C "$E_OTHER" fetch -q origin
  git -C "$E_OTHER" checkout -q -B main origin/main
  printf '%s\n' "$1" >"$E_OTHER/$1"
  git -C "$E_OTHER" add "$1"
  git -C "$E_OTHER" commit -qm "other: $1, never fetched by the pushing clone"
  git -C "$E_OTHER" push -q origin main
  git -C "$E_OTHER" rev-parse HEAD
}
E_ABSENT=$(eother theirs1.txt)
git -C "$E" cat-file -e "${E_ABSENT}^{commit}" 2>/dev/null \
  && fail 'W6-fixture: the pushing clone already holds the destination tip, so W6 proves nothing'
git -C "$E" checkout -q main
printf 'mine\n' >"$E/mine.txt"
git -C "$E" add mine.txt
git -C "$E" commit -qm 'feat: my rewritten main, no revert anywhere'
if out=$(git -C "$E" push --force origin main 2>&1); then
  fail 'W6u: a force push with unreadable destination main was accepted'
fi
case "$out" in *'destination main original commit is unavailable'*) ;; *)
  printf '%s\n' "$out" >&2
  fail 'W6u: the hook did not preserve the unavailable-main refusal'
esac
[ "$(git --git-dir="$BARE_REMOTE" rev-parse main)" = "$E_ABSENT" ] \
  || fail 'W6u: the refused force push moved the destination'
ok 'W6u unavailable destination main refuses before any publication'
git -C "$E" fetch -q --no-write-fetch-head --no-tags --refmap= "$BARE_REMOTE" "$E_ABSENT"
if ! out=$(git -C "$E" push --force origin main 2>&1); then
  printf '%s\n' "$out" >&2
  fail 'W6: a clean `git push --force` over the acquired destination tip was refused by the installed hook'
fi
[ "$(git --git-dir="$BARE_REMOTE" rev-parse main)" = "$(git -C "$E" rev-parse HEAD)" ] \
  || fail 'W6: the accepted force push did not reach the remote'
ok 'W6  a real clean `git push --force` over a destination tip this clone has now acquired PASSES'

E_ABSENT=$(eother theirs2.txt)
git -C "$E" cat-file -e "${E_ABSENT}^{commit}" 2>/dev/null \
  && fail 'W7-fixture: the pushing clone already holds the destination tip, so W7 proves nothing'
git -C "$E" fetch -q --no-write-fetch-head --no-tags --refmap= "$BARE_REMOTE" "$E_ABSENT"
git -C "$E" revert --no-edit HEAD >/dev/null
E_FORCEREV=$(git -C "$E" rev-parse HEAD)
if out=$(git -C "$E" push --force origin main 2>&1); then
  printf '%s\n' "$out" >&2
  fail 'W7: a `git push --force` of a bare revert over the acquired tip was ACCEPTED by the installed hook'
fi
case "$out" in *'a revert that does not say WHY'*) ;; *) printf '%s\n' "$out" >&2; fail 'W7: the hook refused for some other reason than the missing rationale' ;; esac
case "$out" in *"$E_FORCEREV"*) ;; *) fail 'W7: the refusal did not name the bare revert' ;; esac
[ "$(git --git-dir="$BARE_REMOTE" rev-parse main)" = "$E_ABSENT" ] \
  || fail 'W7: the bare revert reached the remote anyway'
ok 'W7  a real `git push --force` of a bare revert over the acquired tip is REFUSED and the remote does not move'

# The e2e above stubs the pin lane, so it cannot see a wiring deletion in the
# OTHER hook. Both are pinned at the source — but at DIFFERENT sources, because
# since 2026-08-27 they are wired differently. hooks-pin names the checker
# literally. scripts/hooks/pre-push declares NO lanes and derives them from the
# manifest's `push` profile, so what must be pinned there is the row plus the
# export the row reads. That is strictly stronger than the old grep: a literal
# in the hook body only proved a string was present, while the profile listing
# is the list the hook will actually execute.
[ -f "$REPO_ROOT/scripts/hooks-pin/pre-push" ] || fail 'W3: scripts/hooks-pin/pre-push is missing'
grep -q 'check_revert_rationale.sh' "$REPO_ROOT/scripts/hooks-pin/pre-push" \
  || fail 'W3: scripts/hooks-pin/pre-push no longer calls the checker'
grep -q 'revert_rc' "$REPO_ROOT/scripts/hooks-pin/pre-push" \
  || fail 'W3: scripts/hooks-pin/pre-push no longer folds the lane verdict into its exit'
[ -f "$REPO_ROOT/scripts/hooks/pre-push" ] || fail 'W3: scripts/hooks/pre-push is missing'
PUSH_LANES="$(cd "$REPO_ROOT" && bash tests/run_trust_comprehensive_harness.sh --list push)" \
  || fail 'W3: the harness cannot list the push profile the full hook derives its lanes from'
case "$PUSH_LANES" in
  *"check_revert_rationale.sh --push-context"*) ;;
  *) fail 'W3: no `push` manifest row runs the checker with --push-context, so the full hook either skips it or judges history instead of the push' ;;
esac
# ANCHORED, not a substring: `#export TRUST_PUSHED_REFS=` satisfied the loose
# grep while the hook silently widened all three push-context lanes to history —
# measured 2026-08-27, `fast.pin-regression` then reported PASS on a push
# carrying a real backward pin move, which is exactly what this guard exists to
# stop. A guard that its own failure mode slips past is not a guard.
grep -Eq '^[[:space:]]*export[[:space:]]+TRUST_PUSHED_REFS=' "$REPO_ROOT/scripts/hooks/pre-push" \
  || fail 'W3: scripts/hooks/pre-push no longer exports the refs --push-context reads; the lane would silently widen to history and still report GREEN'
# BEHAVIOURAL half: the source text above proves wiring exists, not that it WORKS.
# Drive the real checker the way the hook drives it and require it to say so.
# No `| head`: closing the pipe early SIGPIPEs the checker, and under `pipefail`
# that surfaces as a 141 on a CLEAN tree (measured while writing this).
W3_OUT="$(TRUST_PUSHED_REFS="refs/heads/main $(git -C "$REPO_ROOT" rev-parse HEAD) refs/heads/main $(git -C "$REPO_ROOT" rev-parse HEAD~1)" \
  bash "$REPO_ROOT/scripts/check_revert_rationale.sh" --push-context 2>&1 || true)"
W3_SUBJECT="${W3_OUT%%$'\n'*}"
case "$W3_SUBJECT" in
  "SUBJECT: push"*) ;;
  *) fail "W3: --push-context did not read TRUST_PUSHED_REFS (got: $W3_SUBJECT); the lane would judge history, not the push" ;;
esac
ok 'W3  hooks-pin calls the checker and folds its verdict; the full hook derives a --push-context row, exports the refs that row reads, and the checker demonstrably reads them'

printf 'check_revert_rationale_test: %d checks passed\n' "$PASSED"
