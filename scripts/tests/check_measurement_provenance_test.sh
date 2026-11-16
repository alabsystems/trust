#!/usr/bin/env bash
# The mutation proof for the measurement-provenance gate.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# THE PROPERTY UNDER TEST is the one the RCA said could not be mechanised: that
# a measurement published about a tree it was not taken on is REJECTABLE. Every
# case runs against a real throwaway repository with real `git hash-object`
# blobs, because the assertion is about blob identity, not about a string this
# test invents.
#
# A provenance gate that passes on a dirty tree is worse than none, so the
# negative controls come first and each has its accept control beside it.
set -euo pipefail

REPO_ROOT=$(cd -P "${BASH_SOURCE[0]%/*}/../.." && pwd -P)
CHECKER="$REPO_ROOT/scripts/check_measurement_provenance.sh"
HELPER="$REPO_ROOT/scripts/lib/measure_stamp.sh"
LEDGER="$REPO_ROOT/scripts/measurement-provenance-grandfathered.txt"
LEDGER_REL="scripts/measurement-provenance-grandfathered.txt"
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

# PUSH CONTEXT is this lane's, not the fixtures'. scripts/hooks/pre-push exports
# TRUST_PUSHED_REFS (and TRUST_PUSH_REMOTE) to every row; the fixture arms below
# drive the checker on throwaway repositories and must not inherit a real
# push's refs. Captured here for section 5, then removed from the environment.
LANE_PUSH_READING=0
[ -z "${TRUST_PUSHED_REFS+x}" ] || LANE_PUSH_READING=1
LANE_PUSHED_REFS="${TRUST_PUSHED_REFS-}"
LANE_PUSH_REMOTE="${TRUST_PUSH_REMOTE-}"
unset TRUST_PUSHED_REFS TRUST_PUSH_REMOTE

PASSED=0
fail() { printf 'check_measurement_provenance_test: %s\n' "$*" >&2; exit 1; }
ok()   { PASSED=$((PASSED + 1)); printf '  ok  %s\n' "$*"; }

[ -x "$CHECKER" ] || fail "checker is missing or not executable: $CHECKER"
[ -f "$HELPER" ]  || fail "helper is missing: $HELPER"

# ===========================================================================
# 1. The helper must be sourceable from every shell the lane runners use.
#    Measured 2026-08-20: of the in-flight lane runners, some are `#!/bin/bash`
#    and some are `#!/bin/zsh`. A helper that only works in bash is a helper
#    half the fleet cannot adopt, and adoption is the entire problem.
# ===========================================================================
R="$TMP/repo"
git init -q "$R"
git -C "$R" config user.name test
git -C "$R" config user.email test@example.invalid
git -C "$R" config commit.gpgsign false
mkdir -p "$R/crates/trust-thir-lower/src"
SRC=crates/trust-thir-lower/src/lib.rs
printf 'fn f() { let off = q(); }\n' >"$R/$SRC"
git -C "$R" add -A
git -C "$R" commit -qm 'fixture: a soundness-gate path'

for sh in bash zsh sh; do
  command -v "$sh" >/dev/null 2>&1 || { printf '  --  %s not installed; skipped\n' "$sh"; continue; }
  out=$( cd "$R" && "$sh" -c ". '$HELPER'; measure_stamp $SRC" 2>&1 ) \
    || fail "helper failed when sourced from $sh"
  case "$out" in
    *"=== MEASURE-STAMP v1"*"--- trailer  Measured-on: $SRC@"*) ok "helper sources and stamps under $sh" ;;
    *) printf '%s\n' "$out" >&2; fail "helper produced no usable stamp under $sh" ;;
  esac
done

# Executed rather than sourced, which is the retrofit's one-line form.
out=$( cd "$R" && bash "$HELPER" "$SRC" ) || fail "helper failed when executed"
case "$out" in *"--- file     $SRC"*" clean"*) ok "helper reports a clean path as clean" ;;
  *) printf '%s\n' "$out" >&2; fail "helper mislabelled a clean path" ;; esac

# --- a DIRECTORY is stamped as a git tree, so one line names a whole crate ---
out=$( cd "$R" && bash "$HELPER" crates/trust-thir-lower/src ) || fail "helper failed on a directory"
HEADTREE=$(git -C "$R" rev-parse 'HEAD:crates/trust-thir-lower/src')
case "$out" in
  *"--- file     crates/trust-thir-lower/src worktree=$HEADTREE head=$HEADTREE clean"*)
    ok "helper stamps a clean DIRECTORY as its git tree ($(printf '%.10s' "$HEADTREE"))" ;;
  *) printf '%s\n' "$out" >&2; fail "directory stamp did not resolve to the HEAD tree" ;;
esac
# The throwaway index must never touch the real one.
[ -z "$(git -C "$R" diff --cached --name-only)" ] || fail "stamping a directory STAGED something in the real index"
ok "stamping a directory leaves the real index untouched"

# ===========================================================================
# 2. THE LOG GATE. This is the literal deliverable: a published measurement is
#    rejectable when its log carries no stamp, or when the stamp shows dirt.
# ===========================================================================
printf 'test result: ok. 599 passed; 0 failed\n' >"$TMP/nostamp.log"
if ( cd "$R" && bash "$CHECKER" --log "$TMP/nostamp.log" >"$TMP/o" 2>&1 ); then
  cat "$TMP/o" >&2; fail "an UNSTAMPED log was accepted — the gate does not gate"
fi
grep -q 'NO PROVENANCE STAMP' "$TMP/o" || { cat "$TMP/o" >&2; fail "refusal does not name the reason"; }
ok "log with no stamp -> REJECTED, and the refusal says why"

{ ( cd "$R" && bash "$HELPER" "$SRC" ); printf 'test result: ok. 599 passed; 0 failed\n'; } >"$TMP/clean.log"
( cd "$R" && bash "$CHECKER" --log "$TMP/clean.log" >"$TMP/o" 2>&1 ) \
  || { cat "$TMP/o" >&2; fail "a stamped log on a CLEAN tree was rejected"; }
ok "log stamped on a clean tree -> accepted"

# --- THE INCIDENT, replayed byte for byte -----------------------------------
# 2026-08-19 22:47:17: the file was edited and never `git add`ed; the suite was
# then run against that edit. The run was real. The tree was never committed.
printf 'fn f() { let (off, off_source) = q(); }\n' >"$R/$SRC"
MEASURED=$(git -C "$R" hash-object "$R/$SRC")
COMMITTED=$(git -C "$R" rev-parse "HEAD:$SRC")
[ "$MEASURED" != "$COMMITTED" ] || fail "fixture did not actually dirty the tree"
{ ( cd "$R" && bash "$HELPER" "$SRC" ); printf 'test result: ok. 599 passed; 0 failed\n'; } >"$TMP/dirty.log"
if ( cd "$R" && bash "$CHECKER" --log "$TMP/dirty.log" >"$TMP/o" 2>&1 ); then
  cat "$TMP/o" >&2
  fail "A LOG MEASURED ON AN UNCOMMITTED EDIT WAS ACCEPTED. This is the exact defect."
fi
grep -q 'DIFFER FROM HEAD' "$TMP/o" || { cat "$TMP/o" >&2; fail "refusal does not name the dirt"; }
ok "THE INCIDENT: log measured on an uncommitted edit -> REJECTED"

# A stamp is never confused for a clean one when it could not be taken at all.
printf '=== MEASURE-STAMP v1 UNSTAMPABLE\n--- reason   not inside a git worktree\n=== END MEASURE-STAMP v1\n' >"$TMP/unstampable.log"
if ( cd "$R" && bash "$CHECKER" --log "$TMP/unstampable.log" >"$TMP/o" 2>&1 ); then
  cat "$TMP/o" >&2; fail "an UNSTAMPABLE log was accepted"
fi
ok "log whose stamp says UNSTAMPABLE -> REJECTED"

# A stamp that names no path measures nothing in particular.
{ ( cd "$R" && bash "$HELPER" ); printf '599 passed\n'; } >"$TMP/nopath.log"
if ( cd "$R" && bash "$CHECKER" --log "$TMP/nopath.log" >"$TMP/o" 2>&1 ); then
  cat "$TMP/o" >&2; fail "a stamp declaring NO measured path was accepted"
fi
ok "stamp with no declared path -> REJECTED"

# An empty scan is not a pass.
set +e
( cd "$R" && bash "$CHECKER" --log >"$TMP/o" 2>&1 ); rc=$?
set -e
[ "$rc" -eq 2 ] || { cat "$TMP/o" >&2; fail "an empty --log scan returned $rc, not 2"; }
ok "empty --log scan -> exit 2 (fails closed, never green)"

# ===========================================================================
# 3. R1 — A STAMP THAT LIES IS A REFUSED PUSH. The half the RCA called
#    unenforceable, and the reason it is not: a claim about a blob is checkable
#    against the commit that carries it.
# ===========================================================================
git -C "$R" checkout -q -- "$SRC"
git -C "$R" commit -q --allow-empty -m "feat(thir-lower): the offset class is GATED

599 passed, 0 failed, 12 of them this lane's.

Measured-on: $SRC@$MEASURED
"
if ( cd "$R" && bash "$CHECKER" 'HEAD~1..HEAD' >"$TMP/o" 2>&1 ); then
  cat "$TMP/o" >&2
  fail "A COMMIT PUBLISHING A MEASUREMENT OF A TREE IT DOES NOT CARRY WAS ACCEPTED."
fi
grep -q 'DIFFERENT TREE' "$TMP/o" || { cat "$TMP/o" >&2; fail "R1 refusal does not name the disagreement"; }
grep -q "$COMMITTED" "$TMP/o" || { cat "$TMP/o" >&2; fail "R1 refusal does not print the blob the commit actually carries"; }
ok "R1: trailer names blob $(printf '%.10s' "$MEASURED"), commit carries $(printf '%.10s' "$COMMITTED") -> REJECTED"

git -C "$R" commit -q --amend --allow-empty -m "feat(thir-lower): the offset class is GATED

599 passed, 0 failed.

Measured-on: $SRC@$COMMITTED
"
( cd "$R" && bash "$CHECKER" 'HEAD~1..HEAD' >"$TMP/o" 2>&1 ) \
  || { cat "$TMP/o" >&2; fail "a TRUTHFUL stamp was rejected"; }
ok "R1: the same commit stamped truthfully -> GREEN"

# R1 is vacuous where nothing is claimed, which is what makes it safe to apply
# to all of history with no epoch and no waiver list.
git -C "$R" commit -q --allow-empty -m 'chore: nothing claimed here'
( cd "$R" && bash "$CHECKER" 'HEAD~1..HEAD' >"$TMP/o" 2>&1 ) \
  || { cat "$TMP/o" >&2; fail "R1 condemned a commit that makes no claim"; }
ok "R1 is vacuous on a commit carrying no trailer"

# ===========================================================================
# 4. R2 — a soundness-gate commit quoting a count must name a tree.
# ===========================================================================
printf 'fn f() { let off = q(); /* v2 */ }\n' >"$R/$SRC"
git -C "$R" add -A
git -C "$R" commit -qm 'fix(thir-lower): tighten it

The crate suite is 599 passed, 0 failed at this tree.
'
if ( cd "$R" && bash "$CHECKER" 'HEAD~1..HEAD' >"$TMP/o" 2>&1 ); then
  cat "$TMP/o" >&2; fail "R2: an unstamped soundness-gate claim was accepted"
fi
grep -q 'FAIL (R2)' "$TMP/o" || { cat "$TMP/o" >&2; fail "R2 refusal not attributed to R2"; }
ok "R2: soundness-gate commit quoting a count, unstamped -> REJECTED"

git -C "$R" commit -q --amend -m "fix(thir-lower): tighten it

The crate suite is 599 passed, 0 failed at this tree.

Measured-on: $SRC@$(git -C "$R" hash-object "$R/$SRC")
"
( cd "$R" && bash "$CHECKER" 'HEAD~1..HEAD' >"$TMP/o" 2>&1 ) \
  || { cat "$TMP/o" >&2; fail "R2: a truthfully stamped commit was rejected"; }
ok "R2: the same commit, stamped truthfully -> GREEN"

# The documented gap, asserted so it stays documented rather than drifting into
# a belief that R2 covers everything. See WHAT REMAINS CONVENTIONAL in the gate.
mkdir -p "$R/docs" && printf 'notes\n' >"$R/docs/n.md"
git -C "$R" add -A
git -C "$R" commit -qm 'docs: notes

1234 passed, 0 failed somewhere else entirely.
'
( cd "$R" && bash "$CHECKER" 'HEAD~1..HEAD' >"$TMP/o" 2>&1 ) \
  || { cat "$TMP/o" >&2; fail "R2 reached outside the soundness paths; the header says it does not"; }
ok "R2 does NOT reach a claim outside the soundness paths (the documented gap, asserted)"

# ===========================================================================
# 5. The gate's own selftest, and the ratchet on the grandfather ledger.
# ===========================================================================
bash "$CHECKER" --selftest >"$TMP/o" 2>&1 || { cat "$TMP/o" >&2; fail "the gate's --selftest is red"; }
grep -q 'selftest: 19 passed, 0 failed' "$TMP/o" \
  || { cat "$TMP/o" >&2; fail "the selftest case count moved; a case was added or lost silently"; }
ok "the gate's own --selftest: 19 passed, 0 failed"

# THE RATCHET. The grandfather list may only shrink. Adding a row for a NEW
# commit is the same act as deleting the gate.
GF_MAX=5

# THE RATCHET UNDER PUSH CONTEXT. A push publishes its pushed trees' ledgers,
# not this checkout's, so with TRUST_PUSHED_REFS set every non-deletion pushed
# tip's COMMITTED ledger is judged, and the worktree copy is not read at all
# (docs/issues/2026-09-28-push-lanes-judge-the-checkout-not-the-push.md, case
# M: a non-HEAD ref growing the ledger to 6 rows plus a malformed row passed,
# and an uncommitted row refused a clean push). "May only shrink" is judged as
# what it says — rows(tip) ⊆ rows(anchor), the anchor being the tree the gate
# itself takes its waivers from (`--waiver-anchors`: the destination's tip, or
# the merge-base with its main; none means an empty set) — so a committed SWAP,
# which keeps the count at 5, is refused. The GF_MAX ceiling and the row lint
# still apply to each tip, so this reading refuses everything the count did. A
# pushed tip that does not SHIP the ledger is refused, as the standing reading
# refuses a checkout without it (differential F10); a missing ledger at the
# ANCHOR is zero rows. Stderr of the anchor lookup goes to a file, never into
# the anchor lines (a noisy ssh transport made a clean new-branch push exit 2).
# Prints its findings; returns 0 (holds), 1 (violated) or 2 (cannot judge).
prov_ledger_push_reading() {  # <repo> <pushed-ref lines> <destination or "">
  local repo="$1" refs="$2" remote="$3" anchors tag lsha anchor why entry
  local _mode type oid rc=0 n added gentry aentry
  local args=(--waiver-anchors)
  [ -z "$remote" ] || args+=(--remote "$remote")
  # Stderr goes to a FILE, printed only on failure: a transport's warning (an
  # ssh known_hosts notice) is not an anchor line.
  if ! anchors="$( cd "$repo" && printf '%s\n' "$refs" | bash "$CHECKER" "${args[@]}" 2>"$TMP/rt-anchors.err" )"; then
    printf '  x cannot resolve the waiver anchors: %s\n' "$(cat "$TMP/rt-anchors.err" 2>/dev/null) $anchors"
    return 2
  fi
  if [ -z "$anchors" ]; then
    echo "  -- deletion(s) only: no pushed tree carries a ledger to judge"
    return 0
  fi
  while read -r tag lsha anchor why; do
    [ -n "${tag:-}" ] || continue
    [ "$tag" = ANCHOR ] || { printf '  x unexpected anchor line: %s %s\n' "$tag" "$lsha"; return 2; }
    : >"$TMP/rt-raw"; : >"$TMP/rt-tip"; : >"$TMP/rt-anchor"
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
      if ! gentry="$(git -C "$repo" --no-replace-objects ls-tree "$lsha" -- scripts/check_measurement_provenance.sh 2>/dev/null)"; then
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
    git -C "$repo" --no-replace-objects cat-file blob "$oid" >"$TMP/rt-raw" 2>/dev/null \
      || { printf '  x cannot read %s at %s\n' "$LEDGER_REL" "$lsha"; return 2; }
    awk '{ sub(/#.*/, ""); gsub(/[ \t\r\n]/, ""); if ($0 ~ /^[0-9a-f]{40}$/) print }' "$TMP/rt-raw" \
      | LC_ALL=C sort -u >"$TMP/rt-tip"
    if [ "$anchor" != NONE ]; then
      if ! entry="$(git -C "$repo" --no-replace-objects ls-tree "$anchor" -- "$LEDGER_REL" 2>/dev/null)"; then
        printf '  x cannot read the tree of anchor %s\n' "$anchor"; return 2
      fi
      if [ -n "$entry" ]; then
        read -r _mode type oid _ <<< "$entry"
        if [ "$type" = blob ]; then
          { git -C "$repo" --no-replace-objects cat-file blob "$oid" 2>/dev/null \
              | awk '{ sub(/#.*/, ""); gsub(/[ \t\r\n]/, ""); if ($0 ~ /^[0-9a-f]{40}$/) print }' \
              | LC_ALL=C sort -u >"$TMP/rt-anchor"; } \
            || { printf '  x cannot read %s at anchor %s\n' "$LEDGER_REL" "$anchor"; return 2; }
        fi
      fi
    fi
    n=$(grep -cE '^[0-9a-f]{40}$' "$TMP/rt-raw" || true)
    if [ "$n" -gt "$GF_MAX" ]; then
      printf '  x %.12s: the grandfather ledger GREW to %s rows (ceiling %s)\n' "$lsha" "$n" "$GF_MAX"; rc=1
    fi
    { grep -vE '^[0-9a-f]{40}$' "$TMP/rt-raw" || true; } | { grep -vE '^[[:space:]]*(#.*)?$' || true; } >"$TMP/rt-junk"
    if [ -s "$TMP/rt-junk" ]; then
      printf '  x %.12s: the ledger carries rows that are neither a comment nor a 40-hex sha:\n' "$lsha"
      sed 's/^/        /' "$TMP/rt-junk"; rc=1
    fi
    added="$(LC_ALL=C comm -23 "$TMP/rt-tip" "$TMP/rt-anchor")"
    if [ -n "$added" ]; then
      if [ "$anchor" = NONE ]; then
        printf '  x %.12s: %s, so no row can be carried as already grandfathered:\n' "$lsha" "$why"
      else
        printf '  x %.12s: rows not in the anchor %.12s (%s) — the ledger may only shrink:\n' "$lsha" "$anchor" "$why"
      fi
      printf '%s\n' "$added" | sed 's/^/        /'; rc=1
    fi
    [ "$rc" -ne 0 ] || printf '  -- %.12s: %s row(s), a subset of the anchor %.12s (%s)\n' "$lsha" "$(grep -c . "$TMP/rt-tip" || true)" "$anchor" "$why"
  done <<< "$anchors"
  return "$rc"
}

if [ "$LANE_PUSH_READING" -eq 1 ]; then
  set +e
  prov_ratchet_out="$(prov_ledger_push_reading "$REPO_ROOT" "$LANE_PUSHED_REFS" "$LANE_PUSH_REMOTE")"
  prov_ratchet_rc=$?
  set -e
  printf '%s\n' "$prov_ratchet_out"
  if [ "$prov_ratchet_rc" -eq 2 ]; then
    printf 'check_measurement_provenance_test: cannot judge the pushed ledgers\n' >&2; exit 2
  fi
  [ "$prov_ratchet_rc" -eq 0 ] \
    || fail "a pushed tip does not ship the grandfather ledger, or its ledger is not a subset of its anchor's, grew past $GF_MAX rows, or carries a malformed row. A commit that cannot stamp must be amended, not excused."
  ok "every pushed tip ships a grandfather ledger that is well-formed, within $GF_MAX rows, and a subset of its anchor's (may only shrink; the checkout's copy is not the push)"
else
gf_count=$(grep -cE '^[0-9a-f]{40}$' "$LEDGER" || true)
[ "$gf_count" -le "$GF_MAX" ] \
  || fail "the grandfather ledger GREW to $gf_count rows (ceiling $GF_MAX). A commit that cannot stamp must be amended, not excused."
ok "grandfather ledger holds $gf_count/$GF_MAX rows (may only shrink)"

# A malformed row must be INERT, never a wildcard.
grep -vE '^[0-9a-f]{40}$' "$LEDGER" | grep -vE '^[[:space:]]*(#.*)?$' >"$TMP/junk" || true
[ ! -s "$TMP/junk" ] || { cat "$TMP/junk" >&2; fail "the ledger carries rows that are neither a comment nor a 40-hex sha"; }
ok "every ledger row is a comment or a full 40-hex sha"
fi

# ===========================================================================
# 6. The push-context ratchet, on fixtures (case M). Each arm is a shape the
#    worktree count passed or refused wrongly; the fixture is a real repository
#    with a real destination.
# ===========================================================================
M="$TMP/ratchet"
MDEST="$TMP/ratchet-dest.git"
git init -q -b main "$M"
git init -q --bare -b main "$MDEST"
git -C "$M" config user.name test
git -C "$M" config user.email test@example.invalid
git -C "$M" config commit.gpgsign false
mkdir -p "$M/scripts"
mrows() { local i; for i in "$@"; do printf '%040d\n' "$i"; done; }
mledger() {  # <commit message> <row numbers...>: commit a ledger of exactly those rows
  local msg="$1"; shift
  { printf '# fixture ledger\n'; mrows "$@"; } >"$M/$LEDGER_REL"
  git -C "$M" add -A && git -C "$M" commit -qm "$msg"
  git -C "$M" rev-parse HEAD
}
M_BASE=$(mledger 'five rows' 1 2 3 4 5)
git -C "$M" push -q "$MDEST" "$M_BASE:refs/heads/main"
ZERO=0000000000000000000000000000000000000000
mcheck() {  # <want-rc> <needle> <label> <refs> [destination]: the reason must be NAMED
  local want="$1" needle="$2" label="$3" refs="$4" dest="${5:-}" out rc
  set +e; out="$(prov_ledger_push_reading "$M" "$refs" "$dest")"; rc=$?; set -e
  [ "$rc" -eq "$want" ] || { printf '%s\n' "$out" >&2; fail "$label (want rc=$want, got $rc)"; }
  case "$out" in *"$needle"*) ;; *) printf '%s\n' "$out" >&2; fail "$label (the output does not say '$needle')" ;; esac
  ok "$label"
}

# M1 — the audit case: a NON-HEAD ref growing the ledger to 6 rows plus a
# malformed row. The checkout (at M_BASE, clean) holds 5 well-formed rows, so
# the worktree count passed it.
M_GROW=$( { printf '# fixture ledger\n'; mrows 1 2 3 4 5 6; printf 'not-a-sha\n'; } >"$M/$LEDGER_REL" \
  && git -C "$M" add -A && git -C "$M" commit -qm 'grow to six, plus junk' && git -C "$M" rev-parse HEAD )
git -C "$M" checkout -q "$M_BASE"
mcheck 1 'neither a comment' 'M1  a non-HEAD pushed ref growing the ledger to 6 rows plus a malformed row is REFUSED (the checkout holds 5 clean rows)' \
  "refs/heads/main $M_GROW refs/heads/main $M_BASE" "$MDEST"

# M2 — the committed SWAP: 5 rows, one replaced. The count holds; the set does not.
git -C "$M" checkout -q -B work "$M_BASE"
M_SWAP=$(mledger 'swap row 5 for row 9' 1 2 3 4 9)
mcheck 1 'not in the anchor' 'M2  a committed SWAP (count still 5) is REFUSED: row 9 is not in the anchor' \
  "refs/heads/main $M_SWAP refs/heads/main $M_BASE" "$MDEST"
# ...as a new ref too, anchored at the merge-base with the destination's main.
mcheck 1 'merge-base with the destination' 'M2b the same swap pushed as a NEW ref is REFUSED (anchor: merge-base with destination main)' \
  "refs/heads/topic $M_SWAP refs/heads/topic $ZERO" "$MDEST"

# M3 — the same growth committed on HEAD and reverted only on disk.
git -C "$M" checkout -q -B work "$M_GROW"
{ printf '# fixture ledger\n'; mrows 1 2 3 4 5; } >"$M/$LEDGER_REL"
mcheck 1 'GREW to 6' 'M3  growth committed on HEAD and reverted only on disk is REFUSED (the pushed tip is judged)' \
  "refs/heads/main $M_GROW refs/heads/main $M_BASE" "$MDEST"
git -C "$M" checkout -q -- "$LEDGER_REL"

# M4 — block-good: an uncommitted extra row and a malformed one in the checkout
# do not refuse a clean push.
git -C "$M" checkout -q -B work "$M_BASE"
M_CLEAN=$(printf 'x\n' >"$M/other.txt" && git -C "$M" add other.txt && git -C "$M" commit -qm 'unrelated' && git -C "$M" rev-parse HEAD)
{ printf '# fixture ledger\n'; mrows 1 2 3 4 5 6; printf 'not-a-sha\n'; } >"$M/$LEDGER_REL"
mcheck 0 'a subset of the anchor' 'M4  a clean push is NOT refused over an uncommitted row or a malformed row in the checkout' \
  "refs/heads/main $M_CLEAN refs/heads/main $M_BASE" "$MDEST"
git -C "$M" checkout -q -- "$LEDGER_REL"

# M5 — shrinking is the one direction allowed.
M_SHRINK=$(mledger 'retire row 5' 1 2 3 4)
mcheck 0 '4 row(s), a subset' 'M5  a pushed tip that SHRINKS the ledger holds' \
  "refs/heads/main $M_SHRINK refs/heads/main $M_BASE" "$MDEST"

# M6 — never weaker than the count: an anchor already over the ceiling does not
# license a tip that matches it.
git -C "$M" checkout -q -B over "$M_BASE"
M_OVER=$(mledger 'six rows (over the ceiling)' 1 2 3 4 5 6)
M_OVER2=$(printf 'y\n' >"$M/over.txt" && git -C "$M" add over.txt && git -C "$M" commit -qm 'unrelated' && git -C "$M" rev-parse HEAD)
mcheck 1 'GREW to 6' 'M6  a tip equal to an anchor that is already over the ceiling is still REFUSED by the ceiling' \
  "refs/heads/over $M_OVER2 refs/heads/over $M_OVER" "$MDEST"

# M7 — no anchor, no carried rows: a new ref with no destination to anchor it.
mcheck 1 'NO ANCHOR' 'M7  a new ref with NO anchor (no destination named) cannot carry any row' \
  "refs/heads/topic $M_CLEAN refs/heads/topic $ZERO" ""
M_EMPTY=$(git -C "$M" checkout -q --orphan bare-ledger && git -C "$M" rm -rq --cached . && printf '# none\n' >"$M/$LEDGER_REL" \
  && git -C "$M" add "$LEDGER_REL" && git -C "$M" commit -qm 'an empty ledger' && git -C "$M" rev-parse HEAD)
mcheck 0 '0 row(s), a subset' 'M7b ...and a new ref with no anchor whose ledger carries no row holds' \
  "refs/heads/topic $M_EMPTY refs/heads/topic $ZERO" ""
git -C "$M" checkout -qf main 2>/dev/null || git -C "$M" checkout -qf "$M_BASE"

# M8 — fails closed on what it cannot judge; deletions judge nothing.
mcheck 2 'malformed pushed-ref line' 'M8  a malformed pushed-ref line cannot be judged (exit 2), never green' \
  "refs/heads/main ${M_BASE:0:12} refs/heads/main $M_BASE" "$MDEST"
mcheck 0 'deletion(s) only' 'M8b a deletion-only push judges no ledger' \
  "(delete) $ZERO refs/heads/gone $M_BASE" "$MDEST"

# M9 — a pushed tip that does not ship the ledger is REFUSED (the standing
# reading's count on a missing file refuses too); a ledger path that is not a
# file is the same defect.
git -C "$M" checkout -q -B noledger "$M_BASE"
git -C "$M" rm -q "$LEDGER_REL"
git -C "$M" commit -qm 'drop the grandfather ledger'
M_NOLEDGER=$(git -C "$M" rev-parse HEAD)
mcheck 1 'is missing at the pushed tip' 'M9  a pushed tip WITHOUT the grandfather ledger is REFUSED (the standing reading refuses a checkout without it)' \
  "refs/heads/main $M_NOLEDGER refs/heads/main $M_BASE" "$MDEST"
mkdir -p "$M/$LEDGER_REL"
mrows 1 >"$M/$LEDGER_REL/rows"
git -C "$M" add "$LEDGER_REL/rows"
git -C "$M" commit -qm 'the ledger path is a directory'
M_LEDGERDIR=$(git -C "$M" rev-parse HEAD)
mcheck 1 'is missing at the pushed tip' 'M9b a pushed tip whose ledger path is not a file is REFUSED' \
  "refs/heads/main $M_LEDGERDIR refs/heads/main $M_BASE" "$MDEST"
git -C "$M" checkout -qf "$M_BASE"
# M9c-M9f — an archive/ or salvage/ ref: a new ref at a commit OLDER than the
# gate ships neither the gate nor its ledger. Its missing ledger waives nothing
# and main's lane has no gate to run on a checkout of it: nothing to judge.
# The missing ledger is still REFUSED when any one of these holds (each arm
# isolates one; M9 above is the anchor-ships-it case on the main fixture):
#   M9d  there is no anchor;
#   M9e  the anchor ships the ledger (the push REMOVES it);
#   M9f  the tip ships the gate.
# The commits are built from objects alone, so the worktree is not disturbed.
mplumb() {  # <message> <parent | -> <path> <content> [<path> <content>]...: a commit of exactly these files
  local msg="$1" parent="$2" idx="$TMP/mplumb.idx" blob tree; shift 2
  rm -f "$idx"
  while [ "$#" -ge 2 ]; do
    blob=$(printf '%s\n' "$2" | git -C "$M" hash-object -w --stdin)
    GIT_INDEX_FILE="$idx" git -C "$M" update-index --add --cacheinfo 100644 "$blob" "$1"
    shift 2
  done
  tree=$(GIT_INDEX_FILE="$idx" git -C "$M" write-tree)
  if [ "$parent" = - ]; then
    git -C "$M" commit-tree "$tree" -m "$msg"
  else
    git -C "$M" commit-tree "$tree" -p "$parent" -m "$msg"
  fi
}
MDEST_ARCH="$TMP/ratchet-archive-dest.git"
git init -q --bare -b main "$MDEST_ARCH"
M_PRE=$(mplumb 'prehistory: before the gate' - src/lib.rs 'fn main() {}')
M_PRE_GATE=$(mplumb 'the gate and its ledger land' "$M_PRE" src/lib.rs 'fn main() {}' \
  scripts/check_measurement_provenance.sh '# the gate' "$LEDGER_REL" "$(printf '# fixture ledger\n%040d' 1)")
git -C "$M" push -q "$MDEST_ARCH" "$M_PRE_GATE:refs/heads/main"
M_ARCHIVE=$(mplumb 'archive: work from before the gate' "$M_PRE" src/lib.rs 'fn main() { old(); }')
mcheck 0 'nothing to judge' 'M9c a NEW ref at a commit older than the gate (neither gate nor ledger), anchored at a merge-base without the ledger, passes (archive/salvage refs)' \
  "refs/heads/archive/old $M_ARCHIVE refs/heads/archive/old $ZERO" "$MDEST_ARCH"
mcheck 1 'is missing at the pushed tip' 'M9d the same pre-gate tip with NO anchor is REFUSED' \
  "refs/heads/archive/old $M_ARCHIVE refs/heads/archive/old $ZERO" ""
M_DROPALL=$(mplumb 'drop the gate and its ledger' "$M_PRE_GATE" src/lib.rs 'fn main() {}')
mcheck 1 'is missing at the pushed tip' 'M9e a tip that deletes BOTH the gate and its ledger, anchored at a tree that ships the ledger, is REFUSED' \
  "refs/heads/main $M_DROPALL refs/heads/main $M_PRE_GATE" "$MDEST_ARCH"
M_GATEONLY=$(mplumb 'the gate without its ledger' "$M_PRE" src/lib.rs 'fn main() {}' \
  scripts/check_measurement_provenance.sh '# the gate')
mcheck 1 'is missing at the pushed tip' 'M9f a tip that ships the GATE without its ledger is REFUSED even at an anchor without the ledger' \
  "refs/heads/gate-only $M_GATEONLY refs/heads/gate-only $ZERO" "$MDEST_ARCH"

# M10 — a transport that writes to stderr (an ssh known_hosts notice) is not an
# anchor line: a clean new-branch push over it passes, and the swap still fails.
mkdir -p "$TMP/noisy-ssh"
cat >"$TMP/noisy-ssh/ssh" <<'NOISY'
#!/bin/sh
echo "Warning: Permanently added 'fakehost' (ED25519) to the list of known hosts." >&2
for last in "$@"; do :; done
exec sh -c "$last"
NOISY
chmod +x "$TMP/noisy-ssh/ssh"
mnoisy() {  # <want-rc> <needle> <label> <refs>: mcheck, over the noisy transport
  local want="$1" needle="$2" label="$3" refs="$4" out rc
  set +e
  out="$(GIT_SSH_COMMAND="$TMP/noisy-ssh/ssh" GIT_SSH_VARIANT=simple \
         prov_ledger_push_reading "$M" "$refs" "fakehost:$MDEST")"; rc=$?
  set -e
  [ "$rc" -eq "$want" ] || { printf '%s\n' "$out" >&2; fail "$label (want rc=$want, got $rc)"; }
  case "$out" in *"$needle"*) ;; *) printf '%s\n' "$out" >&2; fail "$label (the output does not say '$needle')" ;; esac
  ok "$label"
}
mnoisy 0 'a subset of the anchor' 'M10  over a transport that writes to STDERR, a clean NEW-branch push passes (stderr is not an anchor line)' \
  "refs/heads/topic $M_CLEAN refs/heads/topic $ZERO"
mnoisy 1 'not in the anchor' 'M10b over the same noisy transport, the committed swap as a new ref is still REFUSED' \
  "refs/heads/topic $M_SWAP refs/heads/topic $ZERO"

# ===========================================================================
# 7. AT COMMIT TIME (docs/DECISION_QUEUE.md PUSH-PATH-COMMIT-MSG): the tracked
#    commit-msg hook runs `--commit-msg` on the commit being made, so R1 and R2
#    refuse before a commit exists rather than at push. Real `git commit`s and
#    a real `git merge` through the real hook, in a fixture carrying the real
#    checker; each refusal has its accept control.
# ===========================================================================
C="$TMP/commit-msg"
mkdir -p "$C/scripts/hooks" "$C/scripts/lib" "$C/crates/trust-thir-lower/src" "$C/docs"
cp "$CHECKER" "$C/scripts/"
cp "$REPO_ROOT/scripts/lib/measure_stamp.sh" "$REPO_ROOT/scripts/lib/push_destination.sh" "$C/scripts/lib/"
cp "$REPO_ROOT/scripts/lib/remote_tips.py" "$REPO_ROOT/scripts/lib/landing_targo.py" "$REPO_ROOT/scripts/lib/remote_operation.py" "$C/scripts/lib/"
cp "$REPO_ROOT/scripts/hooks/commit-msg" "$C/scripts/hooks/"
git init -q -b main "$C"
git -C "$C" config user.name test
git -C "$C" config user.email test@example.invalid
git -C "$C" config commit.gpgsign false
git -C "$C" config core.hooksPath scripts/hooks
printf 'fn gate() {}\n' >"$C/$SRC"
printf 'notes\n' >"$C/docs/notes.md"
git -C "$C" add -A
git -C "$C" commit -q --no-verify -m 'fixture: base'
chead() { git -C "$C" rev-parse HEAD; }
ccommit() {  # ccommit <want-rc> <needle> <label> <git commit args...>: a real commit through the hook
  local want="$1" needle="$2" label="$3" before out rc
  shift 3
  before="$(chead)"
  set +e
  out="$(cd "$C" && git commit -q "$@" 2>&1)"; rc=$?
  set -e
  [ "$rc" -eq "$want" ] || { printf '%s\n' "$out" >&2; fail "$label (want rc=$want, got $rc)"; }
  case "$out" in *"$needle"*) ;; *) printf '%s\n' "$out" >&2; fail "$label (the output does not say '$needle')" ;; esac
  if [ "$want" -ne 0 ] && [ "$(chead)" != "$before" ]; then fail "$label (a refused commit moved HEAD)"; fi
  if [ "$want" -eq 0 ] && [ "$(chead)" = "$before" ]; then fail "$label (an accepted commit did not land)"; fi
  ok "$label"
}

printf 'fn gate() { refuse(); }\n' >"$C/$SRC"
git -C "$C" add "$SRC"
ccommit 1 'measure_stamp.sh' 'CM1  an unstamped count claim on a soundness-gate path is REFUSED at commit, naming the stamp helper' \
  -m 'gate: refuse more' -m '599 passed, 0 failed'
stamp="$(cd "$C" && bash scripts/lib/measure_stamp.sh "$SRC" | sed -n 's/^--- trailer  //p')"
[ -n "$stamp" ] || fail "measure_stamp printed no trailer"
ccommit 0 '' 'CM1b the same commit with the stamp of the staged file commits' \
  -m 'gate: refuse more' -m "599 passed, 0 failed

$stamp"

# R1: the wave-SG shape. The staged blob is not the one measured.
printf 'fn gate() { refuse(); refuse_more(); }\n' >"$C/$SRC"
git -C "$C" add "$SRC"
printf 'fn gate() { refuse(); refuse_more(); edited_after(); }\n' >"$C/$SRC"
wrong="$(cd "$C" && bash scripts/lib/measure_stamp.sh "$SRC" | sed -n 's/^--- trailer  //p')"
ccommit 1 'THE MEASUREMENT IS OF A DIFFERENT TREE' 'CM2  a stamp of an edit never added (the incident) is REFUSED at commit' \
  -m 'gate: refuse more again' -m "1 passed

$wrong"
git -C "$C" add "$SRC"
ccommit 0 '' 'CM2b once the measured edit is staged, the same stamp commits' \
  -m 'gate: refuse more again' -m "1 passed

$wrong"

printf 'more notes\n' >>"$C/docs/notes.md"
git -C "$C" add docs/notes.md
ccommit 0 '' 'CM3  a count claim on a commit that touches no soundness-gate path commits' \
  -m 'docs: notes' -m '12 passed'

# `commit -a` hands the hook a temporary index: the stamp is judged against it.
printf 'fn gate() { refuse(); refuse_more(); edited_after(); x(); }\n' >"$C/$SRC"
ccommit 1 'touches a soundness-gate path' 'CM4  `commit -a` with an unstamped claim is REFUSED (the hook judges the -a index)' \
  -a -m 'gate: x' -m '3 passed'
git -C "$C" checkout -q -- "$SRC"

# An edited message: comments and everything from `commit -v`'s scissors line
# are what git drops, so a claim there is not a claim.
printf 'more\n' >>"$C/docs/notes.md"
printf 'fn gate() { y(); }\n' >"$C/$SRC"
git -C "$C" add -A
cat >"$TMP/cm-editor" <<'ED'
#!/bin/sh
printf 'gate: y\n\n# 5 passed, in a comment git strips\n# ------------------------ >8 ------------------------\n+ 7 passed, 0 failed\n' >"$1"
ED
chmod +x "$TMP/cm-editor"
export GIT_EDITOR="$TMP/cm-editor"
ccommit 0 '' 'CM5  an EDITED message (`commit -v`): claims only in comments and below the scissors line commit' -v
unset GIT_EDITOR
case "$(git -C "$C" log -1 --format=%B)" in *passed*) fail "CM5b git stored a claim the hook did not judge" ;; esac
ok "CM5b git stored neither of those claims, so the hook judged what git stored"

# A --no-ff merge carrying a gate edit: judged against every parent, as -m is.
git -C "$C" checkout -q -b topic
printf 'fn gate() { y(); topic(); }\n' >"$C/$SRC"
git -C "$C" add -A
git -C "$C" commit -q --no-verify -m 'gate: topic' -m "$(cd "$C" && bash scripts/lib/measure_stamp.sh "$SRC" | sed -n 's/^--- trailer  //p')"
git -C "$C" checkout -q main
before="$(chead)"
set +e
out="$(cd "$C" && git merge -q --no-ff topic -m 'Merge topic' -m '42 passed, 0 failed' 2>&1)"; rc=$?
set -e
[ "$rc" -ne 0 ] || { printf '%s\n' "$out" >&2; fail "CM6  a --no-ff merge quoting a count over a gate edit committed"; }
case "$out" in *'touches a soundness-gate path'*) ;; *) printf '%s\n' "$out" >&2; fail "CM6  the merge's refusal does not name R2" ;; esac
[ "$(chead)" = "$before" ] || fail "CM6  the refused merge moved HEAD"
ok "CM6  a --no-ff merge quoting a count over a gate edit is REFUSED (the merge is judged against each parent)"
git -C "$C" merge --abort
set +e
out="$(cd "$C" && git merge -q --no-ff topic -m 'Merge topic' 2>&1)"; rc=$?
set -e
[ "$rc" -eq 0 ] || { printf '%s\n' "$out" >&2; fail "CM6b the merge without a count was refused"; }
[ "$(git -C "$C" rev-parse HEAD^2)" = "$(git -C "$C" rev-parse topic)" ] || fail "CM6b the merge did not land"
ok "CM6b the same merge without the count commits"

# The other direction: main merged INTO a topic carrying a gate edit. Against
# the topic parent the merge changes only main's docs; against main it carries
# the gate edit, so a probe judged against HEAD alone (MERGE_HEAD dropped)
# would pass it.
git -C "$C" checkout -q -b topic2
printf 'fn gate() { y(); topic(); topic2(); }\n' >"$C/$SRC"
git -C "$C" add -A
git -C "$C" commit -q --no-verify -m 'gate: topic2' -m "$(cd "$C" && bash scripts/lib/measure_stamp.sh "$SRC" | sed -n 's/^--- trailer  //p')"
git -C "$C" checkout -q main
printf 'main moved\n' >>"$C/docs/notes.md"
git -C "$C" commit -q --no-verify -am 'docs: main moved'
git -C "$C" checkout -q topic2
before="$(chead)"
set +e
out="$(cd "$C" && git merge -q --no-ff main -m 'Merge main into topic2' -m '42 passed, 0 failed' 2>&1)"; rc=$?
set -e
[ "$rc" -ne 0 ] || { printf '%s\n' "$out" >&2; fail "CM6c merging main into a gate topic with a count committed"; }
case "$out" in *'touches a soundness-gate path'*) ;; *) printf '%s\n' "$out" >&2; fail "CM6c the refusal does not name R2" ;; esac
[ "$(chead)" = "$before" ] || fail "CM6c the refused merge moved HEAD"
ok "CM6c merging main INTO a gate topic with a count is REFUSED (judged against MERGE_HEAD too)"
git -C "$C" merge --abort
git -C "$C" checkout -q main

# A tree whose checker has no --commit-msg mode runs nothing (an older branch).
sed -i.bak 's/--commit-msg)/--commit-message-not-here)/' "$C/scripts/check_measurement_provenance.sh"
rm -f "$C/scripts/check_measurement_provenance.sh.bak"
printf 'fn gate() { z(); }\n' >"$C/$SRC"
git -C "$C" add "$SRC"
ccommit 0 '' 'CM7  a checker without --commit-msg (an older tree) runs nothing at commit; the push still judges' \
  -m 'gate: z' -m '9 passed'

python3 -B "$REPO_ROOT/scripts/tests/measurement_provenance_push_scope_test.py" \
  || fail "push destination and multi-ref regression tests failed"
ok "push scope uses the real destination and preserves every unpublished claim"

printf 'check_measurement_provenance_test: %d checks passed\n' "$PASSED"
