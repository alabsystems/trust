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
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

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
grep -q 'selftest: 12 passed, 0 failed' "$TMP/o" \
  || { cat "$TMP/o" >&2; fail "the selftest case count moved; a case was added or lost silently"; }
ok "the gate's own --selftest: 12 passed, 0 failed"

# THE RATCHET. The grandfather list may only shrink. Adding a row for a NEW
# commit is the same act as deleting the gate.
GF_MAX=5
gf_count=$(grep -cE '^[0-9a-f]{40}$' "$LEDGER" || true)
[ "$gf_count" -le "$GF_MAX" ] \
  || fail "the grandfather ledger GREW to $gf_count rows (ceiling $GF_MAX). A commit that cannot stamp must be amended, not excused."
ok "grandfather ledger holds $gf_count/$GF_MAX rows (may only shrink)"

# A malformed row must be INERT, never a wildcard.
grep -vE '^[0-9a-f]{40}$' "$LEDGER" | grep -vE '^[[:space:]]*(#.*)?$' >"$TMP/junk" || true
[ ! -s "$TMP/junk" ] || { cat "$TMP/junk" >&2; fail "the ledger carries rows that are neither a comment nor a 40-hex sha"; }
ok "every ledger row is a comment or a full 40-hex sha"

printf 'check_measurement_provenance_test: %d checks passed\n' "$PASSED"
