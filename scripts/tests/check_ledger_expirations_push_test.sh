#!/usr/bin/env bash
# Self-test for scripts/check_ledger_expirations.py's PUSH reading.
#
# docs/issues/2026-09-28-push-lanes-judge-the-checkout-not-the-push.md, case L:
# `fast.ledger-expirations` read the seven ledgers from the working tree, so a
# pushed tree carrying an expired exception passed whenever the checkout did not
# carry it (a non-HEAD ref; HEAD with the renewal uncommitted; the ledger file
# deleted locally, which walk_ledger reads as EMPTY), and a clean push was
# refused over an uncommitted expiry edit. Under TRUST_PUSHED_REFS the gate must
# judge each pushed tree from git objects and never the working tree; with the
# variable unset it must keep reading the working tree.
#
# Every arm runs on a throwaway git repo holding a copy of the gate (the gate
# finds its ledgers relative to its own file), with TRUST_PUSHED_REFS written
# the way git hands the pre-push hook its stdin.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
GATE="$REPO_ROOT/scripts/check_ledger_expirations.py"
[ -f "$GATE" ] || { echo "check_ledger_expirations push tests: no $GATE" >&2; exit 2; }

PYTHON_BIN=""
for candidate in python3.14 python3.13 python3.12 python3.11 python3 python; do
  if command -v "$candidate" >/dev/null 2>&1; then PYTHON_BIN="$candidate"; break; fi
done
[ -n "$PYTHON_BIN" ] || { echo "check_ledger_expirations push tests: no python3" >&2; exit 2; }

unset TRUST_PUSHED_REFS
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@example.invalid
export GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@example.invalid
unset GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE

TMP="$(mktemp -d)" || exit 2
trap 'rm -rf "${TMP:?}"' EXIT

FAILED=0
pass() { echo "  ok   $1"; }
fail() { echo "  FAIL $1"; FAILED=1; }
ZERO=0000000000000000000000000000000000000000

LEDGER_PATHS="tests/upstream-rust/test-exceptions.toml
tests/upstream-rust/exceptions.toml
tests/upstream-rust/divergence-audit.toml
tests/upstream-rust/patches.toml
tests/upstream-rust/upstream-fixes.toml
tests/trust-comprehensive/divergences.toml
tests/trust-added/compiletest-exceptions.toml"

# A repo whose every ledger is healthy: one active exception expiring in 2099.
W="$TMP/w"
mkdir -p "$W/scripts" "$W/tests/upstream-rust" "$W/tests/trust-comprehensive" "$W/tests/trust-added"
cp "$GATE" "$W/scripts/check_ledger_expirations.py"
printf 'exceptions = []\n' > "$W/tests/upstream-rust/exceptions.toml"
printf 'items = []\n' > "$W/tests/upstream-rust/divergence-audit.toml"
printf 'patches = []\n' > "$W/tests/upstream-rust/patches.toml"
printf 'fixes = []\n' > "$W/tests/upstream-rust/upstream-fixes.toml"
printf 'divergences = []\n' > "$W/tests/trust-comprehensive/divergences.toml"
printf 'exceptions = []\n' > "$W/tests/trust-added/compiletest-exceptions.toml"
printf 'entries = []\n' > "$W/tests/upstream-rust/baseline.toml"
EXC="$W/tests/upstream-rust/test-exceptions.toml"
printf '[[exceptions]]\nid = "keep"\nstatus = "active"\nexpires_on = "2099-12-31"\n' > "$EXC"
git -C "$W" init -q -b main
git -C "$W" add -A && git -C "$W" commit -qm good
GOOD="$(git -C "$W" rev-parse HEAD)"
# `bad` carries an exception that expired on 2026-01-01.
git -C "$W" checkout -q -b bad
printf '\n[[exceptions]]\nid = "stale.exception"\nstatus = "active"\nexpires_on = "2026-01-01"\n' >> "$EXC"
git -C "$W" commit -qam 'an expired exception'
BAD="$(git -C "$W" rev-parse HEAD)"
git -C "$W" checkout -q main

# run <label> <pushed-refs> [gate args...]: the gate with that push context,
# from inside the repo, leaving OUT/RC.
run() {
  local refs="$1"; shift
  OUT="$( cd "$W" && TRUST_PUSHED_REFS="$refs" "$PYTHON_BIN" scripts/check_ledger_expirations.py --warn-days 14 "$@" 2>&1 )"
  RC=$?
}
expect() {  # expect <label> <rc> [grep-pattern]
  if [ "$RC" -ne "$2" ]; then fail "$1: exit $RC, expected $2"; printf '%s\n' "$OUT" | sed 's/^/        /' | head -30; return; fi
  if [ -n "${3:-}" ] && ! printf '%s\n' "$OUT" | grep -qE -- "$3"; then
    fail "$1: output lacks /$3/"; printf '%s\n' "$OUT" | sed 's/^/        /' | head -30; return
  fi
  pass "$1"
}

echo "== 1. standing reading (TRUST_PUSHED_REFS unset): the working tree, as before"
run ""
expect "clean worktree at main is green, no SUBJECT line" 0 "expired: +0"
printf '%s\n' "$OUT" | grep -q '^SUBJECT:' && fail "standing reading printed a SUBJECT line"
git -C "$W" checkout -q bad
run ""
expect "worktree at bad is red" 1 "stale\.exception"
git -C "$W" checkout -q main

echo "== 2. case L (1a): a non-HEAD ref carrying an expired exception"
run "refs/heads/bad $BAD refs/heads/main $GOOD"
expect "pushing bad:main from a clean main is refused" 1 "stale\.exception"
expect "  ... and it names the subject" 1 "^SUBJECT: the pushed trees \(TRUST_PUSHED_REFS: refs/heads/bad "
# The red is keyed, so the pre-push hook can compare it with the destination's
# (INHERITED grading, docs/DECISION_QUEUE.md INHERITED-RED).
expect "  ... keyed: FINDING: EXPIRED <ledger> <id> <date>" 1 \
  "^FINDING: EXPIRED tests/upstream-rust/test-exceptions\.toml stale\.exception 2026-01-01$"
expect "  ... and every cause is keyed: FINDINGS: complete" 1 "^FINDINGS: complete$"

echo "== 3. case L (1b): HEAD is bad, the renewal is only on disk"
git -C "$W" checkout -q bad
sed -i.bak 's/2026-01-01/2099-01-01/' "$EXC" && rm -f "$EXC.bak"
run "refs/heads/bad $BAD refs/heads/main $GOOD"
expect "an uncommitted renewal does not renew the pushed row" 1 "stale\.exception"
git -C "$W" checkout -q -- .
rm -f "$EXC"
run "refs/heads/bad $BAD refs/heads/main $GOOD"
expect "a ledger deleted locally is still read from the pushed tree" 1 "stale\.exception"
git -C "$W" checkout -q -- . && git -C "$W" checkout -q main

echo "== 4. case L (1c): an expired quarantine row committed, renewed only on disk"
DIV="$W/tests/trust-comprehensive/divergences.toml"
git -C "$W" checkout -q -b quarantine main
printf '[[divergences]]\nid = "q.red"\ngate_id = "fast.red"\nstatus = "active"\nexpires_on = "2026-01-01"\n' > "$DIV"
git -C "$W" commit -qam 'an expired quarantine row'
QEXP="$(git -C "$W" rev-parse HEAD)"
sed -i.bak 's/2026-01-01/2099-01-01/' "$DIV" && rm -f "$DIV.bak"
run "refs/heads/quarantine $QEXP refs/heads/main $GOOD"
expect "the committed expiry is judged, not the local renewal" 1 "q\.red"
git -C "$W" checkout -q -- . && git -C "$W" checkout -q main

echo "== 5. block-good: WIP the push does not publish"
printf '\n[[exceptions]]\nid = "wip.expired"\nstatus = "active"\nexpires_on = "2026-01-01"\n' >> "$EXC"
run "refs/heads/main $GOOD refs/heads/main $ZERO"
expect "an uncommitted expired row does not refuse a clean push" 0 "expired: +0"
git -C "$W" checkout -q -- .
printf '# expires_on = "2099-01-01"\n' >> "$W/tests/upstream-rust/baseline.toml"
run "refs/heads/main $GOOD refs/heads/main $ZERO"
expect "an uncommitted expires_on in the exempt baseline does not refuse" 0
git -C "$W" checkout -q -- .
printf 'this is [not toml\n' > "$DIV"
run "refs/heads/main $GOOD refs/heads/main $ZERO"
expect "a half-written local ledger does not refuse a clean push" 0
git -C "$W" checkout -q -- .

echo "== 6. a ledger the pushed tree lacks is named, not read as empty"
git -C "$W" checkout -q -b missing main
git -C "$W" rm -q tests/trust-added/compiletest-exceptions.toml
git -C "$W" commit -qm 'drop a ledger'
MISSING="$(git -C "$W" rev-parse HEAD)"
git -C "$W" checkout -q main
run "refs/heads/missing $MISSING refs/heads/main $GOOD"
expect "a missing walked ledger fails" 1 "^  • tests/trust-added/compiletest-exceptions\.toml$"
expect "  ... keyed: FINDING: MISSING <ledger>" 1 "^FINDING: MISSING tests/trust-added/compiletest-exceptions\.toml$"
git -C "$W" checkout -q -b noexempt main
git -C "$W" rm -q tests/upstream-rust/baseline.toml
git -C "$W" commit -qm 'drop the exempt file'
NOEXEMPT="$(git -C "$W" rev-parse HEAD)"
git -C "$W" checkout -q main
run "refs/heads/noexempt $NOEXEMPT refs/heads/main $GOOD"
expect "a missing exempt file fails, as on disk" 1 "baseline\.toml: exempt file is missing"

echo "== 7. unreadable pushed ledgers fail, naming the path"
git -C "$W" checkout -q -b garbled main
printf 'this is [not toml\n' > "$DIV"
git -C "$W" commit -qam 'garbled ledger'
GARBLED="$(git -C "$W" rev-parse HEAD)"
git -C "$W" checkout -q main
run "refs/heads/garbled $GARBLED refs/heads/main $GOOD"
expect "a non-TOML pushed ledger fails" 1 "divergences\.toml: not TOML"
if printf '%s\n' "$OUT" | grep -q '^FINDINGS: complete$'; then
  fail "an unreadable ledger (an unkeyed cause) printed FINDINGS: complete"
else
  pass "  ... an unreadable ledger is unkeyed: no FINDINGS: complete"
fi
# A keyed cause beside an unkeyed one: the key is printed, the marker is not,
# so the hook cannot grade the unreadable half as a red main already has.
git -C "$W" checkout -q -b garbled-bad bad
printf 'this is [not toml\n' > "$DIV"
git -C "$W" commit -qam 'garbled ledger beside an expired row'
GARBLED_BAD="$(git -C "$W" rev-parse HEAD)"
git -C "$W" checkout -q main
run "refs/heads/garbled-bad $GARBLED_BAD refs/heads/main $GOOD"
expect "an expired row beside an unreadable ledger fails, keying the row" 1 \
  "^FINDING: EXPIRED tests/upstream-rust/test-exceptions\.toml stale\.exception 2026-01-01$"
if printf '%s\n' "$OUT" | grep -q '^FINDINGS: complete$'; then
  fail "a keyed and an unkeyed cause together printed FINDINGS: complete"
else
  pass "  ... and withholds FINDINGS: complete (one cause is unkeyed)"
fi
git -C "$W" checkout -q -b linked main
rm "$DIV" && ln -s ../upstream-rust/exceptions.toml "$DIV"
git -C "$W" add -A && git -C "$W" commit -qm 'ledger as a symlink'
LINKED="$(git -C "$W" rev-parse HEAD)"
git -C "$W" checkout -q main
run "refs/heads/linked $LINKED refs/heads/main $GOOD"
expect "a symlinked pushed ledger is not silently followed" 1 "not a regular file"
run "refs/heads/ghost 1111111111111111111111111111111111111111 refs/heads/main $GOOD"
expect "a pushed sha this clone cannot read is not a pass" 1 "does not name a tree"

echo "== 8. every pushed tree is judged; deletions judge nothing"
run "refs/heads/main $GOOD refs/heads/main $ZERO
refs/heads/bad $BAD refs/heads/bad $ZERO"
expect "a good and a bad ref in one push is refused" 1 "stale\.exception"
run "refs/heads/main $GOOD refs/heads/main $ZERO
refs/heads/quarantine $GOOD refs/heads/quarantine $ZERO"
expect "refs sharing a tree are judged once" 0 "=== refs/heads/main [0-9a-f]{12}, refs/heads/quarantine "
run "(delete) $ZERO refs/heads/bad $BAD"
expect "a deletion-only push prints SKIPPED" 0 "^SKIPPED: "
run "(delete) $ZERO refs/heads/old $BAD
refs/heads/main $GOOD refs/heads/main $ZERO"
expect "a deletion beside a good ref is not judged" 0 "1 deletion\(s\) not judged"

echo "== 9. malformed push context is exit 2"
run "not a ref line"
expect "a malformed line" 2 "malformed TRUST_PUSHED_REFS line"
run "refs/heads/main $GOOD refs/heads/main"
expect "a three-field line" 2 "malformed TRUST_PUSHED_REFS line"

echo "== 10. --json and --strict-warn under push context"
run "refs/heads/bad $BAD refs/heads/main $GOOD" --json
if [ "$RC" -eq 1 ] && printf '%s\n' "$OUT" | "$PYTHON_BIN" -c '
import json, sys
d = json.load(sys.stdin)
t = d["trees"][0]
assert d["skipped"] is False and t["report"]["summary"]["expired"] == 1, d
assert t["missing_ledgers"] == [] and t["unreadable_ledgers"] == [], t
'; then pass "--json reports each pushed tree"; else fail "--json under push context (exit $RC)"; fi
git -C "$W" checkout -q -b soon main
printf '\n[[exceptions]]\nid = "soon"\nstatus = "active"\nexpires_on = "%s"\n' \
  "$("$PYTHON_BIN" -c 'import datetime; print(datetime.date.today() + datetime.timedelta(days=3))')" >> "$EXC"
git -C "$W" commit -qam 'expiring soon'
SOON="$(git -C "$W" rev-parse HEAD)"
git -C "$W" checkout -q main
run "refs/heads/soon $SOON refs/heads/main $GOOD" --strict-warn
expect "--strict-warn on an expiring pushed row is exit 2" 2 "EXPIRING within 14 days"
run "refs/heads/soon $SOON refs/heads/main $GOOD"
expect "without --strict-warn it is a warning" 0 "EXPIRING within 14 days"

echo
if [ "$FAILED" -ne 0 ]; then
  echo "check_ledger_expirations push tests: FAILED"
  exit 1
fi
echo "check_ledger_expirations push tests: all passed"
