#!/usr/bin/env bash
# End-to-end test of scripts/hooks/pre-push's QUARANTINE lookup, through real
# `git push`es to a bare remote.
#
# docs/issues/2026-09-28-push-lanes-judge-the-checkout-not-the-push.md, case H:
# the hook read tests/trust-comprehensive/divergences.toml from the WORKTREE, so
# an uncommitted row shielded a red required lane in a push whose tree carried
# no such row (1a), a row committed on HEAD shielded a push of another ref (1e),
# and an expired committed row renewed only on disk shielded it too (L 1c). In a
# push the ledger now comes from git objects: a red lane is QUARANTINED only if
# an active, unexpired row for it is in every pushed tree AND on the destination
# tip each update starts from; a green lane is refused if any pushed tree
# publishes a row for it; deletion-only pushes quarantine nothing. With nothing
# on stdin (no push) the hook keeps reading the worktree.
#
# The fixture repo carries a COPY of the real hook and of
# scripts/check_ledger_expirations.py, and a stand-in harness whose `--list push`
# names two required lanes: `fast.red`, red unless FIXTURE_LANE_GREEN=1 (a lane
# that judges nothing about the push, the shape a quarantine row shields), and
# the real `fast.ledger-expirations` command.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
HOOK="$REPO_ROOT/scripts/hooks/pre-push"
LEDGER_GATE="$REPO_ROOT/scripts/check_ledger_expirations.py"
for f in "$HOOK" "$LEDGER_GATE"; do
  [ -f "$f" ] || { echo "pre-push quarantine tests: no $f" >&2; exit 2; }
done

PYTHON_BIN=""
for candidate in python3.14 python3.13 python3.12 python3.11 python3 python; do
  if command -v "$candidate" >/dev/null 2>&1; then PYTHON_BIN="$candidate"; break; fi
done
[ -n "$PYTHON_BIN" ] || { echo "pre-push quarantine tests: no python3" >&2; exit 2; }
PYTHON_BIN="$(command -v "$PYTHON_BIN")"

# A push hook running this test must not hand the fixtures its own push.
unset TRUST_PUSHED_REFS TRUST_PUSH_REMOTE FIXTURE_LANE_GREEN
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@example.invalid
export GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@example.invalid
unset GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE

TMP="$(mktemp -d)" || exit 2
trap 'rm -rf "${TMP:?}"' EXIT

FAILED=0
pass() { echo "  ok   $1"; }
fail() { echo "  FAIL $1"; FAILED=1; }

DIVREL="tests/trust-comprehensive/divergences.toml"

# The template every case copies: all ledgers healthy, no quarantine row.
T="$TMP/template"
mkdir -p "$T/scripts/hooks" "$T/tests/upstream-rust" "$T/tests/trust-comprehensive" "$T/tests/trust-added"
cp "$HOOK" "$T/scripts/hooks/pre-push" && chmod +x "$T/scripts/hooks/pre-push"
cp "$LEDGER_GATE" "$T/scripts/check_ledger_expirations.py"
printf 'exceptions = []\n' > "$T/tests/upstream-rust/test-exceptions.toml"
printf 'exceptions = []\n' > "$T/tests/upstream-rust/exceptions.toml"
printf 'items = []\n' > "$T/tests/upstream-rust/divergence-audit.toml"
printf 'patches = []\n' > "$T/tests/upstream-rust/patches.toml"
printf 'fixes = []\n' > "$T/tests/upstream-rust/upstream-fixes.toml"
printf 'exceptions = []\n' > "$T/tests/trust-added/compiletest-exceptions.toml"
printf 'entries = []\n' > "$T/tests/upstream-rust/baseline.toml"
printf '# quarantine ledger (fixture)\n' > "$T/$DIVREL"
cat > "$T/tests/run_trust_comprehensive_harness.sh" <<EOF
#!/usr/bin/env bash
[ "\${1:-}" = "--list" ] || exit 0
printf '%s\t%s\t%s\t%s\t%s\n' fast.red fixture true 2026-09-28 'test "\${FIXTURE_LANE_GREEN:-0}" = 1'
printf '%s\t%s\t%s\t%s\t%s\n' fast.ledger-expirations ledger true 2026-09-28 '$PYTHON_BIN scripts/check_ledger_expirations.py --warn-days 14'
EOF
git -C "$T" init -q -b main
git -C "$T" config core.hooksPath scripts/hooks
git -C "$T" add -A && git -C "$T" commit -qm template

# row <gate> <expires_on>: one quarantine row, appended to the ledger.
row() {
  printf '\n[[divergences]]\nid = "q.%s"\ngate_id = "%s"\nstatus = "active"\nowner = "@t"\nexpires_on = "%s"\nrequired_action = "fix %s"\n' \
    "$1" "$1" "$2" "$1"
}

# new_case <name>: W is a fresh copy of the template, `origin` a fresh bare repo
# holding its main (pushed with --no-verify: the base is not under test).
new_case() {
  echo "-- $1"
  W="$TMP/$1"; R="$TMP/$1.git"
  cp -R "$T" "$W"
  git init -q --bare "$R"
  git -C "$W" remote add origin "$R"
}
base_push() { git -C "$W" push -q --no-verify origin "$@" >/dev/null 2>&1 || { fail "base push $*"; return 1; }; }
commit() { git -C "$W" add -A && git -C "$W" commit -qm "$1"; }

# attempt <label> <pushed|refused> <refspec...>: a real push through the hook.
attempt() {
  local label="$1" want="$2"; shift 2
  OUT="$(git -C "$W" push origin "$@" 2>&1)"
  local rc=$?
  if [ "$want" = pushed ] && [ "$rc" -ne 0 ]; then
    fail "$label: push refused (exit $rc), expected it to land"; printf '%s\n' "$OUT" | sed 's/^/        /' | tail -25; return 1
  fi
  if [ "$want" = refused ] && [ "$rc" -eq 0 ]; then
    fail "$label: push LANDED, expected a refusal"; printf '%s\n' "$OUT" | sed 's/^/        /' | tail -25; return 1
  fi
  return 0
}
# saw <label> <ERE>: the last attempt's output matches.
# A here-string, not `printf | grep -q`: under pipefail, grep -q exiting at its
# first match can fail the printf still writing the rest of a long $OUT (EPIPE,
# or SIGPIPE), and saw read a present line as missing.
saw() {
  if grep -qE -- "$2" <<<"$OUT"; then pass "$1"; else
    fail "$1: output lacks /$2/"; printf '%s\n' "$OUT" | sed 's/^/        /' | tail -25
  fi
}

echo "== case H: the audit reproducers"
new_case h1a-uncommitted-row
base_push main
echo "work" > "$W/work.txt"; commit work
row fast.red 2099-12-31 >> "$W/$DIVREL"
attempt "1a" refused main && saw "1a: an uncommitted row shields nothing" "^FAIL: fast\.red$"

new_case h1e-row-on-head-other-ref
base_push main
git -C "$W" checkout -q -b topic && echo "work" > "$W/work.txt" && commit work
git -C "$W" checkout -q main && row fast.red 2099-12-31 >> "$W/$DIVREL" && commit 'row on HEAD'
attempt "1e" refused topic:main && saw "1e: a row committed on HEAD does not shield another ref" "^FAIL: fast\.red$"

new_case h1c-expired-row-renewed-locally
row fast.red 2026-01-01 >> "$W/$DIVREL" && commit 'expired row' && base_push main
echo "work" > "$W/work.txt"; commit work
sed -i.bak 's/2026-01-01/2099-12-31/' "$W/$DIVREL" && rm -f "$W/$DIVREL.bak"
attempt "1c" refused main && {
  saw "1c: the committed expiry is read, not the local renewal" "^FAIL: fast\.red$"
  saw "1c: fast.ledger-expirations judges the pushed row expired too" "^FAIL: fast\.ledger-expirations$"
}

echo "== what a row still does"
new_case shield-on-destination
row fast.red 2099-12-31 >> "$W/$DIVREL" && commit 'row' && base_push main
echo "work" > "$W/work.txt"; commit work
attempt "a row on the destination and the pushed tree shields" pushed main \
  && saw "the lane reports QUARANTINED with the row" "q\.fast\.red :: expires 2099-12-31 :: fix fast\.red"

new_case self-authored-shield
base_push main
echo "work" > "$W/work.txt"; row fast.red 2099-12-31 >> "$W/$DIVREL"; commit 'break and shield'
attempt "self-authored" refused main \
  && saw "a push cannot author its own quarantine" "Not quarantined: the row is not active on the destination refs/heads/main"

new_case renewal-of-expired-destination-row
row fast.red 2026-01-01 >> "$W/$DIVREL" && commit 'expired row' && base_push main
sed -i.bak 's/2026-01-01/2099-12-31/' "$W/$DIVREL" && rm -f "$W/$DIVREL.bak"
echo "work" > "$W/work.txt"; commit 'renew and work'
attempt "renewal" refused main \
  && saw "renewing an expired row is authoring a shield" "^FAIL: fast\.red$"

new_case stale-row-published
row fast.red 2099-12-31 >> "$W/$DIVREL" && commit 'row' && base_push main
echo "work" > "$W/work.txt"; commit work
FIXTURE_LANE_GREEN=1 attempt "stale" refused main \
  && saw "a green lane with a published row is refused" "^FAIL: fast\.red is GREEN but still quarantined\.$"

new_case stale-row-added-by-push
base_push main
row fast.red 2099-12-31 >> "$W/$DIVREL"; commit 'row for a green lane'
FIXTURE_LANE_GREEN=1 attempt "stale-added" refused main \
  && saw "a row the push adds for a green lane is still stale" "GREEN but still quarantined"

new_case row-removed-by-push
row fast.red 2099-12-31 >> "$W/$DIVREL" && commit 'row' && base_push main
printf 'divergences = []\n' > "$W/$DIVREL"; commit 'fixed; drop the row'
FIXTURE_LANE_GREEN=1 attempt "removed" pushed main && saw "dropping the row with the fix is green" "^PASS: fast\.red$"

echo "== block-good: local state the push does not publish"
new_case wip-row-green-lane
base_push main
echo "work" > "$W/work.txt"; commit work
row fast.red 2099-12-31 >> "$W/$DIVREL"
FIXTURE_LANE_GREEN=1 attempt "wip-row" pushed main && saw "an uncommitted row does not refuse a green push" "^PASS: fast\.red$"

new_case wip-half-written-ledger
base_push main
echo "work" > "$W/work.txt"; commit work
printf 'this is [not toml\n' > "$W/$DIVREL"
FIXTURE_LANE_GREEN=1 attempt "half-written" pushed main && saw "a half-written local ledger does not refuse" "^PRE-PUSH: GREEN$"

echo "== unreadable, multi-ref, create, deletion, unknown destination"
new_case unreadable-pushed-ledger
base_push main
printf 'this is [not toml\n' > "$W/$DIVREL"; commit 'garbled ledger'
FIXTURE_LANE_GREEN=1 attempt "unreadable" refused main \
  && saw "an unreadable pushed ledger refuses every lane" "cannot read $DIVREL from the pushed trees"

new_case multi-ref-not-in-every-tree
row fast.red 2099-12-31 >> "$W/$DIVREL" && commit 'row' && base_push main
git -C "$W" checkout -q -b t2 && printf 'divergences = []\n' > "$W/$DIVREL" && echo w > "$W/w" && commit 'drop row'
git -C "$W" checkout -q main && echo w > "$W/w" && commit work
attempt "multi-ref" refused main t2 \
  && saw "a row must be in every pushed tree" "Not quarantined: the row is not active in every pushed tree"

new_case create-has-no-destination
row fast.red 2099-12-31 >> "$W/$DIVREL"; echo w > "$W/w"; commit 'row and work'
attempt "create" pushed main \
  && saw "a create has no destination tip: the pushed tree decides" "^QUARANTINED: fast\.red"

new_case deletion-only
row fast.red 2099-12-31 >> "$W/$DIVREL" && commit 'row' && base_push main main:refs/heads/topic
attempt "deletion red" refused :topic \
  && saw "a deletion-only push quarantines nothing" "deletion\(s\) only"
FIXTURE_LANE_GREEN=1 attempt "deletion green" pushed :topic && pass "a deletion with green lanes lands"

new_case destination-not-held-here
row fast.red 2099-12-31 >> "$W/$DIVREL" && commit 'row' && base_push main
git clone -q -b main "$R" "$TMP/other" && echo x > "$TMP/other/x" && git -C "$TMP/other" add -A \
  && git -C "$TMP/other" commit -qm other && git -C "$TMP/other" push -q --no-verify origin main 2>/dev/null
echo "work" > "$W/work.txt"; commit work
attempt "unknown destination" refused --force main \
  && saw "a destination tip this clone lacks shields nothing" "Not quarantined: the destination refs/heads/main [0-9a-f]{12} cannot be read here"

echo "== the standing reading (nothing on stdin) still reads the worktree"
new_case standing
echo "work" > "$W/work.txt"; commit work
row fast.red 2099-12-31 >> "$W/$DIVREL"
OUT="$(cd "$W" && bash scripts/hooks/pre-push origin "$R" </dev/null 2>&1)"; rc=$?
if [ "$rc" -eq 0 ]; then saw "no push context: the worktree row shields, as before" "^QUARANTINED: fast\.red"
else fail "standing reading: exit $rc"; printf '%s\n' "$OUT" | sed 's/^/        /' | tail -20; fi

echo
if [ "$FAILED" -ne 0 ]; then
  echo "pre-push quarantine tests: FAILED"
  exit 1
fi
echo "pre-push quarantine tests: all passed"
