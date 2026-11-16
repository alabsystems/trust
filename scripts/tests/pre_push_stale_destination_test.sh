#!/usr/bin/env bash
# End-to-end test of scripts/hooks/pre-push's STALE-DESTINATION stop, through
# real `git push`es to a bare remote.
#
# git sends each update with the remote sha it read before the hook started,
# and the remote refuses the update once that ref has moved. Before each
# `scoped.` lane the hook re-reads the pushed refs on the destination (`git
# ls-remote`) and, when one has moved, stops with `PRE-PUSH: STALE` instead of
# spending the remaining lanes on a push that cannot land (the hook header,
# "A DESTINATION THAT MOVED DOOMS THE PUSH").
#
# The fixture repo carries a COPY of the real hook and a stand-in harness whose
# `--list push` names two fast lanes and three scoped lanes. `mover` lanes play
# another machine landing on the destination mid-hook when FIXTURE_MOVE_IN names
# their tier, on every ref FIXTURE_REF lists; `fast.red` fails when FIXTURE_RED
# is set; `scoped.last` leaves a marker file, so "the hook stopped before it" is
# observable. `scoped.hide` and `scoped.mover` make the destination unreadable
# and readable again, for the case the check must NOT stop on. The hook stops
# only when EVERY pushed update moved, and never hides a lane that already
# FAILED: those are the multi-ref and red cases.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
HOOK="$REPO_ROOT/scripts/hooks/pre-push"
[ -f "$HOOK" ] || { echo "pre-push stale-destination tests: no $HOOK" >&2; exit 2; }

# A push hook running this test must not hand the fixtures its own push.
unset TRUST_PUSHED_REFS TRUST_PUSH_REMOTE FIXTURE_MOVE_IN FIXTURE_HIDE FIXTURE_RED
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@example.invalid
export GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@example.invalid
export TRUST_PRE_PUSH_SHADOW=0
unset GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE

TMP="$(mktemp -d)" || exit 2
trap 'chmod -R u+rwx "${TMP:?}" 2>/dev/null; rm -rf "${TMP:?}"' EXIT

FAILED=0
pass() { echo "  ok   $1"; }
fail() { echo "  FAIL $1"; FAILED=1; }

# mover: another machine's commit lands on each of the destination's $FIXTURE_REF.
cat > "$TMP/mover.sh" <<'EOF'
#!/usr/bin/env bash
[ "${FIXTURE_MOVE_IN:-}" = "$1" ] || exit 0
other="$FIXTURE_OTHER"
for ref in $FIXTURE_REF; do
  git -C "$other" fetch -q origin 2>/dev/null
  git -C "$other" checkout -q -B mover "origin/${ref#refs/heads/}" 2>/dev/null \
    || git -C "$other" checkout -q -B mover origin/main
  echo "$1 $ref" >> "$other/landed-elsewhere.txt"
  git -C "$other" add -A && git -C "$other" commit -qm "landed elsewhere during the hook"
  git -C "$other" push -q --no-verify origin "mover:$ref"
done
EOF

T="$TMP/template"
mkdir -p "$T/scripts/hooks" "$T/tests/trust-comprehensive"
cp "$HOOK" "$T/scripts/hooks/pre-push" && chmod +x "$T/scripts/hooks/pre-push"
printf '# quarantine ledger (fixture)\n' > "$T/tests/trust-comprehensive/divergences.toml"
cat > "$T/tests/run_trust_comprehensive_harness.sh" <<EOF
#!/usr/bin/env bash
[ "\${1:-}" = "--list" ] || exit 0
printf '%s\t%s\t%s\t%s\t%s\n' fast.red fixture true 2026-09-29 '[ -z "\${FIXTURE_RED:-}" ]'
printf '%s\t%s\t%s\t%s\t%s\n' fast.mover fixture true 2026-09-29 'bash "$TMP/mover.sh" fast'
printf '%s\t%s\t%s\t%s\t%s\n' scoped.hide fixture true 2026-09-29 'if [ -n "\${FIXTURE_HIDE:-}" ]; then chmod 000 "\$FIXTURE_HIDE"; fi'
printf '%s\t%s\t%s\t%s\t%s\n' scoped.mover fixture true 2026-09-29 'if [ -n "\${FIXTURE_HIDE:-}" ]; then chmod 755 "\$FIXTURE_HIDE"; fi; bash "$TMP/mover.sh" scoped'
printf '%s\t%s\t%s\t%s\t%s\n' scoped.last fixture true 2026-09-29 'touch "\$FIXTURE_MARK"'
EOF
git -C "$T" init -q -b main
git -C "$T" config core.hooksPath scripts/hooks
git -C "$T" add -A && git -C "$T" commit -qm template

# new_case <name>: W a fresh copy of the template, R a bare `origin` holding its
# main (pushed with --no-verify: the base is not under test), and the other
# machine's clone of R.
new_case() {
  echo "-- $1"
  W="$TMP/$1"; R="$TMP/$1.git"
  cp -R "$T" "$W"
  git init -q --bare "$R"
  git -C "$W" remote add origin "$R"
  git -C "$W" push -q --no-verify origin main >/dev/null 2>&1 || fail "$1: base push"
  git clone -q "$R" "$TMP/$1.other" 2>/dev/null
  export FIXTURE_OTHER="$TMP/$1.other" FIXTURE_MARK="$TMP/$1.last-ran" FIXTURE_REF=refs/heads/main
  echo "work" > "$W/work.txt" && git -C "$W" add -A && git -C "$W" commit -qm work
}

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
# A here-string, not `printf | grep -q`: under pipefail, grep -q exiting at its
# first match can fail the printf still writing the rest of a long $OUT (EPIPE,
# or SIGPIPE), so saw read a present line as missing and not_saw passed it.
saw() {
  if grep -qE -- "$2" <<<"$OUT"; then pass "$1"; else
    fail "$1: output lacks /$2/"; printf '%s\n' "$OUT" | sed 's/^/        /' | tail -25
  fi
}
not_saw() {
  if grep -qE -- "$2" <<<"$OUT"; then
    fail "$1: output has /$2/"; printf '%s\n' "$OUT" | sed 's/^/        /' | tail -25
  else pass "$1"; fi
}
last_ran() { if [ -e "$FIXTURE_MARK" ]; then pass "$1"; else fail "$1"; fi; }
last_skipped() { if [ -e "$FIXTURE_MARK" ]; then fail "$1"; else pass "$1"; fi; }

echo "== control: a destination that stays put"
new_case still
attempt "still" pushed main && saw "every lane runs and the push lands" "^PRE-PUSH: GREEN$"
last_ran "the last scoped lane ran"
not_saw "no STALE stop" "STALE"

echo "== the destination moves mid-hook"
new_case moved-in-scoped-tier
FIXTURE_MOVE_IN=scoped attempt "moved during a scoped lane" refused main && {
  saw "the hook stops with STALE" "^PRE-PUSH: STALE — every ref this push updates moved on the destination"
  saw "naming the ref and both shas" "refs/heads/main: the push expects [0-9a-f]{40}, the remote now has [0-9a-f]{40}"
  saw "and says the remote would refuse it, in git's words" "\(fetch first\)"
  not_saw "and reaches no verdict" "^PRE-PUSH: (GREEN|RED)"
}
last_skipped "the scoped lane after the move never ran"

new_case moved-in-fast-tier
FIXTURE_MOVE_IN=fast attempt "moved during a fast lane" refused main \
  && saw "the check before the first scoped lane stops it" "^PRE-PUSH: STALE"
not_saw "no scoped lane ran" "^=== scoped\."
last_skipped "the last scoped lane never ran"

new_case created-meanwhile
export FIXTURE_REF=refs/heads/topic
git -C "$W" checkout -q -b topic
FIXTURE_MOVE_IN=scoped attempt "a new branch someone else created meanwhile" refused topic \
  && saw "a create whose ref now exists is stale too" "the push expects no ref, the remote now has [0-9a-f]{40}"

echo "== a lane that already FAILED is never hidden by the stop"
new_case red-and-moved
FIXTURE_RED=1 FIXTURE_MOVE_IN=fast attempt "a red fast lane, then the destination moves" refused main && {
  saw "the red lane is named" "^FAIL: fast\.red$"
  saw "the verdict is RED, which a lander stops on" "^PRE-PUSH: RED"
  not_saw "not a STALE retry" "^PRE-PUSH: STALE"
  saw "the moved ref is still named" "refs/heads/main: the push expects"
}
last_skipped "the scoped lanes were not run"

echo "== a push of two refs stops only when both moved"
two_refs() {
  git -C "$W" push -q --no-verify origin main~1:refs/heads/topic >/dev/null 2>&1 || fail "$1: base topic"
  git -C "$W" branch topic main
}
new_case one-of-two-moved
two_refs one-of-two-moved
FIXTURE_MOVE_IN=scoped attempt "main moves, topic does not" refused main topic && {
  not_saw "one update can still land, so no STALE stop" "STALE"
  saw "the hook judges on to a verdict" "^PRE-PUSH: GREEN$"
}
last_ran "the last scoped lane ran"
if [ "$(git -C "$R" rev-parse refs/heads/topic)" = "$(git -C "$W" rev-parse topic)" ]; then
  pass "the update that could land, landed"
else
  fail "topic did not land"
fi

new_case both-moved
two_refs both-moved
export FIXTURE_REF="refs/heads/main refs/heads/topic"
FIXTURE_MOVE_IN=scoped attempt "main and topic both move" refused main topic && {
  saw "every update is doomed, so STALE" "^PRE-PUSH: STALE"
  saw "main is named" "refs/heads/main: the push expects"
  saw "topic is named" "refs/heads/topic: the push expects"
}
last_skipped "the last scoped lane never ran"

echo "== a destination the check cannot read is no reason to stop"
new_case unreadable
FIXTURE_HIDE="$R" attempt "unreadable, then readable again" pushed main && {
  saw "the unreadable destination is said out loud" "could not read the destination's refs"
  saw "and the hook carries on to a verdict" "^PRE-PUSH: GREEN$"
}
last_ran "the last scoped lane ran"

echo
if [ "$FAILED" -ne 0 ]; then
  echo "pre-push stale-destination tests: FAILED"
  exit 1
fi
echo "pre-push stale-destination tests: all passed"
