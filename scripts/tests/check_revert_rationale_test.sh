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
LEDGER="$REPO_ROOT/scripts/revert-rationale-grandfathered.txt"
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

PASSED=0
fail() { printf 'check_revert_rationale_test: %s\n' "$*" >&2; exit 1; }
ok()   { PASSED=$((PASSED + 1)); printf '  ok  %s\n' "$*"; }

[ -x "$CHECKER" ] || fail "checker is missing or not executable: $CHECKER"

R="$TMP/repo"
git init -q "$R"
git -C "$R" config user.name test
git -C "$R" config user.email test@example.invalid
git -C "$R" config commit.gpgsign false
mkdir -p "$R/scripts" "$R/crates/trust-thir-lower/src"
cp "$CHECKER" "$R/scripts/check_revert_rationale.sh"
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
mkdir -p "$E/scripts/hooks-pin" "$E/crates/trust-thir-lower/src"
cp "$CHECKER" "$E/scripts/check_revert_rationale.sh"
cp "$LEDGER" "$E/scripts/revert-rationale-grandfathered.txt"
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
: >"$E/scripts/hooks-pin/pin-waivers.txt"
: >"$E/scripts/hooks-pin/ir-cohort-waivers.txt"
chmod +x "$E"/scripts/*.sh "$E/scripts/check_ir_cohort.py" "$E/scripts/hooks-pin/pre-push"
printf 'fn main() {}\n' >"$E/crates/trust-thir-lower/src/lib.rs"
git -C "$E" add -A
git -C "$E" commit -qm fixture
git -C "$E" config core.hooksPath scripts/hooks-pin
git -C "$E" remote add origin "$BARE_REMOTE"
git -C "$E" push -q origin main >/dev/null 2>&1 \
  || fail 'W0: the green control push was refused, so no later verdict means anything'
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
