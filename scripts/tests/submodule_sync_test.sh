#!/usr/bin/env bash
# Self-test for scripts/submodule_sync.sh.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# The safety property under test is a single claim: the tool must never offer to
# restore a submodule whose worktree holds a commit that NOTHING ELSE HOLDS. `git
# submodule status` prints one `+` for BEHIND, AHEAD and DIVERGENT alike, and
# acting on that `+` is how unlanded work gets thrown away. So this builds a
# superproject that contains all of those states at once — deliberately, not
# opportunistically — and asserts both the classification AND that `--restore`
# moves exactly the safe ones and leaves every other worktree byte-for-byte
# where it was.
#
# A test that only proved the BEHIND case would prove the wrong half: BEHIND is
# the case where being wrong is harmless.
#
# ANCHORING (2026-08-13). A worktree commit the pin lacks is DESTROYED by a
# checkout only if no durable ref holds it; if one does, restoring is lossless
# and refusing is the tool crying wolf. So the fixture also carries anchored
# AHEAD/DIVERGENT modules (must be restored), a DIVERGENT module with two unique
# commits of which only ONE is anchored (must NOT be restored — "every one" is
# the safety property, and a per-module summary would silently drop the second
# commit), one anchored only by a refs/pins/* ref ON THE REMOTE, and one whose
# remote cannot be read at all (must NOT be restored, fail closed).
#
# The pre-anchoring fixture put m_ahead at donor `main` and m_divergent at donor
# `side` — commits the module's own refs/remotes/origin/* already held. Under the
# anchoring rule those are the SAFE case, so they no longer test what they were
# written to test. Both now hold freshly-made commits that exist on no ref at
# all, which is the shape that actually loses work. Their assertions — state,
# ahead/behind counts, and untouched-by-restore — are unchanged.
#
# --FETCH (fixtures H, I). Pins moved to unfetched commits are PIN-MISSING;
# `--fetch` must fetch exactly those by sha (an anchored-only one included,
# which `fetch --all` misses), create no ref, and leave every restore decision
# to the model above — a fetch that reveals unanchored work restores nothing.

set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SYNC="$ROOT/scripts/submodule_sync.sh"
TMP_ROOT="$(mktemp -d)"
DECOY_PIDS=""
trap 'for p in $DECOY_PIDS; do pkill -P "$p"; kill "$p"; done 2>/dev/null; if [ "${FAILURES:-1}" -eq 0 ]; then rm -rf "$TMP_ROOT"; else printf "retained failed sync fixture: %s\n" "$TMP_ROOT" >&2; fi' EXIT

FAILURES=0
fail() { echo "FAIL: $*" >&2; FAILURES=$((FAILURES + 1)); }
pass() { echo "  ok: $*"; }

if [ ! -x "$SYNC" ] && [ ! -f "$SYNC" ]; then
  echo "FAIL: $SYNC not found" >&2
  exit 1
fi

# Local `file://` submodules are refused by default since git 2.38 (CVE-2022-39253).
# The fixture is entirely inside a fresh mktemp dir, so allowing it here is scoped
# to this process and never touches the user's config.
GIT="git -c protocol.file.allow=always -c advice.detachedHead=false"
export GIT_AUTHOR_NAME="sync-test" GIT_AUTHOR_EMAIL="sync-test@example.invalid"
export GIT_COMMITTER_NAME="sync-test" GIT_COMMITTER_EMAIL="sync-test@example.invalid"

# ---------------------------------------------------------------------------
# Build a donor repo with a linear history c1..c4 plus a divergent branch.
# ---------------------------------------------------------------------------
make_donor() {
  local d="$1"
  mkdir -p "$d"
  $GIT init -q -b main "$d"
  local i
  for i in 1 2 3 4; do
    echo "line $i" >>"$d/f.txt"
    $GIT -C "$d" add f.txt
    $GIT -C "$d" commit -qm "c$i"
  done
  # A branch that leaves the shared history at c2 — the DIVERGENT ingredient.
  $GIT -C "$d" checkout -q -b side "$($GIT -C "$d" rev-parse main~2)"
  echo "side work" >>"$d/g.txt"
  $GIT -C "$d" add g.txt
  $GIT -C "$d" commit -qm "s1"
  $GIT -C "$d" checkout -q main
}

sha() { $GIT -C "$1" rev-parse "$2"; }

# A commit that exists in the module worktree and NOWHERE ELSE: made on a
# detached HEAD, pushed nowhere, named by no ref. This is the commit shape whose
# loss the whole tool exists to prevent, and the only shape that proves the
# refusal is real — a commit that some ref already holds proves nothing.
new_commit() { # new_commit <moddir> <text> -> prints the new sha
  local d="$1" t="$2"
  echo "$t" >>"$d/local.txt"
  $GIT -C "$d" add local.txt
  $GIT -C "$d" commit -qm "$t"
  $GIT -C "$d" rev-parse HEAD
}

# ---------------------------------------------------------------------------
# Fixture A — every interesting state in one superproject.
#
#   m_synced           worktree == pin
#   m_behind           worktree = c2, pin = c4      (ancestor of the pin)
#   m_ahead            pin = c2, worktree = c2 + 2 unreferenced commits
#   m_divergent        pin = c4, worktree = c2 + 1 unreferenced commit
#   m_dirty            worktree = c2, pin = c4, plus an uncommitted edit
#   m_ahead_anchored   pin = c2, worktree = c2 + 1 commit held by a local TAG
#   m_div_anchored     pin = c4, worktree = c2 + 1 commit held by a local TAG
#   m_div_partial      pin = c4, worktree = c2 + 2 commits, only the FIRST tagged
#   m_remote_anchored  pin = c2, worktree = c2 + 1 commit held ONLY by a
#                      refs/pins/<sha> ref on the remote
#   m_unreachable      pin = c2, worktree = c2 + 1 unreferenced commit, and an
#                      origin URL that cannot be read
# ---------------------------------------------------------------------------
SUPER="$TMP_ROOT/super"
DONOR="$TMP_ROOT/donor"
make_donor "$DONOR"

mkdir -p "$SUPER"
$GIT init -q -b main "$SUPER"
echo root >"$SUPER/README"
$GIT -C "$SUPER" add README
$GIT -C "$SUPER" commit -qm "root"

for name in m_synced m_behind m_ahead m_divergent m_dirty \
            m_ahead_anchored m_div_anchored m_div_partial \
            m_remote_anchored m_unreachable; do
  $GIT -C "$SUPER" submodule -q add "$DONOR" "$name" 2>/dev/null
done
$GIT -C "$SUPER" commit -qm "add submodules" >/dev/null

C2="$(sha "$DONOR" main~2)"
C4="$(sha "$DONOR" main)"

# Record the pins we want, by moving each worktree and committing the gitlink.
# This is the real mechanism by which the bug is produced, not a simulation of it.
set_pin() { # set_pin <module> <sha>
  $GIT -C "$SUPER/$1" checkout -q "$2"
  $GIT -C "$SUPER" add "$1"
}
set_pin m_synced          "$C4"
set_pin m_behind          "$C4"
set_pin m_ahead           "$C2"
set_pin m_divergent       "$C4"
set_pin m_dirty           "$C4"
set_pin m_ahead_anchored  "$C2"
set_pin m_div_anchored    "$C4"
set_pin m_div_partial     "$C4"
set_pin m_remote_anchored "$C2"
set_pin m_unreachable     "$C2"
$GIT -C "$SUPER" commit -qm "record pins" >/dev/null

# Now walk the worktrees off the pins, exactly as a stale checkout would be.
$GIT -C "$SUPER/m_behind" checkout -q "$C2"
$GIT -C "$SUPER/m_dirty"  checkout -q "$C2"
echo "uncommitted" >>"$SUPER/m_dirty/f.txt"

# AHEAD by two commits that live on no ref anywhere.
new_commit "$SUPER/m_ahead" "ahead-1" >/dev/null
new_commit "$SUPER/m_ahead" "ahead-2" >/dev/null

# DIVERGENT: fork at c2 with one unreferenced commit, so the pin (c4) still
# holds two the worktree lacks.
$GIT -C "$SUPER/m_divergent" checkout -q "$C2"
new_commit "$SUPER/m_divergent" "div-1" >/dev/null

# AHEAD but ANCHORED — the unique commit is held by a local tag.
$GIT -C "$SUPER/m_ahead_anchored" checkout -q "$C2"
AA="$(new_commit "$SUPER/m_ahead_anchored" "kept-by-tag")"
$GIT -C "$SUPER/m_ahead_anchored" tag keep/ahead "$AA"

# DIVERGENT but ANCHORED.
$GIT -C "$SUPER/m_div_anchored" checkout -q "$C2"
DA="$(new_commit "$SUPER/m_div_anchored" "div-kept-by-tag")"
$GIT -C "$SUPER/m_div_anchored" tag keep/div "$DA"

# DIVERGENT with TWO unique commits and only the older one anchored. A per-module
# or HEAD-only anchor check passes this; the required per-commit one does not.
$GIT -C "$SUPER/m_div_partial" checkout -q "$C2"
PP="$(new_commit "$SUPER/m_div_partial" "partial-anchored")"
$GIT -C "$SUPER/m_div_partial" tag keep/partial "$PP"
QQ="$(new_commit "$SUPER/m_div_partial" "partial-UNanchored")"

# Anchored ONLY on the remote, exactly as scripts/audit_first_party_pins.py
# --anchor leaves a superseded pin: pushed to refs/pins/<sha>, held by no local
# ref at all.
RR="$(new_commit "$SUPER/m_remote_anchored" "kept-only-on-the-remote")"
$GIT -C "$SUPER/m_remote_anchored" push -q origin "$RR:refs/pins/$RR"
if [ -z "$($GIT -C "$SUPER/m_remote_anchored" for-each-ref --contains "$RR")" ]; then
  pass "fixture: m_remote_anchored's commit is on NO local ref (remote path is exercised)"
else
  fail "fixture invalid: a local ref holds m_remote_anchored's commit, so the remote check is not exercised"
fi

# AHEAD, unanchored locally, and the remote cannot answer.
UU="$(new_commit "$SUPER/m_unreachable" "unanchored-and-unknowable")"
$GIT -C "$SUPER/m_unreachable" remote set-url origin "$TMP_ROOT/no-such-remote.git"

echo "=== fixture A: classification ==="
JSON="$(bash "$SYNC" --root "$SUPER" --json)"
RC_A=$?

expect_state() { # expect_state <module> <state>
  if printf '%s' "$JSON" | grep -q "\"path\":\"$1\",\"state\":\"$2\""; then
    pass "$1 classified $2"
  else
    fail "$1 not classified $2; got: $(printf '%s' "$JSON" | tr ',' '\n' | grep -A0 "\"path\":\"$1\"" -A1 | head -3)"
  fi
}

expect_state m_synced    SYNCED
expect_state m_behind    BEHIND
expect_state m_ahead     AHEAD
expect_state m_divergent DIVERGENT
expect_state m_dirty     BEHIND
expect_state m_ahead_anchored  AHEAD
expect_state m_div_anchored    DIVERGENT
expect_state m_div_partial     DIVERGENT
expect_state m_remote_anchored AHEAD
expect_state m_unreachable     AHEAD

# The topology stays the topology: ANCHORED is a flag, not a state. A consumer
# matching "state":"AHEAD" must keep seeing AHEAD (asserted above), and must be
# able to read recoverability separately.
expect_anchored() { # expect_anchored <module> <0|1>
  if printf '%s' "$JSON" | grep -q "\"path\":\"$1\",[^}]*\"anchored\":$2"; then
    pass "$1 anchored=$2"
  else
    fail "$1 expected anchored=$2; got $(printf '%s' "$JSON" | tr '{' '\n' | grep "\"path\":\"$1\"")"
  fi
}
expect_anchored m_ahead           0
expect_anchored m_divergent       0
expect_anchored m_dirty           0
expect_anchored m_ahead_anchored  1
expect_anchored m_div_anchored    1
expect_anchored m_div_partial     0
expect_anchored m_remote_anchored 1
expect_anchored m_unreachable     0

# "Every one of them" — the partial case must name the UNANCHORED commit, not
# report a summary that the anchored one satisfies.
if printf '%s' "$JSON" | grep -q "\"path\":\"m_div_partial\",[^}]*\"anchor_detail\":\"${QQ:0:8}[^\"]*no refs/pins"; then
  pass "m_div_partial names the one unanchored commit (${QQ:0:8})"
else
  fail "m_div_partial did not name the unanchored commit; got $(printf '%s' "$JSON" | tr '{' '\n' | grep m_div_partial)"
fi

# A remote that cannot be read is not a remote that said yes.
if printf '%s' "$JSON" | grep -q '"path":"m_unreachable",[^}]*"anchor_detail":"NOT ANCHORED, fail-closed: could not read refs/pins'; then
  pass "unreadable remote fails closed and says so"
else
  fail "unreadable remote did not report a fail-closed reason; got $(printf '%s' "$JSON" | tr '{' '\n' | grep m_unreachable)"
fi

if printf '%s' "$JSON" | grep -q '"path":"m_ahead_anchored",[^}]*"anchor_detail":"[0-9a-f]* refs/tags/keep/ahead'; then
  pass "the anchoring ref is named, not merely counted"
else
  fail "m_ahead_anchored did not name refs/tags/keep/ahead"
fi
if printf '%s' "$JSON" | grep -q "\"path\":\"m_remote_anchored\",[^}]*\"anchor_detail\":\"[0-9a-f]* remote refs/pins/$RR"; then
  pass "the remote anchor names the refs/pins ref it was proved by"
else
  fail "m_remote_anchored did not name its remote refs/pins ref"
fi

# Cost: one ls-remote per REMOTE per run, on the drifted-and-ahead path only.
# Five modules here reach the remote stage; two distinct URLs exist.
NETLOG="$TMP_ROOT/net.log"
SUBMODULE_SYNC_TRACE_NET=1 bash "$SYNC" --root "$SUPER" --json >/dev/null 2>"$NETLOG"
N_DONOR="$(grep -c "net: ls-remote $DONOR\$" "$NETLOG" | tr -d ' ')"
N_TOTAL="$(grep -c 'net: ls-remote' "$NETLOG" | tr -d ' ')"
if [ "$N_DONOR" = "1" ] && [ "$N_TOTAL" = "2" ]; then
  pass "the remote read is cached per remote per run (1 donor probe, 2 total)"
else
  fail "expected 1 donor probe and 2 total, got donor=$N_DONOR total=$N_TOTAL"
fi
# --offline must never touch the network, and must say that is why it refused.
OFFLOG="$TMP_ROOT/net_offline.log"
OFF_JSON="$(SUBMODULE_SYNC_TRACE_NET=1 bash "$SYNC" --root "$SUPER" --offline --json 2>"$OFFLOG")"
if [ ! -s "$OFFLOG" ] \
   && printf '%s' "$OFF_JSON" | grep -q '"path":"m_remote_anchored",[^}]*"anchored":0' \
   && printf '%s' "$OFF_JSON" | grep -q '"path":"m_ahead_anchored",[^}]*"anchored":1'; then
  pass "--offline issues no probe: locally-proved anchors stand, remote-only ones fail closed"
else
  fail "--offline behaved wrongly (probes=$(wc -l <"$OFFLOG" | tr -d ' '))"
fi

# The counts must be real, not just the label.
if printf '%s' "$JSON" | grep -q '"path":"m_behind","state":"BEHIND","ahead":0,"behind":2'; then
  pass "m_behind reports 0 ahead / 2 behind"
else
  fail "m_behind commit counts wrong"
fi
if printf '%s' "$JSON" | grep -q '"path":"m_ahead","state":"AHEAD","ahead":2,"behind":0'; then
  pass "m_ahead reports 2 ahead / 0 behind"
else
  fail "m_ahead commit counts wrong"
fi
if printf '%s' "$JSON" | grep -q '"path":"m_divergent","state":"DIVERGENT","ahead":1,"behind":2'; then
  pass "m_divergent reports 1 ahead / 2 behind"
else
  fail "m_divergent commit counts wrong"
fi
if printf '%s' "$JSON" | grep -q '"path":"m_dirty","state":"BEHIND","ahead":0,"behind":2,"worktree":"[0-9a-f]*","pin":"[0-9a-f]*","dirty":1'; then
  pass "m_dirty reports 1 uncommitted change"
else
  fail "m_dirty did not report its uncommitted change"
fi

# Mixed fixture must demand a human: exit 2.
if [ "$RC_A" -eq 2 ]; then
  pass "exit 2 when at least one module needs review"
else
  fail "expected exit 2 for the mixed fixture, got $RC_A"
fi

# ---------------------------------------------------------------------------
# The safety assertion: --restore must move m_behind and NOTHING else.
# ---------------------------------------------------------------------------
echo "=== fixture A: --restore touches only the provably-lossless modules ==="
before_ahead="$(sha "$SUPER/m_ahead" HEAD)"
before_div="$(sha "$SUPER/m_divergent" HEAD)"
before_dirty="$(sha "$SUPER/m_dirty" HEAD)"
before_dirty_body="$(cat "$SUPER/m_dirty/f.txt")"
before_partial="$(sha "$SUPER/m_div_partial" HEAD)"
before_unreach="$(sha "$SUPER/m_unreachable" HEAD)"

bash "$SYNC" --root "$SUPER" --restore --force >"$TMP_ROOT/restore.log" 2>&1
RC_R=$?

if [ "$(sha "$SUPER/m_behind" HEAD)" = "$C4" ]; then
  pass "m_behind was restored to the pin"
else
  fail "m_behind was not restored (HEAD=$(sha "$SUPER/m_behind" HEAD), pin=$C4)"
fi
if [ "$(sha "$SUPER/m_ahead" HEAD)" = "$before_ahead" ]; then
  pass "m_ahead untouched — its 2 unlanded commits survive"
else
  fail "m_ahead WAS MOVED; unlanded work would have been lost"
fi
if [ "$(sha "$SUPER/m_divergent" HEAD)" = "$before_div" ]; then
  pass "m_divergent untouched"
else
  fail "m_divergent WAS MOVED; divergent work would have been lost"
fi
if [ "$(sha "$SUPER/m_dirty" HEAD)" = "$before_dirty" ] \
   && [ "$(cat "$SUPER/m_dirty/f.txt")" = "$before_dirty_body" ]; then
  pass "m_dirty untouched — the uncommitted edit survives"
else
  fail "m_dirty WAS MOVED; an uncommitted edit would have been lost"
fi
if [ "$RC_R" -eq 2 ]; then
  pass "--restore exits 2 to report what it deliberately skipped"
else
  fail "expected --restore exit 2 with skipped modules, got $RC_R"
fi

# --- the anchored half -----------------------------------------------------
for m in m_ahead_anchored m_div_anchored m_remote_anchored; do
  want="$C2"; [ "$m" = "m_div_anchored" ] && want="$C4"
  if [ "$(sha "$SUPER/$m" HEAD)" = "$want" ]; then
    pass "$m was restored — every commit it held is held by a durable ref"
  else
    fail "$m was NOT restored despite being anchored (HEAD=$(sha "$SUPER/$m" HEAD), pin=$want)"
  fi
done

# Restored is only lossless if the anchor still resolves afterwards.
if [ "$(sha "$SUPER/m_ahead_anchored" keep/ahead)" = "$AA" ] \
   && [ "$(sha "$SUPER/m_div_anchored" keep/div)" = "$DA" ]; then
  pass "the anchoring tags still resolve after the restore — nothing was lost"
else
  fail "an anchoring tag no longer resolves after the restore"
fi
if [ "$($GIT ls-remote "$DONOR" "refs/pins/$RR" | awk '{print $1}')" = "$RR" ]; then
  pass "the remote refs/pins ref still holds m_remote_anchored's commit"
else
  fail "the remote anchor for m_remote_anchored is gone"
fi

# --- the partially-anchored and unreadable halves: unchanged behaviour ------
if [ "$(sha "$SUPER/m_div_partial" HEAD)" = "$before_partial" ]; then
  pass "m_div_partial untouched — ONE unanchored commit is enough to refuse"
else
  fail "m_div_partial WAS MOVED; the unanchored commit ${QQ:0:8} would have been lost"
fi
if [ "$(sha "$SUPER/m_unreachable" HEAD)" = "$before_unreach" ] \
   && [ "$(sha "$SUPER/m_unreachable" HEAD)" = "$UU" ]; then
  pass "m_unreachable untouched — a remote that cannot be read never says yes"
else
  fail "m_unreachable WAS MOVED on the strength of a remote read that failed"
fi

# Silence would make an anchored restore indistinguishable from the unsafe one
# this tool exists to prevent. It must name the commit AND the ref, per module.
if grep -q "ANCHORED m_ahead_anchored" "$TMP_ROOT/restore.log" \
   && grep -q "$AA refs/tags/keep/ahead" "$TMP_ROOT/restore.log" \
   && grep -q "$RR remote refs/pins/$RR" "$TMP_ROOT/restore.log"; then
  pass "--restore prints per module which ref anchors which commit"
else
  fail "--restore did not print the per-module anchor evidence"
fi

# ---------------------------------------------------------------------------
# Fixture B — only safe drift. Must report exit 1 and then reach a clean exit 0.
# ---------------------------------------------------------------------------
echo "=== fixture B: all-safe drift restores to green ==="
SUPER_B="$TMP_ROOT/super_b"
mkdir -p "$SUPER_B"
$GIT init -q -b main "$SUPER_B"
echo root >"$SUPER_B/README"
$GIT -C "$SUPER_B" add README
$GIT -C "$SUPER_B" commit -qm root
$GIT -C "$SUPER_B" submodule -q add "$DONOR" only 2>/dev/null
$GIT -C "$SUPER_B/only" checkout -q "$C4"
$GIT -C "$SUPER_B" add only
$GIT -C "$SUPER_B" commit -qm "pin only@c4" >/dev/null
$GIT -C "$SUPER_B/only" checkout -q "$C2"

bash "$SYNC" --root "$SUPER_B" >/dev/null 2>&1
if [ "$?" -eq 1 ]; then
  pass "exit 1 when every drifted module is restorable"
else
  fail "expected exit 1 for the all-safe fixture"
fi

# The printed command must be the one that actually works. Run the text, not a
# paraphrase of it: a restore command that has drifted from the code is exactly
# the failure this whole lane is about.
CMD="$(bash "$SYNC" --root "$SUPER_B" | grep -E '^\s+git -C .* submodule update --init --no-fetch -- only$' | head -1 | sed 's/^ *//')"
if [ -n "$CMD" ]; then
  ( cd "$SUPER_B" && eval "git -c protocol.file.allow=always ${CMD#git }" ) >/dev/null 2>&1
  if [ "$(sha "$SUPER_B/only" HEAD)" = "$C4" ]; then
    pass "the printed restore command actually restores"
  else
    fail "the printed restore command did not restore"
  fi
else
  fail "no restore command was printed for the all-safe fixture"
fi

SYNCLOG="$TMP_ROOT/net_synced.log"
SUBMODULE_SYNC_TRACE_NET=1 bash "$SYNC" --root "$SUPER_B" >/dev/null 2>"$SYNCLOG"
if [ "$?" -eq 0 ]; then
  pass "exit 0 once every worktree is at its pin"
else
  fail "expected exit 0 after restoring the all-safe fixture"
fi
# The cost rule: the path everybody runs before every build stays network-free.
if [ ! -s "$SYNCLOG" ]; then
  pass "the all-synced path issues no ls-remote at all"
else
  fail "the all-synced path made $(wc -l <"$SYNCLOG" | tr -d ' ') network call(s)"
fi

# ---------------------------------------------------------------------------
# Fixture C — a pin that is not in the local object store must not be guessed at.
# ---------------------------------------------------------------------------
echo "=== fixture C: unfetchable pin ==="
SUPER_C="$TMP_ROOT/super_c"
mkdir -p "$SUPER_C"
$GIT init -q -b main "$SUPER_C"
echo root >"$SUPER_C/README"
$GIT -C "$SUPER_C" add README
$GIT -C "$SUPER_C" commit -qm root
$GIT -C "$SUPER_C" submodule -q add "$DONOR" gone 2>/dev/null
$GIT -C "$SUPER_C" commit -qm "add" >/dev/null
# A syntactically valid gitlink to a commit that exists nowhere.
$GIT -C "$SUPER_C" update-index --add --cacheinfo \
    160000,0123456789012345678901234567890123456789,gone
$GIT -C "$SUPER_C" commit -qm "pin to a commit nobody has" >/dev/null

JSON_C="$(bash "$SYNC" --root "$SUPER_C" --json)"
RC_C=$?
if printf '%s' "$JSON_C" | grep -q '"path":"gone","state":"PIN-MISSING"'; then
  pass "an unresolvable pin is PIN-MISSING, not silently BEHIND"
else
  fail "unresolvable pin misclassified"
fi
if [ "$RC_C" -eq 2 ]; then
  pass "unresolvable pin demands a human (exit 2)"
else
  fail "expected exit 2 for the unfetchable-pin fixture, got $RC_C"
fi
# The ADVICE, not just the state. `fetch --all` fetches each remote's default
# refspec — branches — so it cannot retrieve a commit that is on no branch, and
# an anchored pin (`refs/pins/*`, what audit_first_party_pins.py --anchor parks
# there) is precisely that. Measured 2026-08-30 on first-party/ay b851ff38:
# `fetch --all` exited 0 and the object was STILL absent, so the report repeated
# PIN-MISSING at a reader who had done exactly what it asked. A diagnostic whose
# fix does not fix is worse than none — it spends the reader's trust.
TEXT_C="$(bash "$SYNC" --root "$SUPER_C" 2>&1 || true)"
# Anchor on the `inspect:` line, not on the whole report: the fixed advice
# NAMES `fetch --all` in prose to say do-not-use-it, and a bare substring grep
# matches that too — which is how this assertion first failed against the very
# fix it exists to protect.
if printf '%s' "$TEXT_C" | grep -q 'inspect:.*fetch --all'; then
  fail "PIN-MISSING advises 'fetch --all', which cannot retrieve an anchored pin"
else
  pass "PIN-MISSING does not advise 'fetch --all'"
fi
if printf '%s' "$TEXT_C" | grep -q 'fetch origin 0123456789012345678901234567890123456789'; then
  pass "PIN-MISSING advises fetching the pin BY SHA, which works off-branch"
else
  fail "PIN-MISSING advice does not name the pin sha to fetch"
fi

before_gone="$(sha "$SUPER_C/gone" HEAD)"
bash "$SYNC" --root "$SUPER_C" --restore --force >/dev/null 2>&1
if [ "$(sha "$SUPER_C/gone" HEAD)" = "$before_gone" ]; then
  pass "--restore does not touch a module whose pin it cannot resolve"
else
  fail "--restore moved a module with an unresolvable pin"
fi

# ---------------------------------------------------------------------------
# Fixture D — non-vacuity by mutation.
#
# Every assertion above is satisfied by a tool that simply refuses everything,
# and the two assertions that matter most (ONE unanchored commit is enough; an
# unreadable remote never says yes) are satisfied by a tool that never anchors
# anything. So: neuter the anchor check into "yes, always", and require those
# two cases to go RED. If they stay green under the mutant, they were testing
# nothing.
# ---------------------------------------------------------------------------
echo "=== fixture D: mutation — a trivially-true anchor check must break the suite ==="
MUTANT="$TMP_ROOT/submodule_sync.mutant.sh"
awk '
  { print }
  /^anchor_check/ && !hit {
    print "  ANCHORED_OUT=1; ANCHOR_NOTE_OUT=\047MUTANT: anchor check disabled\047; return 0"
    hit = 1
  }
' "$SYNC" >"$MUTANT"
if [ "$(grep -c 'MUTANT: anchor check disabled' "$MUTANT" | tr -d ' ')" = "1" ]; then
  pass "mutant built (anchor_check returns anchored unconditionally)"
else
  fail "mutation did not apply — anchor_check() signature changed?"
fi

SUPER_D="$TMP_ROOT/super_d"
mkdir -p "$SUPER_D"
$GIT init -q -b main "$SUPER_D"
echo root >"$SUPER_D/README"
$GIT -C "$SUPER_D" add README
$GIT -C "$SUPER_D" commit -qm root
for name in d_partial d_unreachable; do
  $GIT -C "$SUPER_D" submodule -q add "$DONOR" "$name" 2>/dev/null
done
$GIT -C "$SUPER_D" commit -qm "add" >/dev/null
for name in d_partial d_unreachable; do
  $GIT -C "$SUPER_D/$name" checkout -q "$C4"
  $GIT -C "$SUPER_D" add "$name"
done
$GIT -C "$SUPER_D" commit -qm "pin at c4" >/dev/null

$GIT -C "$SUPER_D/d_partial" checkout -q "$C2"
DP="$(new_commit "$SUPER_D/d_partial" "d-anchored")"
$GIT -C "$SUPER_D/d_partial" tag keep/d "$DP"
DQ="$(new_commit "$SUPER_D/d_partial" "d-UNanchored")"
DU="$(new_commit "$SUPER_D/d_unreachable" "d-unknowable")"
$GIT -C "$SUPER_D/d_unreachable" remote set-url origin "$TMP_ROOT/no-such-remote.git"

# Under the REAL tool both must be refused ...
bash "$SYNC" --root "$SUPER_D" --restore --force >/dev/null 2>&1
REAL_PARTIAL="$(sha "$SUPER_D/d_partial" HEAD)"
REAL_UNREACH="$(sha "$SUPER_D/d_unreachable" HEAD)"
if [ "$REAL_PARTIAL" = "$DQ" ] && [ "$REAL_UNREACH" = "$DU" ]; then
  pass "control: the real tool refuses both (the assertions are satisfiable)"
else
  fail "control failed: the real tool moved a module it must refuse"
fi

# ... and under the MUTANT both must move. Anything else means these assertions
# would pass no matter what the anchor check did.
bash "$MUTANT" --root "$SUPER_D" --restore --force >"$TMP_ROOT/mutant.log" 2>&1
FLIPPED=0
if [ "$(sha "$SUPER_D/d_partial" HEAD)" = "$C4" ]; then
  pass "MUTANT flips 'ONE unanchored commit is enough to refuse' to RED (d_partial moved to the pin)"
  FLIPPED=$((FLIPPED + 1))
else
  fail "the partial-anchor assertion is VACUOUS: it passes even with the anchor check disabled"
fi
if [ "$(sha "$SUPER_D/d_unreachable" HEAD)" = "$C4" ]; then
  pass "MUTANT flips 'an unreadable remote never says yes' to RED (d_unreachable moved to the pin)"
  FLIPPED=$((FLIPPED + 1))
else
  fail "the unreachable-remote assertion is VACUOUS: it passes even with the anchor check disabled"
fi
if [ "$FLIPPED" -eq 2 ]; then
  pass "non-vacuity: 2 of 2 anchor-refusal assertions are decided by the anchor check"
fi


# ---------------------------------------------------------------------------
# Fixture E — a submodule can itself be a linked Git worktree. Submodule update
# rewrites its shared core.worktree relative to the linked gitdir, breaking the
# primary checkout. Restore only the selected worktree's detached HEAD.
# ---------------------------------------------------------------------------
echo "=== fixture E: linked submodule worktree preserves the primary ==="
SUPER_E="$TMP_ROOT/super primary"
LINKED_E="$TMP_ROOT/super linked"
$GIT init -q -b main "$SUPER_E"
echo root >"$SUPER_E/README"
$GIT -C "$SUPER_E" add README
$GIT -C "$SUPER_E" commit -qm root
$GIT -C "$SUPER_E" submodule -q add "$DONOR" only 2>/dev/null
$GIT -C "$SUPER_E/only" checkout -q --detach "$C2"
$GIT -C "$SUPER_E" add .gitmodules only
$GIT -C "$SUPER_E" commit -qm "primary keeps c2"
$GIT -C "$SUPER_E" worktree add -q --detach "$LINKED_E" HEAD
$GIT -C "$SUPER_E/only" worktree add -q --detach "$LINKED_E/only" "$C2"
$GIT -C "$LINKED_E" update-index --cacheinfo "160000,$C4,only"
$GIT -C "$LINKED_E" commit -qm "linked parent pins c4"
E_CONFIG="$SUPER_E/.git/modules/only/config"
cp "$E_CONFIG" "$TMP_ROOT/primary-config.before"
linked_primary_unchanged() {
  cmp -s "$E_CONFIG" "$TMP_ROOT/primary-config.before" &&
    [ "$(sha "$SUPER_E/only" HEAD)" = "$C2" ] &&
    [ "$(cat "$SUPER_E/only/f.txt")" = "$(git -C "$DONOR" show "$C2:f.txt")" ] &&
    [ -z "$($GIT -C "$SUPER_E" status --porcelain)" ]
}
E_ADVICE="$(bash "$SYNC" --root "$LINKED_E" --offline)"
E_CMD="$(printf '%s\n' "$E_ADVICE" | grep ' checkout --detach ' | head -1 | sed 's/^ *//')"
if [ -n "$E_CMD" ] && bash -c "$E_CMD" >/dev/null 2>&1 &&
   [ "$(sha "$LINKED_E/only" HEAD)" = "$C4" ] && linked_primary_unchanged; then
  pass "printed linked-worktree command handles spaces and preserves primary metadata/source"
else
  fail "printed linked-worktree command is missing, invalid, or mutates the primary"
fi
# Keep separate controls independent even if an old implementation broke config.
cp "$TMP_ROOT/primary-config.before" "$E_CONFIG"
$GIT -C "$LINKED_E/only" checkout -q --detach "$C2"
if bash "$SYNC" --root "$LINKED_E" --offline --restore >"$TMP_ROOT/linked-restore.log" 2>&1 &&
   [ "$(sha "$LINKED_E/only" HEAD)" = "$C4" ] && linked_primary_unchanged; then
  pass "linked restore reaches the pin without changing primary HEAD, files, or shared config"
else
  fail "linked restore corrupts or moves the primary submodule"
fi
cp "$TMP_ROOT/primary-config.before" "$E_CONFIG"
$GIT -C "$LINKED_E/only" checkout -q --detach "$C2"
echo "linked edit" >>"$LINKED_E/only/f.txt"
cp "$LINKED_E/only/f.txt" "$TMP_ROOT/linked-dirty.before"
bash "$SYNC" --root "$LINKED_E" --offline --restore >"$TMP_ROOT/linked-dirty.log" 2>&1
if [ "$?" -eq 2 ] && [ "$(sha "$LINKED_E/only" HEAD)" = "$C2" ] &&
   cmp -s "$LINKED_E/only/f.txt" "$TMP_ROOT/linked-dirty.before" && linked_primary_unchanged; then
  pass "dirty linked worktree is refused without changing either checkout"
else
  fail "dirty linked worktree was not preserved"
fi
# Commit only the fixture edit on detached HEAD, without a durable ref.
$GIT -C "$LINKED_E/only" add f.txt
$GIT -C "$LINKED_E/only" commit -qm "unique linked work"
E_UNIQUE="$(sha "$LINKED_E/only" HEAD)"
bash "$SYNC" --root "$LINKED_E" --offline --restore >"$TMP_ROOT/linked-unique.log" 2>&1
if [ "$?" -eq 2 ] && [ "$(sha "$LINKED_E/only" HEAD)" = "$E_UNIQUE" ] && linked_primary_unchanged; then
  pass "unanchored linked commit is refused and stays recoverable at its HEAD"
else
  fail "linked-worktree restoration bypassed the unanchored-commit refusal"
fi

# Ordinary absent submodules still need initialization, not a worktree checkout.
echo "=== fixture F: absent submodule initialization ==="
SUPER_F="$TMP_ROOT/super absent"
$GIT clone -q --no-recurse-submodules "$SUPER_E" "$SUPER_F"
if [ ! -e "$SUPER_F/only/.git" ] &&
   GIT_ALLOW_PROTOCOL=file bash "$SYNC" --root "$SUPER_F" --offline --restore \
     >"$TMP_ROOT/absent-restore.log" 2>&1 &&
   [ "$(sha "$SUPER_F/only" HEAD)" = "$C2" ] &&
   [ -z "$($GIT -C "$SUPER_F" status --porcelain)" ]; then
  pass "absent ordinary submodule is initialized to its recorded pin"
else
  fail "absent ordinary submodule initialization regressed"
fi

# An empty submodule directory inherits its parent's Git discovery. The parent
# being linked must not turn initialization advice into a parent HEAD checkout.
SUPER_G="$TMP_ROOT/linked absent"
$GIT -C "$SUPER_E" worktree add -q --detach "$SUPER_G" HEAD
G_HEAD="$(sha "$SUPER_G" HEAD)"
G_ADVICE="$(GIT_ALLOW_PROTOCOL=file bash "$SYNC" --root "$SUPER_G" --offline)"
G_CMD="$(printf '%s\n' "$G_ADVICE" | grep ' submodule update --init --no-fetch -- only$' | head -1 | sed 's/^ *//')"
if [ -n "$G_CMD" ] && GIT_ALLOW_PROTOCOL=file bash -c "$G_CMD" >/dev/null 2>&1 &&
   [ "$(sha "$SUPER_G/only" HEAD)" = "$C2" ] &&
   [ "$(sha "$SUPER_G" HEAD)" = "$G_HEAD" ] && linked_primary_unchanged; then
  pass "absent submodule in a linked parent gets initialization advice and preserves parent HEAD"
else
  fail "absent linked-parent advice mistakes the parent for the submodule"
fi

# ---------------------------------------------------------------------------
# Fixture H — --fetch. A pull moved the pins to commits this checkout never
# fetched: one on a branch, one held ONLY by a refs/pins/<sha> anchor (what
# `fetch --all` cannot reach), one whose fetch reveals unanchored local work,
# and one nobody has. `--fetch --restore` must fetch exactly the missing pins
# and then let the unchanged safety model decide every restore.
# ---------------------------------------------------------------------------
echo "=== fixture H: --fetch retrieves exactly the missing pins ==="
DONOR_H="$TMP_ROOT/donor_h"
make_donor "$DONOR_H"
H4="$(sha "$DONOR_H" main)"
SUPER_H="$TMP_ROOT/super_h"
$GIT init -q -b main "$SUPER_H"
echo root >"$SUPER_H/README"
$GIT -C "$SUPER_H" add README
$GIT -C "$SUPER_H" commit -qm root
for name in h_branch h_anchored h_div h_gone h_behind; do
  $GIT -C "$SUPER_H" submodule -q add "$DONOR_H" "$name" 2>/dev/null
done
$GIT -C "$SUPER_H" commit -qm "add, all pinned at c4" >/dev/null
$GIT -C "$SUPER_H/h_behind" checkout -q "$($GIT -C "$DONOR_H" rev-parse main~2)"
$GIT -C "$SUPER_H/h_div" checkout -q --detach
HD="$(new_commit "$SUPER_H/h_div" "h-unanchored")"
# Protocol v0 serves only advertised tips: the strictest server a by-sha fetch
# of an anchored pin must still work against.
$GIT -C "$SUPER_H/h_anchored" config protocol.version 0

# The donor moves on after the clones: a branch commit, and an off-branch commit
# anchored the way audit_first_party_pins.py --anchor leaves one.
echo "line 5" >>"$DONOR_H/f.txt"
$GIT -C "$DONOR_H" commit -qam c5
H5="$(sha "$DONOR_H" main)"
$GIT -C "$DONOR_H" checkout -q --detach "$H4"
echo "anchored" >>"$DONOR_H/f.txt"
$GIT -C "$DONOR_H" commit -qam anchored-only
HP="$(sha "$DONOR_H" HEAD)"
$GIT -C "$DONOR_H" update-ref "refs/pins/$HP" "$HP"
$GIT -C "$DONOR_H" checkout -q main
GONE=0123456789012345678901234567890123456789
$GIT -C "$SUPER_H" update-index --cacheinfo "160000,$H5,h_branch" \
  --cacheinfo "160000,$HP,h_anchored" --cacheinfo "160000,$H5,h_div" \
  --cacheinfo "160000,$GONE,h_gone"
$GIT -C "$SUPER_H" commit -qm "pull: pins moved" >/dev/null
if [ -z "$($GIT -C "$DONOR_H" branch --contains "$HP")" ] \
   && ! $GIT -C "$SUPER_H/h_anchored" cat-file -e "$HP^{commit}" 2>/dev/null \
   && ! $GIT -C "$SUPER_H/h_branch" cat-file -e "$H5^{commit}" 2>/dev/null; then
  pass "fixture: the new pins are absent locally, and the anchored one is on no branch"
else
  fail "fixture invalid: a moved pin is already local, or the anchored pin is on a branch"
fi
# Why not `fetch --all`: it fetches branches, and exits 0 without the pin.
if $GIT -C "$SUPER_H/h_anchored" fetch -q --all \
   && ! $GIT -C "$SUPER_H/h_anchored" cat-file -e "$HP^{commit}" 2>/dev/null; then
  pass "control: fetch --all succeeds and still leaves the anchored pin missing"
else
  fail "control: fetch --all failed, or it retrieved the anchored pin (fixture invalid)"
fi

H_NET="$TMP_ROOT/h_net.log"
JSON_H0="$(SUBMODULE_SYNC_TRACE_NET=1 bash "$SYNC" --root "$SUPER_H" --json 2>"$H_NET")"
H0_MISSING=0
for m in h_branch h_anchored h_div h_gone; do
  printf '%s' "$JSON_H0" | grep -q "\"path\":\"$m\",\"state\":\"PIN-MISSING\"" && H0_MISSING=$((H0_MISSING + 1))
done
if [ "$H0_MISSING" -eq 4 ] && ! grep -q 'net: fetch' "$H_NET"; then
  pass "control: without --fetch all four are PIN-MISSING and nothing is fetched"
else
  fail "control: expected 4 PIN-MISSING and no fetch, got $H0_MISSING and $(grep -c 'net: fetch' "$H_NET")"
fi
TEXT_H0="$(bash "$SYNC" --root "$SUPER_H" 2>&1 || true)"
if printf '%s' "$TEXT_H0" | grep -q 'scripts/submodule_sync.sh --fetch --restore'; then
  pass "PIN-MISSING advice names the one-command --fetch --restore"
else
  fail "PIN-MISSING advice does not mention --fetch --restore"
fi
bash "$SYNC" --root "$SUPER_H" --fetch --offline >/dev/null 2>&1
if [ "$?" -eq 3 ]; then
  pass "--fetch --offline is refused as a usage error (exit 3)"
else
  fail "--fetch --offline was not refused"
fi

H_REFS_BEFORE="$($GIT -C "$SUPER_H/h_anchored" for-each-ref)"
SUBMODULE_SYNC_TRACE_NET=1 bash "$SYNC" --root "$SUPER_H" --fetch --restore --force \
  >"$TMP_ROOT/h_restore.log" 2>"$H_NET"
RC_H=$?
for pair in "h_branch $H5" "h_anchored $HP" "h_behind $H4"; do
  m="${pair%% *}"; want="${pair#* }"
  if [ "$(sha "$SUPER_H/$m" HEAD)" = "$want" ]; then
    pass "$m fetched (if missing) and restored to its pin"
  else
    fail "$m not at its pin after --fetch --restore (HEAD=$(sha "$SUPER_H/$m" HEAD), pin=$want)"
  fi
done
if [ "$(sha "$SUPER_H/h_div" HEAD)" = "$HD" ] && [ "$(sha "$SUPER_H/h_gone" HEAD)" = "$H4" ]; then
  pass "h_div (unanchored work) and h_gone (pin nobody has) untouched"
else
  fail "--fetch --restore moved h_div or h_gone"
fi
if [ "$RC_H" -eq 2 ]; then
  pass "--fetch --restore still exits 2 for what needs a human"
else
  fail "expected exit 2 from the mixed --fetch --restore, got $RC_H"
fi
# Exactly the missing pins, one by-sha fetch per module that lacks its pin.
H_SPECS="$(sed -n 's/^net: fetch [^ ]* //p' "$H_NET" | sort | tr '\n' ' ')"
H_WANT="$(printf '%s\n' "$H5" "$HP" "$H5" "$GONE" | sort | tr '\n' ' ')"
if [ "$H_SPECS" = "$H_WANT" ]; then
  pass "fetched exactly the missing pins (a present pin, h_behind's, fetched nothing)"
else
  fail "fetch specs were [$H_SPECS], expected [$H_WANT]: $(cat "$H_NET")"
fi
if [ "$($GIT -C "$SUPER_H/h_anchored" for-each-ref)" = "$H_REFS_BEFORE" ]; then
  pass "--fetch created no local ref"
else
  fail "--fetch changed the module's refs"
fi
JSON_H1="$(bash "$SYNC" --root "$SUPER_H" --json 2>/dev/null)"
if printf '%s' "$JSON_H1" | grep -q '"path":"h_div","state":"DIVERGENT","ahead":1,"behind":1,[^}]*"anchored":0' \
   && printf '%s' "$JSON_H1" | grep -q '"path":"h_gone","state":"PIN-MISSING"'; then
  pass "after the fetch h_div classifies DIVERGENT/unanchored and h_gone stays PIN-MISSING"
else
  fail "post-fetch classification wrong: $JSON_H1"
fi

# One command realigns a checkout whose only drift is unfetched pins.
echo "=== fixture I: --fetch --restore aligns a pulled checkout in one command ==="
SUPER_I="$TMP_ROOT/super_i"
$GIT init -q -b main "$SUPER_I"
echo root >"$SUPER_I/README"
$GIT -C "$SUPER_I" add README
$GIT -C "$SUPER_I" commit -qm root
$GIT -C "$SUPER_I" submodule -q add "$DONOR_H" only 2>/dev/null
$GIT -C "$SUPER_I" commit -qm add >/dev/null
echo "line 6" >>"$DONOR_H/f.txt"
$GIT -C "$DONOR_H" commit -qam c6
H6="$(sha "$DONOR_H" main)"
$GIT -C "$SUPER_I" update-index --cacheinfo "160000,$H6,only"
$GIT -C "$SUPER_I" commit -qm "pull: pin moved" >/dev/null
bash "$SYNC" --root "$SUPER_I" --fetch --restore >"$TMP_ROOT/i_restore.log" 2>&1
RC_I=$?
I_NET="$TMP_ROOT/i_net.log"
SUBMODULE_SYNC_TRACE_NET=1 bash "$SYNC" --root "$SUPER_I" --fetch >/dev/null 2>"$I_NET"
RC_I2=$?
if [ "$RC_I" -eq 0 ] && [ "$(sha "$SUPER_I/only" HEAD)" = "$H6" ] && [ "$RC_I2" -eq 0 ]; then
  pass "--fetch --restore exits 0 at the pin, and a re-run reports OK"
else
  fail "one-command realign failed (rc=$RC_I, rerun=$RC_I2): $(cat "$TMP_ROOT/i_restore.log")"
fi
if [ ! -s "$I_NET" ]; then
  pass "--fetch on the all-synced path makes no network call"
else
  fail "--fetch on the all-synced path went to the network: $(cat "$I_NET")"
fi

# ---------------------------------------------------------------------------
# Fixture J — the build detector names THIS root as a path, not as a prefix.
#
# Measured 2026-09-28: with ROOT=<home>/trust, `grep -F "$ROOT"` counted
# every process whose command line mentioned <home>/trust-packs/... or
# <home>/trust-wt-*/... as a build in this repo, so --restore refused on a
# machine where sibling worktrees build all day. A decoy process whose command
# line carries the `x.py` token the candidate probe looks for, and names only
# SIBLING paths, must not block a restore; the same decoy naming a path INSIDE
# the root, or the root itself as the last word, still must. Each decoy runs from
# $TMP_ROOT, so its cwd never places it inside the fixture root: only the
# command-line half of the detector is under test.
# ---------------------------------------------------------------------------
echo "=== fixture J: the build detector does not match a sibling that shares the prefix ==="
SUPER_J="$TMP_ROOT/trust"
mkdir -p "$SUPER_J"
$GIT init -q -b main "$SUPER_J"
echo root >"$SUPER_J/README"
$GIT -C "$SUPER_J" add README
$GIT -C "$SUPER_J" commit -qm root
$GIT -C "$SUPER_J" submodule -q add "$DONOR" only 2>/dev/null
$GIT -C "$SUPER_J/only" checkout -q "$C4"
$GIT -C "$SUPER_J" add only
$GIT -C "$SUPER_J" commit -qm "pin only@c4" >/dev/null
# The spelling the script compares against: git's physical toplevel (on macOS
# mktemp answers /var/..., git answers /private/var/...).
REAL_J="$($GIT -C "$SUPER_J" rev-parse --show-toplevel)"

start_decoy() { # start_decoy <arg>... -> sets DECOY; the process lives ~60 s
  # Output to /dev/null: the decoy's `sleep` child must not hold a caller's pipe.
  ( cd "$TMP_ROOT" && exec bash -c 'sleep 60; exit 0' x.py "$@" ) >/dev/null 2>&1 &
  DECOY=$!
  DECOY_PIDS="$DECOY_PIDS $DECOY"
  local tries=0
  until ps -o command= -p "$DECOY" 2>/dev/null | grep -q 'x\.py'; do
    tries=$((tries + 1))
    [ "$tries" -lt 50 ] || break
    sleep 0.1
  done
}
stop_decoy() { pkill -P "$DECOY" 2>/dev/null; kill "$DECOY" 2>/dev/null; wait "$DECOY" 2>/dev/null; }

$GIT -C "$SUPER_J/only" checkout -q "$C2"
start_decoy "$REAL_J-wt-b/Cargo.toml" "$REAL_J-packs/bin/targo" "$REAL_J.old"
bash "$SYNC" --root "$SUPER_J" --offline --restore >"$TMP_ROOT/sibling-decoy.log" 2>&1
RC_J=$?
if [ "$RC_J" -ne 4 ] && [ "$(sha "$SUPER_J/only" HEAD)" = "$C4" ] && kill -0 "$DECOY" 2>/dev/null; then
  pass "a running process that names only sibling paths does not block --restore"
else
  fail "a sibling-path process blocked --restore (rc=$RC_J: $(head -3 "$TMP_ROOT/sibling-decoy.log" | tr '\n' ' '))"
fi
stop_decoy

$GIT -C "$SUPER_J/only" checkout -q "$C2"
start_decoy "$REAL_J-wt-b/x" "$REAL_J/Cargo.toml"
bash "$SYNC" --root "$SUPER_J" --offline --restore >"$TMP_ROOT/inside-decoy.log" 2>&1
RC_J=$?
if [ "$RC_J" -eq 4 ] && [ "$(sha "$SUPER_J/only" HEAD)" = "$C2" ] \
   && grep -q "REFUSED" "$TMP_ROOT/inside-decoy.log"; then
  pass "a running process that names a path inside the root still blocks --restore"
else
  fail "a process naming a path inside the root did not block --restore (rc=$RC_J)"
fi
stop_decoy

start_decoy "$REAL_J"
bash "$SYNC" --root "$SUPER_J" --offline --restore >"$TMP_ROOT/exact-decoy.log" 2>&1
RC_J=$?
if [ "$RC_J" -eq 4 ] && [ "$(sha "$SUPER_J/only" HEAD)" = "$C2" ]; then
  pass "a running process that names the root itself still blocks --restore"
else
  fail "a process naming the root itself did not block --restore (rc=$RC_J)"
fi
stop_decoy

# cwd-only decoys: the command line names x.py but no path of the root; only the
# cwd is inside it. A SHELL there is an agent harness whose build runs elsewhere
# (measured 2026-10-14) and must not block; any other process there still does.
start_cwd_decoy() { # start_cwd_decoy <program> <arg>... -> sets DECOY, cwd = the root
  ( cd "$SUPER_J" && exec "$@" ) >/dev/null 2>&1 &
  DECOY=$!
  DECOY_PIDS="$DECOY_PIDS $DECOY"
  local tries=0
  until ps -o command= -p "$DECOY" 2>/dev/null | grep -q 'x\.py'; do
    tries=$((tries + 1))
    # A decoy that never exec'd is the test's own subshell, no candidate: every
    # pass case after this would pass without exercising the guard.
    [ "$tries" -lt 50 ] || { fail "cwd decoy $1 never exec'd; the next case tests nothing"; break; }
    sleep 0.1
  done
}

$GIT -C "$SUPER_J/only" checkout -q "$C2"
start_cwd_decoy bash -c 'sleep 60; exit 0' x.py
bash "$SYNC" --root "$SUPER_J" --offline --restore >"$TMP_ROOT/shell-cwd-decoy.log" 2>&1
RC_J=$?
if [ "$RC_J" -ne 4 ] && [ "$(sha "$SUPER_J/only" HEAD)" = "$C4" ] && kill -0 "$DECOY" 2>/dev/null; then
  pass "a shell whose only tie to the root is its cwd does not block --restore"
else
  fail "a cwd-only shell blocked --restore (rc=$RC_J: $(head -3 "$TMP_ROOT/shell-cwd-decoy.log" | tr '\n' ' '))"
fi
stop_decoy

$GIT -C "$SUPER_J/only" checkout -q "$C2"
start_cwd_decoy perl -e 'sleep 60' x.py
bash "$SYNC" --root "$SUPER_J" --offline --restore >"$TMP_ROOT/proc-cwd-decoy.log" 2>&1
RC_J=$?
if [ "$RC_J" -eq 4 ] && [ "$(sha "$SUPER_J/only" HEAD)" = "$C2" ] \
   && grep -q "REFUSED" "$TMP_ROOT/proc-cwd-decoy.log"; then
  pass "a non-shell build process whose cwd is inside the root still blocks --restore"
else
  fail "a non-shell process with its cwd in the root did not block --restore (rc=$RC_J)"
fi
stop_decoy

# Agent-harness decoys (measured 2026-10-31): each agent executable aterm spawns,
# installed under a path with a space as atpkg installs agents, whose argv is a
# task prompt naming targo and cargo/rustc in prose, started with its cwd in the
# root. It counts by its command line only, like a shell. A near-miss name still
# counts by cwd, an agent whose command line names the root still blocks, and two
# mutation controls restore the old name list and the old comm parse alone and
# require the agent case to refuse again.
AGENT_BIN="$TMP_ROOT/agent bin"
mkdir -p "$AGENT_BIN"
for name in codex claude agy muse grok kimi codex-build; do ln -sf "$(command -v perl)" "$AGENT_BIN/$name"; done
AGENT_PROMPT='Record the genuine targo identity; no stock cargo/rustc builds.'
agent_restore() { # agent_restore <sync> <name> <arg>... -> RC_J; decoy left running
  local sync="$1" name="$2"; shift 2
  $GIT -C "$SUPER_J/only" checkout -q "$C2"
  start_cwd_decoy "$AGENT_BIN/$name" -e 'sleep 60' -- "$AGENT_PROMPT" "$@" x.py
  bash "$sync" --root "$SUPER_J" --offline --restore >"$TMP_ROOT/agent-cwd-decoy.log" 2>&1
  RC_J=$?
}

for name in codex claude agy muse grok kimi; do
  agent_restore "$SYNC" "$name"
  if [ "$RC_J" -ne 4 ] && [ "$(sha "$SUPER_J/only" HEAD)" = "$C4" ] && kill -0 "$DECOY" 2>/dev/null; then
    pass "an agent harness ($name, under a path with a space) tied to the root only by its cwd does not block --restore"
  else
    fail "a cwd-only $name agent blocked --restore (rc=$RC_J: $(head -3 "$TMP_ROOT/agent-cwd-decoy.log" | tr '\n' ' '))"
  fi
  stop_decoy
done

agent_restore "$SYNC" codex-build
if [ "$RC_J" -eq 4 ] && [ "$(sha "$SUPER_J/only" HEAD)" = "$C2" ] \
   && grep -q "REFUSED" "$TMP_ROOT/agent-cwd-decoy.log"; then
  pass "a near-miss executable name (codex-build) with its cwd in the root still blocks --restore"
else
  fail "codex-build with its cwd in the root did not block --restore (rc=$RC_J)"
fi
stop_decoy

agent_restore "$SYNC" codex "$REAL_J/Cargo.toml"
if [ "$RC_J" -eq 4 ] && [ "$(sha "$SUPER_J/only" HEAD)" = "$C2" ] \
   && grep -q "REFUSED" "$TMP_ROOT/agent-cwd-decoy.log"; then
  pass "an agent harness whose command line names the root still blocks --restore"
else
  fail "a codex agent naming the root did not block --restore (rc=$RC_J)"
fi
stop_decoy

MUT_AGENT="$TMP_ROOT/submodule_sync.no-agents.sh"
sed 's/|fish|codex|claude|agy|muse|grok|kimi)\$/|fish)$/' "$SYNC" >"$MUT_AGENT"
if cmp -s "$SYNC" "$MUT_AGENT"; then
  fail "mutation (no agent names) did not apply; the agent cases test nothing"
else
  agent_restore "$MUT_AGENT" codex
  if [ "$RC_J" -eq 4 ]; then
    pass "mutation control: without the agent names a cwd-only codex refuses again (the false positive)"
  else
    fail "the no-agent-names mutant did not refuse (rc=$RC_J); the codex case does not exercise the list"
  fi
  stop_decoy
fi
MUT_FIELD="$TMP_ROOT/submodule_sync.field2.sh"
perl -pe 's/\{ n = \$0; sub\(\/\^ \*\[0-9\]\+ \/, "", n\);/{ n = \$2;/' "$SYNC" >"$MUT_FIELD"
if cmp -s "$SYNC" "$MUT_FIELD"; then
  fail "mutation (second-field comm parse) did not apply; the space case tests nothing"
else
  agent_restore "$MUT_FIELD" codex
  if [ "$RC_J" -eq 4 ]; then
    pass "mutation control: reading the name from the second field misses codex under 'agent bin' (the false positive)"
  else
    fail "the second-field mutant did not refuse (rc=$RC_J); the space in the path is not exercised"
  fi
  stop_decoy
fi

# ---------------------------------------------------------------------------
# Fixture K — the concurrent-build guard (`--restore` WITHOUT --force): every
# candidate is examined, and the path-boundary rule holds under mutation.
#
# Fixture J above (upstream 61b9377d71) pins the sibling-prefix rule itself with
# `x.py` decoys; this fixture keeps what that one does not: the 40-PID cap (3),
# more boundary shapes on both sides (1)(2), and mutation controls that restore
# each old rule alone and require its case to turn RED (4). (Written as this
# branch's "fixture J" before upstream landed its own; renamed K on the rebase.)
#
# Measured 2026-09-29 in the landing worktree `.../trust-wt`: `--restore` refused
# with exit 4, naming stage1 builds running in the SIBLING worktrees
# `.../trust-wt-b2` and `.../trust-wt-b3`, because the command-line probe matched
# the root as a bare substring. And on a machine running ~140 compiler processes
# the probe examined only the 40 lowest PIDs, so a build started HERE after them
# was never seen: the guard failed OPEN. A fake "build" is a `sleep` whose argv
# names a path (`exec -a`), started with its cwd OUTSIDE the superproject, so only
# the command-line probe can see it.
# ---------------------------------------------------------------------------
echo "=== fixture K: the concurrent-build guard ==="
SUPER_K="$TMP_ROOT/super_k"
mkdir -p "$SUPER_K"
$GIT init -q -b main "$SUPER_K"
echo root >"$SUPER_K/README"
$GIT -C "$SUPER_K" add README
$GIT -C "$SUPER_K" commit -qm root
$GIT -C "$SUPER_K" submodule -q add "$DONOR" m 2>/dev/null
$GIT -C "$SUPER_K/m" checkout -q "$C4"
$GIT -C "$SUPER_K" add m
$GIT -C "$SUPER_K" commit -qm "pin m at c4" >/dev/null
# The root exactly as the tool computes it (`--show-toplevel` resolves /var -> /private/var).
K_TOP="$($GIT -C "$SUPER_K" rev-parse --show-toplevel)"
K_PIDS=""
fake_build() { # fake_build <argv0>: a sleep whose command line is <argv0>, cwd outside the superproject
  ( cd "$TMP_ROOT" && exec -a "$1" sleep 300 ) &
  K_PIDS="$K_PIDS $!"
}
stop_fakes() {
  if [ -n "$K_PIDS" ]; then kill $K_PIDS 2>/dev/null; wait $K_PIDS 2>/dev/null; fi
  K_PIDS=""
}
trap 'stop_fakes; for p in $DECOY_PIDS; do pkill -P "$p"; kill "$p"; done 2>/dev/null; if [ "${FAILURES:-1}" -eq 0 ]; then rm -rf "$TMP_ROOT"; else printf "retained failed sync fixture: %s\n" "$TMP_ROOT" >&2; fi' EXIT
# guarded_restore <script>: drift m BEHIND its pin (the provably safe case), then a
# guarded restore; returns the tool's exit status.
guarded_restore() {
  $GIT -C "$SUPER_K/m" checkout -q "$C2"
  sleep 1   # the fakes must have exec'd before the probe reads their command lines
  bash "$1" --root "$SUPER_K" --restore >"$TMP_ROOT/k.log" 2>&1
}
k_moved() { [ "$(sha "$SUPER_K/m" HEAD)" = "$C4" ]; }

# (1) builds in checkouts whose path merely STARTS WITH the root are not builds here.
fake_build "$K_TOP-b2/build/bootstrap/debug/rustc --crate-name sibling"
fake_build "${K_TOP}x/build/aarch64-apple-darwin/stage0/bin/cargo build --release"
fake_build "$K_TOP.bak/build/bootstrap/debug/rustc --crate-name sibling-dot"
fake_build "${K_TOP}_old/build/aarch64-apple-darwin/stage0/bin/cargo build --release"
guarded_restore "$SYNC"; rc=$?
if [ "$rc" -eq 0 ] && k_moved; then
  pass "builds in sibling checkouts sharing the root as a prefix do not block --restore"
else
  fail "a sibling checkout's build blocked --restore (rc=$rc): $(head -2 "$TMP_ROOT/k.log" | tr '\n' ' ')"
fi
stop_fakes

# (2) the negative twins: a build that names the root at a path boundary — `/`, a
#     space, a quote, and (review 2026-09-29) ANY other character a directory name
#     cannot continue with: `=` (`--remap-path-prefix=<root>=/src`), a `:` list, a
#     `,` list — refuses (exit 4) and moves nothing. The first rule listed only `/`,
#     whitespace and quotes, so the last three passed the guard (fail open).
for argv0 in "$K_TOP/build/bootstrap/debug/rustc --crate-name here" \
             "/usr/local/bin/targo test --manifest-path $K_TOP" \
             "python3 '$K_TOP'/x.py build --stage 1" \
             "/usr/local/bin/rustc --remap-path-prefix=$K_TOP=/src main.rs" \
             "/usr/local/bin/cargo rustc -- -L native=$K_TOP:/opt/lib" \
             "/usr/local/bin/targo test --roots $K_TOP,/elsewhere"; do
  fake_build "$argv0"
  guarded_restore "$SYNC"; rc=$?
  if [ "$rc" -eq 4 ] && ! k_moved; then
    pass "a build naming the root at a path boundary refuses --restore: ${argv0#"$TMP_ROOT"}"
  else
    fail "a build in THIS checkout did not refuse --restore (rc=$rc): $argv0"
  fi
  stop_fakes
done

# (3) the build HERE is started after 45 sibling decoys, so on an otherwise idle
#     machine at least 45 candidates have lower PIDs than it; a probe that kept only
#     the 40 lowest would never see it.
i=0
while [ "$i" -lt 45 ]; do
  i=$((i + 1))
  fake_build "$K_TOP-decoy$i/build/bootstrap/debug/rustc --crate-name decoy"
done
fake_build "$K_TOP/build/bootstrap/debug/rustc --crate-name after-the-decoys"
guarded_restore "$SYNC"; rc=$?
if [ "$rc" -eq 4 ] && ! k_moved; then
  pass "a build here is seen however many candidate processes precede it"
else
  fail "a build here was missed behind 45 sibling candidates (rc=$rc)"
fi

# (4) non-vacuity by mutation: each old rule, restored alone, must turn its case RED.
MUT_CAP="$TMP_ROOT/submodule_sync.cap40.sh"
sed 's/pgrep -x bootstrap 2>\/dev\/null; } | sort -un)"/pgrep -x bootstrap 2>\/dev\/null; } | sort -un | head -40)"/' \
  "$SYNC" >"$MUT_CAP"
if cmp -s "$SYNC" "$MUT_CAP"; then
  fail "mutation (40-PID cap) did not apply; the cap control tests nothing"
else
  guarded_restore "$MUT_CAP"; rc=$?
  if [ "$rc" -eq 0 ]; then
    pass "mutation control: the 40-PID cap misses the build behind the decoys (the guard failed open)"
  else
    fail "the 40-PID-cap mutant still refused (rc=$rc); case (3) does not exercise the cap"
  fi
fi
stop_fakes
MUT_SUB="$TMP_ROOT/submodule_sync.substring.sh"
sed 's/| cmdlines_naming_root)"/| grep -F "$ROOT" | awk '"'"'{print $1}'"'"')"/' \
  "$SYNC" >"$MUT_SUB"
if cmp -s "$SYNC" "$MUT_SUB"; then
  fail "mutation (substring match) did not apply; the sibling control tests nothing"
else
  fake_build "$K_TOP-b2/build/bootstrap/debug/rustc --crate-name sibling"
  guarded_restore "$MUT_SUB"; rc=$?
  if [ "$rc" -eq 4 ]; then
    pass "mutation control: the substring match refuses on a sibling's build (the false positive)"
  else
    fail "the substring mutant did not refuse on a sibling (rc=$rc); case (1) does not exercise it"
  fi
  stop_fakes
fi
MUT_LIST="$TMP_ROOT/submodule_sync.seplist.sh"
# The first version's boundary: a LIST of five separators instead of the complement
# of the name characters. Restored alone, it must let the `=` case of (2) through.
sed 's|if (after == "" \|\| after !~ /\[A-Za-z0-9._~+@%#-\]/) return 1|if (after == "" \|\| after == "/" \|\| after == " " \|\| after == "\\t" \|\| after == "\\"" \|\| after == "\\047") return 1|' \
  "$SYNC" >"$MUT_LIST"
if cmp -s "$SYNC" "$MUT_LIST"; then
  fail "mutation (separator list) did not apply; the '=' control tests nothing"
else
  fake_build "/usr/local/bin/rustc --remap-path-prefix=$K_TOP=/src main.rs"
  guarded_restore "$MUT_LIST"; rc=$?
  if [ "$rc" -eq 0 ]; then
    pass "mutation control: the five-separator list misses a build naming the root before '=' (the guard failed open)"
  else
    fail "the separator-list mutant still refused (rc=$rc); the '=' case of (2) does not exercise the boundary"
  fi
  stop_fakes
fi

if bash "$ROOT/scripts/tests/submodule_init_state_test.sh" "$SYNC"; then
  pass "pinned but unregistered nested sources are repaired without changing owner files"
else
  fail "nested initialization state regression"
fi

# A fresh parent reveals its children's .gitmodules only after initialization.
# One successful --restore must cover every newly discovered frontier, while
# retaining the same per-module dirty/unanchored/anchored decisions.
echo "=== fixture L: restore closes newly discovered nested frontiers ==="
L_LEAF="$TMP_ROOT/nested-leaf"
$GIT clone -q "$DONOR" "$L_LEAF"
L_CHILD="$L_LEAF"
for L_LEVEL in mid outer super; do
  L_PARENT="$TMP_ROOT/nested-$L_LEVEL"
  $GIT init -q -b main "$L_PARENT"
  echo root >"$L_PARENT/README"
  $GIT -C "$L_PARENT" add README
  $GIT -C "$L_PARENT" commit -qm root
  $GIT -C "$L_PARENT" submodule -q add "$L_CHILD" child
  $GIT -C "$L_PARENT" commit -qam "pin child"
  L_CHILD="$L_PARENT"
done
L_FRESH="$TMP_ROOT/nested-fresh"
$GIT clone -q --no-recurse-submodules "$L_CHILD" "$L_FRESH"
GIT_ALLOW_PROTOCOL=file bash "$SYNC" --root "$L_FRESH" --fetch --restore >"$TMP_ROOT/nested-restore.log" 2>&1
L_RESTORE_RC=$?
L_JSON="$(bash "$SYNC" --root "$L_FRESH" --offline --json)"
L_CHECK_RC=$?
if [ "$L_RESTORE_RC" -eq 0 ] && [ "$L_CHECK_RC" -eq 0 ] &&
   printf '%s\n' "$L_JSON" | python3 -c 'import json,sys; r=json.load(sys.stdin); assert r["total"] == r["synced"] == 3 and r["drifted"] == 0'; then
  pass "one restore reaches all three levels, and a fresh complete census agrees"
else
  fail "nested restore claimed incomplete success (restore=$L_RESTORE_RC, check=$L_CHECK_RC): $L_JSON"
fi

L_WORK="$L_FRESH/child/child/child"
$GIT -C "$L_WORK" checkout -q --detach "$C2"
echo "uncommitted nested work" >>"$L_WORK/f.txt"
L_DIRTY="$($GIT -C "$L_WORK" diff)"
bash "$SYNC" --root "$L_FRESH" --offline --restore >"$TMP_ROOT/nested-dirty.log" 2>&1
L_RC=$?
if [ "$L_RC" -eq 2 ] && [ "$(sha "$L_WORK" HEAD)" = "$C2" ] &&
   [ "$($GIT -C "$L_WORK" diff)" = "$L_DIRTY" ]; then
  pass "nested dirty work is refused without moving its HEAD or edits"
else
  fail "nested discovery bypassed the dirty-work refusal (rc=$L_RC)"
fi

$GIT -C "$L_WORK" checkout -- f.txt
$GIT -C "$L_WORK" checkout -q --detach "$C4"
echo unique >"$L_WORK/unique.txt"
$GIT -C "$L_WORK" add unique.txt
$GIT -C "$L_WORK" commit -qm "unanchored nested work"
L_UNIQUE="$(sha "$L_WORK" HEAD)"
L_REFS="$($GIT -C "$L_WORK" for-each-ref --contains "$L_UNIQUE")"
bash "$SYNC" --root "$L_FRESH" --offline --restore >"$TMP_ROOT/nested-unique.log" 2>&1
L_RC=$?
if [ "$L_RC" -eq 2 ] && [ -z "$L_REFS" ] && [ "$(sha "$L_WORK" HEAD)" = "$L_UNIQUE" ]; then
  pass "nested unanchored detached work is refused and stays at HEAD"
else
  fail "nested discovery moved unanchored work (rc=$L_RC)"
fi

$GIT -C "$L_WORK" update-ref refs/pins/nested-test "$L_UNIQUE"
bash "$SYNC" --root "$L_FRESH" --offline --restore >"$TMP_ROOT/nested-anchored.log" 2>&1
L_RC=$?
if [ "$L_RC" -eq 0 ] && [ "$(sha "$L_WORK" HEAD)" = "$C4" ] &&
   [ "$(sha "$L_WORK" refs/pins/nested-test)" = "$L_UNIQUE" ]; then
  pass "nested anchored restoration preserves the ref holding every unique commit"
else
  fail "nested anchored restoration failed or lost its durable ref (rc=$L_RC)"
fi

# A clean parent may ignore its nested worktree in `git status`. Its safe
# checkout can therefore replace the pin against which a child was classified.
# The old safe row must not authorize `submodule update` against that new pin.
echo "=== fixture M: parent movement invalidates old child decisions ==="
M_ROLLBACK="$(sha "$DONOR" main~3)"
M_PARENT="$TMP_ROOT/parent-changing-child-pin"
$GIT init -q -b main "$M_PARENT"
echo root >"$M_PARENT/README"
$GIT -C "$M_PARENT" add README
$GIT -C "$M_PARENT" commit -qm root
$GIT -C "$M_PARENT" submodule -q add "$DONOR" child
$GIT -C "$M_PARENT" config --file .gitmodules submodule.child.ignore all
$GIT -C "$M_PARENT" add .gitmodules child
$GIT -C "$M_PARENT" commit -qm "old child pin"
M_OLD="$(sha "$M_PARENT" HEAD)"
$GIT -C "$M_PARENT" update-index --cacheinfo "160000,$M_ROLLBACK,child"
$GIT -C "$M_PARENT" commit -qm "roll back child pin"
M_NEW="$(sha "$M_PARENT" HEAD)"
M_SUPER="$TMP_ROOT/super-changing-child-pin"
$GIT init -q -b main "$M_SUPER"
echo root >"$M_SUPER/README"
$GIT -C "$M_SUPER" add README
$GIT -C "$M_SUPER" commit -qm root
$GIT -C "$M_SUPER" submodule -q add "$M_PARENT" parent
$GIT -C "$M_SUPER" commit -qam "new parent pin"
$GIT -C "$M_SUPER/parent" checkout -q --detach "$M_OLD"
$GIT -C "$M_SUPER/parent" submodule -q update --init -- child
M_WORK="$M_SUPER/parent/child"
$GIT -C "$M_WORK" checkout -q --detach "$C2"
$GIT -C "$M_WORK" symbolic-ref -d refs/remotes/origin/HEAD 2>/dev/null || true
for M_REF in $($GIT -C "$M_WORK" for-each-ref --format='%(refname)'); do
  $GIT -C "$M_WORK" update-ref -d "$M_REF"
done
M_REFS="$($GIT -C "$M_WORK" for-each-ref --contains "$C2")"
M_CLEAN="$($GIT -C "$M_SUPER/parent" status --porcelain)"
bash "$SYNC" --root "$M_SUPER" --offline --restore >"$TMP_ROOT/changed-parent.log" 2>&1
M_RC=$?
if [ "$M_RC" -eq 2 ] && [ -z "$M_REFS" ] && [ -z "$M_CLEAN" ] &&
   [ "$(sha "$M_SUPER/parent" HEAD)" = "$M_NEW" ] && [ "$(sha "$M_WORK" HEAD)" = "$C2" ]; then
  pass "a changed parent pin is reclassified before an unanchored child could move"
else
  fail "a stale child decision moved unanchored work (rc=$M_RC, child=$(sha "$M_WORK" HEAD))"
fi

# ---------------------------------------------------------------------------
# Fixture L — a fresh outer checkout reveals nested gitlinks only AFTER its
# restoration. One invocation must discover every level; a later readonly
# invocation must not find the drift the first invocation claimed to repair.
# ---------------------------------------------------------------------------
echo "=== fixture L: restore discovers nested modules and reclassifies changed pins ==="
MIDDLE_L="$TMP_ROOT/nested-middle"
OUTER_L="$TMP_ROOT/nested-outer"
SOURCE_L="$TMP_ROOT/nested-source"
for repo in "$MIDDLE_L" "$OUTER_L" "$SOURCE_L"; do
  $GIT init -q -b main "$repo"
done
$GIT -C "$MIDDLE_L" submodule -q add "$DONOR" leaf
$GIT -C "$MIDDLE_L" commit -qm "middle records leaf"
MIDDLE_L_PIN="$(sha "$MIDDLE_L" HEAD)"
$GIT -C "$OUTER_L" submodule -q add "$MIDDLE_L" inner
$GIT -C "$OUTER_L" commit -qm "outer records middle"
$GIT -C "$SOURCE_L" submodule -q add "$OUTER_L" outer
$GIT -C "$SOURCE_L" commit -qm "root records outer"

COLD_L="$TMP_ROOT/nested-cold"
$GIT clone -q "$SOURCE_L" "$COLD_L"
GIT_ALLOW_PROTOCOL=file bash "$SYNC" --root "$COLD_L" --restore >"$TMP_ROOT/l_restore.log" 2>&1
RC_L=$?
bash "$SYNC" --root "$COLD_L" --offline --quiet >"$TMP_ROOT/l_check.log" 2>&1
CHECK_L=$?
if [ "$RC_L" -eq 0 ] && [ "$CHECK_L" -eq 0 ] &&
   [ "$(sha "$COLD_L/outer/inner" HEAD)" = "$MIDDLE_L_PIN" ] &&
   [ "$(sha "$COLD_L/outer/inner/leaf" HEAD)" = "$C4" ]; then
  pass "one restore initializes all three levels and a fresh full scan agrees"
else
  fail "nested restore was incomplete (restore=$RC_L check=$CHECK_L): $(tail -4 "$TMP_ROOT/l_restore.log")"
fi

# Removing rediscovery reproduces the original false success. This mutant
# exits after the initially visible outer row, leaving the children absent.
MUT_NESTED="$TMP_ROOT/submodule_sync.no-rediscovery.sh"
sed 's/^    scan_modules || exit \$?$/    break # mutant: no nested rediscovery/' \
  "$SYNC" >"$MUT_NESTED"
MUT_COLD_L="$TMP_ROOT/nested-mutant"
$GIT clone -q "$SOURCE_L" "$MUT_COLD_L"
GIT_ALLOW_PROTOCOL=file bash "$MUT_NESTED" --root "$MUT_COLD_L" --restore \
  >"$TMP_ROOT/l_mutant.log" 2>&1
RC_MUT_L=$?
bash "$SYNC" --root "$MUT_COLD_L" --offline --quiet >/dev/null 2>&1
CHECK_MUT_L=$?
if ! cmp -s "$SYNC" "$MUT_NESTED" && [ "$RC_MUT_L" -eq 0 ] && [ "$CHECK_MUT_L" -ne 0 ]; then
  pass "mutation control: no rediscovery returns success with nested drift remaining"
else
  fail "nested mutation did not reproduce false success (restore=$RC_MUT_L check=$CHECK_MUT_L)"
fi

# A nested clone failure cannot inherit the outer checkout's successful exit.
# The URL override is private to this fixture; no user's Git config is changed.
BAD_COLD_L="$TMP_ROOT/nested-failure"
BAD_CONFIG_L="$TMP_ROOT/nested-failure.gitconfig"
$GIT clone -q "$SOURCE_L" "$BAD_COLD_L"
$GIT config --file "$BAD_CONFIG_L" "url.$TMP_ROOT/missing-leaf.insteadOf" "$DONOR"
GIT_ALLOW_PROTOCOL=file GIT_CONFIG_GLOBAL="$BAD_CONFIG_L" GIT_CONFIG_NOSYSTEM=1 \
  bash "$SYNC" --root "$BAD_COLD_L" --restore >"$TMP_ROOT/l_failure.log" 2>&1
RC_BAD_L=$?
if [ "$RC_BAD_L" -ne 0 ] && grep -q 'restoring outer/inner/leaf ... FAILED' "$TMP_ROOT/l_failure.log"; then
  pass "a newly discovered nested restore failure returns failure"
else
  fail "nested failure was hidden (rc=$RC_BAD_L): $(tail -4 "$TMP_ROOT/l_failure.log")"
fi

# A parent can be clean at its old pin while its child holds a commit only HEAD
# retains: that old parent recorded the child itself. Advancing the parent may
# expose an unanchored child. Reclassify it and preserve it rather than trusting
# the old SYNCED row or restoring recursively.
UNIQUE_LEAF_L="$(new_commit "$COLD_L/outer/inner/leaf" "nested unanchored leaf")"
$GIT -C "$COLD_L/outer/inner" add leaf
$GIT -C "$COLD_L/outer/inner" commit -qm "old middle records unique leaf"
UNIQUE_MIDDLE_L="$(sha "$COLD_L/outer/inner" HEAD)"
$GIT -C "$COLD_L/outer" add inner
$GIT -C "$COLD_L/outer" commit -qm "old outer records unique middle"
OLD_OUTER_L="$(sha "$COLD_L/outer" HEAD)"
$GIT -C "$COLD_L/outer" update-index --cacheinfo "160000,$MIDDLE_L_PIN,inner"
$GIT -C "$COLD_L/outer" commit -qm "new outer selects original middle"
NEW_OUTER_L="$(sha "$COLD_L/outer" HEAD)"
$GIT -C "$COLD_L/outer" checkout -q "$OLD_OUTER_L"
$GIT -C "$COLD_L" update-index --cacheinfo "160000,$NEW_OUTER_L,outer"
$GIT -C "$COLD_L" commit -qm "root advances outer"
GIT_ALLOW_PROTOCOL=file bash "$SYNC" --root "$COLD_L" --restore >"$TMP_ROOT/l_unique.log" 2>&1
RC_UNIQUE_L=$?
if [ "$RC_UNIQUE_L" -eq 2 ] &&
   [ "$(sha "$COLD_L/outer" HEAD)" = "$NEW_OUTER_L" ] &&
   [ "$(sha "$COLD_L/outer/inner" HEAD)" = "$UNIQUE_MIDDLE_L" ] &&
   [ "$(sha "$COLD_L/outer/inner/leaf" HEAD)" = "$UNIQUE_LEAF_L" ]; then
  pass "advancing a parent exposes and preserves unanchored nested work"
else
  fail "nested unique work was moved or hidden (rc=$RC_UNIQUE_L): $(tail -5 "$TMP_ROOT/l_unique.log")"
fi

# ---------------------------------------------------------------------------
# Fixture M — --offline restricts an absent module's initial clone, not just
# fetch and anchor probes. A real local Git remote helper records invocation;
# it never opens a network connection, even under the intentionally bad mutant.
# ---------------------------------------------------------------------------
echo "=== fixture M: offline initialization never starts a remote transport ==="
M_BINS="$TMP_ROOT/offline-transport-bin"
M_TRACE="$TMP_ROOT/offline-transport-calls"
mkdir -p "$M_BINS"
cat >"$M_BINS/git-remote-offlineprobe" <<'HELPER'
#!/bin/sh
printf 'called\n' >>"${SUBMODULE_SYNC_OFFLINE_TRANSPORT_LOG:?}"
exit 1
HELPER
chmod +x "$M_BINS/git-remote-offlineprobe"
offline_probe_parent() {
  $GIT clone -q --no-recurse-submodules "$SUPER_E" "$1" || return $?
  $GIT -C "$1" config submodule.only.url offlineprobe::fixture
}

SUPER_M_ONLINE="$TMP_ROOT/online transport control"
offline_probe_parent "$SUPER_M_ONLINE"
: >"$M_TRACE"
PATH="$M_BINS:$PATH" GIT_ALLOW_PROTOCOL=file:offlineprobe \
  SUBMODULE_SYNC_OFFLINE_TRANSPORT_LOG="$M_TRACE" \
  bash "$SYNC" --root "$SUPER_M_ONLINE" --restore >"$TMP_ROOT/m_online.log" 2>&1
RC_M_ONLINE=$?
if [ "$RC_M_ONLINE" -eq 1 ] && [ -s "$M_TRACE" ]; then
  pass "the real Git clone reaches the recording transport when online"
else
  fail "the transport control was vacuous (rc=$RC_M_ONLINE): $(tail -4 "$TMP_ROOT/m_online.log")"
fi

SUPER_M_OFFLINE="$TMP_ROOT/offline transport control"
offline_probe_parent "$SUPER_M_OFFLINE"
M_HEAD="$(sha "$SUPER_M_OFFLINE" HEAD)"
: >"$M_TRACE"
PATH="$M_BINS:$PATH" GIT_ALLOW_PROTOCOL=file:offlineprobe \
  SUBMODULE_SYNC_OFFLINE_TRANSPORT_LOG="$M_TRACE" \
  bash "$SYNC" --root "$SUPER_M_OFFLINE" --offline --restore >"$TMP_ROOT/m_offline.log" 2>&1
RC_M_OFFLINE=$?
if [ "$RC_M_OFFLINE" -eq 1 ] && [ ! -s "$M_TRACE" ] &&
   [ ! -e "$SUPER_M_OFFLINE/only/.git" ] &&
   [ "$(sha "$SUPER_M_OFFLINE" HEAD)" = "$M_HEAD" ] &&
   grep -q '^restoring only ... FAILED' "$TMP_ROOT/m_offline.log"; then
  pass "offline cold restore refuses before any remote-helper invocation and preserves HEAD"
else
  fail "offline initialization reached a remote or hid its failure (rc=$RC_M_OFFLINE)"
fi

# Advice is executable, so it must retain the same offline transport restriction.
M_ADVICE="$(GIT_ALLOW_PROTOCOL=file:offlineprobe bash "$SYNC" --root "$SUPER_M_OFFLINE" --offline)"
M_CMD="$(printf '%s\n' "$M_ADVICE" | grep ' submodule update --init --no-fetch -- only$' | head -1 | sed 's/^ *//')"
: >"$M_TRACE"
PATH="$M_BINS:$PATH" GIT_ALLOW_PROTOCOL=file:offlineprobe \
  SUBMODULE_SYNC_OFFLINE_TRANSPORT_LOG="$M_TRACE" \
  bash -c "$M_CMD" >"$TMP_ROOT/m_advice.log" 2>&1
RC_M_ADVICE=$?
if [ -n "$M_CMD" ] && [ "$RC_M_ADVICE" -ne 0 ] && [ ! -s "$M_TRACE" ] &&
   [ "$(sha "$SUPER_M_OFFLINE" HEAD)" = "$M_HEAD" ]; then
  pass "printed offline initialization advice also refuses the remote transport"
else
  fail "offline initialization advice lost its transport restriction"
fi

# --no-fetch alone does not stop clone. Restore exactly that defect and require
# the native Git child to reach the helper despite the remaining --no-fetch.
MUT_OFFLINE_M="$TMP_ROOT/submodule_sync.offline-clone.sh"
sed 's/export GIT_ALLOW_PROTOCOL="$(offline_clone_protocols)"/: # mutant: protocol guard disabled/' "$SYNC" >"$MUT_OFFLINE_M"
if ! bash -n "$MUT_OFFLINE_M"; then
  fail "the offline-clone mutation must remain a valid program"
fi
SUPER_M_MUTANT="$TMP_ROOT/offline transport mutant"
offline_probe_parent "$SUPER_M_MUTANT"
: >"$M_TRACE"
PATH="$M_BINS:$PATH" GIT_ALLOW_PROTOCOL=file:offlineprobe \
  SUBMODULE_SYNC_OFFLINE_TRANSPORT_LOG="$M_TRACE" \
  bash "$MUT_OFFLINE_M" --root "$SUPER_M_MUTANT" --offline --restore >"$TMP_ROOT/m_mutant.log" 2>&1
RC_M_MUTANT=$?
if ! cmp -s "$SYNC" "$MUT_OFFLINE_M" && [ "$RC_M_MUTANT" -eq 1 ] && [ -s "$M_TRACE" ]; then
  pass "mutation control: --no-fetch alone still starts an initial remote clone"
else
  fail "offline-clone mutant did not expose the actual remote invocation (rc=$RC_M_MUTANT): $(tail -6 "$TMP_ROOT/m_mutant.log")"
fi

# Cold local clones require explicit permission passed to the child process;
# a parent's local config alone must not grant permission in another repository.
SUPER_M_FILE="$TMP_ROOT/offline configured local"
$GIT clone -q --no-recurse-submodules "$SUPER_E" "$SUPER_M_FILE"
$GIT -C "$SUPER_M_FILE" config protocol.file.allow always
env -u GIT_ALLOW_PROTOCOL bash "$SYNC" --root "$SUPER_M_FILE" --offline --restore \
  >"$TMP_ROOT/m_config_only.log" 2>&1
if [ "$?" -eq 1 ] && [ ! -e "$SUPER_M_FILE/only/.git" ]; then
  pass "a parent's file config alone cannot authorize a cold offline child clone"
else
  fail "offline initialization inferred child transport permission from its parent"
fi
GIT_ALLOW_PROTOCOL=file bash "$SYNC" --root "$SUPER_M_FILE" --offline --restore \
  >"$TMP_ROOT/m_file.log" 2>&1
RC_M_FILE=$?
if [ "$RC_M_FILE" -eq 0 ] && [ "$(sha "$SUPER_M_FILE/only" HEAD)" = "$C2" ]; then
  pass "offline initialization preserves the caller's explicit local file permission"
else
  fail "configured local initialization regressed (rc=$RC_M_FILE)"
fi
SUPER_M_DENIED="$TMP_ROOT/offline forbidden local"
$GIT clone -q --no-recurse-submodules "$SUPER_E" "$SUPER_M_DENIED"
$GIT -C "$SUPER_M_DENIED" config protocol.file.allow never
env -u GIT_ALLOW_PROTOCOL bash "$SYNC" --root "$SUPER_M_DENIED" --offline --restore \
  >"$TMP_ROOT/m_denied.log" 2>&1
if [ "$?" -eq 1 ] && [ ! -e "$SUPER_M_DENIED/only/.git" ]; then
  pass "offline initialization never enables a forbidden local file transport"
else
  fail "offline initialization widened local file transport permission"
fi
SUPER_M_RESTRICTED="$TMP_ROOT/offline caller-restricted local"
$GIT clone -q --no-recurse-submodules "$SUPER_E" "$SUPER_M_RESTRICTED"
$GIT -C "$SUPER_M_RESTRICTED" config protocol.file.allow always
GIT_ALLOW_PROTOCOL=offlineprobe bash "$SYNC" --root "$SUPER_M_RESTRICTED" --offline --restore \
  >"$TMP_ROOT/m_restricted.log" 2>&1
if [ "$?" -eq 1 ] && [ ! -e "$SUPER_M_RESTRICTED/only/.git" ]; then
  pass "the caller's narrower protocol whitelist still excludes local cloning"
else
  fail "offline initialization widened the caller's protocol whitelist"
fi

# A cached module needs no transport even when its origin would be unreachable.
$GIT -C "$SUPER_M_FILE/only" remote set-url origin offlineprobe::fixture
mv "$SUPER_M_FILE/only" "$TMP_ROOT/offline-old-worktree"
: >"$M_TRACE"
PATH="$M_BINS:$PATH" GIT_ALLOW_PROTOCOL=offlineprobe \
  SUBMODULE_SYNC_OFFLINE_TRANSPORT_LOG="$M_TRACE" \
  bash "$SYNC" --root "$SUPER_M_FILE" --offline --restore >"$TMP_ROOT/m_cache.log" 2>&1
RC_M_CACHE=$?
if [ "$RC_M_CACHE" -eq 0 ] && [ ! -s "$M_TRACE" ] &&
   [ "$(sha "$SUPER_M_FILE/only" HEAD)" = "$C2" ]; then
  pass "offline initialization reuses a cached selected commit with every transport forbidden"
else
  fail "offline cached initialization regressed (rc=$RC_M_CACHE): $(tail -4 "$TMP_ROOT/m_cache.log")"
fi

# ---------------------------------------------------------------------------
# Fixture N — native partial clones may lazily fetch during ordinary reads or
# checkout. All donors/transports are local; upload-pack records real access.
# ---------------------------------------------------------------------------
echo "=== fixture N: offline promised objects stay missing and unreadable state stays reviewable ==="
N_REMOTE="$TMP_ROOT/promisor donor.git"
N_UPLOAD="$TMP_ROOT/recording-upload-pack"
N_TRACE="$TMP_ROOT/promisor-upload-calls"
$GIT clone -q --bare "$DONOR" "$N_REMOTE"
$GIT -C "$N_REMOTE" config uploadpack.allowFilter true
$GIT -C "$N_REMOTE" config uploadpack.allowAnySHA1InWant true
cat >"$N_UPLOAD" <<'HELPER'
#!/bin/sh
printf 'called\n' >>"${SUBMODULE_SYNC_PROMISOR_LOG:?}"
exec git upload-pack "$@"
HELPER
chmod +x "$N_UPLOAD"
N_BLOB="$($GIT -C "$DONOR" rev-parse "$C4:f.txt")"
promisor_parent() {
  $GIT clone -q --no-recurse-submodules "$SUPER_E" "$1" || return $?
  env -u GIT_NO_LAZY_FETCH git -c protocol.file.allow=always clone -q \
    --no-checkout --filter=blob:none "file://$N_REMOTE" "$1/only" || return $?
  env -u GIT_NO_LAZY_FETCH git -c protocol.file.allow=always -C "$1/only" \
    -c advice.detachedHead=false checkout -q --detach "$C2" || return $?
  $GIT -C "$1" update-index --cacheinfo "160000,$C4,only" || return $?
  $GIT -C "$1" commit -qm "select the local commit with a promised blob" || return $?
  $GIT -C "$1/only" config remote.origin.uploadpack "$N_UPLOAD"
}

SUPER_N="$TMP_ROOT/offline initialized promisor"
promisor_parent "$SUPER_N"
N_HEAD="$(sha "$SUPER_N" HEAD)"
cp "$SUPER_N/only/f.txt" "$TMP_ROOT/n_expected_worktree"
GIT_NO_LAZY_FETCH=1 $GIT -C "$SUPER_N/only" rev-list --objects --missing=print --all \
  | sort >"$TMP_ROOT/n_missing_before"
if ! GIT_NO_LAZY_FETCH=1 $GIT -C "$SUPER_N/only" cat-file -e "$N_BLOB" 2>/dev/null &&
   [ "$(sha "$SUPER_N/only" HEAD)" = "$C2" ]; then
  pass "the native initialized partial clone lacks the selected pin's promised blob"
else
  fail "the native partial-clone control materialized its selected blob too early"
fi
: >"$N_TRACE"
GIT_ALLOW_PROTOCOL=file GIT_NO_LAZY_FETCH=0 SUBMODULE_SYNC_PROMISOR_LOG="$N_TRACE" \
  bash "$SYNC" --root "$SUPER_N" --offline --restore >"$TMP_ROOT/n_restore.log" 2>&1
RC_N_RESTORE=$?
GIT_NO_LAZY_FETCH=1 $GIT -C "$SUPER_N/only" rev-list --objects --missing=print --all \
  | sort >"$TMP_ROOT/n_missing_after"
if [ "$RC_N_RESTORE" -ne 0 ] && [ ! -s "$N_TRACE" ] &&
   [ "$(sha "$SUPER_N/only" HEAD)" = "$C2" ] &&
   [ "$(sha "$SUPER_N" HEAD)" = "$N_HEAD" ] &&
   cmp -s "$SUPER_N/only/f.txt" "$TMP_ROOT/n_expected_worktree" &&
   cmp -s "$TMP_ROOT/n_missing_before" "$TMP_ROOT/n_missing_after" &&
   grep -q '^restoring only ... FAILED' "$TMP_ROOT/n_restore.log"; then
  pass "offline initialized checkout refuses the missing blob without an implicit fetch or HEAD move"
else
  fail "offline initialized checkout fetched or hid missing content (rc=$RC_N_RESTORE): $(tail -4 "$TMP_ROOT/n_restore.log")"
fi

SUPER_N_ADVICE="$TMP_ROOT/offline promisor advice"
promisor_parent "$SUPER_N_ADVICE"
N_ADVICE="$(GIT_ALLOW_PROTOCOL=file bash "$SYNC" --root "$SUPER_N_ADVICE" --offline)"
N_CMD="$(printf '%s\n' "$N_ADVICE" | grep ' submodule update --init --no-fetch -- only$' | head -1 | sed 's/^ *//')"
: >"$N_TRACE"
GIT_ALLOW_PROTOCOL=file GIT_NO_LAZY_FETCH=0 SUBMODULE_SYNC_PROMISOR_LOG="$N_TRACE" \
  bash -c "$N_CMD" >"$TMP_ROOT/n_advice.log" 2>&1
RC_N_ADVICE=$?
if [ -n "$N_CMD" ] && [ "$RC_N_ADVICE" -ne 0 ] && [ ! -s "$N_TRACE" ] &&
   [ "$(sha "$SUPER_N_ADVICE/only" HEAD)" = "$C2" ]; then
  pass "executable initialized-module advice also suppresses promised-object fetching"
else
  fail "offline initialized-module advice lost its no-lazy-fetch restriction"
fi

# The convenience command re-enters this script; it must preserve both the
# offline lane and an explicit fixture/root selection when copied verbatim.
N_ALL_CMD="$(printf '%s\n' "$N_ADVICE" | grep '^    scripts/submodule_sync.sh' | head -1 | sed 's/^ *//')"
: >"$N_TRACE"
GIT_ALLOW_PROTOCOL=file GIT_NO_LAZY_FETCH=0 SUBMODULE_SYNC_PROMISOR_LOG="$N_TRACE" \
  bash -c "$N_ALL_CMD" >"$TMP_ROOT/n_all_advice.log" 2>&1
RC_N_ALL_ADVICE=$?
if [ -n "$N_ALL_CMD" ] && [ "$RC_N_ALL_ADVICE" -ne 0 ] && [ ! -s "$N_TRACE" ] &&
   grep -q -- '--offline' <<<"$N_ALL_CMD" &&
   grep -q -- '--root' <<<"$N_ALL_CMD" &&
   grep -q '^restoring only ... FAILED' "$TMP_ROOT/n_all_advice.log" &&
   [ "$(sha "$SUPER_N_ADVICE/only" HEAD)" = "$C2" ]; then
  pass "the executable convenience advice preserves its offline lane and selected root"
else
  fail "convenience advice changed root, enabled fetching, or failed before restoration (rc=$RC_N_ALL_ADVICE)"
fi

# The direct-checkout branch for a linked module needs the same restrictions,
# and must preserve its primary checkout and shared missing-object inventory.
SUPER_N_LINK="$TMP_ROOT/offline linked promisor"
$GIT clone -q --no-recurse-submodules "$SUPER_E" "$SUPER_N_LINK"
$GIT -C "$SUPER_N_ADVICE/only" worktree add -q --detach "$SUPER_N_LINK/only" "$C2"
$GIT -C "$SUPER_N_LINK" update-index --cacheinfo "160000,$C4,only"
$GIT -C "$SUPER_N_LINK" commit -qm "select promised content in a linked module"
N_LINK_HEAD="$(sha "$SUPER_N_LINK" HEAD)"
N_LINK_INDEX="$($GIT -C "$SUPER_N_LINK/only" rev-parse --absolute-git-dir)/index"
cp "$N_LINK_INDEX" "$TMP_ROOT/n_link_index_before"
GIT_NO_LAZY_FETCH=1 $GIT -C "$SUPER_N_LINK/only" rev-list --objects --missing=print --all \
  | sort >"$TMP_ROOT/n_link_missing_before"
N_LINK_ADVICE="$(GIT_ALLOW_PROTOCOL=file bash "$SYNC" --root "$SUPER_N_LINK" --offline)"
N_LINK_CMD="$(printf '%s\n' "$N_LINK_ADVICE" | grep ' checkout --detach ' | head -1 | sed 's/^ *//')"
: >"$N_TRACE"
GIT_ALLOW_PROTOCOL=file GIT_NO_LAZY_FETCH=0 SUBMODULE_SYNC_PROMISOR_LOG="$N_TRACE" \
  bash -c "$N_LINK_CMD" >"$TMP_ROOT/n_link_advice.log" 2>&1
RC_N_LINK_ADVICE=$?
GIT_ALLOW_PROTOCOL=file GIT_NO_LAZY_FETCH=0 SUBMODULE_SYNC_PROMISOR_LOG="$N_TRACE" \
  bash "$SYNC" --root "$SUPER_N_LINK" --offline --restore >"$TMP_ROOT/n_link_restore.log" 2>&1
RC_N_LINK_RESTORE=$?
GIT_NO_LAZY_FETCH=1 $GIT -C "$SUPER_N_LINK/only" rev-list --objects --missing=print --all \
  | sort >"$TMP_ROOT/n_link_missing_after"
if [ -n "$N_LINK_CMD" ] && [ "$RC_N_LINK_ADVICE" -ne 0 ] && [ "$RC_N_LINK_RESTORE" -eq 1 ] &&
   [ ! -s "$N_TRACE" ] && [ "$(sha "$SUPER_N_LINK" HEAD)" = "$N_LINK_HEAD" ] &&
   [ "$(sha "$SUPER_N_LINK/only" HEAD)" = "$C2" ] &&
   [ "$(sha "$SUPER_N_ADVICE/only" HEAD)" = "$C2" ] &&
   cmp -s "$SUPER_N_LINK/only/f.txt" "$TMP_ROOT/n_expected_worktree" &&
   cmp -s "$N_LINK_INDEX" "$TMP_ROOT/n_link_index_before" &&
   cmp -s "$TMP_ROOT/n_link_missing_before" "$TMP_ROOT/n_link_missing_after" &&
   grep -q '^restoring only ... FAILED' "$TMP_ROOT/n_link_restore.log"; then
  pass "linked checkout advice and restore suppress fetching and preserve both checkouts and missing objects"
else
  fail "linked promised checkout fetched or changed its source (advice=$RC_N_LINK_ADVICE restore=$RC_N_LINK_RESTORE)"
fi

MUT_PROMISOR_N="$TMP_ROOT/submodule_sync.lazy-fetch.sh"
sed '/export GIT_NO_LAZY_FETCH=1/d' "$SYNC" >"$MUT_PROMISOR_N"
SUPER_N_MUTANT="$TMP_ROOT/offline promisor mutant"
promisor_parent "$SUPER_N_MUTANT"
: >"$N_TRACE"
GIT_ALLOW_PROTOCOL=file GIT_NO_LAZY_FETCH=0 SUBMODULE_SYNC_PROMISOR_LOG="$N_TRACE" \
  bash "$MUT_PROMISOR_N" --root "$SUPER_N_MUTANT" --offline --restore >"$TMP_ROOT/n_mutant.log" 2>&1
RC_N_MUTANT=$?
if ! cmp -s "$SYNC" "$MUT_PROMISOR_N" && [ "$RC_N_MUTANT" -eq 0 ] && [ -s "$N_TRACE" ] &&
   [ "$(sha "$SUPER_N_MUTANT/only" HEAD)" = "$C4" ]; then
  pass "mutation control: initialized --no-fetch checkout really invokes the native promisor transport"
else
  fail "the no-lazy-fetch mutant did not reproduce implicit fetching (rc=$RC_N_MUTANT): $(tail -4 "$TMP_ROOT/n_mutant.log")"
fi

# A promised root tree makes ls-tree fail. It must retain the registered module
# in the denominator and require review, rather than claiming NO-GITLINK/green.
N_ROOT_REMOTE="$TMP_ROOT/promisor root.git"
$GIT clone -q --bare "$SUPER_E" "$N_ROOT_REMOTE"
$GIT -C "$N_ROOT_REMOTE" config uploadpack.allowFilter true
$GIT -C "$N_ROOT_REMOTE" config uploadpack.allowAnySHA1InWant true
SUPER_N_ROOT="$TMP_ROOT/offline unreadable root"
env -u GIT_NO_LAZY_FETCH git -c protocol.file.allow=always clone -q \
  --no-checkout --filter=tree:0 "file://$N_ROOT_REMOTE" "$SUPER_N_ROOT"
cp "$SUPER_E/.gitmodules" "$SUPER_N_ROOT/.gitmodules"
$GIT -C "$SUPER_N_ROOT" config remote.origin.uploadpack "$N_UPLOAD"
N_TREE="$($GIT -C "$SUPER_E" rev-parse 'HEAD^{tree}')"
: >"$N_TRACE"
GIT_ALLOW_PROTOCOL=file GIT_NO_LAZY_FETCH=0 SUBMODULE_SYNC_PROMISOR_LOG="$N_TRACE" \
  bash "$SYNC" --root "$SUPER_N_ROOT" --offline --json >"$TMP_ROOT/n_root.log" 2>&1
RC_N_ROOT=$?
if [ "$RC_N_ROOT" -eq 2 ] && [ ! -s "$N_TRACE" ] &&
   grep -q '"total":1' "$TMP_ROOT/n_root.log" &&
   grep -q '"needs_review":1' "$TMP_ROOT/n_root.log" &&
   grep -q '"state":"PIN-UNREADABLE"' "$TMP_ROOT/n_root.log" &&
   ! GIT_NO_LAZY_FETCH=1 $GIT -C "$SUPER_N_ROOT" cat-file -e "$N_TREE" 2>/dev/null; then
  pass "an unreadable promised tree remains one reviewable module without fetching"
else
  fail "unreadable root state fetched or disappeared from the denominator (rc=$RC_N_ROOT): $(tail -4 "$TMP_ROOT/n_root.log")"
fi
: >"$N_TRACE"
GIT_ALLOW_PROTOCOL=file GIT_NO_LAZY_FETCH=0 SUBMODULE_SYNC_PROMISOR_LOG="$N_TRACE" \
  bash "$SYNC" --root "$SUPER_N_ROOT" --json >"$TMP_ROOT/n_root_default.log" 2>&1
if [ "$?" -eq 2 ] && [ ! -s "$N_TRACE" ] &&
   grep -q '"state":"PIN-UNREADABLE"' "$TMP_ROOT/n_root_default.log" &&
   ! GIT_NO_LAZY_FETCH=1 $GIT -C "$SUPER_N_ROOT" cat-file -e "$N_TREE" 2>/dev/null; then
  pass "default diagnosis also exposes local promised-tree absence without lazy fetching"
else
  fail "default diagnosis fetched or hid the promised root tree"
fi
: >"$N_TRACE"
GIT_ALLOW_PROTOCOL=file GIT_NO_LAZY_FETCH=0 SUBMODULE_SYNC_PROMISOR_LOG="$N_TRACE" \
  git -C "$SUPER_N_ROOT" ls-tree HEAD -- only >"$TMP_ROOT/n_root_control.log" 2>&1
if [ "$?" -eq 0 ] && [ -s "$N_TRACE" ] && grep -q "$C2" "$TMP_ROOT/n_root_control.log"; then
  pass "the native ls-tree positive control fetches the genuinely promised root tree"
else
  fail "the missing-root-tree control was vacuous"
fi

# A native status failure must never become dirty=0 and permission to restore.
SUPER_N_STATUS="$TMP_ROOT/offline unreadable status"
promisor_parent "$SUPER_N_STATUS"
N_INDEX="$($GIT -C "$SUPER_N_STATUS/only" rev-parse --absolute-git-dir)/index"
printf 'invalid index\n' >"$N_INDEX"
cp "$N_INDEX" "$TMP_ROOT/n_expected_index"
: >"$N_TRACE"
GIT_ALLOW_PROTOCOL=file SUBMODULE_SYNC_PROMISOR_LOG="$N_TRACE" \
  bash "$SYNC" --root "$SUPER_N_STATUS" --offline --json >"$TMP_ROOT/n_status_state.log" 2>&1
RC_N_STATUS_SCAN=$?
GIT_ALLOW_PROTOCOL=file SUBMODULE_SYNC_PROMISOR_LOG="$N_TRACE" \
  bash "$SYNC" --root "$SUPER_N_STATUS" --offline --restore >"$TMP_ROOT/n_status.log" 2>&1
RC_N_STATUS=$?
if [ "$RC_N_STATUS_SCAN" -eq 2 ] && [ "$RC_N_STATUS" -eq 2 ] && [ ! -s "$N_TRACE" ] &&
   grep -q '"state":"STATUS-UNREADABLE"' "$TMP_ROOT/n_status_state.log" &&
   grep -q '"needs_review":1' "$TMP_ROOT/n_status_state.log" &&
   [ "$(sha "$SUPER_N_STATUS/only" HEAD)" = "$C2" ] &&
   cmp -s "$N_INDEX" "$TMP_ROOT/n_expected_index"; then
  pass "native unreadable status requires review and preserves HEAD and index bytes"
else
  fail "a native status failure became restoration permission (rc=$RC_N_STATUS): $(tail -4 "$TMP_ROOT/n_status.log")"
fi


# ---------------------------------------------------------------------------
# Fixture Q — a present pin is not evidence that its ancestor objects exist.
# Remove only the owned clone's loose ancestor; the donor keeps its copy.
# Explicit refetch must repair the graph before existing safe restore rules run.
# ---------------------------------------------------------------------------
echo "=== fixture Q: missing ancestry is unknown, exact-pin refetch can repair it ==="
DONOR_Q="$TMP_ROOT/ancestry donor"
SUPER_Q="$TMP_ROOT/ancestry parent"
make_donor "$DONOR_Q"
mkdir -p "$SUPER_Q"
$GIT init -q -b main "$SUPER_Q"
echo root >"$SUPER_Q/root"
$GIT -C "$SUPER_Q" add root
$GIT -C "$SUPER_Q" commit -qm root
$GIT -C "$SUPER_Q" submodule -q add "$DONOR_Q" only 2>/dev/null
$GIT -C "$SUPER_Q" commit -qam module
Q_PIN="$(sha "$DONOR_Q" main)"
Q_HEAD="$(sha "$DONOR_Q" main~3)"
Q_MISSING="$(sha "$DONOR_Q" main~2)"
$GIT -C "$SUPER_Q/only" checkout -q --detach "$Q_HEAD"
Q_OBJECTS="$($GIT -C "$SUPER_Q/only" rev-parse --absolute-git-dir)/objects"
Q_FILE="$Q_OBJECTS/${Q_MISSING:0:2}/${Q_MISSING:2}"
Q_REFS="$($GIT -C "$SUPER_Q/only" for-each-ref)"
if [ -f "$Q_FILE" ] && $GIT -C "$SUPER_Q/only" cat-file -e "$Q_PIN^{commit}"; then
  rm -f "$Q_FILE"
  if $GIT -C "$DONOR_Q" cat-file -e "$Q_MISSING^{commit}" &&
     ! $GIT -C "$SUPER_Q/only" cat-file -e "$Q_MISSING^{commit}" 2>/dev/null; then
    pass "fixture: clone lacks an ancestor but retains HEAD/pin and donor retains ancestor"
  else
    fail "fixture did not isolate the missing ancestor to its owned clone"
  fi
else
  fail "fixture requires a real loose ancestor and an already-present pin"
fi
Q_UNREADABLE_ERR="$($GIT -C "$SUPER_Q/only" merge-base "$Q_HEAD" "$Q_PIN" 2>&1 >/dev/null)"
Q_UNREADABLE_RC=$?
# Newer git exits 128 here. Git 2.43.0 exits 1, the status of unrelated roots, and
# says `error: Could not read <sha>`; unrelated roots print nothing.
if [ "$Q_UNREADABLE_RC" -ne 0 ] &&
   { [ "$Q_UNREADABLE_RC" -ne 1 ] || printf '%s' "$Q_UNREADABLE_ERR" | grep -q "Could not read $Q_MISSING"; }; then
  pass "fixture: native merge-base reports unreadable history, not unrelated roots"
else
  fail "fixture did not produce a native ancestry error (rc=$Q_UNREADABLE_RC, stderr: $Q_UNREADABLE_ERR)"
fi
Q_JSON="$(bash "$SYNC" --root "$SUPER_Q" --offline --json)"
Q_SCAN=$?
bash "$SYNC" --root "$SUPER_Q" --offline --restore >"$TMP_ROOT/q_offline.log" 2>&1
Q_RESTORE=$?
if [ "$Q_SCAN" -eq 2 ] && [ "$Q_RESTORE" -eq 2 ] &&
   printf '%s' "$Q_JSON" | grep -q '"state":"ANCESTRY-UNREADABLE"' &&
   [ "$(sha "$SUPER_Q/only" HEAD)" = "$Q_HEAD" ] &&
   ! $GIT -C "$SUPER_Q/only" cat-file -e "$Q_MISSING^{commit}" 2>/dev/null; then
  pass "offline incomplete ancestry stays unknown and moves neither HEAD nor objects"
else
  fail "incomplete ancestry was called unrelated or allowed restoration: $Q_JSON"
fi
Q_TEXT="$(bash "$SYNC" --root "$SUPER_Q" --offline 2>&1 || true)"
if printf '%s' "$Q_TEXT" | grep -q -- '--fetch --restore'; then
  pass "incomplete ancestry names the explicit supported repair"
else
  fail "incomplete ancestry omitted actionable explicit-fetch advice"
fi
SUBMODULE_SYNC_TRACE_NET=1 bash "$SYNC" --root "$SUPER_Q" --fetch --json   >"$TMP_ROOT/q_repaired.json" 2>"$TMP_ROOT/q_net.log"
Q_FETCH=$?
if [ "$Q_FETCH" -eq 1 ] &&
   grep -q '"state":"BEHIND","ahead":0,"behind":3' "$TMP_ROOT/q_repaired.json" &&
   $GIT -C "$SUPER_Q/only" cat-file -e "$Q_MISSING^{commit}" &&
   [ "$(sha "$SUPER_Q/only" HEAD)" = "$Q_HEAD" ] &&
   [ "$($GIT -C "$SUPER_Q/only" for-each-ref)" = "$Q_REFS" ]; then
  pass "explicit exact-pin refetch repairs missing history into safe BEHIND without new refs"
else
  fail "present pin did not permit safe ancestry repair: $(cat "$TMP_ROOT/q_repaired.json")"
fi
bash "$SYNC" --root "$SUPER_Q" --offline --restore >"$TMP_ROOT/q_restored.log" 2>&1
if [ "$?" -eq 0 ] && [ "$(sha "$SUPER_Q/only" HEAD)" = "$Q_PIN" ]; then
  pass "the repaired complete history restores through the existing BEHIND rule"
else
  fail "repaired BEHIND history did not restore safely"
fi

# A complete unrelated graph is not incomplete evidence and must not be fetched
# or restored, even though a real local branch holds the orphan commit.
SUPER_Q_UNRELATED="$TMP_ROOT/unrelated parent"
mkdir -p "$SUPER_Q_UNRELATED"
$GIT init -q -b main "$SUPER_Q_UNRELATED"
echo root >"$SUPER_Q_UNRELATED/root"
$GIT -C "$SUPER_Q_UNRELATED" add root
$GIT -C "$SUPER_Q_UNRELATED" commit -qm root
$GIT -C "$SUPER_Q_UNRELATED" submodule -q add "$DONOR_Q" only 2>/dev/null
$GIT -C "$SUPER_Q_UNRELATED" commit -qam module
$GIT -C "$SUPER_Q_UNRELATED/only" checkout -q --orphan unrelated
$GIT -C "$SUPER_Q_UNRELATED/only" rm -q -rf .
echo unrelated >"$SUPER_Q_UNRELATED/only/unrelated"
$GIT -C "$SUPER_Q_UNRELATED/only" add unrelated
$GIT -C "$SUPER_Q_UNRELATED/only" commit -qm unrelated
Q_ORPHAN="$(sha "$SUPER_Q_UNRELATED/only" HEAD)"
Q_UNRELATED_REFS="$($GIT -C "$SUPER_Q_UNRELATED/only" for-each-ref)"
$GIT -C "$SUPER_Q_UNRELATED/only" merge-base "$Q_ORPHAN" "$Q_PIN" >/dev/null 2>&1
Q_TRUE_UNRELATED=$?
Q_UNRELATED_JSON="$(bash "$SYNC" --root "$SUPER_Q_UNRELATED" --offline --json)"
Q_UNRELATED_SCAN=$?
SUBMODULE_SYNC_TRACE_NET=1 bash "$SYNC" --root "$SUPER_Q_UNRELATED" --fetch --restore   >"$TMP_ROOT/q_unrelated.log" 2>"$TMP_ROOT/q_unrelated_net.log"
Q_UNRELATED_RESTORE=$?
if [ "$Q_UNRELATED_RESTORE" -eq 2 ] && [ "$Q_TRUE_UNRELATED" -eq 1 ] &&
   [ "$Q_UNRELATED_SCAN" -eq 2 ] &&
   printf '%s' "$Q_UNRELATED_JSON" | grep -q '"state":"UNRELATED"' &&
   [ "$(sha "$SUPER_Q_UNRELATED/only" HEAD)" = "$Q_ORPHAN" ] &&
   [ "$($GIT -C "$SUPER_Q_UNRELATED/only" for-each-ref)" = "$Q_UNRELATED_REFS" ] &&
   ! grep -q '^net:' "$TMP_ROOT/q_unrelated_net.log"; then
  pass "genuine complete-history UNRELATED remains refused without fetch or ref changes"
else
  fail "unrelated control failed (merge-base=$Q_TRUE_UNRELATED, restore=$Q_UNRELATED_RESTORE)"
  cat "$TMP_ROOT/q_unrelated.log" "$TMP_ROOT/q_unrelated_net.log" >&2
  printf 'expected HEAD=%s; observed HEAD=%s\n' "$Q_ORPHAN" "$(sha "$SUPER_Q_UNRELATED/only" HEAD)" >&2
  printf 'expected refs:\n%s\nobserved refs:\n%s\n' "$Q_UNRELATED_REFS" "$($GIT -C "$SUPER_Q_UNRELATED/only" for-each-ref)" >&2
fi

# ---------------------------------------------------------------------------
# Fixture O — a present commit can lack its root tree even in a nonpromisor,
# nonshallow store. An exact-pin fetch then succeeds without refilling the tree.
# Neither ancestry nor an equal HEAD is sufficient to claim usable pinned data.
# ---------------------------------------------------------------------------
echo "=== fixture O: present commit with missing root tree ==="
SUPER_O="$TMP_ROOT/incomplete root tree"
mkdir -p "$SUPER_O"
$GIT init -q -b main "$SUPER_O"
echo root >"$SUPER_O/README"
$GIT -C "$SUPER_O" add README
$GIT -C "$SUPER_O" commit -qm root
for name in behind atpin; do
  $GIT -C "$SUPER_O" submodule -q add "$DONOR" "$name" 2>/dev/null
  $GIT -C "$SUPER_O/$name" checkout -q "$C4"
  $GIT -C "$SUPER_O" add "$name"
done
$GIT -C "$SUPER_O" commit -qm "pin both at c4"
$GIT -C "$SUPER_O/behind" checkout -q "$C2"
O_TREE="$($GIT -C "$SUPER_O/behind" rev-parse "$C4^{tree}")"
cp "$SUPER_O/behind/f.txt" "$TMP_ROOT/o_behind_expected"
cp "$SUPER_O/atpin/f.txt" "$TMP_ROOT/o_atpin_expected"
for name in behind atpin; do
  O_GITDIR="$($GIT -C "$SUPER_O/$name" rev-parse --absolute-git-dir)"
  mv "$O_GITDIR/objects/${O_TREE:0:2}/${O_TREE:2}" "$TMP_ROOT/o_saved_tree_$name"
done
if [ "$($GIT -C "$SUPER_O/behind" rev-parse --is-shallow-repository)" = false ] &&
   ! $GIT -C "$SUPER_O/behind" config --get remote.origin.promisor >/dev/null &&
   $GIT -C "$SUPER_O/behind" cat-file -e "$C4^{commit}" &&
   ! $GIT -C "$SUPER_O/behind" cat-file -e "$O_TREE" 2>/dev/null; then
  pass "fixture: full nonpromisor store has the commit but lacks its root tree"
else
  fail "incomplete-root-tree fixture was not established"
fi
$GIT -C "$SUPER_O/behind" fetch -q --no-auto-maintenance origin "$C4" >"$TMP_ROOT/o_fetch.log" 2>&1
if [ "$?" -eq 0 ] && ! $GIT -C "$SUPER_O/behind" cat-file -e "$O_TREE" 2>/dev/null; then
  pass "native exact-pin fetch exits 0 without repairing an already-present commit's tree"
else
  fail "the native already-have fetch control did not reproduce missing-tree behavior"
fi
O_JSON="$(bash "$SYNC" --root "$SUPER_O" --json)"
RC_O=$?
if [ "$RC_O" -eq 2 ] &&
   printf '%s' "$O_JSON" | grep -q '"path":"behind","state":"PIN-INCOMPLETE"' &&
   printf '%s' "$O_JSON" | grep -q '"path":"atpin","state":"PIN-INCOMPLETE"' &&
   printf '%s' "$O_JSON" | grep -q '"restorable":0' &&
   printf '%s' "$O_JSON" | grep -q '"needs_review":2' &&
   printf '%s' "$O_JSON" | grep -q "$O_TREE"; then
  pass "missing root trees require review for both behind and apparently synced modules"
else
  fail "missing-root-tree state was falsely restorable or green: $O_JSON"
fi
SUBMODULE_SYNC_TRACE_NET=1 bash "$SYNC" --root "$SUPER_O" --fetch --json >"$TMP_ROOT/o_fetch_state.log" 2>"$TMP_ROOT/o_fetch_trace"
if [ "$?" -eq 2 ] && [ ! -s "$TMP_ROOT/o_fetch_trace" ]; then
  pass "--fetch does not turn a missing root tree into an automatic history refetch"
else
  fail "--fetch tried to repair known incomplete history implicitly"
fi
bash "$SYNC" --root "$SUPER_O" >"$TMP_ROOT/o_report.log" 2>&1
if grep -q "$O_TREE" "$TMP_ROOT/o_report.log" &&
   grep -q 'Repair the selected pin' "$TMP_ROOT/o_report.log" &&
   grep -q 'GIT_NO_LAZY_FETCH=1 git -C' "$TMP_ROOT/o_report.log" &&
   grep -q 'exact-pin fetch can exit 0' "$TMP_ROOT/o_report.log" &&
   ! grep -q 'fetch --refetch' "$TMP_ROOT/o_report.log"; then
  pass "the report names the missing tree and local inspection without prescribing a broad refetch"
else
  fail "incomplete-object report lacks an actionable bounded diagnosis"
fi
bash "$SYNC" --root "$SUPER_O" --restore --force >"$TMP_ROOT/o_restore.log" 2>&1
if [ "$?" -eq 2 ] && [ "$(sha "$SUPER_O/behind" HEAD)" = "$C2" ] &&
   [ "$(sha "$SUPER_O/atpin" HEAD)" = "$C4" ] &&
   cmp -s "$SUPER_O/behind/f.txt" "$TMP_ROOT/o_behind_expected" &&
   cmp -s "$SUPER_O/atpin/f.txt" "$TMP_ROOT/o_atpin_expected"; then
  pass "incomplete-root refusal preserves both module HEADs and worktree bytes"
else
  fail "an incomplete root tree allowed a restore or changed worktree data"
fi

# Explicit GitHub repair orchestration with a substituted transfer provider.
# Missing trees, refs, indices, worktrees and checkout are genuine local Git.
# This unit provider grants no evidence about Agh's network implementation.
echo "=== fixture Q: explicit Agh repair of present-commit missing trees ==="
SUPER_Q="$TMP_ROOT/github incomplete source"
cp -R "$SUPER_O" "$SUPER_Q"
SUPER_Q="$(cd "$SUPER_Q" && pwd -P)"
Q_PROVIDER="$TMP_ROOT/q-provider"
mkdir -p "$Q_PROVIDER"
printf '%s\n' "$SUPER_Q" >"$Q_PROVIDER/root"
printf '%s\n' "$C4" >"$Q_PROVIDER/pin"
$GIT -C "$SUPER_Q/atpin" cat-file commit "$C4" >"$Q_PROVIDER/commit"
printf 'objects/%s/%s\n' "${O_TREE:0:2}" "${O_TREE:2}" >"$Q_PROVIDER/object-relative"
for name in behind atpin; do
  cp "$TMP_ROOT/o_saved_tree_$name" "$Q_PROVIDER/tree-$name"
  $GIT -C "$SUPER_Q/$name" remote set-url origin https://github.com/fixture/source.git
  $GIT -C "$SUPER_Q" config -f .gitmodules "submodule.$name.url" https://github.com/fixture/source.git
  Q_GITDIR="$($GIT -C "$SUPER_Q/$name" rev-parse --absolute-git-dir)"
  cp "$Q_GITDIR/index" "$Q_PROVIDER/index-$name"
  $GIT -C "$SUPER_Q/$name" for-each-ref --format='%(refname) %(objectname)' >"$Q_PROVIDER/refs-$name"
done
$GIT -C "$SUPER_Q" add .gitmodules
$GIT -C "$SUPER_Q" commit -qm "fixture canonical GitHub URLs"
cat >"$Q_PROVIDER/agh" <<'EOF'
#!/bin/sh
set -eu
base="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd -P)"
printf 'call\n%s\n' "$@" >>"$base/trace"
root="$(cat "$base/root")"; pin="$(cat "$base/pin")"
[ "$#" -eq 9 ] && [ "$9" = --checkout-closure ] && [ "$1" = repo ] && [ "$2" = fetch ] && [ "$3" = fixture/source ]
[ "$5" = --ref ] && [ "$6" = "$pin" ] && [ "$7" = --into ]
[ "$8" = "refs/agh/trust-source-pins/$pin" ]
case "$4" in "$root/behind") name=behind ;; "$root/atpin") name=atpin ;; *) exit 98 ;; esac
case "$(cat "$base/mode")" in
  refuse) echo 'fixture owner-routed Agh refusal' >&2; exit 73 ;;
  no-objects) ;;
  repair)
    git -C "$4" hash-object -w -t commit "$base/commit" >/dev/null
    gitdir="$(git -C "$4" rev-parse --absolute-git-dir)"
    object="$(cat "$base/object-relative")"
    mkdir -p "$(dirname "$gitdir/$object")"
    [ -e "$gitdir/$object" ] || cp "$base/tree-$name" "$gitdir/$object"
    ;;
  *) exit 97 ;;
esac
git -C "$4" update-ref "$8" "$pin"
EOF
chmod +x "$Q_PROVIDER/agh"
printf 'refuse\n' >"$Q_PROVIDER/mode"
PATH="$Q_PROVIDER:$PATH" bash "$SYNC" --root "$SUPER_Q" --json >"$Q_PROVIDER/readonly.log" 2>&1
if [ "$?" -eq 2 ] && [ ! -e "$Q_PROVIDER/trace" ]; then
  pass "read-only missing-tree diagnosis never launches the provider"
else fail "read-only sync attempted a GitHub acquisition"; fi
PATH="$Q_PROVIDER:$PATH" SUBMODULE_SYNC_TRACE_NET=1 bash "$SYNC" --root "$SUPER_Q" --fetch --restore --force \
  >"$Q_PROVIDER/refused.log" 2>&1
if [ "$?" -eq 2 ] && grep -q 'fixture owner-routed Agh refusal' "$Q_PROVIDER/refused.log" &&
   grep -q 'no Git fallback' "$Q_PROVIDER/refused.log" &&
   ! grep -q '^net: fetch ' "$Q_PROVIDER/refused.log" &&
   [ "$(sha "$SUPER_Q/behind" HEAD)" = "$C2" ]; then
  pass "an Agh refusal remains red, retains its reason and never falls back to Git"
else fail "refused Agh repair was hidden or granted restoration"; fi
printf 'no-objects\n' >"$Q_PROVIDER/mode"
PATH="$Q_PROVIDER:$PATH" bash "$SYNC" --root "$SUPER_Q" --fetch --json \
  >"$Q_PROVIDER/no-objects.json" 2>"$Q_PROVIDER/no-objects.log"
if [ "$?" -eq 2 ] && grep -q '"needs_review":2' "$Q_PROVIDER/no-objects.json" &&
   grep -q 'root tree is not locally readable' "$Q_PROVIDER/no-objects.log" &&
   ! $GIT -C "$SUPER_Q/behind" cat-file -e "$O_TREE" 2>/dev/null; then
  pass "provider exit 0 and an exact private ref cannot replace materialized root objects"
else fail "a successful provider without a local tree became a positive classification"; fi
printf 'repair\n' >"$Q_PROVIDER/mode"
echo 'uncommitted owned work' >>"$SUPER_Q/behind/f.txt"
cp "$SUPER_Q/behind/f.txt" "$Q_PROVIDER/dirty-expected"
PATH="$Q_PROVIDER:$PATH" bash "$SYNC" --root "$SUPER_Q" --fetch --restore --force \
  >"$Q_PROVIDER/repaired-dirty.log" 2>&1
Q_RC=$?
Q_PRESERVED=1
for name in behind atpin; do
  Q_GITDIR="$($GIT -C "$SUPER_Q/$name" rev-parse --absolute-git-dir)"
  $GIT -C "$SUPER_Q/$name" for-each-ref --format='%(refname) %(objectname)' \
    | grep -v '^refs/agh/trust-source-pins/' >"$Q_PROVIDER/after-refs-$name"
  cp "$Q_GITDIR/index" "$Q_PROVIDER/after-index-$name"
  cmp -s "$Q_PROVIDER/index-$name" "$Q_GITDIR/index" || Q_PRESERVED=0
  cmp -s "$Q_PROVIDER/refs-$name" "$Q_PROVIDER/after-refs-$name" || Q_PRESERVED=0
  $GIT -C "$SUPER_Q/$name" cat-file -e "$O_TREE" || Q_PRESERVED=0
done
if [ "$Q_RC" -eq 2 ] && [ "$Q_PRESERVED" -eq 1 ] &&
   [ "$(sha "$SUPER_Q/behind" HEAD)" = "$C2" ] && [ "$(sha "$SUPER_Q/atpin" HEAD)" = "$C4" ] &&
   cmp -s "$Q_PROVIDER/dirty-expected" "$SUPER_Q/behind/f.txt"; then
  pass "real object repair preserves dirty work, index, original refs and both HEADs"
else fail "object repair weakened the existing dirty/index/ref/HEAD guards"; fi
cp "$TMP_ROOT/o_behind_expected" "$SUPER_Q/behind/f.txt"
PATH="$Q_PROVIDER:$PATH" bash "$SYNC" --root "$SUPER_Q" --fetch --restore --force \
  >"$Q_PROVIDER/clean-restore.log" 2>&1
if [ "$?" -eq 0 ] && [ "$(sha "$SUPER_Q/behind" HEAD)" = "$C4" ] &&
   [ "$(sha "$SUPER_Q/atpin" HEAD)" = "$C4" ]; then
  pass "after materialization the unchanged lossless restore reaches the exact pins"
else fail "the repaired clean source could not use normal lossless restoration"; fi

# A real native lock failure deterministically exercises stderr preservation;
# Git may legitimately reuse an existing index/worktree without loading a blob.
SUPER_P="$TMP_ROOT/native locked checkout"
mkdir -p "$SUPER_P"
$GIT init -q -b main "$SUPER_P"
echo root >"$SUPER_P/README"
$GIT -C "$SUPER_P" add README
$GIT -C "$SUPER_P" commit -qm root
$GIT -C "$SUPER_P" submodule -q add "$DONOR" only 2>/dev/null
$GIT -C "$SUPER_P/only" checkout -q "$C4"
$GIT -C "$SUPER_P" add only
$GIT -C "$SUPER_P" commit -qm "pin at c4"
$GIT -C "$SUPER_P/only" checkout -q "$C2"
P_GITDIR="$($GIT -C "$SUPER_P/only" rev-parse --absolute-git-dir)"
printf 'owned fixture lock\n' >"$P_GITDIR/index.lock"
cp "$SUPER_P/only/f.txt" "$TMP_ROOT/p_expected_worktree"
bash "$SYNC" --root "$SUPER_P" --restore --force >"$TMP_ROOT/p_restore.log" 2>&1
RC_P=$?
if [ "$RC_P" -ne 0 ] && grep -q 'FAILED (git exit' "$TMP_ROOT/p_restore.log" &&
   grep -q 'index.lock' "$TMP_ROOT/p_restore.log" &&
   [ "$(sha "$SUPER_P/only" HEAD)" = "$C2" ] &&
   cmp -s "$SUPER_P/only/f.txt" "$TMP_ROOT/p_expected_worktree"; then
  pass "a failed real checkout preserves native lock stderr, exit status, HEAD and bytes"
else
  fail "native checkout failure collapsed to an unexplained FAILED: $(cat "$TMP_ROOT/p_restore.log")"
fi

# Missing commit acquisition must use the same Agh-only exact closure path.
Q_GITDIR="$($GIT -C "$SUPER_Q/atpin" rev-parse --absolute-git-dir)"
$GIT -C "$SUPER_Q/atpin" update-ref -d "refs/agh/trust-source-pins/$C4"
rm "$Q_GITDIR/objects/${C4:0:2}/${C4:2}"
if $GIT -C "$SUPER_Q/atpin" cat-file -e "${C4}^{commit}" 2>/dev/null; then
  fail "missing GitHub commit fixture did not remove the selected commit"
else
  PATH="$Q_PROVIDER:$PATH" SUBMODULE_SYNC_TRACE_NET=1 bash "$SYNC" --root "$SUPER_Q" --fetch --restore --force \
    >"$Q_PROVIDER/missing-commit.log" 2>&1
  if [ "$?" -eq 0 ] && $GIT -C "$SUPER_Q/atpin" cat-file -e "${C4}^{commit}" &&
     grep -q 'repaired exact pin' "$Q_PROVIDER/missing-commit.log" &&
     ! grep -q '^net: fetch ' "$Q_PROVIDER/missing-commit.log"; then
    pass "a wholly missing GitHub pin is materialized through Agh without a Git fetch"
  else fail "missing GitHub commit did not use the exact Agh acquisition"; fi
fi

# ---------------------------------------------------------------------------
# Fixture T — a pin fetch the bound ended. The remote holds the pin and is
# sending it; the transfer is only longer than FETCH_TIMEOUT. That used to be
# reported as "origin did not provide pin" (2026-11-10, first-party/trust-ir, a
# 17 GiB transfer under the fixed 600 s bound), which is the message for a pin
# nobody published.
# ---------------------------------------------------------------------------
echo "=== fixture T: a timed-out pin fetch is reported as a timeout ==="
DONOR_T="$TMP_ROOT/donor_t"
make_donor "$DONOR_T"
SUPER_T="$TMP_ROOT/super_t"
$GIT init -q -b main "$SUPER_T"
echo root >"$SUPER_T/README"
$GIT -C "$SUPER_T" add README
$GIT -C "$SUPER_T" commit -qm root
$GIT -C "$SUPER_T" submodule -q add "$DONOR_T" slow 2>/dev/null
$GIT -C "$SUPER_T" commit -qm "add, pinned at c4" >/dev/null
T4="$(sha "$SUPER_T/slow" HEAD)"
echo "line 5" >>"$DONOR_T/f.txt"
$GIT -C "$DONOR_T" commit -qam c5
T5="$(sha "$DONOR_T" main)"
$GIT -C "$SUPER_T" update-index --cacheinfo "160000,$T5,slow"
$GIT -C "$SUPER_T" commit -qm "pull: pin moved" >/dev/null
# The remote answers every request, three seconds late.
$GIT -C "$SUPER_T/slow" config remote.origin.uploadpack "sleep 3; git-upload-pack"
T_LOG="$TMP_ROOT/t_fetch.log"
SUBMODULE_SYNC_FETCH_TIMEOUT=1 bash "$SYNC" --root "$SUPER_T" --fetch --restore --force >"$T_LOG" 2>&1
RC_T=$?
if grep -q 'slow: fetching pin .* did not finish within 1s' "$T_LOG" \
   && grep -q 'SUBMODULE_SYNC_FETCH_TIMEOUT=<seconds>' "$T_LOG" \
   && ! grep -q 'did not provide pin' "$T_LOG"; then
  pass "a fetch the bound ended names the bound, not a pin the remote lacks"
else
  fail "timed-out fetch misreported: $(cat "$T_LOG")"
fi
if [ "$RC_T" -eq 2 ] && [ "$(sha "$SUPER_T/slow" HEAD)" = "$T4" ]; then
  pass "the timed-out module is left where it was and the run exits 2"
else
  fail "after a timed-out fetch: exit $RC_T, HEAD $(sha "$SUPER_T/slow" HEAD) (expected 2 and $T4)"
fi
# Control: the same slow remote under the default bound provides the pin.
bash "$SYNC" --root "$SUPER_T" --fetch --restore --force >"$T_LOG" 2>&1
RC_T=$?
if [ "$RC_T" -eq 0 ] && [ "$(sha "$SUPER_T/slow" HEAD)" = "$T5" ] \
   && grep -q 'slow: fetched pin' "$T_LOG"; then
  pass "control: under the default bound the same remote provides the pin"
else
  fail "control: slow remote not fetched under the default bound (exit $RC_T): $(cat "$T_LOG")"
fi
for bad in abc 0 -5 ''; do
  SUBMODULE_SYNC_FETCH_TIMEOUT="$bad" bash "$SYNC" --root "$SUPER_T" >/dev/null 2>&1
  RC_T=$?
  if [ "$bad" = '' ]; then
    # An empty value is "unset": the default applies.
    [ "$RC_T" -eq 0 ] && pass "an empty SUBMODULE_SYNC_FETCH_TIMEOUT keeps the default" \
      || fail "empty SUBMODULE_SYNC_FETCH_TIMEOUT exited $RC_T"
  elif [ "$RC_T" -eq 3 ]; then
    pass "SUBMODULE_SYNC_FETCH_TIMEOUT='$bad' is refused as a usage error (exit 3)"
  else
    fail "SUBMODULE_SYNC_FETCH_TIMEOUT='$bad' exited $RC_T, expected 3"
  fi
done

echo
if [ "$FAILURES" -eq 0 ]; then
  echo "submodule_sync_test: PASS"
  exit 0
fi
echo "submodule_sync_test: $FAILURES assertion(s) failed"
exit 1
