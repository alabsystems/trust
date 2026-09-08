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

set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SYNC="$ROOT/scripts/submodule_sync.sh"
TMP_ROOT="$(mktemp -d)"
trap 'rm -rf "$TMP_ROOT"' EXIT

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
CMD="$(bash "$SYNC" --root "$SUPER_B" | grep -E '^\s+git -C .* submodule update --init -- only$' | head -1 | sed 's/^ *//')"
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

echo
if [ "$FAILURES" -eq 0 ]; then
  echo "submodule_sync_test: PASS"
  exit 0
fi
echo "submodule_sync_test: $FAILURES assertion(s) failed"
exit 1
