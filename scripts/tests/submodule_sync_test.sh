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
# Fixture WP needs a directory outside TMP_ROOT's top-level directory; it is
# named here so the exit removes it however the run ends.
OUTSIDE_DIRS=""
trap 'for p in $DECOY_PIDS; do pkill -P "$p"; kill "$p"; done 2>/dev/null; for d in $OUTSIDE_DIRS; do rm -rf "$d"; done; if [ "${FAILURES:-1}" -eq 0 ]; then rm -rf "$TMP_ROOT"; else printf "retained failed sync fixture: %s\n" "$TMP_ROOT" >&2; fi' EXIT

FAILURES=0
fail() { echo "FAIL: $*" >&2; FAILURES=$((FAILURES + 1)); }
pass() { echo "  ok: $*"; }
# A captured report is searched with `grep -q ... <<<"$TEXT"`, never
# `printf ... | grep -q`: under pipefail a grep that exits at its first match
# can leave the writer a closed pipe, and the check then fails by timing.

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
# The person's and the machine's git config are neither written nor READ: a
# global submodule.recurse or worktree.useRelativePaths would change what plain
# git does in the fixtures.
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1
# Nor a repository this was started from. A run from a hook, or under
# `git -c`, inherits GIT_DIR, GIT_INDEX_FILE, GIT_CONFIG_PARAMETERS,
# GIT_SHALLOW_FILE and the like, and the fixtures' git would write there.
unset $(git rev-parse --local-env-vars)
# Git reads the person's ignore and attributes files from XDG_CONFIG_HOME
# whatever GIT_CONFIG_GLOBAL says.
export XDG_CONFIG_HOME="$TMP_ROOT/xdg"
# What the script makes with mktemp (a probe's repository) stays in the
# scratch root too, where a check can see that none is left behind.
mkdir -p "$TMP_ROOT/tmp"
export TMPDIR="$TMP_ROOT/tmp"

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
  if grep -q "\"path\":\"$1\",\"state\":\"$2\"" <<<"$JSON"; then
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
  if grep -q "\"path\":\"$1\",[^}]*\"anchored\":$2" <<<"$JSON"; then
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
if grep -q "\"path\":\"m_div_partial\",[^}]*\"anchor_detail\":\"${QQ:0:8}[^\"]*no refs/pins" <<<"$JSON"; then
  pass "m_div_partial names the one unanchored commit (${QQ:0:8})"
else
  fail "m_div_partial did not name the unanchored commit; got $(printf '%s' "$JSON" | tr '{' '\n' | grep m_div_partial)"
fi

# A remote that cannot be read is not a remote that said yes.
if grep -q '"path":"m_unreachable",[^}]*"anchor_detail":"NOT ANCHORED, fail-closed: could not read refs/pins' <<<"$JSON"; then
  pass "unreadable remote fails closed and says so"
else
  fail "unreadable remote did not report a fail-closed reason; got $(printf '%s' "$JSON" | tr '{' '\n' | grep m_unreachable)"
fi

if grep -q '"path":"m_ahead_anchored",[^}]*"anchor_detail":"[0-9a-f]* refs/tags/keep/ahead' <<<"$JSON"; then
  pass "the anchoring ref is named, not merely counted"
else
  fail "m_ahead_anchored did not name refs/tags/keep/ahead"
fi
if grep -q "\"path\":\"m_remote_anchored\",[^}]*\"anchor_detail\":\"[0-9a-f]* remote refs/pins/$RR" <<<"$JSON"; then
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
   && grep -q '"path":"m_remote_anchored",[^}]*"anchored":0' <<<"$OFF_JSON" \
   && grep -q '"path":"m_ahead_anchored",[^}]*"anchored":1' <<<"$OFF_JSON"; then
  pass "--offline issues no probe: locally-proved anchors stand, remote-only ones fail closed"
else
  fail "--offline behaved wrongly (probes=$(wc -l <"$OFFLOG" | tr -d ' '))"
fi

# The counts must be real, not just the label.
if grep -q '"path":"m_behind","state":"BEHIND","ahead":0,"behind":2' <<<"$JSON"; then
  pass "m_behind reports 0 ahead / 2 behind"
else
  fail "m_behind commit counts wrong"
fi
if grep -q '"path":"m_ahead","state":"AHEAD","ahead":2,"behind":0' <<<"$JSON"; then
  pass "m_ahead reports 2 ahead / 0 behind"
else
  fail "m_ahead commit counts wrong"
fi
if grep -q '"path":"m_divergent","state":"DIVERGENT","ahead":1,"behind":2' <<<"$JSON"; then
  pass "m_divergent reports 1 ahead / 2 behind"
else
  fail "m_divergent commit counts wrong"
fi
if grep -q '"path":"m_dirty","state":"BEHIND","ahead":0,"behind":2,"worktree":"[0-9a-f]*","pin":"[0-9a-f]*","dirty":1' <<<"$JSON"; then
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
if grep -q '"path":"gone","state":"PIN-MISSING"' <<<"$JSON_C"; then
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
if grep -q 'inspect:.*fetch --all' <<<"$TEXT_C"; then
  fail "PIN-MISSING advises 'fetch --all', which cannot retrieve an anchored pin"
else
  pass "PIN-MISSING does not advise 'fetch --all'"
fi
if grep -q 'fetch origin 0123456789012345678901234567890123456789' <<<"$TEXT_C"; then
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
# being linked must not turn the advice into a parent HEAD checkout, and the
# advice for a linked parent is a worktree of the repository's own module
# store (fixture W), not a clone under the linked parent's git directory.
SUPER_G="$TMP_ROOT/linked absent"
$GIT -C "$SUPER_E" worktree add -q --detach "$SUPER_G" HEAD
G_HEAD="$(sha "$SUPER_G" HEAD)"
G_ADVICE="$(GIT_ALLOW_PROTOCOL=file bash "$SYNC" --root "$SUPER_G" --offline)"
G_CMD="$(printf '%s\n' "$G_ADVICE" | grep ' worktree add --detach ' | head -1 | sed 's/^ *//')"
if [ -n "$G_CMD" ] && GIT_ALLOW_PROTOCOL=file bash -c "$G_CMD" >/dev/null 2>&1 &&
   [ "$(sha "$SUPER_G/only" HEAD)" = "$C2" ] &&
   [ "$(sha "$SUPER_G" HEAD)" = "$G_HEAD" ] && linked_primary_unchanged &&
   [ ! -e "$(git -C "$SUPER_G" rev-parse --absolute-git-dir)/modules" ]; then
  pass "absent submodule in a linked parent is advised as a worktree of the shared store and preserves parent HEAD"
else
  fail "absent linked-parent advice mistakes the parent for the submodule, or clones a private store"
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
  grep -q "\"path\":\"$m\",\"state\":\"PIN-MISSING\"" <<<"$JSON_H0" && H0_MISSING=$((H0_MISSING + 1))
done
if [ "$H0_MISSING" -eq 4 ] && ! grep -q 'net: fetch' "$H_NET"; then
  pass "control: without --fetch all four are PIN-MISSING and nothing is fetched"
else
  fail "control: expected 4 PIN-MISSING and no fetch, got $H0_MISSING and $(grep -c 'net: fetch' "$H_NET")"
fi
TEXT_H0="$(bash "$SYNC" --root "$SUPER_H" 2>&1 || true)"
if grep -q 'scripts/submodule_sync.sh --fetch --restore' <<<"$TEXT_H0"; then
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
if grep -q '"path":"h_div","state":"DIVERGENT","ahead":1,"behind":1,[^}]*"anchored":0' <<<"$JSON_H1" \
   && grep -q '"path":"h_gone","state":"PIN-MISSING"' <<<"$JSON_H1"; then
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

# ---------------------------------------------------------------------------
# Fixture W — a second worktree of the superproject shares the repository's own
# module stores (DC-13a). After the two documented commands (`git worktree add
# --detach <dir> <commit>`, then `--fetch --restore` there) each of its
# submodule checkouts is a LINKED WORKTREE of <common git dir>/modules/<name>:
# no second copy of any submodule's objects, and nothing borrowed from a store
# that a worktree removal deletes. The first checkout has two shallow stores
# (seven of Trust's nine were on the Mac this was written on), a complete
# store, one with a nested module (trust-cg's layout, where the parent of the
# nested module is itself a linked checkout) and one whose name and path each
# hold a space. The second worktree pins a commit that each of three stores
# lacks, so the one fetch into a shared store runs, by sha:
#   m_shallow  shallow, two commits deep (root W3, HEAD W4). Its pin W5 is a
#              child of HEAD: it DESCENDS from the root. No branch of the
#              remote holds W5.
#   m_old      shallow, one commit (root W4). Its pin W2 is OLDER than the
#              root, and the remote holds history under it (W1) and between
#              the two (W3).
#   m_full     complete. Its pin is W5 too.
# A store is shared as it is. A shallow one gets its pin alone and stays
# shallow, with nothing of the remote's history under the pin or under its
# roots; the complete one gets what it lacks and stays complete; and the first
# checkout reads in each exactly the commits it read before. Then what plain
# git can break in that shape, and that --restore ends it; the second
# worktree's removal; the same path again; a pin that moves in a checkout
# already there; and the stores that are not shared.
# ---------------------------------------------------------------------------
echo "=== fixture W: a second worktree shares the repository's own module stores ==="
DONOR_W="$TMP_ROOT/donor_w" # no space in it: it is a file:// URL below
make_donor "$DONOR_W"
W4="$(sha "$DONOR_W" main)"
W3="$(sha "$DONOR_W" main~1)"
W2="$(sha "$DONOR_W" main~2)"
W1="$(sha "$DONOR_W" main~3)"
W_SIDE="$(sha "$DONOR_W" side)" # leaves main at W2
# The pins a store is asked for by sha are ref tips too, for a git whose
# transport sends only those.
$GIT -C "$DONOR_W" update-ref refs/pins/w1 "$W1"
$GIT -C "$DONOR_W" update-ref refs/pins/w2 "$W2"
$GIT -C "$DONOR_W" update-ref refs/pins/w3 "$W3"
# The remote sends commits without their trees and files when asked, as
# GitHub does: the probe of a shallow store asks for exactly that.
$GIT -C "$DONOR_W" config uploadpack.allowFilter true
W_LEAF_REPO="$TMP_ROOT/w-leaf"
W_MID_REPO="$TMP_ROOT/w-mid"
$GIT clone -q "$DONOR" "$W_LEAF_REPO"
$GIT init -q -b main "$W_MID_REPO"
echo root >"$W_MID_REPO/README"
$GIT -C "$W_MID_REPO" add README
$GIT -C "$W_MID_REPO" commit -qm root
$GIT -C "$W_MID_REPO" submodule -q add "$W_LEAF_REPO" child
$GIT -C "$W_MID_REPO" commit -qam "pin child"
SUPER_W="$TMP_ROOT/w first"
SECOND_W="$TMP_ROOT/w second"
THIRD_W="$TMP_ROOT/w third"
$GIT init -q -b main "$SUPER_W"
echo root >"$SUPER_W/README"
$GIT -C "$SUPER_W" add README
$GIT -C "$SUPER_W" commit -qm root
$GIT -C "$SUPER_W" submodule -q add --depth 2 "file://$DONOR_W" m_shallow 2>/dev/null
$GIT -C "$SUPER_W" submodule -q add --depth 1 "file://$DONOR_W" m_old 2>/dev/null
$GIT -C "$SUPER_W" submodule -q add "$DONOR_W" m_full 2>/dev/null
$GIT -C "$SUPER_W" submodule -q add "$W_MID_REPO" m_nest 2>/dev/null
$GIT -C "$SUPER_W" submodule -q add --name "sp name" "$DONOR_W" "m sp" 2>/dev/null
$GIT -C "$SUPER_W" submodule -q update --init --recursive
$GIT -C "$SUPER_W" commit -qm "two shallow stores, one complete, one with a nested module, one with spaces"
W_NEST="$(sha "$SUPER_W/m_nest" HEAD)"
W_LEAF="$(sha "$SUPER_W/m_nest/child" HEAD)"
W_BODY="$(cat "$SUPER_W/m_full/f.txt")"
# W5 is on no branch of the remote: a detached commit that only refs/pins/w5
# holds, so nothing but a fetch of that sha can bring it. It is made after the
# first checkout cloned, so the complete store lacks it as well. It adds a
# file larger than the limit the restore below gives a probe (W_PROBE_KB): a
# probe that downloaded files would stop there.
W_PROBE_KB=64
$GIT -C "$DONOR_W" checkout -q --detach main
echo "line 5" >>"$DONOR_W/f.txt"
head -c 262144 /dev/urandom >"$DONOR_W/big.bin"
$GIT -C "$DONOR_W" add big.bin
$GIT -C "$DONOR_W" commit -qam c5
W5="$(sha "$DONOR_W" HEAD)"
$GIT -C "$DONOR_W" update-ref refs/pins/w5 "$W5"
$GIT -C "$DONOR_W" checkout -q main
$GIT -C "$SUPER_W" worktree add -q --detach "$SECOND_W" HEAD
$GIT -C "$SECOND_W" update-index --cacheinfo "160000,$W5,m_shallow"
$GIT -C "$SECOND_W" update-index --cacheinfo "160000,$W2,m_old"
$GIT -C "$SECOND_W" update-index --cacheinfo "160000,$W5,m_full"
$GIT -C "$SECOND_W" commit -qm "the second worktree pins a commit each of three stores lacks"
W_SECOND_COMMIT="$(sha "$SECOND_W" HEAD)"
W_STORES="$SUPER_W/.git/modules"
w_lacks() { # <store> <commit>...: the store holds none of them
  local store="$1" c
  shift
  for c in "$@"; do
    ! git --git-dir="$store" cat-file -e "$c^{commit}" 2>/dev/null || return 1
  done
}
w_roots() { # <store> <commit>...: exactly these are its shallow roots
  local store="$1"
  shift
  [ "$(sort "$store/shallow" 2>/dev/null)" = "$(printf '%s\n' "$@" | sort)" ]
}
if [ "$(sha "$DONOR_W" main)" = "$W4" ] &&
   git -C "$DONOR_W" cat-file -e "$W1^{commit}" && git -C "$DONOR_W" cat-file -e "$W3^{commit}" &&
   [ "$(git -C "$SUPER_W/m_shallow" rev-parse --is-shallow-repository)" = true ] &&
   w_roots "$W_STORES/m_shallow" "$W3" && [ "$(sha "$SUPER_W/m_shallow" HEAD)" = "$W4" ] &&
   w_lacks "$W_STORES/m_shallow" "$W5" "$W2" "$W1" &&
   w_roots "$W_STORES/m_old" "$W4" && w_lacks "$W_STORES/m_old" "$W3" "$W2" "$W1" &&
   [ ! -e "$W_STORES/m_full/shallow" ] && w_lacks "$W_STORES/m_full" "$W5" &&
   [ "$(git --git-dir="$W_STORES/m_full" rev-list --count "$W4")" -eq 4 ] &&
   [ -f "$W_STORES/m_nest/modules/child/HEAD" ] && [ -f "$W_STORES/sp name/HEAD" ] &&
   [ ! -e "$SECOND_W/m_shallow/.git" ] && [ ! -e "$SECOND_W/m_old/.git" ] && [ ! -e "$SECOND_W/m_full/.git" ] &&
   [ ! -e "$SECOND_W/m_nest/.git" ] && [ ! -e "$SECOND_W/m sp/.git" ]; then
  pass "fixture: a shallow store whose missing pin descends from its root, one whose missing pin is older than its root, a complete store that lacks its pin, a nested store, a store with spaces, and five ABSENT checkouts"
else
  fail "fixture W invalid: the stores or the second worktree are not in the shape the checks need"
fi

# Copied BEFORE any restore: fixture E takes its copy after its own hand-made
# `worktree add`, so it cannot show that creating the linked checkout leaves
# the first checkout's config alone. These can.
W_COPIES="$TMP_ROOT/w-copies"
mkdir -p "$W_COPIES"
for W_S in m_shallow m_old m_full m_nest m_nest/modules/child "sp name"; do
  cp "$W_STORES/$W_S/config" "$W_COPIES/$(printf '%s' "$W_S" | tr / _).config"
done
cp "$SUPER_W/.git/config" "$W_COPIES/super.config"
# The refs of the stores a fetch goes into: it must write none, and no FETCH_HEAD.
w_store_refs() {
  local s
  for s in m_shallow m_old m_full; do
    git --git-dir="$W_STORES/$s" for-each-ref
    ls "$W_STORES/$s/FETCH_HEAD" 2>&1
  done
}
W_STORE_REFS="$(w_store_refs)"
# Every commit the first checkout reads from each of its checkouts, through
# its HEAD and through every branch, tag and tracking ref of the store, in
# order. The same list afterwards means none was hidden and none was added
# under it. (Not `--all`: that lists other worktrees' HEADs too.)
w_first_history() {
  local m
  for m in m_shallow m_old m_full "m sp" m_nest m_nest/child; do
    printf '%s:\n' "$m"
    git -C "$SUPER_W/$m" rev-list HEAD --branches --tags --remotes 2>&1
  done
}
W_FIRST_HISTORY="$(w_first_history)"
w_configs_unchanged() {
  local s
  for s in m_shallow m_old m_full m_nest m_nest/modules/child "sp name"; do
    cmp -s "$W_STORES/$s/config" "$W_COPIES/$(printf '%s' "$s" | tr / _).config" || return 1
  done
  cmp -s "$SUPER_W/.git/config" "$W_COPIES/super.config"
}
w_first_unchanged() { # the first checkout's HEADs, files and status
  [ "$(sha "$SUPER_W/m_shallow" HEAD)" = "$W4" ] && [ "$(sha "$SUPER_W/m_full" HEAD)" = "$W4" ] &&
    [ "$(sha "$SUPER_W/m_old" HEAD)" = "$W4" ] && [ "$(sha "$SUPER_W/m sp" HEAD)" = "$W4" ] &&
    [ "$(sha "$SUPER_W/m_nest" HEAD)" = "$W_NEST" ] && [ "$(sha "$SUPER_W/m_nest/child" HEAD)" = "$W_LEAF" ] &&
    [ "$(cat "$SUPER_W/m_shallow/f.txt")" = "$W_BODY" ] && [ "$(cat "$SUPER_W/m_full/f.txt")" = "$W_BODY" ] &&
    [ "$(cat "$SUPER_W/m_old/f.txt")" = "$W_BODY" ] && [ "$(cat "$SUPER_W/m_nest/child/f.txt")" = "$W_BODY" ] &&
    [ -z "$($GIT -C "$SUPER_W" status --porcelain)" ]
}
w_linked_to() { # <checkout> <store>: a linked worktree of exactly that store, with no objects of its own
  local gd
  gd="$(git -C "$1" rev-parse --absolute-git-dir 2>/dev/null)" || return 1
  [ -f "$gd/commondir" ] && [ ! -e "$gd/objects" ] && [ ! -e "$2/objects/info/alternates" ] &&
    [ "$(cd "$(git -C "$1" rev-parse --path-format=absolute --git-common-dir)" && pwd -P)" = "$(cd "$2" && pwd -P)" ]
}
w_all_linked() { # <worktree>: every one of its submodule checkouts shares the first checkout's store
  w_linked_to "$1/m_shallow" "$W_STORES/m_shallow" && w_linked_to "$1/m_full" "$W_STORES/m_full" &&
    w_linked_to "$1/m_old" "$W_STORES/m_old" &&
    w_linked_to "$1/m sp" "$W_STORES/sp name" && w_linked_to "$1/m_nest" "$W_STORES/m_nest" &&
    w_linked_to "$1/m_nest/child" "$W_STORES/m_nest/modules/child"
}
w_at_pins() { # <worktree>: every checkout at the pin the second worktree's commit records
  [ "$(sha "$1/m_shallow" HEAD)" = "$W5" ] && [ "$(sha "$1/m_full" HEAD)" = "$W5" ] &&
    [ "$(sha "$1/m_old" HEAD)" = "$W2" ] && [ "$(sha "$1/m sp" HEAD)" = "$W4" ] &&
    [ "$(sha "$1/m_nest" HEAD)" = "$W_NEST" ] && [ "$(sha "$1/m_nest/child" HEAD)" = "$W_LEAF" ]
}

# The report names the steps the restore takes. A store that lacks the pin
# gets the script's own --restore line: what brings the pin is chosen by what
# its history ends at, under the store's lock, and is not one git command. A
# plain `git fetch` is never printed for a store other checkouts read.
# Offline that fetch cannot run, so the row keeps the old line, and a store
# that holds its pin is still shared.
W_ADVICE="$(GIT_ALLOW_PROTOCOL=file bash "$SYNC" --root "$SECOND_W" 2>&1)"
RC_W_ADVICE=$?
W_ADVICE_OFFLINE="$(GIT_ALLOW_PROTOCOL=file bash "$SYNC" --root "$SECOND_W" --offline 2>&1)"
RC_W_ADVICE_OFFLINE=$?
# One line for each of m_shallow, m_old and m_full, and the report's closing one.
if [ "$RC_W_ADVICE" -eq 1 ] && [ "$RC_W_ADVICE_OFFLINE" -eq 1 ] &&
   [ "$(grep -c -e '^    scripts/submodule_sync.sh --root .* --restore$' <<<"$W_ADVICE")" -eq 4 ] &&
   ! grep -q -e ' fetch ' -e '--unshallow' -e '--deepen' -e '--depth' <<<"$W_ADVICE" &&
   ! grep -q -e ' worktree add --detach .*/m_shallow ' -e ' worktree add --detach .*/m_old ' \
             -e ' worktree add --detach .*/m_full ' -e ' submodule update ' <<<"$W_ADVICE" &&
   grep -q -e " worktree add --detach .*/m\\\\ sp $W4\$" <<<"$W_ADVICE" &&
   grep -q -e ' submodule update --init --no-fetch -- m_shallow$' <<<"$W_ADVICE_OFFLINE" &&
   grep -q -e ' submodule update --init --no-fetch -- m_full$' <<<"$W_ADVICE_OFFLINE" &&
   ! grep -q -e ' worktree add --detach .*/m_shallow ' -e ' worktree add --detach .*/m_full ' <<<"$W_ADVICE_OFFLINE" &&
   ! grep -q -e ' fetch ' <<<"$W_ADVICE_OFFLINE" &&
   grep -q -e " worktree add --detach .*/m\\\\ sp $W4\$" <<<"$W_ADVICE_OFFLINE" &&
   [ ! -e "$SECOND_W/m_shallow/.git" ] && w_configs_unchanged && [ "$(w_store_refs)" = "$W_STORE_REFS" ]; then
  pass "the report names this script's own restore for a shared store that lacks its pin, never a plain fetch, and offline keeps the old line for a pin it cannot fetch"
else
  fail "the second worktree's report does not name the shared-store steps (online=$RC_W_ADVICE offline=$RC_W_ADVICE_OFFLINE): $(printf '%s\n' "$W_ADVICE" | grep -e ' fetch ' -e ' worktree add ' -e ' --restore' | head -6)"
fi

# The probe of a shallow store may write W_PROBE_KB here. W5's commits fit in
# that many times over; W5's files do not.
SUBMODULE_SYNC_PROBE_LIMIT_KB="$W_PROBE_KB" SUBMODULE_SYNC_TRACE_NET=1 GIT_ALLOW_PROTOCOL=file \
  bash "$SYNC" --root "$SECOND_W" --fetch --restore >"$TMP_ROOT/w-restore.log" 2>&1
RC_W=$?
bash "$SYNC" --root "$SECOND_W" --offline >"$TMP_ROOT/w-check.log" 2>&1
RC_W_CHECK=$?
# NEGATIVE CONTROLS, each run against this check (2026-11-14, git 2.56.0):
#  * delete restore_module's `if module_store_for ...; then ... fi` block: each
#    store is cloned again under <second git dir>/modules, the path `find`
#    names. The mutant below is the same control kept in the suite.
#  * delete `--no-write-fetch-head` from shared_fetch: each store a pin was
#    fetched into gains a FETCH_HEAD the first checkout would read.
#  * delete `--filter=tree:0` from probe_pin: the probe of m_shallow downloads
#    W5's files, passes its limit and is ended, the pin's ancestry is unread,
#    and m_shallow is cloned under the worktree (`not shared from`).
if [ "$RC_W" -eq 0 ] && [ "$RC_W_CHECK" -eq 0 ] && w_at_pins "$SECOND_W" &&
   [ ! -e "$(git -C "$SECOND_W" rev-parse --absolute-git-dir)/modules" ] &&
   [ -z "$(find "$SUPER_W/.git" -path '*/worktrees/*/modules' -print | head -1)" ] &&
   w_all_linked "$SECOND_W" &&
   ! grep -q -e 'not shared from' "$TMP_ROOT/w-restore.log" &&
   [ "$(w_store_refs)" = "$W_STORE_REFS" ] &&
   w_configs_unchanged && w_first_unchanged; then
  pass "a second worktree adds no private submodule store"
else
  fail "a second worktree's restore made a private store, missed a pin, wrote a ref, or changed the first checkout (restore=$RC_W check=$RC_W_CHECK): $(tail -6 "$TMP_ROOT/w-restore.log")"
fi

# A shallow store is shared as it is, and never deepened.
#   m_shallow  the pin W5 is a child of HEAD W4: every line of its history
#              ends at a commit the store reads. It arrives WITH that link
#              and no more: the store's one root is still W3, its `shallow`
#              file is the one it had, and W2 and W1, which the remote holds
#              under the root, are not in the store.
#   m_old      the pin W2 is older than the store's root W4: a plain fetch
#              would bring W1 with it, down to the remote's first commit. It
#              arrives ALONE, as one more root: W1 (under the pin) and W3
#              (between the pin and the root) are not in the store.
# The probes that decided this are gone, and each asked once.
# NEGATIVE CONTROLS, each run against this check (2026-11-14, git 2.56.0):
#  * shared_fetch, `--unshallow` in place of `--depth 1`: m_old loses its
#    `shallow` file and holds W3 and W1.
#  * shared_fetch, no `set -- "$@" --depth 1` (the pin without a depth):
#    m_old holds W1, the remote's history under a pin older than its root.
#  * shared_fetch, `--depth 2` in place of `--depth 1`: m_old holds W1.
#  * probe_pin, no `if (!related) { print "alone"; exit 0 }` (every pin
#    fetched with its history): m_old holds W1.
#  * probe_pin, `print "alone"; exit 0` as the END block's first statement
#    (every pin fetched alone): W5 is a second root of m_shallow, cut from W4.
if [ "$(git -C "$SUPER_W/m_shallow" rev-parse --is-shallow-repository)" = true ] &&
   [ "$(git -C "$SUPER_W/m_old" rev-parse --is-shallow-repository)" = true ] &&
   w_roots "$W_STORES/m_shallow" "$W3" && w_lacks "$W_STORES/m_shallow" "$W2" "$W1" &&
   [ "$(git --git-dir="$W_STORES/m_shallow" rev-list "$W5" | tr '\n' ' ')" = "$W5 $W4 $W3 " ] &&
   w_roots "$W_STORES/m_old" "$W4" "$W2" && w_lacks "$W_STORES/m_old" "$W1" "$W3" &&
   [ "$(git --git-dir="$W_STORES/m_old" rev-list --count "$W2")" -eq 1 ] &&
   grep -q -e '^submodule_sync --restore: m_shallow: the shared store .* now holds pin .*, with its history down to commits the store held$' "$TMP_ROOT/w-restore.log" &&
   grep -q -e '^submodule_sync --restore: m_old: the shared store .* now holds pin .*, alone; the store stays shallow$' "$TMP_ROOT/w-restore.log" &&
   [ "$(grep -c -e '^net: probe ' "$TMP_ROOT/w-restore.log")" -eq 2 ] &&
   [ "$(grep -c -e '^net: store fetch ' "$TMP_ROOT/w-restore.log")" -eq 3 ] &&
   [ -z "$(find "$TMPDIR" -name 'submodule_sync.probe.*' -print | head -1)" ]; then
  pass "a shallow store is shared as it is: a pin that descends from what it holds arrives with that link, a pin older than its root arrives alone, and none of the remote's history under a root or under the pin arrives"
else
  fail "sharing a shallow store deepened it, completed it, cut a pin from the commit it descends from, or brought history the pin did not need (m_shallow roots: $(cat "$W_STORES/m_shallow/shallow" 2>&1 | tr '\n' ' '); m_old roots: $(cat "$W_STORES/m_old/shallow" 2>&1 | tr '\n' ' ')): $(grep -e 'shared store' "$TMP_ROOT/w-restore.log" | head -3)"
fi

# A complete store stays complete: it gets the history its pin reaches, and no
# `shallow` file, which would cut history the first checkout reads and which
# scripts/check_dependency_cycle_anchor.py would refuse there too.
# NEGATIVE CONTROL, run against this check (2026-11-14, git 2.56.0): make
# shared_fetch's `case "$plan" in` read `case alone in` (a depth for every
# store), and m_full gains a `shallow` file naming W5.
if [ ! -e "$W_STORES/m_full/shallow" ] &&
   [ "$(git -C "$SUPER_W/m_full" rev-parse --is-shallow-repository)" = false ] &&
   [ "$(git --git-dir="$W_STORES/m_full" rev-list --count "$W5")" -eq 5 ] &&
   [ ! -e "$W_STORES/sp name/shallow" ] && [ ! -e "$W_STORES/m_nest/shallow" ]; then
  pass "a complete store that lacked the pin is shared complete: no shallow file, and the pin with its history"
else
  fail "sharing a complete store made it shallow or left the pin without its history: $(cat "$W_STORES/m_full/shallow" 2>&1)"
fi

# Nothing the first checkout could read became unreadable, and nothing was put
# under what it reads: each of its checkouts lists the commits it listed,
# through its HEAD and through every ref of its store.
# NEGATIVE CONTROLS, each run against this check (2026-11-14, git 2.56.0), in
# shared_fetch:
#  * `--unshallow` in place of `--depth 1`: m_old reads W3, W2 and W1 under
#    its HEAD W4.
#  * `--depth 2` for every pin of a shallow store (`case alone in`, and 2 for
#    1): m_shallow's HEAD W4 becomes a root, and W3, which the first checkout
#    read under it, is hidden.
if [ "$(w_first_history)" = "$W_FIRST_HISTORY" ] &&
   [ "$(git -C "$SUPER_W/m_shallow" rev-list --count HEAD)" -eq 2 ] &&
   [ "$(git -C "$SUPER_W/m_old" rev-list --count HEAD)" -eq 1 ] &&
   [ "$(git -C "$SUPER_W/m_full" rev-list --count HEAD)" -eq 4 ]; then
  pass "the first checkout reads every commit it read before the second worktree's restore, and no other"
else
  fail "the second worktree's restore hid a commit the first checkout read, or put history under one: $(diff <(printf '%s\n' "$W_FIRST_HISTORY") <(w_first_history) | head -6)"
fi

# Plain git's other trap costs the second worktree alone. A recursive checkout
# there points the linked checkout's .git file where git expects a private
# store, and git then fails in that checkout (measured, git 2.56.0: `fatal:
# gitfile does not point to a valid repository`). The store still registers the
# checkout, so the row is DISCONNECTED, restorable (exit 1, not 2), and the
# second worktree's own --restore names that registration in the .git file
# again and moves nothing.
$GIT -C "$SECOND_W" -c submodule.recurse=true checkout -q --detach HEAD~1 >/dev/null 2>&1
$GIT -C "$SECOND_W" -c submodule.recurse=false checkout -q --detach "$W_SECOND_COMMIT" >/dev/null 2>&1
# A git that refuses the recursive checkout instead: do the same damage by hand.
if git -C "$SECOND_W/m_shallow" rev-parse HEAD >/dev/null 2>&1; then
  printf 'gitdir: %s\n' "$(git -C "$SECOND_W" rev-parse --absolute-git-dir)/modules/m_shallow" >"$SECOND_W/m_shallow/.git"
fi
if [ "$(sha "$SECOND_W" HEAD)" = "$W_SECOND_COMMIT" ] && ! git -C "$SECOND_W/m_shallow" rev-parse HEAD >/dev/null 2>&1; then
  pass "fixture: a recursive checkout in the second worktree left its own m_shallow unreadable"
else
  fail "fixture W invalid: the second worktree's m_shallow still answers after the recursive checkout, or its HEAD moved"
fi
W_RELINK_REPORT="$(bash "$SYNC" --root "$SECOND_W" --offline 2>&1)"
RC_W_RELINK_REPORT=$?
bash "$SYNC" --root "$SECOND_W" --offline --restore >"$TMP_ROOT/w-relink.log" 2>&1
RC_W_RELINK=$?
# NEGATIVE CONTROL, tried by hand: replace reconnect_children's `relink_child
# "$child" "$display" "$STORE_OUT"` call with `:` and this fails (the second
# worktree's restore exits 1: m_shallow could not be reconnected).
if [ "$RC_W_RELINK_REPORT" -eq 1 ] &&
   grep -q -e '^    m_shallow  \[DISCONNECTED\]  — its \.git file names no repository' <<<"$W_RELINK_REPORT" &&
   grep -q -e "^    printf 'gitdir: %s\\\\n' .*/modules/m_shallow/worktrees/[^ ]* >.*/m_shallow/\\.git\$" <<<"$W_RELINK_REPORT" &&
   [ "$RC_W_RELINK" -eq 0 ] && grep -q '^relinked m_shallow: ' "$TMP_ROOT/w-relink.log" &&
   w_at_pins "$SECOND_W" &&
   [ -z "$(git -C "$SECOND_W/m_shallow" status --porcelain 2>&1)" ] &&
   [ -z "$(find "$SECOND_W/m_shallow" -name '.git.submodule_sync.*' -print)" ] &&
   w_all_linked "$SECOND_W" &&
   w_configs_unchanged && w_first_unchanged; then
  pass "a recursive checkout in the second worktree cannot leave its linked checkout broken"
else
  fail "the second worktree's checkout stayed broken, or its relink touched the first checkout (report=$RC_W_RELINK_REPORT restore=$RC_W_RELINK): $(tail -4 "$TMP_ROOT/w-relink.log")"
fi

# The trap. Plain git in the second worktree, even an update that moves nothing,
# rewrites core.worktree in the store both checkouts share, and the first
# checkout's git then fails in that submodule. Nothing can stop plain git, and
# printed advices elsewhere still name it, so the tool has to end the breakage
# itself, and from the worktree that did it: nothing in the second worktree
# looks wrong, every checkout there still reads its pin, and the first
# checkout may not run anything for hours. So the second worktree's own scan
# reads drift (exit 1), and its own --restore puts the value back.
git -C "$SECOND_W" submodule absorbgitdirs >/dev/null 2>&1
if w_configs_unchanged; then W_ABSORB=ok; else W_ABSORB=changed; fi
w_spring_trap() { # <path in the second worktree> <store, under $W_STORES>...
  local path="$1" s copy
  shift
  $GIT -C "$SECOND_W" submodule update --recursive -- "$path" >/dev/null 2>&1
  for s in "$@"; do
    copy="$W_COPIES/$(printf '%s' "$s" | tr / _).config"
    # A git that no longer rewrites the value: do the same damage by hand.
    if cmp -s "$W_STORES/$s/config" "$copy"; then
      git config --file "$W_STORES/$s/config" core.worktree ../../../no-such-directory
    fi
  done
}
w_spring_trap m_full m_full
if git -C "$SUPER_W/m_full" rev-parse HEAD >/dev/null 2>&1; then
  fail "fixture W invalid: the first checkout's m_full still answers after the trap"
else
  pass "fixture: plain git in the second worktree left the first checkout's m_full unreadable"
fi
W_TRAP_REPORT="$(bash "$SYNC" --root "$SECOND_W" --offline 2>&1)"
RC_W_TRAP_REPORT=$?
W_TRAP_QUIET="$(bash "$SYNC" --root "$SECOND_W" --offline --quiet 2>&1)"
bash "$SYNC" --root "$SECOND_W" --offline --restore >"$TMP_ROOT/w-trap-second.log" 2>&1
RC_W_TRAP_SECOND=$?
# Nothing has run in the first checkout: its git answers again all the same.
if git -C "$SUPER_W/m_full" rev-parse HEAD >/dev/null 2>&1; then W_FIRST_READS=yes; else W_FIRST_READS=no; fi
bash "$SYNC" --root "$SUPER_W" --offline >"$TMP_ROOT/w-trap-first.log" 2>&1
RC_W_TRAP_FIRST=$?
# NEGATIVE CONTROL, tried by hand: delete the `[ -z "$MAIN_ROOT" ] ||
# reconnect_children "$MAIN_ROOT" "$MAIN_ROOT"` line and this fails (the second
# worktree's restore exits 1 and the first checkout's m_full stays unreadable).
if [ "$W_ABSORB" = ok ] && [ "$RC_W_TRAP_REPORT" -eq 1 ] &&
   grep -q -e '/m_full  \[DISCONNECTED\]  — the first checkout.s git fails here' <<<"$W_TRAP_REPORT" &&
   grep -q -e '^    git config --file .*/modules/m_full/config core\.worktree \.\./\.\./\.\./m_full$' <<<"$W_TRAP_REPORT" &&
   grep -q -e '^submodule sync: DRIFT .*(1 restorable, 0 needing review)' <<<"$W_TRAP_QUIET" &&
   [ "$RC_W_TRAP_SECOND" -eq 0 ] && grep -q -e '^reconnected .*/m_full: ' "$TMP_ROOT/w-trap-second.log" &&
   [ "$W_FIRST_READS" = yes ] && [ "$RC_W_TRAP_FIRST" -eq 0 ] &&
   w_all_linked "$SECOND_W" && w_at_pins "$SECOND_W" &&
   w_configs_unchanged && w_first_unchanged; then
  pass "plain git in the second worktree cannot leave the first checkout broken"
else
  fail "the first checkout stayed broken after the second worktree's own restore (absorb=$W_ABSORB report=$RC_W_TRAP_REPORT second=$RC_W_TRAP_SECOND reads=$W_FIRST_READS first=$RC_W_TRAP_FIRST): $(tail -4 "$TMP_ROOT/w-trap-second.log")"
fi

# A store that holds the pin is shared with no fetch, shallow or complete, so
# offline too: the next worktree at the same pins is populated with the
# network closed, from the pins the second worktree's restore left in the
# stores, and each shallow store's roots are the ones it had.
FIFTH_W="$TMP_ROOT/w fifth"
$GIT -C "$SUPER_W" worktree add -q --detach "$FIFTH_W" "$W_SECOND_COMMIT"
W_FIFTH_ADVICE="$(bash "$SYNC" --root "$FIFTH_W" --offline 2>&1)"
bash "$SYNC" --root "$FIFTH_W" --offline --restore >"$TMP_ROOT/w-fifth.log" 2>&1
RC_W_FIFTH=$?
# NEGATIVE CONTROL, run against this check (2026-11-14, git 2.56.0): make
# restore_absent_from_store's condition read `if store_is_shallow "$store" ||
# ! git ... cat-file -e ...` (a shallow store always fetched) and the offline
# restore of m_shallow and m_old stops for want of a network.
if ! grep -q -e ' fetch ' -e ' submodule update ' <<<"$W_FIFTH_ADVICE" &&
   grep -q -e " worktree add --detach .*/m_shallow $W5\$" <<<"$W_FIFTH_ADVICE" &&
   grep -q -e " worktree add --detach .*/m_old $W2\$" <<<"$W_FIFTH_ADVICE" &&
   [ "$RC_W_FIFTH" -eq 0 ] && w_at_pins "$FIFTH_W" && w_all_linked "$FIFTH_W" &&
   [ ! -e "$(git -C "$FIFTH_W" rev-parse --absolute-git-dir)/modules" ] &&
   w_roots "$W_STORES/m_shallow" "$W3" && w_roots "$W_STORES/m_old" "$W4" "$W2" &&
   [ ! -e "$W_STORES/m_full/shallow" ] && [ "$(w_first_history)" = "$W_FIRST_HISTORY" ] &&
   w_configs_unchanged && w_first_unchanged; then
  pass "a store that already holds the pin is shared offline, shallow or complete, with no fetch"
else
  fail "a third checkout of pins the stores hold needed the network, a private store or a new root (rc=$RC_W_FIFTH): $(tail -4 "$TMP_ROOT/w-fifth.log")"
fi
$GIT -C "$SUPER_W" worktree remove --force "$FIFTH_W" >/dev/null 2>&1

# Mutation control for the first check: with the shared-store lookup answering
# "no store", the same restore of a third worktree succeeds the old way, with a
# whole clone of each store under that worktree's own git directory.
MUT_W="$TMP_ROOT/submodule_sync.private-stores.sh"
awk '{ print } /^module_store_for\(\)/ { print "  return 1 # mutant: no shared store" }' "$SYNC" >"$MUT_W"
$GIT -C "$SUPER_W" worktree add -q --detach "$THIRD_W" "$W_SECOND_COMMIT"
GIT_ALLOW_PROTOCOL=file bash "$MUT_W" --root "$THIRD_W" --fetch --restore >"$TMP_ROOT/w-mutant.log" 2>&1
RC_MUT_W=$?
THIRD_W_GIT="$(git -C "$THIRD_W" rev-parse --absolute-git-dir)"
if ! cmp -s "$SYNC" "$MUT_W" && [ "$RC_MUT_W" -eq 0 ] && w_at_pins "$THIRD_W" &&
   [ -d "$THIRD_W_GIT/modules/m_full/objects" ] && [ -d "$THIRD_W_GIT/modules/m_shallow/objects" ] &&
   [ -d "$THIRD_W_GIT/modules/m_old/objects" ] && [ -d "$THIRD_W_GIT/modules/sp name/objects" ]; then
  pass "mutation control: without the shared-store lookup the same restore clones every store again"
else
  fail "the private-store mutant did not reproduce the old layout (rc=$RC_MUT_W): $(tail -4 "$TMP_ROOT/w-mutant.log")"
fi

# Removal. The second worktree goes the way git removes one (`git worktree
# remove --force`: git refuses a worktree with populated submodules without
# it), and in the worst state plain git can leave: the trap sprung on the
# module with a nested module, one level down as well, and the second worktree
# gone before its own restore ran. The four stores nothing poisoned must read
# their pins with nothing run but git's own prune and gc (w_reads_pin). The
# other two must read theirs after the first checkout's own --restore, which
# its scan calls lossless (exit 1).
w_spring_trap m_nest m_nest m_nest/modules/child
if git -C "$SUPER_W/m_nest" rev-parse HEAD >/dev/null 2>&1 ||
   git -C "$SUPER_W/m_nest/child" rev-parse HEAD >/dev/null 2>&1; then
  fail "fixture W invalid: the first checkout's m_nest or its nested child still answers after the trap"
fi
# What is removed is the shared shape, not a worktree with stores of its own.
# (The recursive checkout above left <second git dir>/modules/m_shallow with a
# config and nothing else; no objects are under it.)
if w_all_linked "$SECOND_W" &&
   [ -z "$(find "$(git -C "$SECOND_W" rev-parse --absolute-git-dir)" -name objects -print | head -1)" ]; then
  W_SHARED_AT_REMOVAL=yes
else
  W_SHARED_AT_REMOVAL=no
fi
$GIT -C "$SUPER_W" worktree remove --force "$SECOND_W" >"$TMP_ROOT/w-remove.log" 2>&1
RC_W_REMOVE=$?
w_reads_pin() { # <checkout> <pin>: prune, collect garbage NOW, then read all of the pin
  git -C "$1" worktree prune 2>/dev/null &&
    git -C "$1" gc -q --prune=now 2>/dev/null &&
    [ "$(sha "$1" HEAD)" = "$2" ] &&
    git -C "$1" rev-list --objects HEAD >/dev/null 2>&1 &&
    [ -z "$(git -C "$1" status --porcelain 2>/dev/null)" ]
}
if w_reads_pin "$SUPER_W/m_shallow" "$W4" && w_reads_pin "$SUPER_W/m_full" "$W4" &&
   w_reads_pin "$SUPER_W/m_old" "$W4" && w_reads_pin "$SUPER_W/m sp" "$W4"; then W_UNTOUCHED=ok; else W_UNTOUCHED=broken; fi
bash "$SYNC" --root "$SUPER_W" --offline >"$TMP_ROOT/w-removed-report.log" 2>&1
RC_W_REMOVED_REPORT=$?
bash "$SYNC" --root "$SUPER_W" --offline --restore >"$TMP_ROOT/w-removed.log" 2>&1
RC_W_REMOVED=$?
bash "$SYNC" --root "$SUPER_W" --offline >"$TMP_ROOT/w-removed-check.log" 2>&1
RC_W_REMOVED_CHECK=$?
# NEGATIVE CONTROLS, each run against this check (2026-11-14, git 2.56.0):
#  * delete restore_module's `if module_store_for ...; then ... fi` block: the
#    second worktree then has stores of its own (W_SHARED_AT_REMOVAL=no), and
#    what this line says about the shared shape is not shown.
#  * delete reconnect_children's own recursive call (`reconnect_children
#    "$child" "$display"`): m_nest is reconnected, its nested child is not, and
#    the first checkout's restore exits 1.
if [ "$W_SHARED_AT_REMOVAL" = yes ] && [ "$RC_W_REMOVE" -eq 0 ] && [ ! -e "$SECOND_W" ] &&
   [ "$W_UNTOUCHED" = ok ] && [ "$RC_W_REMOVED_REPORT" -eq 1 ] &&
   grep -q -e '^    m_nest  \[DISCONNECTED\]  — its git directory names another worktree' "$TMP_ROOT/w-removed-report.log" &&
   [ "$RC_W_REMOVED" -eq 0 ] && [ "$RC_W_REMOVED_CHECK" -eq 0 ] &&
   grep -q '^reconnected m_nest: ' "$TMP_ROOT/w-removed.log" &&
   grep -q '^reconnected m_nest/child: ' "$TMP_ROOT/w-removed.log" &&
   w_reads_pin "$SUPER_W/m_shallow" "$W4" && w_reads_pin "$SUPER_W/m_full" "$W4" &&
   w_reads_pin "$SUPER_W/m_old" "$W4" && w_reads_pin "$SUPER_W/m sp" "$W4" &&
   w_reads_pin "$SUPER_W/m_nest" "$W_NEST" && w_reads_pin "$SUPER_W/m_nest/child" "$W_LEAF" &&
   [ -z "$(find "$W_STORES" -path '*/worktrees/*' -print | head -1)" ] &&
   [ "$(w_first_history)" = "$W_FIRST_HISTORY" ] &&
   w_configs_unchanged && w_first_unchanged; then
  pass "the first checkout reads every pin after the second worktree is removed"
else
  fail "removing the second worktree cost the first checkout a pin, a config or a clean status (shared=$W_SHARED_AT_REMOVAL remove=$RC_W_REMOVE untouched=$W_UNTOUCHED report=$RC_W_REMOVED_REPORT restore=$RC_W_REMOVED check=$RC_W_REMOVED_CHECK): $(tail -4 "$TMP_ROOT/w-removed.log")"
fi

# What the shape avoids (Trust's audit of 2026-11-10, cause 4): objects borrowed
# from a store under another worktree's git directory are gone when that
# worktree is. The mutant's third worktree has such a store.
BORROWER_W="$TMP_ROOT/w borrower"
$GIT clone -q --no-checkout --shared "$THIRD_W/m_full" "$BORROWER_W"
if [ -s "$BORROWER_W/.git/objects/info/alternates" ] &&
   git -C "$BORROWER_W" cat-file -e "$W4^{commit}" 2>/dev/null; then W_BORROWED=ok; else W_BORROWED=no; fi
rm -rf "$THIRD_W"
$GIT -C "$SUPER_W" worktree prune
if [ "$W_BORROWED" = ok ] && ! git -C "$BORROWER_W" cat-file -e "$W4^{commit}" 2>/dev/null; then
  pass "control: objects borrowed from another worktree's store are lost when that worktree is removed"
else
  fail "the borrowing control did not reproduce the loss (borrowed=$W_BORROWED)"
fi

# The same path again. A removed worktree's registration stays in each store
# until git's own gc prunes it, and `git worktree add` refuses a path a
# registration still names. A worktree made again at that path (here after
# `rm -rf` and a prune of the superproject, the other way worktrees go) takes
# each registration up again: nothing only the registration held moves, no
# store is cloned, and no second registration is added.
FOURTH_W="$TMP_ROOT/w fourth"
$GIT -C "$SUPER_W" worktree add -q --detach "$FOURTH_W" "$W_SECOND_COMMIT"
GIT_ALLOW_PROTOCOL=file bash "$SYNC" --root "$FOURTH_W" --fetch --restore >"$TMP_ROOT/w-fourth.log" 2>&1
RC_W_FOURTH=$?
if w_all_linked "$FOURTH_W"; then W_FOURTH_SHARED=yes; else W_FOURTH_SHARED=no; fi
rm -rf "$FOURTH_W"
$GIT -C "$SUPER_W" worktree prune
$GIT -C "$SUPER_W" worktree add -q --detach "$FOURTH_W" "$W_SECOND_COMMIT"
W_FOURTH_ADVICE="$(bash "$SYNC" --root "$FOURTH_W" --offline 2>&1)"
GIT_ALLOW_PROTOCOL=file bash "$SYNC" --root "$FOURTH_W" --fetch --restore >"$TMP_ROOT/w-fourth-again.log" 2>&1
RC_W_FOURTH_AGAIN=$?
bash "$SYNC" --root "$FOURTH_W" --offline >/dev/null 2>&1
RC_W_FOURTH_CHECK=$?
w_registrations() { # <store>: how many checkouts it registers
  find "$1/worktrees" -mindepth 1 -maxdepth 1 -type d 2>/dev/null | wc -l | tr -d ' '
}
# NEGATIVE CONTROL, tried by hand: delete restore_absent_from_store's `if
# registration_of ...; then ... fi` block and this fails (`worktree add`
# refuses each path, and every store is cloned again under the worktree).
if [ "$RC_W_FOURTH" -eq 0 ] && [ "$W_FOURTH_SHARED" = yes ] &&
   [ "$(printf '%s\n' "$W_FOURTH_ADVICE" | grep -c -e '^    scripts/submodule_sync.sh --root .* --offline --restore$')" -eq 6 ] &&
   ! grep -q -e ' worktree add ' <<<"$W_FOURTH_ADVICE" &&
   [ "$RC_W_FOURTH_AGAIN" -eq 0 ] && [ "$RC_W_FOURTH_CHECK" -eq 0 ] &&
   w_at_pins "$FOURTH_W" && w_all_linked "$FOURTH_W" &&
   [ ! -e "$(git -C "$FOURTH_W" rev-parse --absolute-git-dir)/modules" ] &&
   [ -z "$($GIT -C "$FOURTH_W" status --porcelain)" ] &&
   [ -z "$(git -C "$FOURTH_W/m_full" status --porcelain)" ] &&
   [ "$(cat "$FOURTH_W/m_nest/child/f.txt")" = "$W_BODY" ] &&
   [ "$(w_registrations "$W_STORES/m_shallow")" -eq 1 ] && [ "$(w_registrations "$W_STORES/m_full")" -eq 1 ] &&
   [ "$(w_registrations "$W_STORES/m_old")" -eq 1 ] &&
   [ "$(w_registrations "$W_STORES/m_nest/modules/child")" -eq 1 ] &&
   w_configs_unchanged && w_first_unchanged; then
  pass "a worktree made again at a removed worktree's path takes up its registrations and adds no private store"
else
  fail "a stale registration stopped the restore, was forced, or sent the worktree to private stores (first=$RC_W_FOURTH shared=$W_FOURTH_SHARED again=$RC_W_FOURTH_AGAIN check=$RC_W_FOURTH_CHECK): $(tail -4 "$TMP_ROOT/w-fourth-again.log")"
fi

# A pull in a second worktree moves three pins to commits the shared stores
# lack, with the checkouts already there. `--fetch` takes each pin by sha: the
# remote's branch has moved since, and the stores' tracking refs, which the
# first checkout reads, must not move with it, nor a FETCH_HEAD appear.
#   m_full     complete; W6 is a child of its HEAD W5
#   m_shallow  shallow, root W3; W_SIDE is on a line that left main at W2,
#              under the root: a plain fetch would bring W2 and W1 with it
#   m_old      shallow, roots W4 and W2; W3 is a child of its HEAD W2
# The remote no longer filters, as one that never offered to: each probe is
# then sent its commits' files too, a few bytes here, and reads the same
# ancestry from them.
$GIT -C "$DONOR_W" config --unset uploadpack.allowFilter
echo "main moved" >>"$DONOR_W/g.txt"
$GIT -C "$DONOR_W" add g.txt
$GIT -C "$DONOR_W" commit -qm "main moves on"
$GIT -C "$DONOR_W" checkout -q --detach "$W5"
echo "line 6" >>"$DONOR_W/f.txt"
$GIT -C "$DONOR_W" commit -qam c6
W6="$(sha "$DONOR_W" HEAD)"
$GIT -C "$DONOR_W" update-ref refs/pins/w6 "$W6"
$GIT -C "$DONOR_W" checkout -q main
$GIT -C "$FOURTH_W" update-index --cacheinfo "160000,$W6,m_full"
$GIT -C "$FOURTH_W" update-index --cacheinfo "160000,$W_SIDE,m_shallow"
$GIT -C "$FOURTH_W" update-index --cacheinfo "160000,$W3,m_old"
$GIT -C "$FOURTH_W" commit -qm "three pins move to commits the shared stores lack"
if w_roots "$W_STORES/m_shallow" "$W3" && w_lacks "$W_STORES/m_shallow" "$W_SIDE" "$W2" "$W1" &&
   w_roots "$W_STORES/m_old" "$W4" "$W2" && w_lacks "$W_STORES/m_old" "$W3" "$W1" &&
   [ ! -e "$W_STORES/m_full/shallow" ] && w_lacks "$W_STORES/m_full" "$W6" &&
   [ "$(w_store_refs)" = "$W_STORE_REFS" ] && [ "$(sha "$DONOR_W" main)" != "$W4" ]; then
  pass "fixture: three linked checkouts whose new pins their stores lack, and a remote branch that moved"
else
  fail "fixture W invalid: the stores are not in the shape the moved-pin checks need"
fi
# While this sync starts, another process holds m_shallow's lock, as a second
# sync deciding about the same store would, and says when it lets go.
W_LOCK_HELD="$TMP_ROOT/w-lock-held"
: >"$TMP_ROOT/w-fourth-fetch.log"
perl -e 'open(my $l, ">>", $ARGV[0]) or die; flock($l, 2) or die;
         open(my $held, ">", $ARGV[1]) or die; close $held; sleep 2;
         open(my $log, ">>", $ARGV[2]) or die; print $log "lock released\n"; close $log' \
  "$W_STORES/m_shallow/submodule_sync.lock" "$W_LOCK_HELD" "$TMP_ROOT/w-fourth-fetch.log" &
W_LOCK_PID=$!
while [ ! -e "$W_LOCK_HELD" ] && kill -0 "$W_LOCK_PID" 2>/dev/null; do sleep 0.1; done
SUBMODULE_SYNC_TRACE_NET=1 GIT_ALLOW_PROTOCOL=file bash "$SYNC" --root "$FOURTH_W" --fetch --restore >>"$TMP_ROOT/w-fourth-fetch.log" 2>&1
RC_W_FOURTH_FETCH=$?
wait "$W_LOCK_PID" 2>/dev/null
W_FOURTH_MOVED="$(bash "$SYNC" --root "$FOURTH_W" --offline 2>&1)"
RC_W_FOURTH_MOVED=$?
# NEGATIVE CONTROL, run against this check (2026-11-14, git 2.56.0): make
# fetch_pin's `elif [ -n "$store" ]; then` read `elif false; then` (a linked
# checkout fetched as any other) and this fails (refs/remotes/origin/main
# moves in each shared store).
if [ "$(sha "$FOURTH_W/m_full" HEAD)" = "$W6" ] &&
   w_linked_to "$FOURTH_W/m_full" "$W_STORES/m_full" && w_linked_to "$FOURTH_W/m_shallow" "$W_STORES/m_shallow" &&
   w_linked_to "$FOURTH_W/m_old" "$W_STORES/m_old" &&
   [ ! -e "$W_STORES/m_full/shallow" ] &&
   [ "$(git --git-dir="$W_STORES/m_full" rev-list --count "$W6")" -eq 6 ] &&
   [ "$(w_store_refs)" = "$W_STORE_REFS" ] &&
   [ -z "$(find "$W_STORES/m_full" "$W_STORES/m_shallow" "$W_STORES/m_old" -name FETCH_HEAD -print)" ] &&
   w_configs_unchanged && w_first_unchanged; then
  pass "a pin fetched for a checkout that shares its store moves no ref the first checkout reads"
else
  fail "a --fetch in the second worktree moved a ref, wrote a FETCH_HEAD or made a complete store shallow (rc=$RC_W_FOURTH_FETCH): $(tail -4 "$TMP_ROOT/w-fourth-fetch.log")"
fi
# A checkout's HEAD is named to the remote as something the store has. The
# fourth worktree's m_full sat at W5, which no ref of the store holds, when
# its pin moved to W6: the remote sent W6, and not W5's 256 KiB file again.
# NEGATIVE CONTROL, run against this check (2026-11-14, git 2.56.0): delete
# shared_fetch's `for tip in $(store_head_commits "$store"); do ...; done`
# line, and a second pack of m_full holds the file.
w_packs_holding() { # <store> <object>: how many of the store's packs hold it
  local n=0 idx listing
  for idx in "$1"/objects/pack/*.idx; do
    [ -f "$idx" ] || continue
    listing="$(git show-index <"$idx" 2>/dev/null)"
    ! grep -q -e " $2" <<<"$listing" || n=$((n + 1))
  done
  echo "$n"
}
W_BIG="$(git -C "$DONOR_W" rev-parse "$W5:big.bin")"
if [ "$(w_packs_holding "$W_STORES/m_full" "$W_BIG")" -eq 1 ]; then
  pass "a fetch into a shared store is not sent again what a checkout's HEAD alone holds"
else
  fail "the remote sent a shared store objects a checkout's HEAD already held: $(w_packs_holding "$W_STORES/m_full" "$W_BIG") packs of m_full hold W5's file"
fi

# A moved pin is bounded as an absent checkout's is. W_SIDE arrives alone:
# its line left the history under m_shallow's root, and W2 and W1 would have
# come with it. W3 arrives with its link to m_old's HEAD W2, and nothing
# else: W2 is still a root, and W1 under it is not in the store.
# NEGATIVE CONTROL, run against this check (2026-11-14, git 2.56.0): delete
# probe_pin's `if (!related) { print "alone"; exit 0 }` line and m_shallow
# holds W2 and W1.
if git --git-dir="$W_STORES/m_shallow" cat-file -e "$W_SIDE^{commit}" 2>/dev/null &&
   w_roots "$W_STORES/m_shallow" "$W3" "$W_SIDE" && w_lacks "$W_STORES/m_shallow" "$W2" "$W1" &&
   [ "$(git --git-dir="$W_STORES/m_shallow" rev-list --count "$W_SIDE")" -eq 1 ] &&
   w_roots "$W_STORES/m_old" "$W4" "$W2" && w_lacks "$W_STORES/m_old" "$W1" &&
   [ "$(git --git-dir="$W_STORES/m_old" rev-list "$W3" | tr '\n' ' ')" = "$W3 $W2 " ] &&
   [ "$(w_first_history)" = "$W_FIRST_HISTORY" ] &&
   [ -z "$(find "$TMPDIR" -name 'submodule_sync.probe.*' -print | head -1)" ]; then
  pass "a pin fetched for a checkout that shares a shallow store arrives with its link to what the store holds, or alone, and never with the remote's history under a root"
else
  fail "a --fetch in the second worktree deepened a shallow shared store or cut a pin from its parent (m_shallow roots: $(cat "$W_STORES/m_shallow/shallow" 2>&1 | tr '\n' ' '); m_old roots: $(cat "$W_STORES/m_old/shallow" 2>&1 | tr '\n' ' ')): $(tail -4 "$TMP_ROOT/w-fourth-fetch.log")"
fi

# What the scan then reads is what a shallow clone of the worktree's own
# reads, through the same merge-base.
#   m_old      W3 is one commit ahead of HEAD W2 and its link was fetched:
#              BEHIND, lossless, and the restore moves to it.
#   m_shallow  W5 and W_SIDE have no merge base in the store: UNRELATED,
#              review, and nothing moves. A clone of the worktree's own
#              reads that pair the same way with all of W_SIDE's history
#              fetched, because its root W3 hides W2, the commit the two
#              lines share (measured, git 2.56.0: `merge-base` exits 1).
# NEGATIVE CONTROL, run against this check (2026-11-14, git 2.56.0): make
# probe_pin's END block begin `print "alone"; exit 0` (every pin fetched
# alone) and m_old reads UNRELATED and stays at W2.
if [ "$RC_W_FOURTH_FETCH" -eq 2 ] && [ "$RC_W_FOURTH_MOVED" -eq 2 ] &&
   [ "$(sha "$FOURTH_W/m_old" HEAD)" = "$W3" ] &&
   grep -q -e '^restoring m_old \.\.\. ok ' "$TMP_ROOT/w-fourth-fetch.log" &&
   ! grep -q -e 'm_old' -e 'm_full' <<<"$W_FOURTH_MOVED" &&
   [ "$(sha "$FOURTH_W/m_shallow" HEAD)" = "$W5" ] &&
   grep -q -e '^  m_shallow  \[UNRELATED\]$' "$TMP_ROOT/w-fourth-fetch.log" &&
   grep -q -e '^    m_shallow  \[UNRELATED\]' <<<"$W_FOURTH_MOVED"; then
  pass "a pin one commit ahead in a shallow shared store reads BEHIND and is moved to, and a pin on a line that left the history under the store's root reads UNRELATED, as each does in a shallow clone of the worktree's own"
else
  fail "a moved pin in a shallow shared store was misread (fetch=$RC_W_FOURTH_FETCH scan=$RC_W_FOURTH_MOVED m_old=$(sha "$FOURTH_W/m_old" HEAD)): $(grep -e 'm_shallow' -e 'm_old' <<<"$W_FOURTH_MOVED" | head -4)"
fi

# The test that a store lacks a pin and the fetch that follows are one step
# for every sync (lock_store): this one's probe of m_shallow, which comes
# before anything is fetched there, waited for the other process to let go.
# NEGATIVE CONTROL, run against this check (2026-11-14, git 2.56.0): make
# lock_store begin `return 1` (no lock) and the probe is made while the other
# process still holds the lock.
if [ "$(grep -n -e '^lock released$' -e "^net: probe .* $W_SIDE\$" "$TMP_ROOT/w-fourth-fetch.log" | cut -d: -f2- | tr '\n' ' ')" = "lock released net: probe file://$DONOR_W $W_SIDE " ]; then
  pass "a sync waits for a store's lock before it tests for a pin and fetches it"
else
  fail "a sync probed or fetched into a store whose lock another process held: $(grep -n -e '^lock released$' -e '^net: ' "$TMP_ROOT/w-fourth-fetch.log" | head -4)"
fi

# The first checkout moves to a pin a second worktree fetched first: W5, which
# the second worktree's restore brought into m_shallow. The link to the first
# checkout's HEAD W4 came with it, so the move reads BEHIND and is made, with
# the network closed. (A pin fetched alone would be a root here: UNRELATED,
# exit 2, for the checkout that fetched nothing.)
# NEGATIVE CONTROL, run against this check (2026-11-14, git 2.56.0): make
# probe_pin's END block begin `print "alone"; exit 0` and this restore exits
# 2 with m_shallow UNRELATED, at W4.
$GIT -C "$SUPER_W" update-index --cacheinfo "160000,$W5,m_shallow"
$GIT -C "$SUPER_W" commit -qm "the first checkout's pin moves to a commit a second worktree fetched first"
bash "$SYNC" --root "$SUPER_W" --offline --restore >"$TMP_ROOT/w-first-moved.log" 2>&1
RC_W_FIRST_MOVED=$?
W_FIRST_MOVED_HEAD="$(sha "$SUPER_W/m_shallow" HEAD)"
$GIT -C "$SUPER_W/m_shallow" checkout -q --detach "$W4"
$GIT -C "$SUPER_W" reset -q --hard HEAD~1
if [ "$RC_W_FIRST_MOVED" -eq 0 ] && [ "$W_FIRST_MOVED_HEAD" = "$W5" ] &&
   grep -q -e '^restoring m_shallow \.\.\. ok ' "$TMP_ROOT/w-first-moved.log" &&
   w_configs_unchanged && w_first_unchanged && [ "$(w_first_history)" = "$W_FIRST_HISTORY" ]; then
  pass "the first checkout moves to a pin a second worktree fetched first, as BEHIND, with no fetch"
else
  fail "the first checkout could not move to a pin the second worktree's restore brought (rc=$RC_W_FIRST_MOVED head=$W_FIRST_MOVED_HEAD): $(tail -4 "$TMP_ROOT/w-first-moved.log")"
fi

# What is left of that defect (docs/OPEN_ISSUES.md,
# SECOND-WORKTREE-STALE-REGISTRATION-1; docs/PLAN.md PKG-S7 names the custody
# step, and no tracker row drops a registration under
# <common git dir>/modules/<name>/worktrees yet). A registration whose HEAD is
# a commit nothing else holds, or whose index holds a staged change, is not
# taken up, because that would move its HEAD off the commit or discard what
# was staged, and is not forced, because that would delete it: that one module
# is cloned privately, and the registration stays as it was. When a row pins
# what such a registration holds and drops it, this check inverts.
#
# The worktree made again pins two commits the stores lack as well, and what
# is fetched for a registration is decided before it is fetched:
#   m_shallow  its registration's HEAD is W5 and the pin W6 is a child of it:
#              W6 arrives with that link, and the registration is taken up.
#   m_old      its registration's HEAD is W3 and the pin W1 is older than the
#              store's roots. It could only arrive alone, which never shows a
#              registration's HEAD to be its ancestor, so NOTHING is fetched
#              into the store, and that module is cloned privately.
W_UNLANDED="$(new_commit "$FOURTH_W/m_full" "unlanded work in a worktree about to be removed")"
echo "staged, never committed" >"$FOURTH_W/m sp/staged.txt"
$GIT -C "$FOURTH_W/m sp" add staged.txt
rm -rf "$FOURTH_W"
$GIT -C "$SUPER_W" worktree prune
$GIT -C "$SUPER_W" worktree add -q --detach "$FOURTH_W" "$W_SECOND_COMMIT"
$GIT -C "$FOURTH_W" update-index --cacheinfo "160000,$W6,m_shallow"
$GIT -C "$FOURTH_W" update-index --cacheinfo "160000,$W1,m_old"
$GIT -C "$FOURTH_W" commit -qm "the worktree made again pins two commits the stores lack"
SUBMODULE_SYNC_TRACE_NET=1 GIT_ALLOW_PROTOCOL=file bash "$SYNC" --root "$FOURTH_W" --fetch --restore >"$TMP_ROOT/w-fourth-unlanded.log" 2>&1
RC_W_FOURTH_UNLANDED=$?
FOURTH_W_GIT="$(git -C "$FOURTH_W" rev-parse --absolute-git-dir)"
W_UNLANDED_HEAD=""
for W_REG in "$W_STORES/m_full"/worktrees/*; do
  [ -f "$W_REG/HEAD" ] && W_UNLANDED_HEAD="$(git --git-dir="$W_REG" rev-parse HEAD 2>/dev/null)"
done
W_STAGED=""
for W_REG in "$W_STORES/sp name"/worktrees/*; do
  [ -f "$W_REG/HEAD" ] && W_STAGED="$(git --git-dir="$W_REG" diff-index --cached --name-only HEAD -- 2>/dev/null)"
done
W_OLD_REG_HEAD=""
for W_REG in "$W_STORES/m_old"/worktrees/*; do
  [ -f "$W_REG/HEAD" ] && W_OLD_REG_HEAD="$(git --git-dir="$W_REG" rev-parse HEAD 2>/dev/null)"
done
# NEGATIVE CONTROLS, each tried by hand: delete readopt_registration's
# `merge-base --is-ancestor` line and m_full's registration is taken up and
# its HEAD moved off the commit; delete registration_is_idle's `diff-index
# --cached` line and the staged file is gone from the other registration's
# index.
if [ "$RC_W_FOURTH_UNLANDED" -eq 0 ] &&
   [ "$(sha "$FOURTH_W/m_full" HEAD)" = "$W5" ] && [ "$(sha "$FOURTH_W/m sp" HEAD)" = "$W4" ] &&
   [ "$(sha "$FOURTH_W/m_nest" HEAD)" = "$W_NEST" ] && [ "$(sha "$FOURTH_W/m_nest/child" HEAD)" = "$W_LEAF" ] &&
   [ -d "$FOURTH_W_GIT/modules/m_full/objects" ] && [ -d "$FOURTH_W_GIT/modules/sp name/objects" ] &&
   w_linked_to "$FOURTH_W/m_nest/child" "$W_STORES/m_nest/modules/child" &&
   [ "$W_UNLANDED_HEAD" = "$W_UNLANDED" ] && [ "$(w_registrations "$W_STORES/m_full")" -eq 1 ] &&
   [ "$W_STAGED" = staged.txt ] && [ "$(w_registrations "$W_STORES/sp name")" -eq 1 ] &&
   grep -q -e '^submodule_sync --restore: m_full: not shared from .*; cloning a private store$' "$TMP_ROOT/w-fourth-unlanded.log" &&
   w_configs_unchanged && w_first_unchanged; then
  pass "a registration holding a commit or a staged change nothing else holds is left alone, and that module is cloned privately"
else
  fail "a registration with unlanded work was taken up, forced or lost (rc=$RC_W_FOURTH_UNLANDED head=$W_UNLANDED_HEAD staged=$W_STAGED): $(tail -6 "$TMP_ROOT/w-fourth-unlanded.log")"
fi
# NEGATIVE CONTROLS, each run against this check (2026-11-14, git 2.56.0):
#  * drop `${reg:+history}` from restore_absent_from_store's shared_fetch
#    call: W1 is fetched into m_old alone, a third root no checkout can use,
#    before the registration is refused.
#  * make probe_pin's END block begin `print "alone"; exit 0`: W6 is not
#    fetched, m_shallow's registration is not taken up, and it is cloned
#    privately.
if [ "$(sha "$FOURTH_W/m_shallow" HEAD)" = "$W6" ] && w_linked_to "$FOURTH_W/m_shallow" "$W_STORES/m_shallow" &&
   [ ! -e "$FOURTH_W_GIT/modules/m_shallow" ] && [ "$(w_registrations "$W_STORES/m_shallow")" -eq 1 ] &&
   [ "$(git --git-dir="$W_STORES/m_shallow" rev-list "$W6" | tr '\n' ' ')" = "$W6 $W5 $W4 $W3 " ] &&
   w_roots "$W_STORES/m_shallow" "$W3" "$W_SIDE" &&
   [ "$(sha "$FOURTH_W/m_old" HEAD)" = "$W1" ] && [ -d "$FOURTH_W_GIT/modules/m_old/objects" ] &&
   w_lacks "$W_STORES/m_old" "$W1" && w_roots "$W_STORES/m_old" "$W4" "$W2" &&
   [ "$W_OLD_REG_HEAD" = "$W3" ] && [ "$(w_registrations "$W_STORES/m_old")" -eq 1 ] &&
   grep -q -e '^submodule_sync --restore: m_old: .* did not bring pin .* into the shared store .* (it shares no history with the store, and the pin alone is no use here)$' "$TMP_ROOT/w-fourth-unlanded.log" &&
   ! grep -q -e "^net: store fetch .* $W1\$" "$TMP_ROOT/w-fourth-unlanded.log" &&
   [ "$(w_first_history)" = "$W_FIRST_HISTORY" ]; then
  pass "a registration is taken up again with a pin fetched with its history, and a pin that could only arrive alone is not fetched for one"
else
  fail "a worktree made again at a registered path fetched a pin no registration could use, or lost one it could (m_shallow=$(sha "$FOURTH_W/m_shallow" HEAD) m_old registration=$W_OLD_REG_HEAD; m_old roots: $(cat "$W_STORES/m_old/shallow" 2>&1 | tr '\n' ' ')): $(grep -e 'm_old' -e 'm_shallow' "$TMP_ROOT/w-fourth-unlanded.log" | head -4)"
fi
# An unreadable ancestry is not repaired by a refetch in a shallow store other
# checkouts read. A refetch names nothing the store has, so the remote sends
# every object from the pin down to the store's roots again, or past them. The
# pin here is a commit whose parent is in no repository: merge-base cannot
# read its ancestry, the row is ANCESTRY-UNREADABLE (review), and no refetch
# is started.
# NEGATIVE CONTROL, run against this check (2026-11-14, git 2.56.0): delete
# fetch_pin's `if store_is_shallow "$store"; then ... return 1; fi` and a
# refetch is started in m_shallow (`net: refetch`).
W_ORPHAN="$(printf 'tree %s\nparent %s\nauthor sync-test <sync-test@example.invalid> 0 +0000\ncommitter sync-test <sync-test@example.invalid> 0 +0000\n\nits parent is in no repository\n' \
  "$(sha "$FOURTH_W/m_shallow" 'HEAD^{tree}')" "$(echo "no repository holds this" | git hash-object --stdin)" |
  git -C "$FOURTH_W/m_shallow" hash-object -t commit -w --stdin)"
$GIT -C "$FOURTH_W" update-index --cacheinfo "160000,$W_ORPHAN,m_shallow"
$GIT -C "$FOURTH_W" commit -qm "m_shallow's pin is a commit whose ancestry no store can read"
W_ORPHAN_REPORT="$(SUBMODULE_SYNC_TRACE_NET=1 GIT_ALLOW_PROTOCOL=file bash "$SYNC" --root "$FOURTH_W" --fetch 2>&1)"
RC_W_ORPHAN=$?
if [ "$RC_W_ORPHAN" -eq 2 ] &&
   grep -q -e '^    m_shallow  \[ANCESTRY-UNREADABLE\]$' <<<"$W_ORPHAN_REPORT" &&
   grep -q -e '^submodule_sync --fetch: m_shallow: not refetched: its store .*/modules/m_shallow is shallow and other checkouts read it' <<<"$W_ORPHAN_REPORT" &&
   grep -q -e '^      refetch there, because a refetch has no bound in a shallow store\.$' <<<"$W_ORPHAN_REPORT" &&
   ! grep -q -e '^net: ' -e 'Explicit repair' <<<"$W_ORPHAN_REPORT" &&
   [ "$(sha "$FOURTH_W/m_shallow" HEAD)" = "$W6" ] &&
   w_roots "$W_STORES/m_shallow" "$W3" "$W_SIDE" && [ "$(w_first_history)" = "$W_FIRST_HISTORY" ] &&
   w_configs_unchanged && w_first_unchanged; then
  pass "an unreadable ancestry starts no refetch in a shallow store other checkouts read"
else
  fail "a linked checkout's unreadable ancestry was refetched into a shallow shared store, or misreported (rc=$RC_W_ORPHAN): $(grep -e 'm_shallow' -e '^net: ' <<<"$W_ORPHAN_REPORT" | head -4)"
fi

# A NEW checkout's pin may add SUBMODULE_SYNC_LINK_LIMIT_KB to a store at
# most. Past that nothing enters the store, and that one module gets a store
# of its own holding the pin alone. A sixth worktree pins, under a limit of
# 64 KiB:
#   m_shallow  W_MERGE, a merge of W6 (which the store reads) with a line
#              that leaves the history at W1, under the store's roots, and
#              adds a 256 KiB file. It shares history with the store, so it
#              would arrive by a plain fetch, with that line whole.
#   m_old      W6: what the store lacks of its history is W5 and W6, and W5
#              holds the other 256 KiB file.
#   m_full     W_MERGE: the complete store lacks the merge and the line.
# NEGATIVE CONTROLS, each run against this check (2026-11-14, git 2.56.0):
#  * delete shared_fetch's `[ -z "$limit" ] || ulimit -f "$limit" || exit 1`:
#    the three stores gain the pins and the history, and no store of its own
#    is made.
#  * delete `${alone:+--depth 1}` from restore_module's clone: the two stores
#    cloned over file:// are whole, and hold W1.
$GIT -C "$DONOR_W" checkout -q --detach "$W1"
head -c 262144 /dev/urandom >"$DONOR_W/under.bin"
$GIT -C "$DONOR_W" add under.bin
$GIT -C "$DONOR_W" commit -qm "a line that leaves the history under every root"
W_UNDER="$(sha "$DONOR_W" HEAD)"
$GIT -C "$DONOR_W" checkout -q --detach "$W6"
$GIT -C "$DONOR_W" merge -q --no-edit "$W_UNDER"
W_MERGE="$(sha "$DONOR_W" HEAD)"
$GIT -C "$DONOR_W" update-ref refs/pins/wmerge "$W_MERGE"
$GIT -C "$DONOR_W" checkout -q main
W_MAIN="$(sha "$DONOR_W" main)"
SIXTH_W="$TMP_ROOT/w sixth"
$GIT -C "$SUPER_W" worktree add -q --detach "$SIXTH_W" "$W_SECOND_COMMIT"
$GIT -C "$SIXTH_W" update-index --cacheinfo "160000,$W_MERGE,m_shallow"
$GIT -C "$SIXTH_W" update-index --cacheinfo "160000,$W6,m_old"
$GIT -C "$SIXTH_W" update-index --cacheinfo "160000,$W_MERGE,m_full"
$GIT -C "$SIXTH_W" commit -qm "a sixth worktree pins three commits whose history is more than the limit"
SUBMODULE_SYNC_LINK_LIMIT_KB=64 SUBMODULE_SYNC_TRACE_NET=1 GIT_ALLOW_PROTOCOL=file \
  bash "$SYNC" --root "$SIXTH_W" --fetch --restore >"$TMP_ROOT/w-sixth.log" 2>&1
RC_W_SIXTH=$?
SIXTH_W_GIT="$(git -C "$SIXTH_W" rev-parse --absolute-git-dir)"
if [ "$RC_W_SIXTH" -eq 0 ] && [ "$(sha "$SIXTH_W/m_shallow" HEAD)" = "$W_MERGE" ] &&
   [ "$(sha "$SIXTH_W/m_old" HEAD)" = "$W6" ] && [ "$(sha "$SIXTH_W/m_full" HEAD)" = "$W_MERGE" ] &&
   w_lacks "$W_STORES/m_shallow" "$W_MERGE" "$W_UNDER" "$W1" && w_roots "$W_STORES/m_shallow" "$W3" "$W_SIDE" &&
   w_lacks "$W_STORES/m_old" "$W6" "$W5" "$W1" && w_roots "$W_STORES/m_old" "$W4" "$W2" &&
   w_lacks "$W_STORES/m_full" "$W_MERGE" "$W_UNDER" && [ ! -e "$W_STORES/m_full/shallow" ] &&
   [ -z "$(find "$W_STORES" -name 'submodule_sync.incoming.*' -o -name 'tmp_pack_*')" ] &&
   [ "$(w_registrations "$W_STORES/m_shallow")" -eq 1 ] && [ "$(w_registrations "$W_STORES/m_full")" -eq 1 ] &&
   w_roots "$SIXTH_W_GIT/modules/m_shallow" "$W_MAIN" "$W_MERGE" && w_lacks "$SIXTH_W_GIT/modules/m_shallow" "$W1" "$W6" &&
   w_roots "$SIXTH_W_GIT/modules/m_old" "$W_MAIN" "$W6" && w_lacks "$SIXTH_W_GIT/modules/m_old" "$W1" "$W5" &&
   [ -d "$SIXTH_W_GIT/modules/m_full/objects" ] &&
   [ "$(grep -c -e ' did not bring pin .* into the shared store .* (what the store lacks of its history is more than the 64 KiB a new checkout may add to a store other checkouts read (SUBMODULE_SYNC_LINK_LIMIT_KB))$' "$TMP_ROOT/w-sixth.log")" -eq 3 ] &&
   [ "$(grep -c -e '^submodule_sync --restore: m_[a-z]*: not shared from .*; cloning a private store of pin [0-9a-f]\{8\} alone$' "$TMP_ROOT/w-sixth.log")" -eq 3 ] &&
   w_configs_unchanged && w_first_unchanged && [ "$(w_first_history)" = "$W_FIRST_HISTORY" ]; then
  pass "a pin whose history is more than a new checkout may add to a store enters none, and that module's own store holds the pin alone"
else
  fail "a new checkout's pin passed the limit into a shared store, or its module was cloned whole (rc=$RC_W_SIXTH; m_shallow store roots: $(cat "$W_STORES/m_shallow/shallow" 2>&1 | tr '\n' ' '); own m_shallow roots: $(cat "$SIXTH_W_GIT/modules/m_shallow/shallow" 2>&1 | tr '\n' ' '); left: $(find "$W_STORES" -name 'submodule_sync.incoming.*' -o -name 'tmp_pack_*' | tr '\n' ' ')): $(grep -e '^submodule_sync' "$TMP_ROOT/w-sixth.log" | head -6)"
fi
# A pin that MOVES in a checkout already linked is fetched as a clone of its
# own would fetch it, by a plain fetch under the time bound. The fourth
# worktree's m_shallow moves to W_MERGE: it arrives with the line under the
# roots whole, the store's roots stay where they were, and the move reads
# BEHIND, where the pin alone would read UNRELATED.
# NEGATIVE CONTROL, run against this check (2026-11-14, git 2.56.0): make
# probe_pin's walk print `alone` at the first line that ends at a commit with
# no parent that is not a root (`if (!root[c]) { print "alone"; exit 0 }`
# where it reads `if (root[c]) related = 1`): W_MERGE arrives as a third
# root and the row is UNRELATED.
$GIT -C "$FOURTH_W" update-index --cacheinfo "160000,$W_MERGE,m_shallow"
$GIT -C "$FOURTH_W" commit -qm "m_shallow moves to a merge of a line from under the store's roots"
SUBMODULE_SYNC_TRACE_NET=1 GIT_ALLOW_PROTOCOL=file bash "$SYNC" --root "$FOURTH_W" --fetch --restore >"$TMP_ROOT/w-fourth-merge.log" 2>&1
RC_W_FOURTH_MERGE=$?
if [ "$RC_W_FOURTH_MERGE" -eq 0 ] && [ "$(sha "$FOURTH_W/m_shallow" HEAD)" = "$W_MERGE" ] &&
   w_linked_to "$FOURTH_W/m_shallow" "$W_STORES/m_shallow" &&
   [ "$(git --git-dir="$W_STORES/m_shallow" rev-list "$W_MERGE" | sort | tr '\n' ' ')" = "$(printf '%s\n' "$W_MERGE" "$W_UNDER" "$W1" "$W6" "$W5" "$W4" "$W3" | sort | tr '\n' ' ')" ] &&
   w_roots "$W_STORES/m_shallow" "$W3" "$W_SIDE" && w_lacks "$W_STORES/m_shallow" "$W2" &&
   grep -q -e '^submodule_sync --fetch: m_shallow: fetched pin .* (missing, with its history down to commits the store held)$' "$TMP_ROOT/w-fourth-merge.log" &&
   grep -q -e '^restoring m_shallow \.\.\. ok ' "$TMP_ROOT/w-fourth-merge.log" &&
   [ -z "$(find "$W_STORES" -name 'submodule_sync.incoming.*' -o -name 'tmp_pack_*')" ] &&
   w_configs_unchanged && w_first_unchanged && [ "$(w_first_history)" = "$W_FIRST_HISTORY" ]; then
  pass "a moved pin that merges a line from under the store's roots arrives with it, as in a clone of its own, and reads BEHIND"
else
  fail "a merge of a line from under the roots did not arrive as a clone of its own would fetch it (rc=$RC_W_FOURTH_MERGE head=$(sha "$FOURTH_W/m_shallow" HEAD); roots: $(cat "$W_STORES/m_shallow/shallow" 2>&1 | tr '\n' ' ')): $(grep -e 'm_shallow' -e '^net: ' "$TMP_ROOT/w-fourth-merge.log" | head -5)"
fi

# ---------------------------------------------------------------------------
# Fixture X — stores a second worktree does not share. Each module has one
# reason and nothing else wrong, so each guard of shared_store_of,
# module_store_for and own_store_names_another_worktree decides one row:
#   x_ok    nothing: the control, shared
#   x_alt   the store borrows objects (objects/info/alternates)
#   x_obj   the store's objects directory is a symbolic link
#   x_wtc   extensions.worktreeConfig, with core.worktree still in the store's
#           own config: git would apply it to a linked checkout too
#   x_lost  the store's core.worktree resolves nowhere and the first checkout
#           has no checkout left to say what it should be
#   x_priv  the second worktree already has a private store of its own
# A module that is not shared is populated as it always was, by a clone under
# the worktree, and the first checkout's stores are left byte for byte.
# ---------------------------------------------------------------------------
echo "=== fixture X: stores a second worktree does not share ==="
SUPER_X="$TMP_ROOT/x first"
SECOND_X="$TMP_ROOT/x second"
$GIT init -q -b main "$SUPER_X"
echo root >"$SUPER_X/README"
$GIT -C "$SUPER_X" add README
$GIT -C "$SUPER_X" commit -qm root
for X_M in x_ok x_alt x_obj x_wtc x_lost x_priv; do
  $GIT -C "$SUPER_X" submodule -q add "$DONOR" "$X_M" 2>/dev/null
done
$GIT -C "$SUPER_X" commit -qm "six modules"
X_STORES="$SUPER_X/.git/modules"
mkdir -p "$TMP_ROOT/x-lender"
cp -R "$X_STORES/x_alt/objects" "$TMP_ROOT/x-lender/objects"
printf '%s\n' "$TMP_ROOT/x-lender/objects" >"$X_STORES/x_alt/objects/info/alternates"
mv "$X_STORES/x_obj/objects" "$TMP_ROOT/x-objects"
ln -s "$TMP_ROOT/x-objects" "$X_STORES/x_obj/objects"
git config --file "$X_STORES/x_wtc/config" core.repositoryformatversion 1
git config --file "$X_STORES/x_wtc/config" extensions.worktreeConfig true
rm -rf "$SUPER_X/x_lost"
mkdir "$SUPER_X/x_lost"
git config --file "$X_STORES/x_lost/config" core.worktree ../../../no-such-directory
$GIT -C "$SUPER_X" worktree add -q --detach "$SECOND_X" HEAD
SECOND_X_GIT="$(git -C "$SECOND_X" rev-parse --absolute-git-dir)"
$GIT -C "$SECOND_X" submodule -q update --init -- x_priv 2>/dev/null
rm -rf "$SECOND_X/x_priv"
mkdir "$SECOND_X/x_priv"
X_COPIES="$TMP_ROOT/x-copies"
mkdir -p "$X_COPIES"
for X_M in x_ok x_alt x_obj x_wtc x_lost x_priv; do cp "$X_STORES/$X_M/config" "$X_COPIES/$X_M.config"; done
x_configs_unchanged() {
  local m
  for m in x_ok x_alt x_obj x_wtc x_lost x_priv; do cmp -s "$X_STORES/$m/config" "$X_COPIES/$m.config" || return 1; done
}
x_private() { # <module>: populated from a store of the second worktree's own, at its pin
  [ -d "$SECOND_X_GIT/modules/$1/objects" ] && [ "$(sha "$SECOND_X/$1" HEAD)" = "$C4" ] &&
    [ "$(cd "$(git -C "$SECOND_X/$1" rev-parse --absolute-git-dir)" && pwd -P)" = "$(cd "$SECOND_X_GIT/modules/$1" && pwd -P)" ] &&
    [ ! -e "$X_STORES/$1/worktrees" ]
}
GIT_ALLOW_PROTOCOL=file bash "$SYNC" --root "$SECOND_X" --fetch --restore >"$TMP_ROOT/x-restore.log" 2>&1
RC_X=$?
X_RESULT=""
for X_M in x_alt x_obj x_wtc x_lost x_priv; do
  if x_private "$X_M"; then X_RESULT="$X_RESULT $X_M=private"; else X_RESULT="$X_RESULT $X_M=SHARED-OR-BROKEN"; fi
done
# NEGATIVE CONTROLS, each tried by hand: delete the one guard a row names.
# Without shared_store_of's alternates or objects-symlink test, or
# module_store_for's private-store test, that row alone reads
# SHARED-OR-BROKEN. Without its worktreeConfig test x_wtc is still cloned
# privately, but only after a linked checkout was made there and removed
# again; without its `rev-parse --git-dir` probe, x_lost only after a fetch
# into a store git cannot open. The log names either attempt.
if [ "$RC_X" -eq 0 ] && [ "$X_RESULT" = " x_alt=private x_obj=private x_wtc=private x_lost=private x_priv=private" ] &&
   [ "$(sha "$SECOND_X/x_ok" HEAD)" = "$C4" ] && [ ! -e "$SECOND_X_GIT/modules/x_ok" ] &&
   [ -f "$(git -C "$SECOND_X/x_ok" rev-parse --absolute-git-dir)/commondir" ] &&
   ! grep -q -e 'not shared from' -e 'submodule_sync --restore:' "$TMP_ROOT/x-restore.log" &&
   x_configs_unchanged && [ "$(sha "$SUPER_X/x_wtc" HEAD)" = "$C4" ] &&
   [ -z "$($GIT -C "$SUPER_X/x_wtc" status --porcelain)" ]; then
  pass "a store that borrows objects, has a worktree config, has no checkout to name, or is already private is not shared"
else
  fail "a store that must not be shared was, or its module was not populated (rc=$RC_X:$X_RESULT): $(tail -4 "$TMP_ROOT/x-restore.log")"
fi

# A copied checkout whose .git file still names the ORIGINAL's store is not
# this superproject's checkout of that store: reconnecting it would point the
# original's store at the copy. Its parent has a store of its own for that
# module, which is how the predicate tells.
COPY_X="$TMP_ROOT/x copy"
$GIT clone -q --no-recurse-submodules "$SUPER_X" "$COPY_X"
$GIT -C "$COPY_X" submodule -q update --init -- x_ok 2>/dev/null
printf 'gitdir: %s\n' "$(cd "$X_STORES/x_ok" && pwd -P)" >"$COPY_X/x_ok/.git"
bash "$SYNC" --root "$COPY_X" --offline --restore >"$TMP_ROOT/x-copy.log" 2>&1
# NEGATIVE CONTROL, tried by hand: delete own_store_names_another_worktree's
# `[ "$own" = "$target" ] || return 1` and the original's config is rewritten.
if x_configs_unchanged && [ "$(sha "$SUPER_X/x_ok" HEAD)" = "$C4" ] &&
   ! grep -q '^reconnected ' "$TMP_ROOT/x-copy.log"; then
  pass "a copied checkout that names another superproject's store is not reconnected to it"
else
  fail "a copied checkout rewrote the original store's config: $(tail -3 "$TMP_ROOT/x-copy.log")"
fi

# ---------------------------------------------------------------------------
# Fixture WA — a shared store whose remote is GitHub. A GitHub pin is read
# through Agh alone (fetch_pin, scripts/lib/github_source_transport.py), so a
# second worktree's pin comes into the first checkout's store through Agh,
# with no plain git fetch or probe, and under the store's own lock. A refusal
# brings nothing into the store and no Git fetch stands in for it.
# ---------------------------------------------------------------------------
echo "=== fixture WA: a GitHub pin comes into a shared store through Agh ==="
DONOR_WA="$TMP_ROOT/donor_wa"
make_donor "$DONOR_WA"
SUPER_WA="$TMP_ROOT/wa first"
$GIT init -q -b main "$SUPER_WA"
echo root >"$SUPER_WA/README"
$GIT -C "$SUPER_WA" add README
$GIT -C "$SUPER_WA" commit -qm root
$GIT -C "$SUPER_WA" submodule -q add "$DONOR_WA" m_gh 2>/dev/null
# The store's remote, the superproject's registration and .gitmodules all
# name GitHub, so no step can reach the donor except the provider below.
$GIT -C "$SUPER_WA/m_gh" remote set-url origin https://github.com/fixture/shared.git
$GIT -C "$SUPER_WA" config submodule.m_gh.url https://github.com/fixture/shared.git
$GIT -C "$SUPER_WA" config -f .gitmodules submodule.m_gh.url https://github.com/fixture/shared.git
$GIT -C "$SUPER_WA" add .gitmodules
$GIT -C "$SUPER_WA" commit -qm "a module whose remote is GitHub"
# The pin the second worktree records: a grandchild of the store's HEAD that
# no ref of the donor holds, so only an exact acquisition brings it. Its
# parent's f.txt is in neither the store nor the pin's tree, so a fetch that
# brings the pin's checkout without its history's files leaves it out.
$GIT -C "$DONOR_WA" checkout -q --detach main
echo "line 5" >>"$DONOR_WA/f.txt"
$GIT -C "$DONOR_WA" commit -qam c5
echo "line 6" >>"$DONOR_WA/f.txt"
$GIT -C "$DONOR_WA" commit -qam c6
WA5="$(sha "$DONOR_WA" HEAD)"
$GIT -C "$DONOR_WA" checkout -q main
$GIT -C "$DONOR_WA" config uploadpack.allowAnySHA1InWant true
$GIT -C "$DONOR_WA" config uploadpack.allowFilter true
WA_STORE="$(cd "$SUPER_WA/.git/modules/m_gh" && pwd -P)"
WA_PROVIDER="$TMP_ROOT/wa-provider"
mkdir -p "$WA_PROVIDER"
printf '%s\n' "$DONOR_WA" >"$WA_PROVIDER/donor"
printf '%s\n' "$WA_STORE" >"$WA_PROVIDER/store"
cat >"$WA_PROVIDER/agh" <<'EOF'
#!/bin/sh
# Stands in for `agh repo fetch REPO DIR --ref PIN --into REF`, into <DIR>
# under the private ref. Without --checkout-closure (Agh's NativeExact) it is
# an unfiltered fetch negotiated against <DIR>. With it (Agh's selected
# checkout), or in mode `filtered`, it is what Agh installs then: a
# blob-filtered fetch into a scratch repository, whose pack is moved into
# <DIR> with no promisor marker.
set -eu
base="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd -P)"
printf '%s\n' "$4" >>"$base/trace"
printf '%s\n' "$*" >>"$base/argv"
case "$#:${9:-}" in
  8:) closure=0 ;;
  9:--checkout-closure) closure=1 ;;
  *) exit 97 ;;
esac
[ "$1" = repo ] && [ "$2" = fetch ] && [ "$3" = fixture/shared ]
[ "$5" = --ref ] && [ "$7" = --into ] && [ "$8" = "refs/agh/trust-source-pins/$6" ]
[ "$4" = "$(cat "$base/store")" ] || exit 98
mode="$(cat "$base/mode")"
case "$mode" in
  fetch|filtered) ;;
  *) echo 'fixture owner-routed Agh refusal' >&2; exit 73 ;;
esac
if [ "$closure" -eq 0 ] && [ "$mode" = fetch ]; then
  git -c protocol.file.allow=always --git-dir="$4" fetch -q --no-tags --no-write-fetch-head \
    "$(cat "$base/donor")" "+$6:$8"
  exit 0
fi
scratch="$base/scratch.$$"
rm -rf "$scratch"
git init -q --bare "$scratch"
git --git-dir="$scratch" config extensions.partialClone origin
git --git-dir="$scratch" config remote.origin.url "file://$(cat "$base/donor")"
git --git-dir="$scratch" config remote.origin.promisor true
git -c protocol.file.allow=always --git-dir="$scratch" fetch -q --no-tags --filter=blob:none origin "+$6:refs/agh/source"
cp "$scratch"/objects/pack/pack-*.pack "$scratch"/objects/pack/pack-*.idx "$4/objects/pack/"
rm -rf "$scratch"
git --git-dir="$4" update-ref "$8" "$6"
EOF
chmod +x "$WA_PROVIDER/agh"
wa_second() { # <dir>: a second worktree whose commit pins WA5
  $GIT -C "$SUPER_WA" worktree add -q --detach "$1" HEAD
  $GIT -C "$1" update-index --cacheinfo "160000,$WA5,m_gh"
  $GIT -C "$1" commit -qm "the second worktree pins a commit the shared store lacks"
}
WA_REFUSED="$TMP_ROOT/wa refused"
wa_second "$WA_REFUSED"
printf 'refuse\n' >"$WA_PROVIDER/mode"
PATH="$WA_PROVIDER:$PATH" SUBMODULE_SYNC_TRACE_NET=1 GIT_ALLOW_PROTOCOL=file \
  bash "$SYNC" --root "$WA_REFUSED" --fetch --restore >"$TMP_ROOT/wa-refused.log" 2>&1
RC_WA_REFUSED=$?
if [ "$RC_WA_REFUSED" -ne 0 ] && [ -s "$WA_PROVIDER/trace" ] &&
   grep -q 'fixture owner-routed Agh refusal' "$TMP_ROOT/wa-refused.log" &&
   grep -q 'no Git fallback' "$TMP_ROOT/wa-refused.log" &&
   ! grep -q -e '^net: store fetch ' -e '^net: probe ' -e '^net: fetch ' "$TMP_ROOT/wa-refused.log" &&
   ! git --git-dir="$WA_STORE" cat-file -e "$WA5^{commit}" 2>/dev/null &&
   [ ! -e "$WA_STORE/worktrees" ]; then
  pass "an Agh refusal for a shared store's GitHub pin brings nothing into the store and no Git fetch stands in"
else
  fail "a refused Agh fetch for a shared store was hidden or replaced by Git (rc=$RC_WA_REFUSED): $(tail -4 "$TMP_ROOT/wa-refused.log")"
fi
$GIT -C "$SUPER_WA" worktree remove --force "$WA_REFUSED" >/dev/null 2>&1 || true
# An Agh that brings the pin without its history's files: what the
# selected-checkout closure installs. Nothing of it may be used, and the
# store is left as complete as it was.
wa_store_complete() {
  ! git --git-dir="$WA_STORE" rev-list --objects --missing=print --all 2>/dev/null | grep -q '^?'
}
WA_FILTERED="$TMP_ROOT/wa filtered"
wa_second "$WA_FILTERED"
printf 'filtered\n' >"$WA_PROVIDER/mode"
PATH="$WA_PROVIDER:$PATH" SUBMODULE_SYNC_TRACE_NET=1 GIT_ALLOW_PROTOCOL=file \
  bash "$SYNC" --root "$WA_FILTERED" --fetch --restore >"$TMP_ROOT/wa-filtered.log" 2>&1
RC_WA_FILTERED=$?
if [ "$RC_WA_FILTERED" -ne 0 ] &&
   grep -q 'without every object its history needs' "$TMP_ROOT/wa-filtered.log" &&
   ! git --git-dir="$WA_STORE" rev-parse -q --verify "refs/agh/trust-source-pins/$WA5" >/dev/null &&
   [ ! -e "$WA_STORE/worktrees" ] && wa_store_complete &&
   ! grep -q -e '^net: store fetch ' -e '^net: probe ' -e '^net: fetch ' "$TMP_ROOT/wa-filtered.log"; then
  pass "a pin Agh brings into a shared store without its history's files is not used, and no ref holds it there"
else
  fail "a shared store took a pin without its history's files (rc=$RC_WA_FILTERED): $(tail -4 "$TMP_ROOT/wa-filtered.log")"
fi
$GIT -C "$SUPER_WA" worktree remove --force "$WA_FILTERED" >/dev/null 2>&1 || true
rm -f "$WA_PROVIDER/trace" "$WA_PROVIDER/argv"
WA_SECOND="$TMP_ROOT/wa second"
wa_second "$WA_SECOND"
printf 'fetch\n' >"$WA_PROVIDER/mode"
# NEGATIVE CONTROLS, tried by hand (2026-11-16): route restore_absent_from_store's
# GitHub store through shared_fetch again and the log names a store fetch that
# GIT_ALLOW_PROTOCOL=file refuses; the module is then cloned privately. Drop
# `native` from shared_agh_fetch and the provider installs the closure, which
# is refused, and the module is not linked.
PATH="$WA_PROVIDER:$PATH" SUBMODULE_SYNC_TRACE_NET=1 GIT_ALLOW_PROTOCOL=file \
  bash "$SYNC" --root "$WA_SECOND" --fetch --restore >"$TMP_ROOT/wa-restore.log" 2>&1
RC_WA=$?
WA_GITDIR="$(git -C "$WA_SECOND/m_gh" rev-parse --absolute-git-dir 2>/dev/null)"
if [ "$RC_WA" -eq 0 ] && [ "$(sha "$WA_SECOND/m_gh" HEAD)" = "$WA5" ] &&
   [ -f "$WA_GITDIR/commondir" ] && [ ! -e "$WA_GITDIR/objects" ] &&
   [ "$(cd "$(git -C "$WA_SECOND/m_gh" rev-parse --path-format=absolute --git-common-dir)" && pwd -P)" = "$WA_STORE" ] &&
   [ ! -e "$(git -C "$WA_SECOND" rev-parse --absolute-git-dir)/modules" ] &&
   [ "$(cat "$WA_PROVIDER/trace")" = "$WA_STORE" ] &&
   grep -q '^net: agh source-pin native https://github.com/fixture/shared.git ' "$TMP_ROOT/wa-restore.log" &&
   ! grep -q -e '^net: store fetch ' -e '^net: probe ' -e '^net: fetch ' -e 'not shared from' "$TMP_ROOT/wa-restore.log" &&
   ! grep -q -e '--checkout-closure' "$WA_PROVIDER/argv" &&
   ! git --git-dir="$WA_STORE" rev-parse -q --verify "refs/agh/trust-source-pins/$WA5" >/dev/null &&
   wa_store_complete && git --git-dir="$WA_STORE" gc -q 2>/dev/null &&
   git --git-dir="$WA_STORE" merge-base --is-ancestor "$(sha "$SUPER_WA/m_gh" HEAD)" "$WA5" &&
   [ "$(sha "$SUPER_WA/m_gh" HEAD)" = "$(sha "$DONOR_WA" main)" ] &&
   [ -z "$($GIT -C "$SUPER_WA" status --porcelain)" ]; then
  pass "a shared store's GitHub pin comes through Agh's unfiltered exact fetch, with its history and its files, leaves no ref, and the second worktree adds no private store"
else
  fail "a shared store's GitHub pin did not come through Agh alone (rc=$RC_WA): $(tail -4 "$TMP_ROOT/wa-restore.log")"
fi

# ---------------------------------------------------------------------------
# Fixture WP — a second worktree whose path shares only a top-level directory
# with the first checkout's. Plain `git submodule update` in a linked checkout
# there writes a core.worktree that, read from the store, names the second
# worktree's own checkout: the first checkout's git then works in it without
# an error, and x.py's `reset --hard` and `clean -dfx` there delete its edits.
# The hazard is shown with plain git first, so the check is not vacuous where
# no such directory can be made; that machine skips it, by name.
# ---------------------------------------------------------------------------
echo "=== fixture WP: a checkout whose store would name it as the first checkout's is not linked ==="
DONOR_WP="$TMP_ROOT/donor_wp"
make_donor "$DONOR_WP"
SUPER_WP="$TMP_ROOT/wp first"
$GIT init -q -b main "$SUPER_WP"
echo root >"$SUPER_WP/README"
$GIT -C "$SUPER_WP" add README
$GIT -C "$SUPER_WP" commit -qm root
$GIT -C "$SUPER_WP" submodule -q add "$DONOR_WP" m 2>/dev/null
$GIT -C "$SUPER_WP" commit -qm "one complete store"
WP_STORE="$(cd "$SUPER_WP/.git/modules/m" && pwd -P)"
WP_FIRST_M="$(cd "$SUPER_WP/m" && pwd -P)"
WP_WORKTREE_VALUE="$(git config --file "$WP_STORE/config" core.worktree)"
WP_OUT=""
for WP_BASE in /tmp /var/tmp /dev/shm; do
  WP_CAND="$(mktemp -d "$WP_BASE/submodule_sync_wp.XXXXXX" 2>/dev/null)" || continue
  OUTSIDE_DIRS="$OUTSIDE_DIRS $WP_CAND"
  $GIT -C "$SUPER_WP" worktree add -q --detach "$WP_CAND/probe" HEAD
  git -c worktree.useRelativePaths=false --git-dir="$WP_STORE" worktree add -q --detach "$WP_CAND/probe/m" HEAD
  (cd "$WP_CAND/probe" && $GIT submodule -q update -- m) >/dev/null 2>&1
  WP_TOP="$(git -C "$SUPER_WP/m" rev-parse --show-toplevel 2>/dev/null)"
  WP_HAZARD=0
  [ -z "$WP_TOP" ] || [ "$(cd "$WP_TOP" && pwd -P)" != "$(cd "$WP_CAND/probe/m" && pwd -P)" ] || WP_HAZARD=1
  git --git-dir="$WP_STORE" worktree remove --force "$WP_CAND/probe/m" >/dev/null 2>&1
  $GIT -C "$SUPER_WP" worktree remove --force "$WP_CAND/probe" >/dev/null 2>&1
  git config --file "$WP_STORE/config" core.worktree "$WP_WORKTREE_VALUE"
  if [ "$WP_HAZARD" -eq 1 ]; then WP_OUT="$WP_CAND"; break; fi
  rm -rf "$WP_CAND"
done
if [ -z "$WP_OUT" ]; then
  echo "  skip: no directory here shares only a top-level directory with $TMP_ROOT (tried /tmp, /var/tmp, /dev/shm)"
else
  WP_SECOND="$WP_OUT/second"
  $GIT -C "$SUPER_WP" worktree add -q --detach "$WP_SECOND" HEAD
  # NEGATIVE CONTROL, tried by hand (2026-11-16): make link_would_alias
  # answer no and the checkout is linked; the `git submodule update` below
  # then makes the first checkout's git read the second worktree's checkout.
  GIT_ALLOW_PROTOCOL=file bash "$SYNC" --root "$WP_SECOND" --offline --restore >"$TMP_ROOT/wp-restore.log" 2>&1
  RC_WP=$?
  WP_GITDIR="$(git -C "$WP_SECOND/m" rev-parse --absolute-git-dir 2>/dev/null)"
  (cd "$WP_SECOND" && $GIT submodule -q update -- m) >/dev/null 2>&1
  WP_TOP="$(git -C "$SUPER_WP/m" rev-parse --show-toplevel 2>/dev/null)"
  if [ "$RC_WP" -eq 0 ] && grep -q 'not linked to' "$TMP_ROOT/wp-restore.log" &&
     [ -n "$WP_GITDIR" ] && [ ! -e "$WP_GITDIR/commondir" ] && [ ! -e "$WP_STORE/worktrees" ] &&
     [ "$(sha "$WP_SECOND/m" HEAD)" = "$(sha "$SUPER_WP/m" HEAD)" ] &&
     [ -n "$WP_TOP" ] && [ "$(cd "$WP_TOP" && pwd -P)" = "$WP_FIRST_M" ]; then
    pass "a second worktree that shares only a top-level directory with the first gets a private store, and the first checkout's git still reads its own checkout"
  else
    fail "a second worktree beside a top-level directory was linked (rc=$RC_WP, first checkout's git reads ${WP_TOP:-nothing}): $(tail -3 "$TMP_ROOT/wp-restore.log")"
  fi
  $GIT -C "$SUPER_WP" worktree remove --force "$WP_SECOND" >/dev/null 2>&1 || true
fi

# ---------------------------------------------------------------------------
# Fixture WL — a store another sync holds. The waiter says it waits, gives up
# after SUBMODULE_SYNC_LOCK_WAIT seconds, brings nothing into the store, and
# gives its module a store of its own.
# ---------------------------------------------------------------------------
echo "=== fixture WL: a store another sync holds is waited for, within a bound ==="
DONOR_WL="$TMP_ROOT/donor_wl"
make_donor "$DONOR_WL"
SUPER_WL="$TMP_ROOT/wl first"
$GIT init -q -b main "$SUPER_WL"
echo root >"$SUPER_WL/README"
$GIT -C "$SUPER_WL" add README
$GIT -C "$SUPER_WL" commit -qm root
$GIT -C "$SUPER_WL" submodule -q add "$DONOR_WL" m 2>/dev/null
$GIT -C "$SUPER_WL" commit -qm "one complete store"
# A pin the store lacks, on the donor's main, so a clone of the module's own
# brings it.
echo "line 5" >>"$DONOR_WL/f.txt"
$GIT -C "$DONOR_WL" commit -qam c5
WL5="$(sha "$DONOR_WL" main)"
WL_STORE="$(cd "$SUPER_WL/.git/modules/m" && pwd -P)"
WL_SECOND="$TMP_ROOT/wl second"
$GIT -C "$SUPER_WL" worktree add -q --detach "$WL_SECOND" HEAD
$GIT -C "$WL_SECOND" update-index --cacheinfo "160000,$WL5,m"
$GIT -C "$WL_SECOND" commit -qm "a pin the store lacks"
: >>"$WL_STORE/submodule_sync.lock"
perl -e 'use Fcntl qw(:flock); open(my $l, ">>", $ARGV[0]) or exit 1; flock($l, LOCK_EX) or exit 1; open(my $r, ">", $ARGV[1]); close($r); sleep 120' \
  "$WL_STORE/submodule_sync.lock" "$TMP_ROOT/wl-held" &
WL_HOLDER=$!
DECOY_PIDS="$DECOY_PIDS $WL_HOLDER"
while kill -0 "$WL_HOLDER" 2>/dev/null && [ ! -e "$TMP_ROOT/wl-held" ]; do sleep 0.1; done
# NEGATIVE CONTROL, tried by hand (2026-11-16): a blocking flock in
# lock_store waits until the holder ends, two minutes on, and then links.
SUBMODULE_SYNC_LOCK_WAIT=6 GIT_ALLOW_PROTOCOL=file \
  bash "$SYNC" --root "$WL_SECOND" --fetch --restore >"$TMP_ROOT/wl-restore.log" 2>&1
RC_WL=$?
WL_GITDIR="$(git -C "$WL_SECOND/m" rev-parse --absolute-git-dir 2>/dev/null)"
if [ -e "$TMP_ROOT/wl-held" ] && kill -0 "$WL_HOLDER" 2>/dev/null && [ "$RC_WL" -eq 0 ] &&
   grep -q 'waiting for another sync to finish with' "$TMP_ROOT/wl-restore.log" &&
   grep -q "is busy: another sync held its lock for 6s" "$TMP_ROOT/wl-restore.log" &&
   ! git --git-dir="$WL_STORE" cat-file -e "$WL5^{commit}" 2>/dev/null && [ ! -e "$WL_STORE/worktrees" ] &&
   [ -n "$WL_GITDIR" ] && [ ! -e "$WL_GITDIR/commondir" ] && [ "$(sha "$WL_SECOND/m" HEAD)" = "$WL5" ]; then
  pass "a store another sync holds is waited for, said so, and given up after the bound; the module gets a store of its own"
else
  fail "a held store was not given up within the bound (rc=$RC_WL): $(tail -4 "$TMP_ROOT/wl-restore.log")"
fi
kill "$WL_HOLDER" 2>/dev/null
wait "$WL_HOLDER" 2>/dev/null

# ---------------------------------------------------------------------------
# Fixture WK — a pin that is in a shared store without its history: a depth
# fetch killed after its pack was installed and before its `shallow` line was
# written leaves exactly this (here it is planted). It is not "already
# there": the restore fetches it again, and the store reads it whole.
# ---------------------------------------------------------------------------
echo "=== fixture WK: a pin present without its history is fetched again ==="
DONOR_WK="$TMP_ROOT/donor_wk"
make_donor "$DONOR_WK"
$GIT -C "$DONOR_WK" config uploadpack.allowFilter true
$GIT -C "$DONOR_WK" config uploadpack.allowAnySHA1InWant true
WK4="$(sha "$DONOR_WK" main)"
WK2="$(sha "$DONOR_WK" main~2)"
SUPER_WK="$TMP_ROOT/wk first"
$GIT init -q -b main "$SUPER_WK"
echo root >"$SUPER_WK/README"
$GIT -C "$SUPER_WK" add README
$GIT -C "$SUPER_WK" commit -qm root
$GIT -C "$SUPER_WK" submodule -q add --depth 1 "file://$DONOR_WK" m 2>/dev/null
$GIT -C "$SUPER_WK" commit -qm "one shallow store"
WK_STORE="$(cd "$SUPER_WK/.git/modules/m" && pwd -P)"
# The pin, its tree and its files, and not its parent, into the store, with
# no `shallow` line for it.
$GIT -C "$DONOR_WK" rev-list --objects --no-walk "$WK2" | cut -d' ' -f1 |
  $GIT -C "$DONOR_WK" pack-objects -q --stdout | git --git-dir="$WK_STORE" unpack-objects -q
WK_SECOND="$TMP_ROOT/wk second"
$GIT -C "$SUPER_WK" worktree add -q --detach "$WK_SECOND" HEAD
$GIT -C "$WK_SECOND" update-index --cacheinfo "160000,$WK2,m"
$GIT -C "$WK_SECOND" commit -qm "a pin the store holds without its history"
if git --git-dir="$WK_STORE" cat-file -e "$WK2^{commit}" &&
   ! git --git-dir="$WK_STORE" rev-list --objects "$WK2" >/dev/null 2>&1 &&
   [ "$(cat "$WK_STORE/shallow")" = "$WK4" ]; then
  pass "fixture: the shared store holds the pin, not its parent, and no shallow line for it"
else
  fail "fixture WK invalid: the pin is not planted without its history"
fi
# NEGATIVE CONTROL, tried by hand (2026-11-16): with pin_whole testing only
# `cat-file -e`, the restore links the pin as it is and the store's walk of
# it still fails.
GIT_ALLOW_PROTOCOL=file SUBMODULE_SYNC_TRACE_NET=1 \
  bash "$SYNC" --root "$WK_SECOND" --fetch --restore >"$TMP_ROOT/wk-restore.log" 2>&1
RC_WK=$?
WK_GITDIR="$(git -C "$WK_SECOND/m" rev-parse --absolute-git-dir 2>/dev/null)"
if [ "$RC_WK" -eq 0 ] && grep -q '^net: store fetch ' "$TMP_ROOT/wk-restore.log" &&
   git --git-dir="$WK_STORE" rev-list --objects "$WK2" >/dev/null 2>&1 &&
   w_roots "$WK_STORE" "$WK4" "$WK2" &&
   [ -n "$WK_GITDIR" ] && [ -f "$WK_GITDIR/commondir" ] && [ "$(sha "$WK_SECOND/m" HEAD)" = "$WK2" ] &&
   [ -z "$(ls -d "$WK_STORE"/submodule_sync.incoming.* 2>/dev/null)" ]; then
  pass "a pin present in a shared store without its history is fetched again, and every checkout of the store reads it whole"
else
  fail "a pin present without its history was taken as it was (rc=$RC_WK): $(tail -4 "$TMP_ROOT/wk-restore.log")"
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
   { [ "$Q_UNREADABLE_RC" -ne 1 ] || grep -q "Could not read $Q_MISSING" <<<"$Q_UNREADABLE_ERR"; }; then
  pass "fixture: native merge-base reports unreadable history, not unrelated roots"
else
  fail "fixture did not produce a native ancestry error (rc=$Q_UNREADABLE_RC, stderr: $Q_UNREADABLE_ERR)"
fi
Q_JSON="$(bash "$SYNC" --root "$SUPER_Q" --offline --json)"
Q_SCAN=$?
bash "$SYNC" --root "$SUPER_Q" --offline --restore >"$TMP_ROOT/q_offline.log" 2>&1
Q_RESTORE=$?
if [ "$Q_SCAN" -eq 2 ] && [ "$Q_RESTORE" -eq 2 ] &&
   grep -q '"state":"ANCESTRY-UNREADABLE"' <<<"$Q_JSON" &&
   [ "$(sha "$SUPER_Q/only" HEAD)" = "$Q_HEAD" ] &&
   ! $GIT -C "$SUPER_Q/only" cat-file -e "$Q_MISSING^{commit}" 2>/dev/null; then
  pass "offline incomplete ancestry stays unknown and moves neither HEAD nor objects"
else
  fail "incomplete ancestry was called unrelated or allowed restoration: $Q_JSON"
fi
Q_TEXT="$(bash "$SYNC" --root "$SUPER_Q" --offline 2>&1 || true)"
if grep -Fq -- "$Q_MISSING" <<<"$Q_JSON" &&
   grep -Fq -- "$Q_MISSING" <<<"$Q_TEXT" &&
   grep -Fq -- 'Could not read' <<<"$Q_JSON"; then
  pass "incomplete ancestry retains Git's actual missing-object diagnosis in both reports"
else
  fail "incomplete ancestry hides the missing object behind its exit status"
fi
if grep -q -- '--fetch --restore' <<<"$Q_TEXT"; then
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
   grep -q '"state":"UNRELATED"' <<<"$Q_UNRELATED_JSON" &&
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
   grep -q '"path":"behind","state":"PIN-INCOMPLETE"' <<<"$O_JSON" &&
   grep -q '"path":"atpin","state":"PIN-INCOMPLETE"' <<<"$O_JSON" &&
   grep -q '"restorable":0' <<<"$O_JSON" &&
   grep -q '"needs_review":2' <<<"$O_JSON" &&
   grep -q "$O_TREE" <<<"$O_JSON"; then
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
# The two byte bounds of a fetch into a store several checkouts read are
# read the same way.
for knob in SUBMODULE_SYNC_FETCH_TIMEOUT SUBMODULE_SYNC_PROBE_LIMIT_KB SUBMODULE_SYNC_LINK_LIMIT_KB; do
  for bad in abc 0 -5 ''; do
    env "$knob=$bad" bash "$SYNC" --root "$SUPER_T" >/dev/null 2>&1
    RC_T=$?
    if [ "$bad" = '' ]; then
      # An empty value is "unset": the default applies.
      [ "$RC_T" -eq 0 ] && pass "an empty $knob keeps the default" \
        || fail "empty $knob exited $RC_T"
    elif [ "$RC_T" -eq 3 ]; then
      pass "$knob='$bad' is refused as a usage error (exit 3)"
    else
      fail "$knob='$bad' exited $RC_T, expected 3"
    fi
  done
done

echo
if [ "$FAILURES" -eq 0 ]; then
  echo "submodule_sync_test: PASS"
  exit 0
fi
echo "submodule_sync_test: $FAILURES assertion(s) failed"
exit 1
