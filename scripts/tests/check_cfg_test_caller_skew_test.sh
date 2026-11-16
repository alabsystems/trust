#!/usr/bin/env bash
# The push-subject proof for `scripts/check_cfg_test_caller_skew.py`.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# `--selftest` proves the lane's READING (what counts as a skewed site) with no
# repository. This file proves its SUBJECT — which files a push is judged on —
# against real throwaway repositories and a real bare destination, because the
# subject is a property of `git ls-remote`, `rev-list` and a merge, not of a
# string this test invents.
#
# The defect it pins: an UPDATE was judged on every file `old..new` reached, so
# a branch that merged main re-read every file main had changed and was refused
# on sites the destination already carried byte for byte (crystal/callee-sidecar
# a573093063..d5e68f9812: 12 sites, four files identical to origin/main). The
# fix judges only what the push introduces to the destination it names, on the
# evidence scripts/lib/push_destination.sh reads for the revert lane too. Every
# GREEN arm below carries a control that is RED on the same range without a
# destination, so the skew is demonstrably inside the range; every RED arm is a
# skew the push really introduces, including the two cross-file shapes a
# file-level exclusion could have dropped.
set -euo pipefail
# The pre-push hook exports these; a fixture must never inherit the real push
# (TRUST_PUSH_REMOTE made K1-control ls-remote the real remote, 2026-09-28).
unset TRUST_PUSHED_REFS TRUST_PUSH_REMOTE

REPO_ROOT=$(cd -P "${BASH_SOURCE[0]%/*}/../.." && pwd -P)
CHECKER="$REPO_ROOT/scripts/check_cfg_test_caller_skew.py"
DESTINATION_LIB="$REPO_ROOT/scripts/lib/push_destination.sh"
HOOK="$REPO_ROOT/scripts/hooks-pin/pre-push"
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
ZERO=0000000000000000000000000000000000000000

PASSED=0
fail() { printf 'check_cfg_test_caller_skew_test: %s\n' "$*" >&2; exit 1; }
ok()   { PASSED=$((PASSED + 1)); printf '  ok  %s\n' "$*"; }

[ -f "$CHECKER" ] || fail "checker is missing: $CHECKER"
[ -f "$DESTINATION_LIB" ] || fail "destination reader is missing: $DESTINATION_LIB"

newrepo() {  # <dir>
  git init -q -b main "$1"
  git -C "$1" config user.name test
  git -C "$1" config user.email test@example.invalid
  git -C "$1" config commit.gpgsign false
  mkdir -p "$1/scripts/lib" "$1/crates/demo/src"
  cp "$CHECKER" "$1/scripts/check_cfg_test_caller_skew.py"
  cp "$DESTINATION_LIB" "$1/scripts/lib/push_destination.sh"
  cp "$REPO_ROOT/scripts/lib/remote_tips.py" "$REPO_ROOT/scripts/lib/landing_targo.py" "$REPO_ROOT/scripts/lib/remote_operation.py" "$1/scripts/lib/"
}
put() {  # <repo> <path> <content> <message>
  printf '%s\n' "$3" >"$1/$2"
  git -C "$1" add "$2"
  git -C "$1" commit -qm "$4"
}

# A free function with one production and one #[cfg(test)] caller, as both
# measured regressions had. <params> and <args> are spelled by the caller.
fn_file() {  # <name> <params> <prod-args> <test-args>
  cat <<EOF
pub(crate) fn $1($2) {}

fn production() {
    $1($3);
}

#[cfg(test)]
mod tests {
    use super::*;
    fn helper() {
        $1($4);
    }
}
EOF
}

R="$TMP/repo"
DEST="$TMP/dest.git"
newrepo "$R"
git init -q --bare -b main "$DEST"

# BASE: every file main and the lane will touch, all consistent.
fn_file main_fn 'a: u32' '1' '1' >"$R/crates/demo/src/main_owned.rs"
printf 'pub(crate) struct S { pub a: u32 }\n' >"$R/crates/demo/src/s.rs"
printf 'pub(crate) struct T { pub a: u32 }\n' >"$R/crates/demo/src/t.rs"
printf 'fn make() -> u32 { 0 }\n' >"$R/crates/demo/src/uses_t.rs"
printf 'pub(crate) struct U { pub a: u32 }\n' >"$R/crates/demo/src/u.rs"
fn_file lane_fn 'a: u32' '1' '1' >"$R/crates/demo/src/lane.rs"
git -C "$R" add -A
git -C "$R" commit -qm 'fixture: the lane checker, its destination reader, and a crate'
BASE=$(git -C "$R" rev-parse HEAD)

# Published MAIN: widens main_fn and leaves its #[cfg(test)] caller behind — a
# real skew that reached the destination without this lane, the shape of a
# site already on origin/main — and does the same ACROSS files: widens U and
# adds a literal of the old U beside it (the cross-file shape of the 2026-09-27
# Fact/Bounds readings). It also adds a literal of T in uses_t.rs, and widens S
# (updating nothing that constructs it, because nothing on main does).
git -C "$R" checkout -q -b m "$BASE"
fn_file main_fn 'a: u32, b: u32' '1, 2' '1' >"$R/crates/demo/src/main_owned.rs"
printf 'pub(crate) struct U { pub a: u32, pub b: u32 }\n' >"$R/crates/demo/src/u.rs"
printf 'fn mk() -> U { U { a: 1 } }\n' >"$R/crates/demo/src/uses_u.rs"
printf 'pub(crate) struct S { pub a: u32, pub b: u32 }\n' >"$R/crates/demo/src/s.rs"
printf 'fn make() -> T { T { a: 1 } }\n' >"$R/crates/demo/src/uses_t.rs"
git -C "$R" add -A
git -C "$R" commit -qm 'main: widen main_fn and U (one caller and one literal left behind) and S; construct T'
M_SKEW=$(git -C "$R" rev-parse HEAD)
git -C "$R" push -q "$DEST" "$M_SKEW:refs/heads/main"
MAIN_SITE="crates/demo/src/main_owned.rs:11"
MAIN_PAIR="crates/demo/src/uses_u.rs:1"

# The LANE: published once, then updated to a head that merges main.
git -C "$R" checkout -q -b lane "$BASE"
put "$R" crates/demo/src/lane_notes.rs 'fn notes() {}' 'lane: a first commit'
L_OLD=$(git -C "$R" rev-parse HEAD)
git -C "$R" push -q "$DEST" "$L_OLD:refs/heads/lane"
git -C "$R" merge -q --no-edit m
L_MERGED=$(git -C "$R" rev-parse HEAD)
git -C "$R" diff --name-only "$L_OLD" "$L_MERGED" | grep -qx crates/demo/src/main_owned.rs \
  || fail 'K1-fixture: main_owned.rs is not inside old..new, so K1 would prove nothing'

lane() {  # <new> <old> [--remote DEST | -] [extra ref line]
  local dest="${3:-$DEST}" args=(--push-context)
  [ "$dest" = - ] || args+=(--remote "$dest")
  ( cd "$R" && TRUST_PUSHED_REFS="refs/heads/lane $1 refs/heads/lane $2${4:+
$4}" python3 scripts/check_cfg_test_caller_skew.py "${args[@]}" 2>&1 )
}
subject() { printf '%s\n' "$1" | grep -m1 '^SUBJECT:' || true; }

# ------------------------------------------------------------------ K1 GREEN
if out=$(lane "$L_MERGED" "$L_OLD" -); then
  printf '%s\n' "$out" >&2
  fail 'K1-control: with no destination the merged-in skew passed; the arm is vacuous'
fi
case "$out" in *"$MAIN_SITE"*) ;; *) printf '%s\n' "$out" >&2; fail 'K1-control: the no-destination refusal did not name main'"'"'s site' ;; esac
case "$out" in *"$MAIN_PAIR"*'U { .. }'*'missing b'*) ;; *) printf '%s\n' "$out" >&2; fail 'K1-control: the no-destination refusal did not name main'"'"'s cross-file pair' ;; esac
if ( cd "$R" && python3 scripts/check_cfg_test_caller_skew.py --range "$L_OLD..$L_MERGED" >/dev/null 2>&1 ); then
  fail 'K1-control: the explicit --range audit excused main'"'"'s published skew'
fi
out=$(lane "$L_MERGED" "$L_OLD") \
  || { printf '%s\n' "$out" >&2; fail 'K1: an update was refused over a skewed site already on destination main'; }
case "$out" in *"$MAIN_SITE"*|*"$MAIN_PAIR"*) fail 'K1: a published site was still judged' ;; *) ;; esac
case "$out" in *'not this push'"'"'s'*) ;; *) printf '%s\n' "$out" >&2; fail 'K1: the verdict did not say which files it set aside' ;; esac
K1_ALONE="$(subject "$out")"
out=$(lane "$L_MERGED" "$L_OLD" "$DEST" "refs/heads/tmp $L_OLD refs/heads/tmp $ZERO") \
  || { printf '%s\n' "$out" >&2; fail 'K1: the update beside a throwaway new ref was refused'; }
case "$(subject "$out")" in "${K1_ALONE%%)*}"*) ;; *) fail "K1: one update, two subjects — alone: $K1_ALONE; beside a new ref: $(subject "$out")" ;; esac
out=$( ( cd "$R" && TRUST_PUSH_REMOTE="$DEST" TRUST_PUSHED_REFS="refs/heads/lane $L_MERGED refs/heads/lane $L_OLD" \
  python3 scripts/check_cfg_test_caller_skew.py --push-context 2>&1 ) ) \
  || { printf '%s\n' "$out" >&2; fail 'K1: --push-context with TRUST_PUSH_REMOTE (the full hook path) refused the update'; }
ok 'K1  an update merging skewed sites already on destination main (same-file and cross-file) PASSES — alone, beside a new ref, via TRUST_PUSH_REMOTE; without a destination and as --range it is still refused'

# Main MOVES ON after the lane merged it and rewrites both files again. The
# lane's copies are now at no destination TIP — only at the main commit the
# lane merged, a destination-side parent of what the push introduces. That is
# the real shape (crystal/m0 merged c6eb148a34; origin/main has moved past it),
# and those files are still not the push's.
git -C "$R" checkout -q m
fn_file main_fn 'a: u32, b: u32' '1, 2' '1, 2' >"$R/crates/demo/src/main_owned.rs"
printf 'fn mk() -> U { U { a: 1, b: 2 } }\n' >"$R/crates/demo/src/uses_u.rs"
git -C "$R" commit -qam 'main: repair its own caller and literal'
M_NEXT=$(git -C "$R" rev-parse HEAD)
git -C "$R" push -q "$DEST" "$M_NEXT:refs/heads/main"
out=$(lane "$L_MERGED" "$L_OLD") \
  || { printf '%s\n' "$out" >&2; fail 'K1c: after main moved on, the update was refused over files main had published'; }
case "$out" in *"$MAIN_SITE"*|*"$MAIN_PAIR"*) fail 'K1c: a published site was still judged' ;; *) ;; esac
if lane "$L_MERGED" "$L_OLD" - >/dev/null; then
  fail 'K1c-control: with no destination the merged-in skew passed; the arm is vacuous'
fi
git -C "$R" push -q -f "$DEST" "$M_SKEW:refs/heads/main"
git -C "$R" checkout -q lane
ok 'K1c  after destination main moves on, files carried from the main commit the lane merged are still not the push'"'"'s'

# The same, with the lane ALSO touching that crate cleanly: main's cross-file
# pair is then read as context (a pair with one introduced end must be judged,
# K3), and must still not be blamed, because neither of its files is the push's.
git -C "$R" checkout -q -b lane-clean "$L_MERGED"
put "$R" crates/demo/src/lane_notes.rs 'fn notes() -> u32 { 1 }' 'lane: a clean edit in the same crate'
L_CLEAN=$(git -C "$R" rev-parse HEAD)
out=$(lane "$L_CLEAN" "$L_OLD") \
  || { printf '%s\n' "$out" >&2; fail 'K1b: a clean update in the crate that carries main'"'"'s published pair was refused'; }
case "$out" in *'read only as cross-file context'*) ;; *) printf '%s\n' "$out" >&2; fail 'K1b: the verdict did not report its cross-file context' ;; esac
case "$out" in *"(0 of them read only"*) printf '%s\n' "$out" >&2; fail 'K1b: no context was read, so the arm proves nothing about the pair rule' ;; *) ;; esac
if lane "$L_CLEAN" "$L_OLD" - >/dev/null; then
  fail 'K1b-control: with no destination main'"'"'s published pair passed; the arm is vacuous'
fi
ok 'K1b  a clean update in the SAME crate as main'"'"'s published cross-file pair PASSES: the pair is read as context and not blamed'

# ------------------------------------------------------------------ K2 RED
# The lane widens its OWN function and leaves its #[cfg(test)] caller behind.
git -C "$R" checkout -q lane
fn_file lane_fn 'a: u32, b: u32' '1, 2' '1' >"$R/crates/demo/src/lane.rs"
git -C "$R" commit -qam 'lane: widen lane_fn, cfg(test) caller left behind'
L_SKEW=$(git -C "$R" rev-parse HEAD)
LANE_SITE="crates/demo/src/lane.rs:11"
if out=$(lane "$L_SKEW" "$L_OLD"); then
  printf '%s\n' "$out" >&2
  fail 'K2: an update introducing a NEW skewed call site passed'
fi
case "$out" in *"$LANE_SITE"*'lane_fn(..) takes 2'*) ;; *) printf '%s\n' "$out" >&2; fail 'K2: the refusal did not name the introduced site' ;; esac
case "$out" in *"$MAIN_SITE"*|*"$MAIN_PAIR"*) fail 'K2: the refusal blamed main'"'"'s already-published site' ;; *) ;; esac
if out=$(lane "$L_SKEW" "$L_OLD" "$DEST" "refs/heads/tmp $L_OLD refs/heads/tmp $ZERO"); then
  fail 'K2: a throwaway new ref beside the update hid the introduced skew'
fi
case "$out" in *"$LANE_SITE"*) ;; *) fail 'K2: the throwaway-ref refusal did not name the introduced site' ;; esac
ok 'K2  an update INTRODUCING a skewed call site is REFUSED by site, alone and beside a throwaway new ref; main'"'"'s published site is not blamed'

# ---------------------------------------------- K3 RED: the cross-file shapes
# A file-level exclusion must not drop a pair with ONE introduced end.
# (a) the lane widens T; uses_t.rs is main's, byte-identical on the destination,
#     and its `T { a: 1 }` no longer names every field.
git -C "$R" checkout -q -b lane-t "$L_MERGED"
printf 'pub(crate) struct T { pub a: u32, pub b: u32 }\n' >"$R/crates/demo/src/t.rs"
git -C "$R" commit -qam 'lane: widen T'
L_T=$(git -C "$R" rev-parse HEAD)
[ "$(git -C "$R" rev-parse "$L_T:crates/demo/src/uses_t.rs")" = "$(git -C "$R" rev-parse "$M_SKEW:crates/demo/src/uses_t.rs")" ] \
  || fail 'K3a-fixture: uses_t.rs is not byte-identical to destination main'
if out=$(lane "$L_T" "$L_OLD"); then
  printf '%s\n' "$out" >&2
  fail 'K3a: widening a struct left a literal in a destination-carried file behind, and passed'
fi
case "$out" in *'crates/demo/src/uses_t.rs:1'*'T { .. }'*'missing b'*) ;; *) printf '%s\n' "$out" >&2; fail 'K3a: the refusal did not name the stale literal in the carried file' ;; esac
case "$out" in *"$MAIN_SITE"*|*"$MAIN_PAIR"*) fail 'K3a: the refusal blamed main'"'"'s already-published site' ;; *) ;; esac
# (b) main widened S; the lane, written before it merged main, constructs S with
#     the old field list in a file of its own.
git -C "$R" checkout -q -b lane-s "$L_OLD"
put "$R" crates/demo/src/lane_s.rs 'fn build() -> S { S { a: 1 } }' 'lane: construct S'
git -C "$R" merge -q --no-edit m
L_S=$(git -C "$R" rev-parse HEAD)
if out=$(lane "$L_S" "$L_OLD"); then
  printf '%s\n' "$out" >&2
  fail 'K3b: a literal the push adds against a struct main widened passed'
fi
case "$out" in *'crates/demo/src/lane_s.rs:1'*'S { .. }'*'missing b'*) ;; *) printf '%s\n' "$out" >&2; fail 'K3b: the refusal did not name the introduced stale literal' ;; esac
case "$out" in *"$MAIN_SITE"*|*"$MAIN_PAIR"*) fail 'K3b: the refusal blamed main'"'"'s already-published site' ;; *) ;; esac
ok 'K3  a cross-file pair with one introduced end is still REFUSED both ways: a widened struct vs a carried literal, and an introduced literal vs a struct main widened'

# ------------------------------------------------- K4 RED: forged local refs
# The introduced skew stays refused however many LOCAL refs claim it is already
# published: a local branch, refs/remotes/origin/main, and a remote configured
# AT the destination whose tracking ref is forged to the skewed head.
git -C "$R" branch -q forged-local "$L_SKEW"
git -C "$R" update-ref refs/remotes/origin/main "$L_SKEW"
git -C "$R" remote add dest "$DEST"
git -C "$R" update-ref refs/remotes/dest/main "$L_SKEW"
git -C "$R" update-ref refs/remotes/dest/lane "$L_SKEW"
for d in "$DEST" dest; do
  if out=$(lane "$L_SKEW" "$L_OLD" "$d"); then
    printf '%s\n' "$out" >&2
    fail "K4: forged local refs hid the introduced skew (--remote $d)"
  fi
  case "$out" in *"$LANE_SITE"*) ;; *) fail "K4: the refusal did not name the introduced site (--remote $d)" ;; esac
done
if ( cd "$R" && TRUST_PUSH_REMOTE="$DEST" TRUST_PUSHED_REFS="refs/heads/lane $L_SKEW refs/heads/lane $L_OLD" \
  python3 scripts/check_cfg_test_caller_skew.py --push-context >/dev/null 2>&1 ); then
  fail 'K4: --push-context passed the introduced skew under forged tracking refs'
fi
# A NEW ref is judged against the destination's advertised main, never the
# local origin/main — which is forged to the skewed head right now, and would
# otherwise make base..head empty.
if out=$( ( cd "$R" && TRUST_PUSHED_REFS="refs/heads/fresh $L_SKEW refs/heads/fresh $ZERO" \
  python3 scripts/check_cfg_test_caller_skew.py --push-context --remote "$DEST" 2>&1 ) ); then
  printf '%s\n' "$out" >&2
  fail 'K4: a NEW ref carrying the skew passed while origin/main was forged to it'
fi
case "$out" in *"$LANE_SITE"*) ;; *) printf '%s\n' "$out" >&2; fail 'K4: the new-ref refusal did not name the introduced site' ;; esac
case "$out" in *"$MAIN_SITE"*|*"$MAIN_PAIR"*) fail 'K4: the new-ref refusal blamed main'"'"'s published site' ;; *) ;; esac
git -C "$R" update-ref -d refs/remotes/origin/main
git -C "$R" remote remove dest
git -C "$R" branch -q -D forged-local
ok 'K4  local branches, a forged origin/main and a forged tracking ref of a remote AT the destination exclude nothing — update and new ref alike'

# ------------------------------------------------ K5 GREEN: nothing introduced
out=$( ( cd "$R" && TRUST_PUSHED_REFS="refs/heads/copy $M_SKEW refs/heads/copy $ZERO" \
  python3 scripts/check_cfg_test_caller_skew.py --push-context --remote "$DEST" 2>&1 ) ) \
  || { printf '%s\n' "$out" >&2; fail 'K5: a new ref naming a commit already on the destination was refused'; }
case "$out" in *'nothing introduced'*) ;; *) printf '%s\n' "$out" >&2; fail 'K5: the verdict did not say the ref introduces nothing' ;; esac
ok 'K5  a new ref naming a commit the destination already has introduces nothing and PASSES'

# --------------------------------------------------- K6 fails CLOSED, exit 2
if out=$(lane "$L_MERGED" "$L_OLD" "$TMP/missing.git"); then
  fail 'K6: an update to an unreadable destination reported success'
else
  rc=$?
fi
[ "$rc" -eq 2 ] || fail "K6: expected exit 2 for an unreadable destination, got $rc"
case "$out" in *'could NOT READ the push destination'*) ;; *) printf '%s\n' "$out" >&2; fail 'K6: the refusal did not say the destination was unreadable' ;; esac
mv "$R/scripts/lib/push_destination.sh" "$TMP/away.sh"
if out=$(lane "$L_MERGED" "$L_OLD"); then
  mv "$TMP/away.sh" "$R/scripts/lib/push_destination.sh"
  fail 'K6: with the destination reader missing the update reported success'
else
  rc=$?
fi
mv "$TMP/away.sh" "$R/scripts/lib/push_destination.sh"
[ "$rc" -eq 2 ] || fail "K6: expected exit 2 with the destination reader missing, got $rc"
EMPTY="$TMP/empty.git"
git init -q --bare -b main "$EMPTY"
git -C "$R" push -q "$EMPTY" "$L_OLD:refs/heads/other"
if out=$( ( cd "$R" && TRUST_PUSHED_REFS="refs/heads/fresh $L_SKEW refs/heads/fresh $ZERO" \
  python3 scripts/check_cfg_test_caller_skew.py --push-context --remote "$EMPTY" 2>&1 ) ); then
  fail 'K6: a new ref to a destination with no main reported success'
else
  rc=$?
fi
[ "$rc" -eq 2 ] || fail "K6: expected exit 2 for a new ref with no destination main, got $rc"
ok 'K6  an unreadable destination, a missing destination reader, and a new ref with no destination main all fail closed (exit 2)'

# ------------------------------------------------ the WIRING, end to end
# A real `git push` through scripts/hooks-pin/pre-push — the hook that is
# installed — with every OTHER lane it declares stubbed green, so the only
# thing that can decide the push is the lane under test.
[ -f "$HOOK" ] || fail "the installed pre-push hook is missing: $HOOK"
E="$TMP/e2e"
EREMOTE="$TMP/e2e-remote.git"
git init -q --bare -b main "$EREMOTE"
newrepo "$E"
mkdir -p "$E/scripts/hooks-pin"
cp "$HOOK" "$E/scripts/hooks-pin/pre-push"
: >"$E/scripts/hooks-pin/pin-waivers.txt"
: >"$E/scripts/hooks-pin/ir-cohort-waivers.txt"
HOOK_LANES="$(grep -Eo '^[A-Z_]*CHECKER="scripts/[^"]+"' "$HOOK" | sed -E 's/^[A-Z_]*CHECKER="([^"]+)"/\1/' || true)"
case "$HOOK_LANES" in
  *'scripts/check_cfg_test_caller_skew.py'*) ;;
  *) fail 'W0-fixture: hooks-pin/pre-push no longer declares the lane under test as a checker path' ;;
esac
while IFS= read -r lane_path; do
  [ -n "$lane_path" ] || continue
  [ "$lane_path" = scripts/check_cfg_test_caller_skew.py ] && continue
  case "$lane_path" in
    *.py) printf '#!/usr/bin/env python3\nprint("OK (fixture stub)")\n' >"$E/$lane_path" ;;
    *) printf '#!/usr/bin/env bash\necho "OK (fixture stub)"\nexit 0\n' >"$E/$lane_path" ;;
  esac
done <<<"$HOOK_LANES"
chmod +x "$E"/scripts/*.sh "$E"/scripts/*.py "$E/scripts/hooks-pin/pre-push"
for f in main_owned.rs s.rs t.rs u.rs uses_t.rs lane.rs; do
  git -C "$R" show "$BASE:crates/demo/src/$f" >"$E/crates/demo/src/$f"
done
git -C "$E" add -A
git -C "$E" commit -qm fixture
# The remote is SEEDED with main by a fetch, which runs no pre-push: a new
# branch is judged against the destination's own main, and a destination with
# no main fails closed (K6), exactly as the old reading failed on a missing
# origin/main. Every push below is a real one, through the hook.
git --git-dir="$EREMOTE" fetch -q "$E" refs/heads/main:refs/heads/main
git -C "$E" config core.hooksPath scripts/hooks-pin
git -C "$E" remote add origin "$EREMOTE"
put "$E" crates/demo/src/readme.rs 'fn readme() {}' 'main: a clean change'
if ! w0_out="$(git -C "$E" push origin main 2>&1)"; then
  printf '%s\n' "$w0_out" >&2
  fail 'W0: the green control push was refused (hook output above), so no later verdict means anything'
fi
case "$w0_out" in *'SUBJECT: what this push introduces to'*) ;; *) printf '%s\n' "$w0_out" >&2; fail 'W0: the hook did not hand the skew lane its destination' ;; esac
git -C "$E" checkout -q -b topic
put "$E" crates/demo/src/lane_notes.rs 'fn notes() {}' 'topic: a first commit'
if ! w0_out="$(git -C "$E" push origin topic 2>&1)"; then
  printf '%s\n' "$w0_out" >&2
  fail 'W0: the clean topic branch was refused'
fi
ok 'W0  a clean update and a clean new branch pass the hook, which hands the lane its destination (the accept control for the wiring)'

# main gains a skew that reaches the remote WITHOUT this hook — written in by a
# fetch, which runs no pre-push.
git -C "$E" checkout -q main
fn_file main_fn 'a: u32, b: u32' '1, 2' '1' >"$E/crates/demo/src/main_owned.rs"
git -C "$E" commit -qam 'main: widen main_fn (its cfg(test) caller left behind)'
E_MAIN=$(git -C "$E" rev-parse HEAD)
git --git-dir="$EREMOTE" fetch -q "$E" refs/heads/main:refs/heads/main
git -C "$E" checkout -q topic
git -C "$E" merge -q --no-edit main
if ! out=$(git -C "$E" push origin topic 2>&1); then
  printf '%s\n' "$out" >&2
  fail 'W1: an update merging a skew already on remote main was refused by the installed hook'
fi
[ "$(git --git-dir="$EREMOTE" rev-parse topic)" = "$(git -C "$E" rev-parse HEAD)" ] \
  || fail 'W1: the accepted update did not reach the remote'
ok 'W1  a real `git push` updating a branch that merged main'"'"'s published skew PASSES'

E_TOPIC=$(git -C "$E" rev-parse HEAD)
fn_file lane_fn 'a: u32, b: u32' '1, 2' '1' >"$E/crates/demo/src/lane.rs"
git -C "$E" commit -qam 'topic: widen lane_fn, cfg(test) caller left behind'
if out=$(git -C "$E" push origin topic 2>&1); then
  printf '%s\n' "$out" >&2
  fail 'W2: an update introducing a NEW skewed call site was ACCEPTED by the installed hook'
fi
case "$out" in *"$LANE_SITE"*) ;; *) printf '%s\n' "$out" >&2; fail 'W2: the hook refused for some other reason than the introduced skew' ;; esac
case "$out" in *'skew=1'*) ;; *) fail 'W2: the hook did not attribute the refusal to the skew lane' ;; esac
case "$out" in *"$MAIN_SITE"*|*"$MAIN_PAIR"*) fail 'W2: the hook blamed main'"'"'s already-published site' ;; *) ;; esac
[ "$(git --git-dir="$EREMOTE" rev-parse topic)" = "$E_TOPIC" ] \
  || fail 'W2: the introduced skew reached the remote anyway'
ok 'W2  a real `git push` of an update introducing a skewed site is REFUSED, the remote does not move'

# Both hook sets hand the lane its destination: hooks-pin passes --remote, and
# the full hook exports what the manifest's --push-context row reads.
grep -q 'skew_args+=(--remote "\$2")' "$HOOK" \
  || fail 'W3: scripts/hooks-pin/pre-push no longer hands the skew lane its destination'
grep -Eq '^[[:space:]]*export[[:space:]]+TRUST_PUSH_REMOTE=' "$REPO_ROOT/scripts/hooks/pre-push" \
  || fail 'W3: scripts/hooks/pre-push no longer exports TRUST_PUSH_REMOTE; the lane would judge every file in range'
PUSH_LANES="$(cd "$REPO_ROOT" && bash tests/run_trust_comprehensive_harness.sh --list push)" \
  || fail 'W3: the harness cannot list the push profile the full hook derives its lanes from'
case "$PUSH_LANES" in
  *"check_cfg_test_caller_skew.py --push-context"*) ;;
  *) fail 'W3: no `push` manifest row runs the lane with --push-context' ;;
esac
ok 'W3  hooks-pin passes the destination; the full hook exports it to the --push-context row'

printf 'check_cfg_test_caller_skew_test: %d checks passed\n' "$PASSED"
