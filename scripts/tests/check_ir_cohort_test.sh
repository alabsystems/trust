#!/usr/bin/env bash
# check_ir_cohort_test.sh --- falsification tests for the M0 cohort gate.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# The gate went green on its first run against the real superproject. That is
# exactly the situation in which a gate must be shown to REFUTE: a checker that
# only ever agrees with you is indistinguishable from `exit 0`. Each case below
# builds a synthetic cohort in a temp directory, and asserts the gate's verdict.
#
# The fixture is a real git repository with a real nested trust-ir object store,
# because the gate's evidence is git plumbing --- `git show <rev>:<path>`,
# `merge-base --is-ancestor`, `ls-tree`. Faking those would test a mock.
set -uo pipefail

GATE="$(cd "$(dirname "$0")/.." && pwd)/check_ir_cohort.py"
[ -f "$GATE" ] || { echo "gate not found at $GATE" >&2; exit 1; }
# Inventory integrity is part of the cohort contract, including nested inactive
# worktrees and callers with an inherited alternate Git index.
python3 "$(dirname "$GATE")/tests/check_ir_cohort_inventory_test.py" || exit 1

pass=0
fail=0

note() { printf '  %s\n' "$*"; }

# Build a fixture cohort. Args: <dir>. Populates a repo whose gitlink-equivalent
# is HEAD of the nested store; callers then add declarations and re-run.
make_fixture() {
  local dir="$1"
  mkdir -p "$dir/first-party/trust-ir/crates/trust-ir/src"
  git -C "$dir" init -q -b main
  git -C "$dir" config user.email t@example.invalid
  git -C "$dir" config user.name  T

  local store="$dir/first-party/trust-ir"
  git -C "$store" init -q -b main
  git -C "$store" config user.email t@example.invalid
  git -C "$store" config user.name  T

  # Revision A: the ratified semantics.
  for f in ty inst binary node value constant; do
    printf 'pub const MARKER: u32 = 1; // %s\n' "$f" > "$store/crates/trust-ir/src/$f.rs"
  done
  git -C "$store" add -A && git -C "$store" commit -qm "A"
  REV_A="$(git -C "$store" rev-parse HEAD)"

  # Revision B: a DIFFERENT semantics (the surface changed).
  printf 'pub const MARKER: u32 = 2; // ty CHANGED\n' > "$store/crates/trust-ir/src/ty.rs"
  git -C "$store" add -A && git -C "$store" commit -qm "B"
  REV_B="$(git -C "$store" rev-parse HEAD)"

  # Revision C: same content as B in the SURFACE, different commit. This is the
  # case that must NOT be flagged: different revision, identical meaning.
  printf 'fn unrelated() {}\n' > "$store/crates/trust-ir/src/README_NOT_SURFACE.rs"
  git -C "$store" add -A && git -C "$store" commit -qm "C"
  REV_C="$(git -C "$store" rev-parse HEAD)"

  # The store's REMOTE: a bare repository publishing main at REV_C and nothing
  # else (the fork below is never pushed). The gate reads THIS, with ls-remote;
  # the store's own refs/remotes/origin/main is not evidence (2026-10-15).
  REMOTE="$dir.trust-ir-remote.git"
  git init -q --bare -b main "$REMOTE"
  git -C "$store" remote add origin "$REMOTE"
  git -C "$store" push -q origin main

  # A fork: reachable from no remote branch.
  git -C "$store" checkout -q -b fork "$REV_A"
  printf 'pub const MARKER: u32 = 99; // FORKED\n' > "$store/crates/trust-ir/src/ty.rs"
  git -C "$store" add -A && git -C "$store" commit -qm "FORK"
  REV_FORK="$(git -C "$store" rev-parse HEAD)"
  git -C "$store" checkout -q main

  # The superproject records the store as a gitlink at REV_A (the ratified pin).
  git -C "$dir" update-index --add --cacheinfo 160000,"$REV_A",first-party/trust-ir
  printf 'x\n' > "$dir/placeholder"
  git -C "$dir" add placeholder
  git -C "$dir" commit -qm "super"
}

decl() {  # <dir> <path> <rev>
  local dir="$1" path="$2" rev="$3"
  mkdir -p "$(dirname "$dir/$path")"
  cat > "$dir/$path" <<EOF
[dependencies]
trust-ir = { git = "https://github.com/alabsystems/trust-ir.git", rev = "$rev" }
EOF
  git -C "$dir" add "$path"
  git -C "$dir" commit -qm "decl $path" >/dev/null
}

check() {  # <name> <dir> <expected exit: 0|1>
  local name="$1" dir="$2" want="$3"
  local out; out="$(python3 "$GATE" --root "$dir" 2>&1)"; local got=$?
  if [ "$got" = "$want" ]; then
    printf 'ok    %s\n' "$name"; pass=$((pass+1))
  else
    printf 'FAIL  %s (wanted exit %s, got %s)\n' "$name" "$want" "$got"
    printf '%s\n' "$out" | sed 's/^/      | /'
    fail=$((fail+1))
  fi
}

# Every ref in a store, plus its FETCH_HEAD: what the gate must leave as it found.
refstate() {
  git -C "$1" for-each-ref --format='%(objectname) %(refname)'
  local fh; fh="$(git -C "$1" rev-parse --path-format=absolute --git-path FETCH_HEAD)"
  if [ -f "$fh" ]; then cat "$fh"; else echo '<no FETCH_HEAD>'; fi
}

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

# ---------------------------------------------------------------------------
# 1. A coherent cohort passes.
D="$TMP/coherent"; make_fixture "$D"
decl "$D" "a/Cargo.toml" "$REV_A"
decl "$D" "b/Cargo.toml" "$REV_A"
check "coherent cohort passes" "$D" 0

# 2. THE KEY NON-FLAG: two different revisions with the same semantic surface
#    must be treated as coherent. Gating on revision equality would fail here,
#    and that false positive is what teaches a lane to waive.
D="$TMP/samesemantics"; make_fixture "$D"
decl "$D" "a/Cargo.toml" "$REV_B"
decl "$D" "b/Cargo.toml" "$REV_C"
# Ratified is REV_A's schema, so B/C are one divergent group, not two. Confirm
# the gate reports ONE divergence rather than two.
out="$(python3 "$GATE" --root "$D" 2>&1)"
if [ "$(printf '%s\n' "$out" | grep -c 'diverges from the cohort schema')" = "1" ]; then
  printf 'ok    different revisions, identical surface = ONE group\n'; pass=$((pass+1))
else
  printf 'FAIL  different revisions with identical surface were not merged\n'
  printf '%s\n' "$out" | sed 's/^/      | /'; fail=$((fail+1))
fi

# 3. Divergence with no waiver fails closed.
D="$TMP/diverge"; make_fixture "$D"
decl "$D" "a/Cargo.toml" "$REV_A"
decl "$D" "b/Cargo.toml" "$REV_B"
check "unwaived divergence fails" "$D" 1

# 4. An OFF-MAIN revision fails, and is NOT rescued by a waiver. This is the
#    fork case the header calls never-waivable; if a waiver could cover it the
#    whole distinction would be decorative.
D="$TMP/fork"; make_fixture "$D"
decl "$D" "a/Cargo.toml" "$REV_A"
decl "$D" "b/Cargo.toml" "$REV_FORK"
mkdir -p "$D/scripts/hooks-pin"
# Waive every schema we can name, including the fork's.
FORK_DIGEST="$(python3 "$GATE" --root "$D" --report 2>&1 | grep -o 'schema [0-9a-f]\{12\}' | awk '{print $2}' | sort -u | tr '\n' ' ')"
for d in $FORK_DIGEST; do
  echo "trust-ir | $d | 2099-01-01 | test | blanket attempt" >> "$D/scripts/hooks-pin/ir-cohort-waivers.txt"
done
check "off-main revision is not waivable" "$D" 1

# 5. An unresolvable revision fails.
D="$TMP/missing"; make_fixture "$D"
decl "$D" "a/Cargo.toml" "$REV_A"
decl "$D" "b/Cargo.toml" "0123456789012345678901234567890123456789"
check "unresolvable revision fails" "$D" 1

# 6. An EXPIRED waiver stops applying.
D="$TMP/expired"; make_fixture "$D"
decl "$D" "a/Cargo.toml" "$REV_A"
decl "$D" "b/Cargo.toml" "$REV_B"
B_DIGEST="$(python3 "$GATE" --root "$D" 2>&1 | grep -o 'schema [0-9a-f]\{12\} diverges' | awk '{print $2}' | head -1)"
mkdir -p "$D/scripts/hooks-pin"
echo "trust-ir | $B_DIGEST | 2020-01-01 | test | long past" > "$D/scripts/hooks-pin/ir-cohort-waivers.txt"
check "expired waiver fails" "$D" 1

# 7. A live waiver permits exactly its own divergence.
echo "trust-ir | $B_DIGEST | 2099-01-01 | test | current" > "$D/scripts/hooks-pin/ir-cohort-waivers.txt"
check "live waiver permits its divergence" "$D" 0

# 8. A waiver whose divergence is GONE fails, so rows cannot rot in place.
D="$TMP/stale"; make_fixture "$D"
decl "$D" "a/Cargo.toml" "$REV_A"
mkdir -p "$D/scripts/hooks-pin"
echo "trust-ir | deadbeefcafe | 2099-01-01 | test | covers nothing" > "$D/scripts/hooks-pin/ir-cohort-waivers.txt"
check "stale waiver fails until deleted" "$D" 1

# 9. A malformed waiver row fails rather than being skipped silently.
D="$TMP/malformed"; make_fixture "$D"
decl "$D" "a/Cargo.toml" "$REV_A"
mkdir -p "$D/scripts/hooks-pin"
echo "trust-ir | missing-fields" > "$D/scripts/hooks-pin/ir-cohort-waivers.txt"
check "malformed waiver row fails" "$D" 1

# 10. An empty inventory must not be a vacuous green.
D="$TMP/empty"; make_fixture "$D"
check "empty inventory is not vacuous green" "$D" 1


# 11. An UNGATED dependency (one in UNGATED_BY_DECISION) still gets the
#     never-waivable checks. The first cut `continue`d before them, which
#     quietly exempted five first-party repos from resolvability and
#     containment as well as from the digest -- a far bigger exemption than
#     the one that was actually decided.
D="$TMP/ungated"; make_fixture "$D"
decl "$D" "a/Cargo.toml" "$REV_A"
mkdir -p "$D/ty"
cat > "$D/ty/Cargo.toml" <<EOF
[dependencies]
ty = { git = "https://github.com/alabsystems/ty.git", rev = "0123456789012345678901234567890123456789" }
EOF
git -C "$D" add ty/Cargo.toml && git -C "$D" commit -qm "ungated dep" >/dev/null
check "ungated dep with an unresolvable rev still fails" "$D" 1


# 12. An archived manifest snapshot that the CONSTELLATION gate has verified is no
#     build input (docs/audits/first-party-constellation-exclusions-v1.json) is no
#     dependency edge here either --- but only when it is ON that list, and only
#     when the list carries the schema this gate understands. Measured 2026-09-16:
#     a byte-preserved OLD manifest under a non-workspace spike directory read as
#     an off-main FORK, the never-waivable case, from a file nothing builds.
#
#     The fixture path is a `spikes/` one ON PURPOSE, and the choice is load-bearing
#     rather than arbitrary. This list and the unconditional `reports/` skip below
#     are DIFFERENT mechanisms over DIFFERENT populations: of the 43 live exclusion
#     rows, 40 are trust-wp `spikes/*` directories that no `reports` segment reaches.
#     An earlier cut of these four checks used a `reports/.../originals` fixture, and
#     when the `reports/` skip landed it caught the fixture FIRST --- so three of them
#     went green against a gate that had stopped consulting the exclusion list at all.
#     A fixture outside both populations would test nothing; this one tests exactly
#     the list.
D="$TMP/excluded"; make_fixture "$D"
decl "$D" "a/Cargo.toml" "$REV_A"
decl "$D" "first-party/trust-wp/spikes/clean-cert-spike/Cargo.toml" "$REV_FORK"
check "an off-main archive OUTSIDE the exclusion list still fails" "$D" 1
mkdir -p "$D/docs/audits"
cat > "$D/docs/audits/first-party-constellation-exclusions-v1.json" <<'EOF'
{"schema": "trust.constellation.exclusions.v1", "exclusions": [
  {"repository": "trust-wp", "path": "spikes/clean-cert-spike",
   "reason": "test: non-workspace historical spike, declares its own [workspace], no member, never built"}]}
EOF
check "the same archive ON the exclusion list is skipped" "$D" 0
cat > "$D/docs/audits/first-party-constellation-exclusions-v1.json" <<'EOF'
{"schema": "trust.constellation.exclusions.v2", "exclusions": [
  {"repository": "trust-wp", "path": "spikes/clean-cert-spike", "reason": "wrong schema"}]}
EOF
check "an exclusions file of another schema excludes nothing (fail-closed)" "$D" 1
cat > "$D/docs/audits/first-party-constellation-exclusions-v1.json" <<'EOF'
{"schema": "trust.constellation.exclusions.v1", "exclusions": [
  {"repository": "trust-wp", "path": "spikes/OTHER-spike", "reason": "a different archive"}]}
EOF
check "an exclusion for a different path does not cover it" "$D" 1

# 13. The `reports/` skip is UNCONDITIONAL --- it consults no list. It landed
#     untested; this is its pin. A manifest under a `reports/` path is an artifact
#     of a past measurement, so an off-main revision it declares is not a fork of
#     anything live, and the gate must not report one. Stated as the pair it is:
#     the same declaration OUTSIDE `reports/` still fails, so what is being measured
#     here is the path segment and not the revision.
D="$TMP/reports-artifact"; make_fixture "$D"
decl "$D" "a/Cargo.toml" "$REV_A"
decl "$D" "first-party/ty/reports/perf/snap/originals/Cargo.toml" "$REV_FORK"
check "an off-main manifest under reports/ is skipped with no exclusion list" "$D" 0
D="$TMP/reports-control"; make_fixture "$D"
decl "$D" "a/Cargo.toml" "$REV_A"
decl "$D" "first-party/ty/perf/snap/originals/Cargo.toml" "$REV_FORK"
check "the same manifest OUTSIDE reports/ still fails (control)" "$D" 1

# 14. NO BASIS IS NOT A FORK. A remote that publishes no main gives nothing to
#     be contained in. The gate once printed OFF-MAIN, "the fork case", its
#     harshest unwaivable verdict, about revisions it had compared against
#     nothing. This is case 1's passing cohort with only the REMOTE's main
#     deleted. It must STILL fail (the gate may not get weaker), but name the
#     real reason, on both the consumer row and the ratified-anchor row, and
#     never call it a fork.
D="$TMP/no-basis"; make_fixture "$D"
decl "$D" "a/Cargo.toml" "$REV_A"
decl "$D" "b/Cargo.toml" "$REV_A"
git --git-dir "$REMOTE" update-ref -d refs/heads/main
out="$(python3 "$GATE" --root "$D" 2>&1)"; got=$?
if [ "$got" = 1 ] \
  && printf '%s\n' "$out" | grep -q 'trust-ir@[0-9a-f]\{8\}: CONTAINMENT UNRESOLVED --- the remote publishes no refs/heads/main' \
  && printf '%s\n' "$out" | grep -q 'RATIFIED ANCHOR CONTAINMENT UNRESOLVED' \
  && ! printf '%s\n' "$out" | grep -q 'fork case' \
  && ! printf '%s\n' "$out" | grep -q 'OFF-MAIN'; then
  printf 'ok    a remote with no main is CONTAINMENT UNRESOLVED, still exit 1, never "fork case"\n'; pass=$((pass+1))
else
  printf 'FAIL  no remote main: wanted exit 1 + CONTAINMENT UNRESOLVED and no fork verdict (got exit %s)\n' "$got"
  printf '%s\n' "$out" | sed 's/^/      | /'; fail=$((fail+1))
fi

# 15. A STALE LOCAL REF IS NOT EVIDENCE (2026-10-15). The case that bit real
#     machines (2026-09-27, six false "fork case" rows; RED pushes 2026-10-14/15)
#     was a PRESENT but stale refs/remotes/origin/main. Here the remote's main
#     has moved to D, the store's origin/main still names REV_A, and the cohort
#     and the gitlink are on D. The gate reads the remote: COHERENT. It must
#     move no ref doing so --- origin/main stays stale, and no FETCH_HEAD.
D="$TMP/stale-ref"; make_fixture "$D"
store="$D/first-party/trust-ir"
printf 'not surface\n' > "$store/crates/trust-ir/src/STALE_NOT_SURFACE.rs"
git -C "$store" add -A && git -C "$store" commit -qm "D" && git -C "$store" push -q origin main
REV_D="$(git -C "$store" rev-parse HEAD)"
git -C "$store" update-ref refs/remotes/origin/main "$REV_A"
git -C "$D" update-index --cacheinfo 160000,"$REV_D",first-party/trust-ir
git -C "$D" commit -qm "pin D" >/dev/null
decl "$D" "a/Cargo.toml" "$REV_D"
decl "$D" "b/Cargo.toml" "$REV_D"
before="$(refstate "$store")"
out="$(python3 "$GATE" --root "$D" 2>&1)"; got=$?
if [ "$got" = 0 ] && printf '%s\n' "$out" | grep -q '^IR COHORT COHERENT' \
  && [ "$(refstate "$store")" = "$before" ] \
  && [ "$(git -C "$store" rev-parse refs/remotes/origin/main)" = "$REV_A" ]; then
  printf 'ok    stale local origin/main, the remote main has the pin: COHERENT, no ref moved\n'; pass=$((pass+1))
else
  printf 'FAIL  stale local origin/main: wanted exit 0, COHERENT and every ref unchanged (got exit %s)\n' "$got"
  printf '%s\n' "$out" | sed 's/^/      | /'; fail=$((fail+1))
fi

# 16. THE STORE HAS NEVER SEEN THE REVISION: another clone pushed E and this
#     store never fetched. It used to be UNRESOLVABLE. The gate fetches E's
#     objects by sha, writing no ref and no FETCH_HEAD, and judges it.
D="$TMP/never-seen"; make_fixture "$D"
store="$D/first-party/trust-ir"
git clone -q "$REMOTE" "$D.other"
git -C "$D.other" config user.email t@example.invalid
git -C "$D.other" config user.name T
printf 'elsewhere\n' > "$D.other/crates/trust-ir/src/ELSEWHERE_NOT_SURFACE.rs"
git -C "$D.other" add -A && git -C "$D.other" commit -qm "E" && git -C "$D.other" push -q origin main
REV_E="$(git -C "$D.other" rev-parse HEAD)"
git -C "$D" update-index --cacheinfo 160000,"$REV_E",first-party/trust-ir
git -C "$D" commit -qm "pin E" >/dev/null
decl "$D" "a/Cargo.toml" "$REV_E"
before="$(refstate "$store")"
out="$(python3 "$GATE" --root "$D" 2>&1)"; got=$?
if [ "$got" = 0 ] && printf '%s\n' "$out" | grep -q '^IR COHORT COHERENT' \
  && [ "$(refstate "$store")" = "$before" ] \
  && git -C "$store" cat-file -e "$REV_E^{commit}"; then
  printf 'ok    a revision this store never fetched is fetched by sha, judged COHERENT, no ref written\n'; pass=$((pass+1))
else
  printf 'FAIL  never-fetched revision: wanted exit 0, COHERENT, the object present, refs unchanged (got exit %s)\n' "$got"
  printf '%s\n' "$out" | sed 's/^/      | /'; fail=$((fail+1))
fi

# 17. THE NETWORK IS DOWN: the remote cannot be read. COULD NOT RUN, exit 2 ---
#     never COHERENT, never a fork, never UNRESOLVABLE. Case 1's passing cohort
#     with the remote moved away.
D="$TMP/offline"; make_fixture "$D"
decl "$D" "a/Cargo.toml" "$REV_A"
mv "$REMOTE" "$REMOTE.gone"
out="$(python3 "$GATE" --root "$D" 2>&1)"; got=$?
if [ "$got" = 2 ] && printf '%s\n' "$out" | grep -q '^IR COHORT COULD NOT RUN' \
  && ! printf '%s\n' "$out" | grep -q 'IR COHORT COHERENT' \
  && ! printf '%s\n' "$out" | grep -q 'OFF-MAIN\|fork case\|UNRESOLVABLE'; then
  printf 'ok    an unreadable remote is COULD NOT RUN (exit 2), never a pass or a fork\n'; pass=$((pass+1))
else
  printf 'FAIL  unreadable remote: wanted exit 2 + COULD NOT RUN and no verdict (got exit %s)\n' "$got"
  printf '%s\n' "$out" | sed 's/^/      | /'; fail=$((fail+1))
fi
# ... and a definite finding beside it is still a finding (exit 1, not 2).
decl "$D" "b/Cargo.toml" "0123456789012345678901234567890123456789"
mkdir -p "$D/ty"
cat > "$D/ty/Cargo.toml" <<EOF
[dependencies]
ty = { git = "https://github.com/alabsystems/ty.git", rev = "0123456789012345678901234567890123456789" }
EOF
git -C "$D" add ty/Cargo.toml && git -C "$D" commit -qm "ungated dep, no store" >/dev/null
check "a finding beside an unreadable remote still exits 1" "$D" 1

# 17b. AN UNREAD REMOTE DOES NOT MAKE A LIVE WAIVER STALE (2026-11-13: agh rate
#      limited every remote read, and the gate told the reader to delete the
#      row that covered a real divergence). The digest comes from the local
#      store, so case 7's waived divergence is still waived, the run says
#      COULD NOT RUN (exit 2), and nothing calls the row stale.
D="$TMP/offline-waiver"; make_fixture "$D"
decl "$D" "a/Cargo.toml" "$REV_A"
decl "$D" "b/Cargo.toml" "$REV_B"
B_DIGEST="$(python3 "$GATE" --root "$D" 2>&1 | grep -o 'schema [0-9a-f]\{12\} diverges' | awk '{print $2}' | head -1)"
mkdir -p "$D/scripts/hooks-pin"
echo "trust-ir | $B_DIGEST | 2099-01-01 | test | current" > "$D/scripts/hooks-pin/ir-cohort-waivers.txt"
mv "$REMOTE" "$REMOTE.gone"
out="$(python3 "$GATE" --root "$D" 2>&1)"; got=$?
if [ -n "$B_DIGEST" ] && [ "$got" = 2 ] && printf '%s\n' "$out" | grep -q '^IR COHORT COULD NOT RUN' \
  && printf '%s\n' "$out" | grep -q "waived  $B_DIGEST" \
  && ! printf '%s\n' "$out" | grep -q 'STALE waiver'; then
  printf 'ok    an unread remote leaves a live waiver waived, not stale (exit 2)\n'; pass=$((pass+1))
else
  printf 'FAIL  unread remote + live waiver: wanted exit 2, the divergence waived, no STALE row (got exit %s)\n' "$got"
  printf '%s\n' "$out" | sed 's/^/      | /'; fail=$((fail+1))
fi
# ... and a revision the store does not hold has no digest, so a waiver for
# that repository cannot be judged stale either; with the remote back, the
# same row covering nothing is stale again (case 8).
D="$TMP/offline-undigested"; make_fixture "$D"
decl "$D" "a/Cargo.toml" "$REV_A"
decl "$D" "b/Cargo.toml" "0123456789012345678901234567890123456789"
mkdir -p "$D/scripts/hooks-pin"
echo "trust-ir | deadbeefcafe | 2099-01-01 | test | covers nothing yet" > "$D/scripts/hooks-pin/ir-cohort-waivers.txt"
git -C "$D" add scripts && git -C "$D" commit -qm "waiver" >/dev/null
mv "$REMOTE" "$REMOTE.gone"
out="$(python3 "$GATE" --root "$D" 2>&1)"; got=$?
if [ "$got" = 2 ] && printf '%s\n' "$out" | grep -q '^IR COHORT COULD NOT RUN' \
  && ! printf '%s\n' "$out" | grep -q 'STALE waiver'; then
  printf 'ok    an unread, undigested revision leaves its repository'"'"'s waiver unjudged (exit 2)\n'; pass=$((pass+1))
else
  printf 'FAIL  unread undigested revision: wanted exit 2 and no STALE row (got exit %s)\n' "$got"
  printf '%s\n' "$out" | sed 's/^/      | /'; fail=$((fail+1))
fi
mv "$REMOTE.gone" "$REMOTE"
decl "$D" "b/Cargo.toml" "$REV_A"
out="$(python3 "$GATE" --root "$D" 2>&1)"; got=$?
if [ "$got" = 1 ] && printf '%s\n' "$out" | grep -q 'STALE waiver'; then
  printf 'ok    with the remote readable the row covering nothing is stale again\n'; pass=$((pass+1))
else
  printf 'FAIL  readable remote: wanted exit 1 and the STALE row (got exit %s)\n' "$got"
  printf '%s\n' "$out" | sed 's/^/      | /'; fail=$((fail+1))
fi

# 18. A SHALLOW STORE MUST NOT READ AS A FORK (2026-10-26). The by-sha fetch
#     brings the pin and the remote tip but not the history between them,
#     so in a depth-1 store `merge-base --is-ancestor` answers 1 for a pin
#     that IS on main: twelve false OFF-MAIN rows on the real tree, every
#     pin contained. Case 1's passing cohort with the store replaced by a
#     depth-1 clone of the same remote must stay COHERENT (the gate earns
#     one --unshallow fetch, still writing no ref).
D="$TMP/shallow-store"; make_fixture "$D"
store="$D/first-party/trust-ir"
rm -rf "$store"
git clone -q --depth 1 "file://$REMOTE" "$store"
before="$(refstate "$store")"
decl "$D" "a/Cargo.toml" "$REV_A"
decl "$D" "b/Cargo.toml" "$REV_A"
check "a depth-1 shallow store still judges a contained pin COHERENT" "$D" 0
if [ "$(refstate "$store")" = "$before" ]; then
  printf 'ok    the unshallow fetch moved no ref in the shallow store\n'; pass=$((pass+1))
else
  printf 'FAIL  the unshallow fetch moved a ref in the shallow store\n'; fail=$((fail+1))
fi

# 19. A shallow SERVING repository may successfully unshallow only part of
#     the client's history. A missing ancestry path is still unread, not a
#     finding; ancestry that can already be walked remains positive evidence.
D="$TMP/shallow-server"; make_fixture "$D"
store="$D/first-party/trust-ir"
git --git-dir="$REMOTE" branch old "$REV_A"
git -C "$store" push -q origin "$REV_FORK:refs/heads/side"
shallow_remote="$TMP/shallow-serving.git"
git clone -q --bare --depth 2 --no-single-branch "file://$REMOTE" "$shallow_remote"
rm -rf "${store:?}"
git clone -q --depth 1 --no-single-branch "file://$shallow_remote" "$store"
before="$(refstate "$store")"
decl "$D" "a/Cargo.toml" "$REV_A"
decl "$D" "b/Cargo.toml" "$REV_A"
out="$(python3 "$GATE" --root "$D" 2>&1)"; got=$?
if [ "$got" = 2 ] && printf '%s\n' "$out" | grep -q 'COULD NOT RUN' \
  && ! printf '%s\n' "$out" | grep -q 'OFF-MAIN\|fork case\|UNRESOLVABLE'; then
  printf 'ok    incomplete serving history is unread, not a false fork\n'; pass=$((pass+1))
else
  printf 'FAIL  shallow server: wanted exit 2 and no false fork (got exit %s)\n' "$got"
  printf '%s\n' "$out" | sed 's/^/      | /'; fail=$((fail+1))
fi
if [ "$(refstate "$store")" = "$before" ]; then
  printf 'ok    the shallow-server fetch moved no ref\n'; pass=$((pass+1))
else
  printf 'FAIL  the shallow-server fetch moved a ref\n'; fail=$((fail+1))
fi
if python3 - "$GATE" "$store" "$REMOTE" "$REV_A" "$REV_B" "$REV_FORK" <<'PY'
from pathlib import Path
import subprocess
import sys
from unittest.mock import patch

sys.path.insert(0, str(Path(sys.argv[1]).parent))
from lib import remote_tips as rt

store, full_remote = Path(sys.argv[2]), Path(sys.argv[3])
ancestor, positive, fork = sys.argv[4:]
tips = rt.RemoteTips()
assert tips._is_shallow(store / ".git") is True
assert tips.judge(store, positive, scope="main").state == rt.CONTAINED
assert tips.judge(store, ancestor, scope="main").state == rt.UNJUDGED
assert tips._is_shallow(store / ".git") is True

subprocess.run(["git", "-C", str(store), "remote", "set-url", "origin",
                full_remote.as_uri()], check=True)
tips = rt.RemoteTips()
assert tips.judge(store, ancestor, scope="main").state == rt.CONTAINED
assert tips.judge(store, fork, scope="main").state == rt.NOT_CONTAINED
# Positive ancestry can be established before progressive deepening exhausts
# unrelated history. A negative finding still requires a complete store.
assert tips._is_shallow(store / ".git") is False

actual_run = rt._run
for code, output in ((128, ""), (0, "malformed\n")):
    def unread_state(args, **kwargs):
        if args[-1] == "--is-shallow-repository":
            return subprocess.CompletedProcess(args, code, output, "state unavailable")
        return actual_run(args, **kwargs)

    with patch.object(rt, "_run", side_effect=unread_state):
        assert rt.RemoteTips().judge(store, fork, scope="main").state == rt.UNJUDGED
        assert rt.RemoteTips().judge(store, positive, scope="main").state == rt.CONTAINED
PY
then
  printf 'ok    shallow, complete and unreadable histories retain their distinct verdicts\n'; pass=$((pass+1))
else
  printf 'FAIL  shallow-server controls or unreadable-history classification\n'; fail=$((fail+1))
fi

# 20. Remote containment concerns immutable commits, not a local replacement
#     or graft view. Such a view can forge either ancestry or object presence.
D="$TMP/replacement-views"; make_fixture "$D"
if python3 - "$GATE" "$D/first-party/trust-ir" "$REV_B" "$REV_C" "$REV_FORK" <<'PY'
from pathlib import Path
import os
import subprocess
import sys
from unittest.mock import patch

sys.path.insert(0, str(Path(sys.argv[1]).parent))
from lib import remote_tips as rt

store = Path(sys.argv[2])
positive, tip, fork = sys.argv[3:]

def local_git(*args, check=True):
    env = dict(os.environ)
    for key in ("GIT_NO_REPLACE_OBJECTS", "GIT_REPLACE_REF_BASE", "GIT_GRAFT_FILE"):
        env.pop(key, None)
    return subprocess.run(["git", "-C", str(store), *args], env=env,
                          text=True, capture_output=True, check=check)

def expect_raw(label):
    for scope in ("main", "durable"):
        tips = rt.RemoteTips()
        actual = tips.judge(store, positive, scope=scope)
        assert actual.state == rt.CONTAINED, (label, scope, actual)
        actual = tips.judge(store, fork, scope=scope)
        assert actual.state == rt.NOT_CONTAINED, (label, scope, actual)

expect_raw("unmodified control")
local_git("replace", "--graft", tip, fork)
replacement = local_git("rev-parse", "refs/replace/" + tip).stdout.strip()
assert local_git("merge-base", "--is-ancestor", fork, tip, check=False).returncode == 0
expect_raw("local replace ref")
local_git("replace", "-d", tip)

custom_base = "refs/test-replacements/"
local_git("update-ref", custom_base + tip, replacement)
with patch.dict(os.environ, {"GIT_REPLACE_REF_BASE": custom_base}):
    expect_raw("custom replacement namespace")
local_git("update-ref", "-d", custom_base + tip)

missing = "0123456789012345678901234567890123456789"
local_git("update-ref", "refs/replace/" + missing, tip)
assert local_git("cat-file", "-t", missing).stdout.strip() == "commit"
assert rt.RemoteTips.present(store / ".git", [missing, tip]) == {tip}
local_git("update-ref", "-d", "refs/replace/" + missing)

graft = store / ".git" / "info" / "grafts"
graft.write_text(tip + " " + fork + "\n")
assert local_git("merge-base", "--is-ancestor", fork, tip, check=False).returncode == 0
expect_raw("local info/grafts")
graft.unlink()

external_graft = store / ".git" / "info" / "external-grafts"
external_graft.write_text(tip + " " + fork + "\n")
with patch.dict(os.environ, {"GIT_GRAFT_FILE": str(external_graft)}):
    expect_raw("ambient graft path")
PY
then
  printf 'ok    remote ancestry and presence ignore local replacement and graft views\n'; pass=$((pass+1))
else
  printf 'FAIL  local metadata changed a remote containment or presence verdict\n'; fail=$((fail+1))
fi

# 21. A split semantic implementation is part of its root's surface. Keeping
#     ty.rs identical while changing its compiled helper used to read COHERENT.
D="$TMP/split-semantics"; make_fixture "$D"
store="$D/first-party/trust-ir"
mkdir -p "$store/crates/trust-ir/src/ty"
printf 'mod observed_meaning;\n' >> "$store/crates/trust-ir/src/ty.rs"
printf 'pub const MEANING: u32 = 1;\n' > "$store/crates/trust-ir/src/ty/observed_meaning.rs"
git -C "$store" add -A && git -C "$store" commit -qm "split semantic implementation"
REV_SPLIT="$(git -C "$store" rev-parse HEAD)"
printf 'pub const MEANING: u32 = 2;\n' > "$store/crates/trust-ir/src/ty/observed_meaning.rs"
git -C "$store" add -A && git -C "$store" commit -qm "change only semantic helper"
REV_SPLIT_CHANGED="$(git -C "$store" rev-parse HEAD)"
git -C "$store" push -q origin main
git -C "$D" update-index --cacheinfo 160000,"$REV_SPLIT",first-party/trust-ir
git -C "$D" commit -qm "pin split semantics"
decl "$D" "a/Cargo.toml" "$REV_SPLIT"
decl "$D" "b/Cargo.toml" "$REV_SPLIT_CHANGED"
check "a changed split semantic implementation is divergent" "$D" 1

# Every declared root gets the same protection, including nested directories
# and non-UTF-8 include_bytes! inputs. The digest reads the named revision:
# uncommitted worktree contents cannot supply or conceal a change.
if python3 - "$GATE" "$store" <<'PY'
import importlib.util
from pathlib import Path
import subprocess
import sys

spec = importlib.util.spec_from_file_location("ir_cohort", sys.argv[1])
cohort = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cohort)
store = Path(sys.argv[2])
surface = cohort.SEMANTIC_SURFACE["trust-ir"]

def git(*args):
    return subprocess.run(["git", "-C", str(store), *args], check=True,
                          capture_output=True, text=True).stdout.strip()

def commit():
    git("add", "-A")
    git("commit", "-qm", "semantic subtree mutation")
    return git("rev-parse", "HEAD")

before = git("rev-parse", "HEAD")
for root in surface:
    child = store / root.removesuffix(".rs") / "nested" / "meaning data.bin"
    child.parent.mkdir(parents=True, exist_ok=True)
    child.write_bytes(b"\x00\xff\r\n")
    added = commit()
    initial = cohort.semantic_digest(store, added, surface)
    assert initial != cohort.semantic_digest(store, before, surface), root
    child.write_bytes(b"\x00\xfe\r\n")
    assert cohort.semantic_digest(store, added, surface) == initial, root
    changed = commit()
    changed_digest = cohort.semantic_digest(store, changed, surface)
    assert changed_digest != initial, root
    git("replace", changed, added)
    assert cohort.semantic_digest(store, changed, surface) == changed_digest, root
    git("replace", "-d", changed)
    child.unlink()
    removed = commit()
    assert cohort.semantic_digest(store, removed, surface) == cohort.semantic_digest(store, before, surface), root
    before = removed

assert cohort.semantic_digest(store, "0" * 40, surface) is None
PY
then
  printf 'ok    every split subtree binds exact committed bytes, additions, removals and replacement immunity\n'; pass=$((pass+1))
else
  printf 'FAIL  split subtree content, membership or revision binding\n'; fail=$((fail+1))
fi

# 22. WP defines a proof algorithm, not another IR wire format. Its revision
# still has to resolve on its remote main, and the IR it consumes stays gated.
D="$TMP/wp-consumer"; make_fixture "$D"
decl "$D" "a/Cargo.toml" "$REV_A"
WP_STORE="$D/first-party/trust-wp"
WP_REMOTE="$D.trust-wp-remote.git"
mkdir -p "$WP_STORE"
git -C "$WP_STORE" init -q -b main
git -C "$WP_STORE" config user.email t@example.invalid
git -C "$WP_STORE" config user.name T
cat > "$WP_STORE/Cargo.toml" <<EOF
[dependencies]
trust-ir = { git = "https://github.com/alabsystems/trust-ir.git", rev = "$REV_A" }
EOF
git -C "$WP_STORE" add -A && git -C "$WP_STORE" commit -qm "WP consumes canonical IR"
WP_A="$(git -C "$WP_STORE" rev-parse HEAD)"
git init -q --bare -b main "$WP_REMOTE"
git -C "$WP_STORE" remote add origin "$WP_REMOTE"
git -C "$WP_STORE" push -q origin main
cat > "$D/.gitmodules" <<EOF
[submodule "first-party/trust-ir"]
    path = first-party/trust-ir
    url = $REMOTE
[submodule "first-party/trust-wp"]
    path = first-party/trust-wp
    url = $WP_REMOTE
EOF
git -C "$D" add .gitmodules
git -C "$D" update-index --add --cacheinfo 160000,"$WP_A",first-party/trust-wp
git -C "$D" commit -qm "record WP consumer"
git -C "$D" submodule init -q
decl_wp() {
  mkdir -p "$D/consumer"
  cat > "$D/consumer/Cargo.toml" <<EOF
[dependencies]
trust-wp-lib = { git = "https://github.com/alabsystems/trust-wp.git", rev = "$1" }
EOF
  git -C "$D" add consumer/Cargo.toml
  git -C "$D" commit -qm "select WP input"
}
decl_wp "$WP_A"
out="$(python3 "$GATE" --root "$D" 2>&1)"; got=$?
if [ "$got" = 0 ] && printf '%s\n' "$out" | grep -q '^== trust-wp:' \
    && printf '%s\n' "$out" | grep -q 'WP consumer, not an IR format'; then
  printf 'ok    WP consumer is inventoried without inventing an IR surface\n'; pass=$((pass+1))
else
  printf 'FAIL  WP consumer registration (exit %s)\n' "$got"
  printf '%s\n' "$out" | sed 's/^/      | /'; fail=$((fail+1))
fi
sed "s/$REV_A/$REV_B/" "$WP_STORE/Cargo.toml" > "$WP_STORE/new-manifest"
mv "$WP_STORE/new-manifest" "$WP_STORE/Cargo.toml"
git -C "$WP_STORE" add Cargo.toml && git -C "$WP_STORE" commit -qm "WP consumes divergent IR"
git -C "$WP_STORE" push -q origin main
WP_B="$(git -C "$WP_STORE" rev-parse HEAD)"
git -C "$D" update-index --cacheinfo 160000,"$WP_B",first-party/trust-wp
git -C "$D" commit -qm "record changed WP consumer"
decl_wp "$WP_B"
check "WP consumer's divergent IR still refuses" "$D" 1
git -C "$WP_STORE" checkout -q -b unpublished "$WP_A"
printf 'unpublished\n' > "$WP_STORE/note"
git -C "$WP_STORE" add note && git -C "$WP_STORE" commit -qm "unpublished WP"
decl_wp "$(git -C "$WP_STORE" rev-parse HEAD)"
check "WP consumer still refuses an off-main revision" "$D" 1
decl_wp "0123456789012345678901234567890123456789"
check "WP consumer still refuses an unresolvable revision" "$D" 1

printf '\n%d passed, %d failed\n' "$pass" "$fail"
[ "$fail" = 0 ]
