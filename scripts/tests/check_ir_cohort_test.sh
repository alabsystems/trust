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

  git -C "$store" update-ref refs/remotes/origin/main "$REV_C"

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

printf '\n%d passed, %d failed\n' "$pass" "$fail"
[ "$fail" = 0 ]
