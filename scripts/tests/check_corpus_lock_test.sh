#!/usr/bin/env bash
# check_corpus_lock_test.sh --- falsification tests for the corpus lock.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# The lock went green on its first run against the real tree (2000 files, zero
# drift). That is exactly when a checker has to be shown to REFUTE: one that
# only ever agrees is indistinguishable from `exit 0`. Each case builds a
# synthetic repo and a synthetic sweep artifact, then asserts the verdict.
set -uo pipefail

TOOL="$(cd "$(dirname "$0")/.." && pwd)/trust_ir_corpus_lock.py"
[ -f "$TOOL" ] || { echo "tool not found at $TOOL" >&2; exit 1; }

pass=0; fail=0
ok()   { printf 'ok    %s\n' "$1"; pass=$((pass+1)); }
bad()  { printf 'FAIL  %s\n' "$1"; shift; printf '%s\n' "$*" | sed 's/^/      | /'; fail=$((fail+1)); }

TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT

# A synthetic repo with a synthetic recorded sweep naming three files.
make_repo() {
  local d="$1"
  mkdir -p "$d/tests/ui/a" "$d/art" "$d/scripts"
  git -C "$d" init -q -b main
  git -C "$d" config user.email t@example.invalid
  git -C "$d" config user.name T
  printf 'fn one() {}\n'   > "$d/tests/ui/a/one.rs"
  printf 'fn two() {}\n'   > "$d/tests/ui/a/two.rs"
  printf 'fn three() {}\n' > "$d/tests/ui/a/three.rs"
  cat > "$d/art/data.json" <<'JSON'
{"provenance": {"repo_head": "deadbeef", "date_utc": "2026-08-19T00:00:00+00:00"},
 "corpora": {"ui_sample": {"sample_meta": {"seed": 1, "sampled": 3, "eligible": 3},
   "files": [{"file": "tests/ui/a/one.rs"}, {"file": "tests/ui/a/two.rs"},
             {"file": "tests/ui/a/three.rs"}]}}}
JSON
  git -C "$d" add -A >/dev/null && git -C "$d" commit -qm init
}

run() { python3 "$TOOL" "$@" 2>&1; }
gen() { run --generate --from-artifact "$1/art" --lock "$1/scripts/c.lock" --root "$1"; }
chk() { run --check --lock "$1/scripts/c.lock" --root "$1" ${2:-}; }

# 1. Generate, then check: clean tree passes and locks all three.
D="$TMP/clean"; make_repo "$D"
out="$(cd "$D" && gen "$D")"
n="$(grep -c '^[0-9a-f]\{64\}  ' "$D/scripts/c.lock")"
[ "$n" = 3 ] && ok "generate locks every recorded file" || bad "generate locked $n of 3" "$out"
out="$(cd "$D" && chk "$D")"; rc=$?
[ "$rc" = 0 ] && ok "clean tree checks OK" || bad "clean tree should pass" "$out"

# 2. A MISSING locked file fails. This is the case that means "the corpus cannot
#    be measured as specified", so it must fail with or without --strict.
D="$TMP/missing"; make_repo "$D"; (cd "$D" && gen "$D" >/dev/null)
rm "$D/tests/ui/a/two.rs"
out="$(cd "$D" && chk "$D")"; rc=$?
[ "$rc" != 0 ] && ok "missing locked file fails" || bad "missing file should fail" "$out"
out="$(cd "$D" && chk "$D" --strict)"; rc=$?
[ "$rc" != 0 ] && ok "missing locked file fails under --strict too" || bad "should fail" "$out"

# 3. CONTENT DRIFT is reported, but does not fail without --strict --- test files
#    legitimately evolve, and the lock pins the corpus's IDENTITY, not the tree's
#    history. Under --strict it must fail, or the flag would be decorative.
D="$TMP/drift"; make_repo "$D"; (cd "$D" && gen "$D" >/dev/null)
printf 'fn two() { let _ = 1; }\n' > "$D/tests/ui/a/two.rs"
out="$(cd "$D" && chk "$D")"; rc=$?
if [ "$rc" = 0 ] && printf '%s' "$out" | grep -q 'content drift: 1'; then
  ok "content drift is reported but not fatal"
else bad "drift should report 1 and pass" "$out"; fi
out="$(cd "$D" && chk "$D" --strict)"; rc=$?
[ "$rc" != 0 ] && ok "content drift fails under --strict" || bad "--strict should fail" "$out"

# 4. THE POINT OF THE WHOLE EXERCISE: a locked file that gains a `//~`
#    annotation stays in the corpus. Under the old seeded sampler it would have
#    silently left the population and shrunk the denominator.
D="$TMP/annot"; make_repo "$D"; (cd "$D" && gen "$D" >/dev/null)
printf 'fn two() {}\n//~ ERROR something\n' > "$D/tests/ui/a/two.rs"
out="$(cd "$D" && chk "$D")"; rc=$?
if [ "$rc" = 0 ] \
   && printf '%s' "$out" | grep -q 'would not be re-selected by today.s filters: 1' \
   && printf '%s' "$out" | grep -q 'locked files: 3'; then
  ok "a file gaining //~ stays locked and is reported, not dropped"
else bad "annotated file should stay in the corpus and be flagged" "$out"; fi

# 5. An EMPTY lock is not a vacuous green.
D="$TMP/empty"; make_repo "$D"; mkdir -p "$D/scripts"
printf '# only a comment\n' > "$D/scripts/c.lock"
out="$(cd "$D" && chk "$D")"; rc=$?
[ "$rc" != 0 ] && ok "empty lock is not a vacuous green" || bad "empty lock should fail" "$out"

# 6. An ABSENT lock fails rather than silently doing nothing.
D="$TMP/absent"; make_repo "$D"
out="$(cd "$D" && chk "$D")"; rc=$?
[ "$rc" != 0 ] && ok "absent lock fails" || bad "absent lock should fail" "$out"

# 7. Generating from an artifact whose file has vanished drops it AND says so,
#    because a silently smaller corpus is a silently different denominator.
D="$TMP/genmissing"; make_repo "$D"
rm "$D/tests/ui/a/three.rs"
out="$(cd "$D" && gen "$D")"
if printf '%s' "$out" | grep -q '1 missing and dropped' \
   && grep -q 'WARNING' "$D/scripts/c.lock"; then
  ok "generate drops vanished files and records the warning in the lock"
else bad "generate should report and record the drop" "$out"; fi

printf '\n%d passed, %d failed\n' "$pass" "$fail"
[ "$fail" = 0 ]
