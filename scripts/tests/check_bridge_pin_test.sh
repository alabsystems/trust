#!/usr/bin/env bash
# Self-test for scripts/check_bridge_pin.sh --check and --fix.
#
# Every case runs on a throwaway superproject with two real submodules standing
# in for first-party/trust-ir and first-party/clean, and a vendored-olean
# directory with its MANIFEST.toml. Section 1 is the standing reading
# (TRUST_PUSHED_REFS unset): the index, the indexed manifest and the submodule
# checkouts. Sections 2-4 are the push reading, where the gate must judge the
# PUSHED commits' trees -- their gitlinks, manifest blob and olean blobs --
# never the index or the submodule checkouts. Sections 2 and 3 are the
# reproduced cases of docs/issues/2026-09-28-push-lanes-judge-the-checkout-not-
# the-push.md (case B): each passed a bad push or refused a good one when the
# lane judged the index.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
set -uo pipefail
ROUTING_ONLY=0
if [[ "${1:-}" == --reuse-routing-only && "$#" == 1 ]]; then
  ROUTING_ONLY=1
elif [[ "$#" != 0 ]]; then
  echo "usage: check_bridge_pin_test.sh [--reuse-routing-only]" >&2
  exit 2
fi

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
GATE="$REPO_ROOT/scripts/check_bridge_pin.sh"
[ -f "$GATE" ] || { echo "check_bridge_pin tests: no $GATE" >&2; exit 2; }

# A push hook that runs this file must not hand the fixtures its own push.
unset TRUST_PUSHED_REFS
# Hermetic git for the fixtures: no user/global hooks, signing, or rewrites.
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@example.invalid
export GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@example.invalid
unset GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_COMMON_DIR GIT_OBJECT_DIRECTORY

TMP="$(mktemp -d)" || exit 2
trap 'rm -rf "$TMP"' EXIT

FAILED=0
pass() { echo "  ok   $1"; }
fail() { echo "  FAIL $1"; FAILED=1; }

ZERO=0000000000000000000000000000000000000000
MDIR=crates/trust-clean/fixtures/trustir-oleans
PLAT=x86_64-test-linux

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{ print $1 }'
  else
    shasum -a 256 "$1" | awk '{ print $1 }'
  fi
}

# write_manifest <super dir> <trustir_commit> <clean_commit>: a manifest whose
# digests are those of the olean files on disk.
write_manifest() {
  local dir="$1" ti="$2" cl="$3" m="$1/$MDIR"
  cat > "$m/MANIFEST.toml" <<EOF
schema = "trust.trust-clean.trustir-oleans.manifest.v2"

[provenance]
trustir_commit = "$ti"
clean_commit = "$cl"

[files]
"TrustIr/A.olean" = "$(sha256_file "$m/TrustIr/A.olean")"
"TrustIr/B.olean" = "$(sha256_file "$m/TrustIr/B.olean")"

[platforms."$PLAT"]
built_from_trustir_commit = "$ti"

[platforms."$PLAT".files]
"TrustIr/P.olean" = "$(sha256_file "$m/platform/$PLAT/TrustIr/P.olean")"
EOF
}

# The two submodule sources, three commits each.
for name in trust-ir clean; do
  src="$TMP/src/$name"
  mkdir -p "$src"
  git -C "$src" init -q -b main
  for n in 1 2 3; do
    echo "$name $n" > "$src/file.txt"
    git -C "$src" add file.txt
    git -C "$src" commit -q -m "$name $n"
  done
done
TI1="$(git -C "$TMP/src/trust-ir" rev-parse HEAD~2)"
TI2="$(git -C "$TMP/src/trust-ir" rev-parse HEAD~1)"
CL1="$(git -C "$TMP/src/clean" rev-parse HEAD~2)"
CL2="$(git -C "$TMP/src/clean" rev-parse HEAD~1)"

# The base superproject: gate, submodules at TI1/CL1, oleans and manifest.
BASE="$TMP/base"
mkdir -p "$BASE/scripts" "$BASE/$MDIR/TrustIr" "$BASE/$MDIR/platform/$PLAT/TrustIr"
git -C "$BASE" init -q -b main
cp "$GATE" "$BASE/scripts/check_bridge_pin.sh"
for name in trust-ir clean; do
  git -C "$BASE" -c protocol.file.allow=always submodule add -q \
    "$TMP/src/$name" "first-party/$name" >/dev/null 2>&1 \
    || { echo "check_bridge_pin tests: cannot add submodule $name" >&2; exit 2; }
done
git -C "$BASE/first-party/trust-ir" checkout -q "$TI1"
git -C "$BASE/first-party/clean" checkout -q "$CL1"
echo "olean A" > "$BASE/$MDIR/TrustIr/A.olean"
echo "olean B" > "$BASE/$MDIR/TrustIr/B.olean"
echo "olean P" > "$BASE/$MDIR/platform/$PLAT/TrustIr/P.olean"
write_manifest "$BASE" "$TI1" "$CL1"
git -C "$BASE" add -A
git -C "$BASE" commit -q -m good
GOOD="$(git -C "$BASE" rev-parse HEAD)"

CASE=0
d=""
# fresh: point $d at a private copy of the base superproject (relative
# submodule gitdirs make a plain copy a working repository).
fresh() {
  CASE=$((CASE + 1))
  d="$TMP/case$CASE"
  cp -R "$BASE" "$d" || { echo "check_bridge_pin tests: cannot copy the fixture" >&2; exit 2; }
}

# commit_tree <dir> <from> <edit command...>: a commit on top of <from> whose
# tree is <from>'s after running the edit against a scratch index -- the
# checkout and the real index are never touched. Prints the new sha.
commit_tree() {
  local dir="$1" from="$2" tree
  shift 2
  (
    export GIT_INDEX_FILE="$TMP/scratch.index"
    rm -f "$GIT_INDEX_FILE"
    cd "$dir" && git read-tree "$from" && "$@" >/dev/null && tree="$(git write-tree)" \
      && git commit-tree "$tree" -p "$from" -m case
  )
}

# blob_of <dir> <text>: a blob holding <text>.
blob_of() { printf '%s\n' "$2" | git -C "$1" hash-object -w --stdin; }

# pushed_line <ref> <sha>: the pre-push stdin line of a push creating <ref>.
pushed_line() { echo "$1 $2 $1 $ZERO"; }

OUT=""
RC=0
# run_gate <dir> [<TRUST_PUSHED_REFS>]: the gate as the hook runs it.
run_gate() {
  local dir="$1"
  if [ "$#" -ge 2 ]; then
    OUT="$(cd "$dir" && TRUST_PUSHED_REFS="$2" bash scripts/check_bridge_pin.sh --check 2>&1)"
  else
    OUT="$(cd "$dir" && env -u TRUST_PUSHED_REFS bash scripts/check_bridge_pin.sh --check 2>&1)"
  fi
  RC=$?
}

# expect <name> <rc> [<pattern that must appear>] [<pattern that must not>]
expect() {
  local name="$1" rc="$2" want="${3:-}" unwanted="${4:-}"
  if [ "$RC" != "$rc" ]; then
    fail "$name: exit $RC, expected $rc"
    printf '%s\n' "$OUT" | sed 's/^/         /'
    return
  fi
  if [ -n "$want" ] && ! printf '%s\n' "$OUT" | grep -qE -- "$want"; then
    fail "$name: output lacks /$want/"
    printf '%s\n' "$OUT" | sed 's/^/         /'
    return
  fi
  if [ -n "$unwanted" ] && printf '%s\n' "$OUT" | grep -qE -- "$unwanted"; then
    fail "$name: output has /$unwanted/"
    printf '%s\n' "$OUT" | sed 's/^/         /'
    return
  fi
  pass "$name"
}

# Manifest text of <dir>'s HEAD with <from> replaced by <to> on its key line.
edited_manifest() {
  git -C "$1" show "HEAD:$MDIR/MANIFEST.toml" | sed "s/^$2 = \"[0-9a-f]*\"/$2 = \"$3\"/"
}

echo "0. ROOT release tags retain their raw labels and route the peeled commit"
fresh
cat >> "$d/$MDIR/MANIFEST.toml" <<'EOF'

[source_reuse]
schema = "trust.bridge-source-reuse.v1"
EOF
git -C "$d" add "$MDIR/MANIFEST.toml"
git -C "$d" commit -q -m routing-subject
routing_commit="$(git -C "$d" rev-parse HEAD)"
git -C "$d" tag -a -m release routing-release
routing_tag="$(git -C "$d" rev-parse routing-release)"
mkdir -p "$d/route-bin"
# This tests ONLY the shell-to-verifier argument boundary, not input equality.
# The Rust verifier has independent real-Git controls. No Rust build or proof
# is performed by this recorder or its local admission stand-in.
cat > "$d/scripts/build-slot" <<'EOF'
#!/usr/bin/env bash
[[ "$1" == -- ]] || exit 98
shift
exec "$@"
EOF
# The gate runs the checkout's scripts/build-slot, never one found on PATH
# (none is on PATH where the push profile runs): a decoy there refuses.
cat > "$d/route-bin/build-slot" <<'EOF'
#!/usr/bin/env bash
echo "a build-slot found on PATH ran" >&2
exit 99
EOF
cat > "$d/route-bin/record-targo" <<'EOF'
#!/usr/bin/env bash
last=""
for arg in "$@"; do last="$arg"; done
printf '%s\n' "$last" >> "$ROUTING_CALLS"
[[ "$last" == "$ROUTING_COMMIT" ]] || exit 97
printf 'SOURCE_REUSE %s %s %s\n' "$ROUTING_IR" "$ROUTING_CLEAN" "$ROUTING_COMMIT"
EOF
chmod +x "$d/scripts/build-slot" "$d/route-bin/build-slot" "$d/route-bin/record-targo"
saved_path="$PATH"
export PATH="$d/route-bin:$PATH" TARGO="$d/route-bin/record-targo"
export ROUTING_COMMIT="$routing_commit" ROUTING_IR="$TI1" ROUTING_CLEAN="$CL1" ROUTING_CALLS="$d/routing-calls"
run_gate "$d" "$(pushed_line refs/tags/release "$routing_tag")"
expect "annotated ROOT release tag passes its peeled commit" 0 "BRIDGE PIN OK" "BRIDGE SOURCE REUSE REFUSED"
[[ "$(cat "$ROUTING_CALLS")" == "$routing_commit" \
  && "$OUT" == *"refs/tags/release ${routing_tag:0:12}"* ]] || fail "raw tag label or exact commit argument was lost"
: > "$ROUTING_CALLS"
run_gate "$d" "$(pushed_line refs/tags/release "$routing_tag")
$(pushed_line refs/heads/main "$routing_commit")"
expect "tag and commit with identical ancestry share one verifier call" 0 "BRIDGE PIN OK"
[[ "$(wc -l < "$ROUTING_CALLS" | tr -d ' ')" == 1 ]] || fail "equal commit ancestry did not deduplicate"
export PATH="$saved_path"
unset TARGO ROUTING_COMMIT ROUTING_IR ROUTING_CLEAN ROUTING_CALLS
if [[ "$ROUTING_ONLY" == 1 ]]; then
  [[ "$FAILED" == 0 ]] || exit 1
  echo "check_bridge_pin routing controls: all cases passed (argument boundary only)"
  exit 0
fi

echo "1. the standing reading (TRUST_PUSHED_REFS unset) is unchanged"
fresh
run_gate "$d"
expect "clean checkout at the pins: OK" 0 "^BRIDGE PIN OK: committed pins == manifest == clean checkouts; 3 staged olean digest"
touch "$d/first-party/clean/scratch.txt"
run_gate "$d"
expect "untracked file in a submodule: refused" 1 "checkout has tracked or untracked changes"
fresh
git -C "$d/first-party/trust-ir" checkout -q "$TI2"
git -C "$d" add first-party/trust-ir
run_gate "$d"
expect "staged gitlink without a manifest regen: refused" 1 "BRIDGE PIN DRIFT: indexed first-party/trust-ir"
run_gate "$d" "   "
expect "a blank TRUST_PUSHED_REFS is the standing reading" 1 "BRIDGE PIN DRIFT: indexed first-party/trust-ir" "^SUBJECT"
# A LABEL exported by the caller must not prefix the standing reading's lines:
# only the push reading labels a verdict with the ref it judges.
fresh
git -C "$d" show "HEAD:$MDIR/MANIFEST.toml" \
  | sed "s/^built_from_trustir_commit = \"[0-9a-f]*\"/built_from_trustir_commit = \"$TI2\"/" \
  > "$TMP/stale.toml"
cp "$TMP/stale.toml" "$d/$MDIR/MANIFEST.toml"
git -C "$d" add "$MDIR/MANIFEST.toml"
export LABEL=x
run_gate "$d"
unset LABEL
expect "an exported LABEL does not prefix the standing reading" 1 \
  "^BRIDGE PLATFORM STALE \\(disclosed\\): $PLAT" "^\\[x\\]"

echo "2. push reading: a bad pushed tree is refused (passed when the index was judged)"
# 1a: a non-HEAD ref whose manifest names the wrong clean commit and one of
# whose oleans is corrupted; the checkout stays clean at main.
fresh
man="$(blob_of "$d" "$(edited_manifest "$d" clean_commit "$CL2")")"
bad_olean="$(blob_of "$d" "corrupted")"
bad="$(commit_tree "$d" "$GOOD" git update-index \
  --cacheinfo "100644,$man,$MDIR/MANIFEST.toml" \
  --cacheinfo "100644,$bad_olean,$MDIR/TrustIr/A.olean")"
run_gate "$d"
expect "(1a) control: the index reading passes the checkout" 0 "BRIDGE PIN OK"
run_gate "$d" "$(pushed_line refs/heads/bad "$bad")"
expect "(1a) non-HEAD ref, wrong clean_commit + corrupted olean: refused" 1 \
  "\\[refs/heads/bad [0-9a-f]{12}\\] BRIDGE PIN DRIFT: pushed first-party/clean pin=$CL1  !=  pushed manifest clean_commit=$CL2"
expect "(1a) ... and the corrupted olean is named" 1 \
  "BRIDGE DIGEST MISMATCH: $MDIR/TrustIr/A.olean pushed sha256="
expect "(1a) ... emits complete tree-local FINDING keys (PIN-DRIFT)" 1 \
  "^FINDING: PIN-DRIFT first-party/clean $CL1 clean_commit $CL2\$"
expect "(1a) ... emits complete tree-local FINDING keys (DIGEST-MISMATCH)" 1 \
  "^FINDING: DIGEST-MISMATCH $MDIR/TrustIr/A\\.olean [0-9a-f]{64} [0-9a-f]{64}\$"
expect "(1a) ... marks FINDINGS: complete when all tree-local checks ran" 1 \
  "^FINDINGS: complete\$"
# 1b: HEAD carries a gitlink bump without a regen; the repair is only staged.
fresh
git -C "$d/first-party/trust-ir" checkout -q "$TI2"
git -C "$d" add first-party/trust-ir
git -C "$d" commit -q -m "bump trust-ir, no regen"
write_manifest "$d" "$TI2" "$CL1"
git -C "$d" add "$MDIR/MANIFEST.toml"
run_gate "$d"
expect "(1b) control: the staged repair passes the index reading" 0 "BRIDGE PIN OK"
run_gate "$d" "$(pushed_line refs/heads/main "$(git -C "$d" rev-parse HEAD)")"
expect "(1b) HEAD with its repair staged, not committed: refused" 1 \
  "BRIDGE PIN DRIFT: pushed first-party/trust-ir pin=$TI2  !=  pushed manifest trustir_commit=$TI1"
# 1d: a non-HEAD ref bumping a gitlink with no manifest regen.
fresh
bump="$(commit_tree "$d" "$GOOD" git update-index --cacheinfo "160000,$TI2,first-party/trust-ir")"
run_gate "$d" "$(pushed_line refs/heads/topic "$bump")"
expect "(1d) non-HEAD gitlink bump without a regen: refused" 1 \
  "BRIDGE PIN DRIFT: pushed first-party/trust-ir pin=$TI2"
run_gate "$d" "refs/heads/topic $bump refs/heads/main $GOOD"
expect "(1d) ... also as \`git push origin topic:main\`" 1 "BRIDGE PIN DRIFT: pushed first-party/trust-ir"

echo "3. push reading: a good pushed tree passes whatever the checkout holds (refused when the index was judged)"
fresh
touch "$d/first-party/clean/scratch.txt"
run_gate "$d" "$(pushed_line refs/heads/main "$GOOD")"
expect "untracked file in first-party/clean: OK, WARN" 0 \
  "BRIDGE CHECKOUT WARN \\(local hygiene, not judged for this push\\): first-party/clean checkout has tracked or untracked changes"
fresh
echo "wip" >> "$d/first-party/trust-ir/file.txt"
run_gate "$d" "$(pushed_line refs/heads/main "$GOOD")"
expect "tracked edit in the trust-ir checkout: OK, WARN" 0 "BRIDGE CHECKOUT WARN .*first-party/trust-ir"
fresh
echo "local" > "$d/first-party/clean/local.txt"
git -C "$d/first-party/clean" add local.txt
git -C "$d/first-party/clean" commit -q -m local
run_gate "$d" "$(pushed_line refs/heads/main "$GOOD")"
expect "local commit in the clean checkout: OK, WARN" 0 \
  "BRIDGE CHECKOUT WARN .*first-party/clean checkout=[0-9a-f]{40}  !=  pushed pin=$CL1"
fresh
git -C "$d/first-party/trust-ir" checkout -q "$TI2"
git -C "$d" add first-party/trust-ir
run_gate "$d" "$(pushed_line refs/heads/main "$GOOD")"
expect "staged WIP gitlink: OK" 0 "BRIDGE PIN OK: pushed pins == pushed manifest; 3 olean digest"
fresh
bump="$(commit_tree "$d" "$GOOD" git update-index --cacheinfo "160000,$TI2,first-party/trust-ir")"
git -C "$d" branch -q good "$GOOD"
git -C "$d" checkout -q "$bump"
git -C "$d/first-party/trust-ir" checkout -q "$TI2"
run_gate "$d"
expect "bad HEAD: control, the index reading refuses" 1 "BRIDGE PIN DRIFT"
run_gate "$d" "$(pushed_line refs/heads/good "$GOOD")"
expect "bad HEAD, a good ref pushed: OK" 0 "BRIDGE PIN OK"
run_gate "$d" "(delete) $ZERO refs/heads/gone $GOOD"
expect "bad HEAD, a deletion-only push: SKIPPED" 0 "^SKIPPED: deletion\\(s\\) only"
fresh
git -C "$d" worktree add -q --detach "$TMP/linked$CASE" "$GOOD" >/dev/null 2>&1
cp "$GATE" "$TMP/linked$CASE/scripts/check_bridge_pin.sh"
run_gate "$TMP/linked$CASE"
expect "linked worktree, no submodules: control, the index reading refuses" 2 "is not an initialized git checkout"
run_gate "$TMP/linked$CASE" "$(pushed_line refs/heads/main "$GOOD")"
expect "linked worktree, no submodules: OK (pins read from the module stores)" 0 \
  "BRIDGE PIN OK" "^\\[.*UNREADABLE"

echo "4. push reading: every other refusal holds"
fresh
ghost="1234567890abcdef1234567890abcdef12345678"
man="$(blob_of "$d" "$(edited_manifest "$d" clean_commit "$ghost")")"
ghostpin="$(commit_tree "$d" "$GOOD" git update-index \
  --cacheinfo "160000,$ghost,first-party/clean" \
  --cacheinfo "100644,$man,$MDIR/MANIFEST.toml")"
run_gate "$d" "$(pushed_line refs/heads/ghost "$ghostpin")"
expect "a pin absent from every submodule store: refused (unkeyed, not inheritable)" 1 \
  "BRIDGE PIN UNREADABLE: pushed first-party/clean pin=$ghost" "^FINDINGS: complete\$"
gone="$(commit_tree "$d" "$GOOD" git rm -q --cached "$MDIR/TrustIr/B.olean")"
run_gate "$d" "$(pushed_line refs/heads/gone "$gone")"
expect "an olean listed but absent from the pushed tree: refused" 1 \
  "BRIDGE DIGEST MISSING: $MDIR/TrustIr/B.olean is listed in the manifest but absent from the pushed tree"
link="$(blob_of "$d" "A.olean")"
sym="$(commit_tree "$d" "$GOOD" git update-index --cacheinfo "120000,$link,$MDIR/TrustIr/B.olean")"
run_gate "$d" "$(pushed_line refs/heads/sym "$sym")"
expect "an olean that is a symlink in the pushed tree: refused" 1 "is not a regular file in the pushed tree"
nomani="$(commit_tree "$d" "$GOOD" git rm -q --cached "$MDIR/MANIFEST.toml")"
run_gate "$d" "$(pushed_line refs/heads/nomani "$nomani")"
expect "no manifest in the pushed tree: refused (incomplete, not inheritable)" 1 \
  "MANIFEST.toml is missing from the pushed tree" "^FINDINGS: complete\$"
nolink="$(commit_tree "$d" "$GOOD" git rm -q --cached first-party/trust-ir)"
run_gate "$d" "$(pushed_line refs/heads/nolink "$nolink")"
expect "no trust-ir gitlink in the pushed tree: refused" 1 "the pushed tree has no gitlink at first-party/trust-ir"
run_gate "$d" "$(pushed_line refs/heads/main "$GOOD")
$(pushed_line refs/heads/gone "$gone")"
expect "a multi-ref push with one bad tree: refused, the bad ref named" 1 \
  "\\[refs/heads/gone [0-9a-f]{12}\\] BRIDGE DIGEST MISSING"
# A gitlink naming an annotated TAG object, with a manifest that agrees with
# it. A checkout of that gitlink lands on the tagged commit, which is not the
# sha the manifest names, so peeling the tag would pass a pin the bridge
# consumer's PinDrift refuses. Control first: the tagged commit itself passes.
fresh
git -C "$d/first-party/trust-ir" tag -a -m tag ti2tag "$TI2"
tag="$(git -C "$d/first-party/trust-ir" rev-parse ti2tag)"
for pin in "$TI2" "$tag"; do
  man="$(blob_of "$d" "$(git -C "$d" show "HEAD:$MDIR/MANIFEST.toml" | sed "s/\"$TI1\"/\"$pin\"/g")")"
  pinned="$(commit_tree "$d" "$GOOD" git update-index \
    --cacheinfo "160000,$pin,first-party/trust-ir" \
    --cacheinfo "100644,$man,$MDIR/MANIFEST.toml")"
  run_gate "$d" "$(pushed_line refs/heads/pinned "$pinned")"
  if [ "$pin" = "$TI2" ]; then
    expect "control: a consistent bump to the tagged commit passes" 0 "BRIDGE PIN OK"
  else
    expect "a gitlink naming an annotated tag object, manifest agreeing: refused" 1 \
      "BRIDGE PIN UNREADABLE: pushed first-party/trust-ir pin=$tag"
  fi
done
run_gate "$d" "$(pushed_line refs/heads/nowhere 0123456789012345678901234567890123456789)"
expect "a pushed sha this repository cannot read: refused (unkeyed, not inheritable)" 1 \
  "does not name a tree here" "^FINDINGS: complete\$"
run_gate "$d" "refs/heads/main $GOOD refs/heads/main"
expect "a malformed TRUST_PUSHED_REFS line: exit 2" 2 "malformed TRUST_PUSHED_REFS line"
run_gate "$d" "refs/heads/main $GOOD refs/heads/main $ZERO extra"
expect "a TRUST_PUSHED_REFS line with a fifth field: exit 2" 2 "malformed TRUST_PUSHED_REFS line"

echo "5. linked-worktree regeneration never repairs shared submodule configuration"

# Keep generation cheap here: real Git/index/config checks use a producer that
# updates only provenance, retaining the fixture's exact sample olean digests.
# The production producer and bridge replay are qualified separately.
install_fixture_regen() {
  cat > "$1/scripts/regen-trustir-oleans.sh" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
[[ "$1" == --write ]]
root="$(cd "$(dirname "$0")/.." && pwd)"
manifest="$root/crates/trust-clean/fixtures/trustir-oleans/MANIFEST.toml"
ti="$(git -C "$root/first-party/trust-ir" rev-parse HEAD)"
cl="$(git -C "$root/first-party/clean" rev-parse HEAD)"
sample="$root/crates/trust-clean/fixtures/trustir-oleans/TrustIr/A.olean"
if command -v sha256sum >/dev/null 2>&1; then
  hash="$(sha256sum "$sample" | awk '{ print $1 }')"
else
  hash="$(shasum -a 256 "$sample" | awk '{ print $1 }')"
fi
sed -e "s/^trustir_commit = .*/trustir_commit = \"$ti\"/" \
    -e "s/^built_from_trustir_commit = .*/built_from_trustir_commit = \"$ti\"/" \
    -e "s/^clean_commit = .*/clean_commit = \"$cl\"/" \
    -e "s/^\"TrustIr\/A.olean\" = .*/\"TrustIr\/A.olean\" = \"$hash\"/" \
    "$manifest" > "$manifest.new"
mv "$manifest.new" "$manifest"
touch "$root/regen-called"
if [[ -f "$root/change-source-during-regen" ]]; then
  git -C "$root/first-party/clean" checkout -q HEAD~1
fi
if [[ -f "$root/change-index-during-regen" ]]; then
  old="$(git -C "$root/first-party/clean" rev-parse HEAD~1)"
  git -C "$root" update-index --cacheinfo "160000,$old,first-party/clean"
fi
if [[ -f "$root/dirty-during-regen" ]]; then
  echo keep-my-edit >> "$root/first-party/clean/file.txt"
fi
if [[ -f "$root/corrupt-during-regen" ]]; then
  echo corrupt >> "$root/crates/trust-clean/fixtures/trustir-oleans/TrustIr/A.olean"
fi
EOF
  chmod +x "$1/scripts/regen-trustir-oleans.sh"
}

run_fix() {
  OUT="$(cd "$1" && env -u TRUST_PUSHED_REFS bash scripts/check_bridge_pin.sh --fix 2>&1)"
  RC=$?
}

# Real submodule worktrees share primary module configuration, reproducing the
# layout at risk. Also exercise modern per-superproject-worktree module stores.
linked_fixture() {
  fresh
  linked="$TMP/fix-linked$CASE"
  git -C "$d" worktree add -q --detach "$linked" "$GOOD" || exit 2
  if [[ "${1:-shared}" == per-worktree ]]; then
    git -C "$linked" -c protocol.file.allow=always submodule update --init --checkout -q || exit 2
  else
    git -C "$d/first-party/trust-ir" worktree add -q --detach "$linked/first-party/trust-ir" "$TI1" || exit 2
    git -C "$d/first-party/clean" worktree add -q --detach "$linked/first-party/clean" "$CL2" || exit 2
  fi
  git -C "$linked/first-party/trust-ir" checkout -q "$TI1" || exit 2
  git -C "$linked/first-party/clean" checkout -q "$CL2" || exit 2
  git -C "$linked" add first-party/clean || exit 2
  install_fixture_regen "$linked"
}

shared_config_hashes() {
  git -C "$d" hash-object "$d/.git/config" \
    "$d/.git/modules/first-party/trust-ir/config" \
    "$d/.git/modules/first-party/clean/config"
}

primary_unchanged() {
  [[ -z "$(git -C "$d" status --porcelain=v1 --untracked-files=all)" \
    && "$(git -C "$d/first-party/trust-ir" rev-parse HEAD)" == "$TI1" \
    && "$(git -C "$d/first-party/clean" rev-parse HEAD)" == "$CL1" \
    && "$(cat "$d/first-party/clean/file.txt")" == 'clean 1' ]] \
    || fail "primary checkout bytes, HEADs or status changed"
}

linked_fixture
before="$(shared_config_hashes)"
run_fix "$linked"
expect "ready linked checkouts regenerate" 0 "BRIDGE PIN FIXED: worktree manifest regenerated"
[[ -f "$linked/regen-called" ]] || fail "ready linked checkouts invoke producer"
[[ "$(shared_config_hashes)" == "$before" ]] || fail "linked regeneration changed shared config"
primary_unchanged
[[ "$(git -C "$d/first-party/trust-ir" rev-parse HEAD)" == "$TI1" \
  && "$(git -C "$d/first-party/clean" rev-parse HEAD)" == "$CL1" ]] \
  || fail "linked regeneration changed primary checkouts"
run_gate "$linked"
expect "regenerated manifest must still be staged" 1 "BRIDGE PIN DRIFT"
git -C "$linked" add "$MDIR/MANIFEST.toml"
run_gate "$linked"
expect "ready linked regeneration passes after staging exact manifest" 0 "BRIDGE PIN OK"

linked_fixture
rm -rf "$linked/first-party/clean"
before="$(shared_config_hashes)"
run_fix "$linked"
expect "missing linked checkout is not initialized" 2 "refuses checkout repair from a linked worktree"
[[ ! -e "$linked/first-party/clean/.git" && ! -e "$linked/regen-called" \
  && "$(shared_config_hashes)" == "$before" ]] || fail "missing checkout refusal mutated state"
primary_unchanged

linked_fixture
git -C "$linked/first-party/clean" checkout -q "$CL1"
before="$(shared_config_hashes)"
run_fix "$linked"
expect "wrong linked checkout is not repaired" 2 "refuses checkout repair from a linked worktree"
[[ "$(git -C "$linked/first-party/clean" rev-parse HEAD)" == "$CL1" \
  && ! -e "$linked/regen-called" && "$(shared_config_hashes)" == "$before" ]] \
  || fail "wrong checkout refusal mutated state"
primary_unchanged

for dirty_path in file.txt scratch.txt; do
  linked_fixture
  echo keep-my-edit > "$linked/first-party/clean/$dirty_path"
  run_fix "$linked"
  expect "dirty linked checkout ($dirty_path) is preserved" 1 "checkout has tracked or untracked changes"
  [[ "$(cat "$linked/first-party/clean/$dirty_path")" == keep-my-edit \
    && ! -e "$linked/regen-called" ]] || fail "dirty checkout refusal lost state"
done

for changed in source index; do
  linked_fixture
  touch "$linked/change-$changed-during-regen"
  run_fix "$linked"
  expect "$changed change during regeneration is refused" 1 "source or index changed" "BRIDGE PIN FIXED"
done

linked_fixture per-worktree
before="$(shared_config_hashes)"
module_dir="$(git -C "$linked/first-party/clean" rev-parse --absolute-git-dir)"
module_before="$(git -C "$d" hash-object "$module_dir/config" "$module_dir/HEAD" "$module_dir/index")"
run_fix "$linked"
expect "per-worktree module gitfiles regenerate" 0 "BRIDGE PIN FIXED"
[[ "$(shared_config_hashes)" == "$before" \
  && "$(git -C "$d" hash-object "$module_dir/config" "$module_dir/HEAD" "$module_dir/index")" == "$module_before" ]] \
  || fail "per-worktree module metadata changed"
primary_unchanged

linked_fixture
other="$TMP/foreign-clean$CASE"
git clone -q --no-hardlinks "$TMP/src/clean" "$other"
git -C "$other" checkout -q "$CL2"
git -C "$other" config core.worktree "$other"
printf 'gitdir: %s/.git\n' "$other" > "$linked/first-party/clean/.git"
echo wrong-source-bytes > "$linked/first-party/clean/file.txt"
run_fix "$linked"
expect "misbound module gitfile refuses before generation" 1 "not bound to its source directory" "BRIDGE PIN FIXED"
[[ ! -e "$linked/regen-called" ]] || fail "misbound checkout invoked producer"

linked_fixture
before="$(shared_config_hashes)"
OUT="$(cd "$linked" && GIT_DIR="$d/.git" GIT_WORK_TREE="$d" \
  GIT_INDEX_FILE="$d/.git/index" GIT_COMMON_DIR="$d/.git" \
  bash scripts/check_bridge_pin.sh --fix 2>&1)"
RC=$?
expect "foreign Git environment cannot redirect linked regeneration" 0 "BRIDGE PIN FIXED"
[[ "$(shared_config_hashes)" == "$before" ]] || fail "foreign environment changed shared config"
primary_unchanged

linked_fixture
touch "$linked/dirty-during-regen"
run_fix "$linked"
expect "dirty source at generation endpoint refuses" 1 "checkout has tracked or untracked changes" "BRIDGE PIN FIXED"
[[ "$(tail -n 1 "$linked/first-party/clean/file.txt")" == keep-my-edit ]] \
  || fail "generation endpoint dirty edit was lost"

linked_fixture
touch "$linked/corrupt-during-regen"
run_fix "$linked"
expect "generated artifact with mismatched digest refuses" 1 "BRIDGE DIGEST MISMATCH.*generated" "BRIDGE PIN FIXED"

linked_fixture
write_manifest "$linked" "$TI1" "$CL2"
sed "s/$(sha256_file "$linked/$MDIR/TrustIr/A.olean")/$(printf '0%.0s' {1..64})/" \
  "$linked/$MDIR/MANIFEST.toml" > "$TMP/bad-digest.toml"
cp "$TMP/bad-digest.toml" "$linked/$MDIR/MANIFEST.toml"
git -C "$linked" add "$MDIR/MANIFEST.toml"
run_fix "$linked"
expect "matching pins with bad indexed digest regenerate and validate" 0 "BRIDGE PIN FIXED"
[[ -e "$linked/regen-called" ]] || fail "bad indexed digest did not invoke producer"

fresh
git -C "$d" update-index --cacheinfo "160000,$CL2,first-party/clean"
install_fixture_regen "$d"
run_fix "$d"
expect "primary checkout repair remains available" 0 "BRIDGE PIN FIXED: worktree manifest regenerated"
[[ "$(git -C "$d/first-party/clean" rev-parse HEAD)" == "$CL2" ]] \
  || fail "primary checkout was not repaired"
git -C "$d" add "$MDIR/MANIFEST.toml"
run_gate "$d"
expect "primary checkout repair passes after staging manifest" 0 "BRIDGE PIN OK"

echo "6. push reading: FINDING keys (BRIDGE-PIN-FINDINGS-1)"
# What the hook's INHERITED-RED compares: every key a push prints must appear
# on the destination's replay, and `FINDINGS: complete` must mean that no
# cause went unkeyed. keys_of reads $OUT as the hook's findings_of does.
TI3="$(git -C "$TMP/src/trust-ir" rev-parse HEAD)"
CL3="$(git -C "$TMP/src/clean" rev-parse HEAD)"
REC_B="$(sha256_file "$BASE/$MDIR/TrustIr/B.olean")"
keys_of() { printf '%s\n' "$OUT" | sed -n 's/^FINDING: //p' | LC_ALL=C sort -u; }
# expect_keys <name> <rc> <complete|incomplete> [<key>...]: exactly these keys,
# and the marker present (complete) or absent (incomplete).
expect_keys() {
  local name="$1" rc="$2" marker="$3" want got has=0
  shift 3
  want="$(if [ "$#" -gt 0 ]; then printf '%s\n' "$@" | LC_ALL=C sort -u; fi)"
  got="$(keys_of)"
  printf '%s\n' "$OUT" | grep -qE '^FINDINGS: complete$' && has=1
  if [ "$RC" != "$rc" ]; then
    fail "$name: exit $RC, expected $rc"
  elif [ "$got" != "$want" ]; then
    fail "$name: keys differ"
    printf 'want:\n%s\ngot:\n%s\n' "$want" "$got" | sed 's/^/         /'
  elif [ "$marker" = complete ] && [ "$has" != 1 ]; then
    fail "$name: no FINDINGS: complete"
  elif [ "$marker" = incomplete ] && [ "$has" != 0 ]; then
    fail "$name: FINDINGS: complete printed"
  else
    pass "$name"
    return
  fi
  printf '%s\n' "$OUT" | sed 's/^/         /'
}
# manifest_with <sed or awk program...>: HEAD's manifest text, edited.
manifest_with() { git -C "$d" show "HEAD:$MDIR/MANIFEST.toml" | "$@"; }

fresh
# (6a) main's red of 2026-11-09 in miniature: both gitlinks moved, no regen.
drift="$(commit_tree "$d" "$GOOD" git update-index \
  --cacheinfo "160000,$TI2,first-party/trust-ir" --cacheinfo "160000,$CL2,first-party/clean")"
K_IR="PIN-DRIFT first-party/trust-ir $TI2 trustir_commit $TI1"
K_CL="PIN-DRIFT first-party/clean $CL2 clean_commit $CL1"
run_gate "$d" "HEAD $drift refs/heads/main $GOOD"
expect_keys "(6a) both gitlinks moved without a regen: both PIN-DRIFT keys, complete" 1 complete "$K_IR" "$K_CL"
# (6b) a key names nothing of the push: the same tree as another commit, pushed
# to another ref from another tip, keys byte for byte the same.
twin="$(git -C "$d" commit-tree "$drift^{tree}" -p "$drift" -m twin)"
run_gate "$d" "refs/heads/topic $twin refs/heads/main $drift"
expect_keys "(6b) the same tree under another commit and ref: the same keys" 1 complete "$K_IR" "$K_CL"
# (6c) a push that changes any identity of a drifted cause gets a key the
# destination lacks, so it is never inherited.
moved="$(commit_tree "$d" "$drift" git update-index --cacheinfo "160000,$TI3,first-party/trust-ir")"
run_gate "$d" "HEAD $moved refs/heads/main $drift"
expect_keys "(6c) the push moves a drifted pin again: a new key" 1 complete \
  "PIN-DRIFT first-party/trust-ir $TI3 trustir_commit $TI1" "$K_CL"
man="$(blob_of "$d" "$(edited_manifest "$d" clean_commit "$CL3")")"
recommitted="$(commit_tree "$d" "$drift" git update-index --cacheinfo "100644,$man,$MDIR/MANIFEST.toml")"
run_gate "$d" "HEAD $recommitted refs/heads/main $drift"
expect_keys "(6c) the push changes a drifted manifest commit: a new key" 1 complete \
  "$K_IR" "PIN-DRIFT first-party/clean $CL2 clean_commit $CL3"
printf 'rebuilt\n' > "$TMP/rebuilt"
olean="$(blob_of "$d" "rebuilt")"
rebuilt="$(commit_tree "$d" "$drift" git update-index --cacheinfo "100644,$olean,$MDIR/TrustIr/B.olean")"
run_gate "$d" "HEAD $rebuilt refs/heads/main $drift"
expect_keys "(6c) the push changes a vendored olean under the drift: a new DIGEST-MISMATCH key" 1 complete \
  "$K_IR" "$K_CL" "DIGEST-MISMATCH $MDIR/TrustIr/B.olean $(sha256_file "$TMP/rebuilt") $REC_B"
# (6d) a partial repair prints a subset of the destination's keys.
man="$(blob_of "$d" "$(edited_manifest "$d" clean_commit "$CL2")")"
half="$(commit_tree "$d" "$drift" git update-index --cacheinfo "100644,$man,$MDIR/MANIFEST.toml")"
run_gate "$d" "HEAD $half refs/heads/main $drift"
expect_keys "(6d) a push repairing one side: a subset of the destination's keys" 1 complete "$K_IR"
# (6e) digest causes, keyed with path, mode/object and recorded digest.
gone="$(commit_tree "$d" "$GOOD" git rm -q --cached "$MDIR/TrustIr/B.olean")"
run_gate "$d" "$(pushed_line refs/heads/gone "$gone")"
expect_keys "(6e) an olean listed but absent: DIGEST-MISSING, complete" 1 complete \
  "DIGEST-MISSING $MDIR/TrustIr/B.olean $REC_B"
link="$(blob_of "$d" "A.olean")"
sym="$(commit_tree "$d" "$GOOD" git update-index --cacheinfo "120000,$link,$MDIR/TrustIr/B.olean")"
run_gate "$d" "$(pushed_line refs/heads/sym "$sym")"
expect_keys "(6e) an olean that is a symlink: DIGEST-MODE, complete" 1 complete \
  "DIGEST-MODE $MDIR/TrustIr/B.olean 120000:blob:$link $REC_B"
# (6f) no platform built from trustir_commit: the key names every platform's
# provenance, so a push that rewrites it is not the destination's red.
man="$(blob_of "$d" "$(manifest_with sed "s/^built_from_trustir_commit = .*/built_from_trustir_commit = \"$TI2\"/")")"
nocur="$(commit_tree "$d" "$GOOD" git update-index --cacheinfo "100644,$man,$MDIR/MANIFEST.toml")"
run_gate "$d" "HEAD $nocur refs/heads/main $GOOD"
expect_keys "(6f) no platform built from trustir_commit: PLATFORM-NO-CURRENT, complete" 1 complete \
  "PLATFORM-NO-CURRENT $TI1 $PLAT:$TI2"
man="$(blob_of "$d" "$(manifest_with sed "s/^built_from_trustir_commit = .*/built_from_trustir_commit = \"$TI3\"/")")"
reprov="$(commit_tree "$d" "$nocur" git update-index --cacheinfo "100644,$man,$MDIR/MANIFEST.toml")"
run_gate "$d" "HEAD $reprov refs/heads/main $nocur"
expect_keys "(6f) the push rewrites that platform's provenance: a new key" 1 complete \
  "PLATFORM-NO-CURRENT $TI1 $PLAT:$TI3"
# (6g) every unkeyed cause withholds the marker, beside a keyed cause too, so
# a red the push adds behind the destination's can never be inherited.
cdrift="$(commit_tree "$d" "$GOOD" git update-index --cacheinfo "160000,$CL2,first-party/clean")"
run_gate "$d" "HEAD $cdrift refs/heads/main $GOOD"
expect_keys "(6g) control: the clean-side drift alone is complete" 1 complete "$K_CL"
ghost="1234567890abcdef1234567890abcdef12345678"
p="$(commit_tree "$d" "$cdrift" git update-index --cacheinfo "160000,$ghost,first-party/trust-ir")"
run_gate "$d" "HEAD $p refs/heads/main $GOOD"
expect_keys "(6g) beside a pin this clone cannot read" 1 incomplete \
  "PIN-DRIFT first-party/trust-ir $ghost trustir_commit $TI1" "$K_CL"
man="$(blob_of "$d" "$(manifest_with sed 's/^trustir_commit = .*/trustir_commit = "not-a-commit"/')")"
p="$(commit_tree "$d" "$cdrift" git update-index --cacheinfo "100644,$man,$MDIR/MANIFEST.toml")"
run_gate "$d" "HEAD $p refs/heads/main $GOOD"
expect_keys "(6g) beside a malformed manifest commit" 1 incomplete "$K_CL"
man="$(blob_of "$d" "$(manifest_with awk -v dup="clean_commit = \"$CL1\"" '{ print } /^\[provenance\]$/ { print dup }')")"
p="$(commit_tree "$d" "$GOOD" git update-index --cacheinfo "100644,$man,$MDIR/MANIFEST.toml" \
  --cacheinfo "160000,$TI2,first-party/trust-ir")"
run_gate "$d" "HEAD $p refs/heads/main $GOOD"
expect_keys "(6g) beside a duplicated manifest field" 1 incomplete "$K_IR"
man="$(blob_of "$d" "$(manifest_with sed 's/^built_from_trustir_commit = .*/built_from_trustir_commit = ""/')")"
p="$(commit_tree "$d" "$cdrift" git update-index --cacheinfo "100644,$man,$MDIR/MANIFEST.toml")"
run_gate "$d" "HEAD $p refs/heads/main $GOOD"
expect_keys "(6g) beside a platform with no provenance" 1 incomplete "$K_CL" "PLATFORM-NO-CURRENT $TI1 $PLAT:"
never="$(printf 'never stored\n' | git -C "$d" hash-object --stdin)"
p="$(
  export GIT_INDEX_FILE="$TMP/scratch.index"
  rm -f "$GIT_INDEX_FILE"
  cd "$d" && git read-tree "$cdrift" \
    && git update-index --cacheinfo "100644,$never,$MDIR/TrustIr/B.olean" \
    && git commit-tree "$(git write-tree --missing-ok)" -p "$cdrift" -m unreadable
)"
run_gate "$d" "HEAD $p refs/heads/main $GOOD"
expect_keys "(6g) beside an olean blob this clone cannot read" 1 incomplete "$K_CL"
expect "(6g) ... which is named" 1 "BRIDGE DIGEST UNREADABLE: blob $never"
link="$(blob_of "$d" "elsewhere.toml")"
p="$(commit_tree "$d" "$GOOD" git update-index --cacheinfo "120000,$link,$MDIR/MANIFEST.toml")"
run_gate "$d" "HEAD $cdrift refs/heads/main $GOOD
$(pushed_line refs/heads/symmani "$p")"
expect_keys "(6g) beside a tree whose manifest is a symlink" 1 incomplete "$K_CL"
nomani="$(commit_tree "$d" "$GOOD" git rm -q --cached "$MDIR/MANIFEST.toml")"
run_gate "$d" "HEAD $cdrift refs/heads/main $GOOD
$(pushed_line refs/heads/nomani "$nomani")"
expect_keys "(6g) beside a tree with no manifest" 1 incomplete "$K_CL"
run_gate "$d" "HEAD $cdrift refs/heads/main $GOOD
$(pushed_line refs/heads/nowhere 0123456789012345678901234567890123456789)"
expect_keys "(6g) beside a pushed sha this clone cannot read" 1 incomplete "$K_CL"
# [source_reuse]: the verifier is a stand-in here (section 0 explains why);
# only how its refusal and a red reuse tree are keyed is under test.
mkdir -p "$d/reuse-bin"
cat > "$d/scripts/build-slot" <<'EOF'
#!/usr/bin/env bash
[[ "$1" == -- ]] || exit 98
shift
exec "$@"
EOF
cat > "$d/reuse-bin/targo" <<'EOF'
#!/usr/bin/env bash
[[ "${REUSE_STUB:-}" == select ]] || { echo "stand-in verifier: refused" >&2; exit 1; }
last=""
for arg in "$@"; do last="$arg"; done
printf 'SOURCE_REUSE %s %s %s\n' "$STUB_IR" "$STUB_CLEAN" "$last"
EOF
chmod +x "$d/scripts/build-slot" "$d/reuse-bin/targo"
man="$(blob_of "$d" "$(git -C "$d" show "HEAD:$MDIR/MANIFEST.toml"
  printf '\n[source_reuse]\nschema = "trust.bridge-source-reuse.v1"\n')")"
reuse="$(commit_tree "$d" "$GOOD" git update-index --cacheinfo "100644,$man,$MDIR/MANIFEST.toml")"
export TARGO="$d/reuse-bin/targo" REUSE_STUB=refuse
run_gate "$d" "HEAD $cdrift refs/heads/main $GOOD
$(pushed_line refs/heads/reuse "$reuse")"
expect_keys "(6g) beside a [source_reuse] tree the verifier refuses" 1 incomplete "$K_CL"
expect "(6g) ... which is named" 1 "BRIDGE SOURCE REUSE REFUSED"
export REUSE_STUB=select STUB_IR="$TI2" STUB_CLEAN="$CL1"
run_gate "$d" "$(pushed_line refs/heads/reuse "$reuse")"
expect_keys "(6g) a red [source_reuse] tree: keyed, never complete" 1 incomplete \
  "PIN-DRIFT first-party/trust-ir $TI1 trustir_commit $TI2"
unset TARGO REUSE_STUB STUB_IR STUB_CLEAN
# (6h) a green push prints no key and no marker; a disclosed stale platform
# is no refusal and no key.
run_gate "$d" "HEAD $GOOD refs/heads/main $GOOD"
expect_keys "(6h) a clean pushed tree: exit 0, no key, no marker" 0 incomplete
man="$(blob_of "$d" "$(git -C "$d" show "HEAD:$MDIR/MANIFEST.toml"
  printf '\n[platforms."y-stale"]\nbuilt_from_trustir_commit = "%s"\n' "$TI2")")"
p="$(commit_tree "$d" "$GOOD" git update-index --cacheinfo "100644,$man,$MDIR/MANIFEST.toml")"
run_gate "$d" "HEAD $p refs/heads/main $GOOD"
expect_keys "(6h) a disclosed stale platform beside a current one: exit 0, no key" 0 incomplete
expect "(6h) ... which is disclosed" 0 "BRIDGE PLATFORM STALE \\(disclosed\\): y-stale"
# (6i) the standing reading reads the index and the checkouts, which no
# destination replay reproduces: red there prints no key and no marker.
fresh
git -C "$d/first-party/trust-ir" checkout -q "$TI2"
git -C "$d" add first-party/trust-ir
run_gate "$d"
expect_keys "(6i) the standing reading, red: no key, no marker" 1 incomplete

if [ "$FAILED" != 0 ]; then
  echo "check_bridge_pin tests: FAILED"
  exit 1
fi
echo "check_bridge_pin tests: all cases passed"
