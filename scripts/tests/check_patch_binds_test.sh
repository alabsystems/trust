#!/usr/bin/env bash
# Self-test for scripts/check_patch_binds.py.
#
# The gate's whole value is that it distinguishes states that look alike in a
# build log, so each gets a case here: BINDS, UNBOUND (the version moved out
# from under the lock), DUPLICATED (the source named by the patch also
# resolved), compatible coexistence at another version or unrelated source,
# SKIPPED (the submodule is simply not checked out, which is a different
# gate's problem and must not be reported as this one's), and MISSING (every
# other missing patch manifest). The push-context cases (section 8 onward) run
# on throwaway git repos: under TRUST_PUSHED_REFS the gate must judge the pushed
# commits' trees -- and the submodule manifests those trees PIN -- never the
# working tree.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
GATE="$REPO_ROOT/scripts/check_patch_binds.py"
[ -f "$GATE" ] || { echo "check_patch_binds tests: no $GATE" >&2; exit 2; }

# The cases before section 8 are the no-push reading; a push hook that runs
# this file must not hand them its own push context.
unset TRUST_PUSHED_REFS
# Hermetic git for the fixtures: no user/global hooks, signing, or rewrites.
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@example.invalid
export GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@example.invalid
unset GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE

TMP="$(mktemp -d)" || exit 2
trap 'rm -rf "$TMP"' EXIT

FAILED=0
pass() { echo "  ok   $1"; }
fail() { echo "  FAIL $1"; FAILED=1; }

# Build a synthetic workspace. $1 = case dir, $2 = crate version line for the
# patched crate's manifest, $3 = the Cargo.lock body, and optional $4 = patch
# source URL.
scaffold() {
  local dir="$1" crate_version="$2" lock="$3"
  local patch_source="${4:-https://example.invalid/widget.git}"
  mkdir -p "$dir/vendored/crates/widget"
  cat > "$dir/Cargo.toml" <<EOF
[workspace]
members = ["vendored/crates/widget"]

[patch."$patch_source"]
widget = { path = "vendored/crates/widget" }
EOF
  cat > "$dir/vendored/crates/widget/Cargo.toml" <<EOF
[package]
name = "widget"
$crate_version
edition = "2021"
EOF
  printf '%s' "$lock" > "$dir/Cargo.lock"
}

expect() {
  local want="$1" label="$2" dir="$3" needle="${4:-}"
  local out rc
  out="$(python3 "$GATE" "$dir" 2>&1)"; rc=$?
  check_result "$want" "$label" "$needle" "$out" "$rc"
}

# expect_push WANT LABEL DIR REFS [NEEDLE]: the same, with TRUST_PUSHED_REFS=REFS.
expect_push() {
  local want="$1" label="$2" dir="$3" refs="$4" needle="${5:-}"
  local out rc
  out="$(TRUST_PUSHED_REFS="$refs" python3 "$GATE" "$dir" 2>&1)"; rc=$?
  check_result "$want" "$label" "$needle" "$out" "$rc"
}

check_result() {
  local want="$1" label="$2" needle="$3" out="$4" rc="$5"
  if [ "$rc" != "$want" ]; then
    fail "$label (exit $rc, wanted $want)"; printf '%s\n' "$out" | sed 's/^/       /'
    return
  fi
  # A here-string, not `printf | grep -q`: under pipefail, grep -q exiting at
  # the first match can SIGPIPE the printf and report a present needle as
  # missing (flaked once under parallel load, 2026-09-28).
  if [ -n "$needle" ] && ! grep -q -- "$needle" <<<"$out"; then
    fail "$label (exit ok but output lacks '$needle')"; printf '%s\n' "$out" | sed 's/^/       /'
    return
  fi
  pass "$label"
}

LOCK_ONE='[[package]]
name = "widget"
version = "1.5.0"
'

# 1. manifest version == lock version -> binds.
scaffold "$TMP/binds" 'version = "1.5.0"' "$LOCK_ONE"
expect 0 "matching versions bind" "$TMP/binds" "1 path-redirecting"

# 2. the pin moved across a version bump -> the patch stops applying.
scaffold "$TMP/unbound" 'version = "0.2.0"' "$LOCK_ONE"
expect 1 "version bump under a stale lock is UNBOUND" "$TMP/unbound" "UNBOUND"

# 3. The patched GIT source resolving at ANOTHER version is a SPLIT, not benign
#    coexistence. This case previously asserted exit 0 with the rationale that
#    "another version is a distinct Cargo package identity and may coexist when
#    its dependency requirement cannot accept the patched version". That is true
#    of Cargo's identity rules and FALSE as a health claim, and the difference
#    was measured on 2026-08-28: origin/main carried exactly this shape — ay-core
#    0.17.0 from the submodule path beside ay-core 0.18.0 from
#    git+.../ay.git?rev=45eb977133, because first-party/clean's declarations moved
#    to `version = "0.18.0"` while the ay pin stayed at 0.17.0 — and this gate
#    exited 0 while `./x.py build --stage 2` could not compile
#    rustc_mir_transform ("multiple different versions of crate `ay_core`").
#    A patch that one consumer silently escapes is the failure this gate names.
scaffold "$TMP/coexist" 'version = "1.5.0"' '[[package]]
name = "widget"
version = "1.5.0"

[[package]]
name = "widget"
version = "2.0.0"
source = "git+https://example.invalid/widget.git#deadbeef"
'
expect 1 "the patched git source at another version is a SPLIT" "$TMP/coexist" "SPLIT"

# 3a. ...but `[patch.crates-io]` is the opposite case, and the rule must not
#     swallow it. Semver-major neighbours from the registry (rustc-hash 1.1.0
#     beside 2.1.2) coexist by design in every real Rust graph; a rule that
#     failed on them would be turned off within a day. Measured: without this
#     carve-out the strengthened gate FAILS on a healthy trust tree at
#     [patch."crates-io"] rustc-hash.
scaffold "$TMP/coexist-registry" 'version = "1.5.0"' '[[package]]
name = "widget"
version = "1.5.0"

[[package]]
name = "widget"
version = "2.0.0"
source = "registry+https://github.com/rust-lang/crates.io-index"
' 'crates-io'
expect 0 "a registry other-version neighbour still coexists" "$TMP/coexist-registry" "other-version"

# 3b. The same name+version from the source named by the patch is the exact
#     duplicate the patch must prevent, even when the path row is present. The
#     lock's query/fragment and `.git` spelling are canonicalized deliberately.
scaffold "$TMP/dup" 'version = "1.5.0"' '[[package]]
name = "widget"
version = "1.5.0"

[[package]]
name = "widget"
version = "1.5.0"
source = "git+https://example.invalid/widget?rev=abc123#deadbeef"
'
expect 1 "the patched source cannot resolve beside its replacement" "$TMP/dup" "DUPLICATED"

# 3c. Cargo's CanonicalUrl treats GitHub's supported transports as the same
#     HTTPS source. The gate must not miss that duplicate spelling.
scaffold "$TMP/github-scheme" 'version = "1.5.0"' '[[package]]
name = "widget"
version = "1.5.0"

[[package]]
name = "widget"
version = "1.5.0"
source = "git+git://github.com/owner/widget?rev=abc123#deadbeef"
' 'https://github.com/owner/widget.git'
expect 1 "GitHub transport aliases are the patched source" "$TMP/github-scheme" "DUPLICATED"

# 3d. GitHub repository paths are case-insensitive in Cargo's canonical
#     identity, independently of the transport rule above.
scaffold "$TMP/github-case" 'version = "1.5.0"' '[[package]]
name = "widget"
version = "1.5.0"

[[package]]
name = "widget"
version = "1.5.0"
source = "git+https://github.com/OWNER/WIDGET?rev=abc123#deadbeef"
' 'https://github.com/Owner/Widget.git'
expect 1 "GitHub repository path case is canonical" "$TMP/github-case" "DUPLICATED"

# 3e. url::Url removes an explicit default port before Cargo compares source
#     identities. A spelling with :443 must not evade the duplicate check.
scaffold "$TMP/github-default-port" 'version = "1.5.0"' '[[package]]
name = "widget"
version = "1.5.0"

[[package]]
name = "widget"
version = "1.5.0"
source = "git+https://github.com:443/owner/widget#deadbeef"
' 'https://github.com/owner/widget.git'
expect 1 "a URL default port does not create another source" "$TMP/github-default-port" "DUPLICATED"

# 3f. The original URL parser removes HTTP's :80 before Cargo rewrites a
#     GitHub source to HTTPS. Check that order independently of HTTPS :443.
scaffold "$TMP/github-original-default-port" 'version = "1.5.0"' '[[package]]
name = "widget"
version = "1.5.0"

[[package]]
name = "widget"
version = "1.5.0"
source = "git+https://github.com/owner/widget#deadbeef"
' 'http://github.com:80/owner/widget.git'
expect 1 "the original scheme default port is removed before GitHub rewrite" "$TMP/github-original-default-port" "DUPLICATED"

# 3g. url::Url resolves dot segments before Cargo's CanonicalUrl comparison.
scaffold "$TMP/github-dot-segment" 'version = "1.5.0"' '[[package]]
name = "widget"
version = "1.5.0"

[[package]]
name = "widget"
version = "1.5.0"
source = "git+https://github.com/owner/else/../widget#deadbeef"
' 'https://github.com/owner/widget.git'
expect 1 "URL dot segments do not evade the patched source" "$TMP/github-dot-segment" "DUPLICATED"

# 3h. An empty segment is still a path segment: `..` removes it rather than
#     becoming a no-op. This pins the URL parser's root-aware stack behavior.
scaffold "$TMP/github-double-slash-dot" 'version = "1.5.0"' '[[package]]
name = "widget"
version = "1.5.0"

[[package]]
name = "widget"
version = "1.5.0"
source = "git+https://github.com/owner//../widget#deadbeef"
' 'https://github.com/owner/widget.git'
expect 1 "duplicate slash plus dot segment stays source-identical" "$TMP/github-double-slash-dot" "DUPLICATED"

# 3i. A same-version source outside the explicitly audited URL subset is not
#     waved through as unrelated. This is the fail-closed half of the parser
#     boundary, using a Cargo-supported file URL that this gate does not parse.
scaffold "$TMP/unsupported-source" 'version = "1.5.0"' '[[package]]
name = "widget"
version = "1.5.0"

[[package]]
name = "widget"
version = "1.5.0"
source = "git+file:///tmp/widget#deadbeef"
'
expect 1 "an unaudited source spelling fails closed" "$TMP/unsupported-source" "UNSUPPORTED"

# 3j. WHATWG parses compact/numeric IPv4 spellings into a canonical address.
#     They are deliberately outside the audited DNS subset, so reject rather
#     than compare `127.1` textually with `127.0.0.1` and call them unrelated.
scaffold "$TMP/unsupported-ipv4-source" 'version = "1.5.0"' "$LOCK_ONE" \
  'https://127.1/owner/widget.git'
expect 1 "WHATWG IPv4 source spellings fail closed" "$TMP/unsupported-ipv4-source" "UNSUPPORTED"

# 3k. An unrelated source with the same name and version is a distinct Cargo
#     package identity and may coexist with the path-owned replacement.
scaffold "$TMP/unrelated" 'version = "1.5.0"' '[[package]]
name = "widget"
version = "1.5.0"

[[package]]
name = "widget"
version = "1.5.0"
source = "registry+https://github.com/rust-lang/crates.io-index"
'
expect 0 "same name/version from an unrelated source may coexist" "$TMP/unrelated" "unrelated-source"

# 3l. A sourced row of the right version without the path-owned row is not a
#     binding merely because its name and version happen to match.
scaffold "$TMP/source-only" 'version = "1.5.0"' '[[package]]
name = "widget"
version = "1.5.0"
source = "registry+https://github.com/rust-lang/crates.io-index"
'
expect 1 "a sourced exact version is still UNBOUND" "$TMP/source-only" "UNBOUND"

# 4. the crate is not in the lock at all.
scaffold "$TMP/unlocked" 'version = "1.5.0"' '[[package]]
name = "other"
version = "0.1.0"
'
expect 1 "absent from the lock is UNLOCKED" "$TMP/unlocked" "UNLOCKED"

# 5. `version.workspace = true` resolves against [workspace.package].
mkdir -p "$TMP/wsver/vendored/crates/widget"
cat > "$TMP/wsver/Cargo.toml" <<'EOF'
[workspace]
members = ["vendored/crates/widget"]

[patch."https://example.invalid/widget.git"]
widget = { path = "vendored/crates/widget" }
EOF
cat > "$TMP/wsver/vendored/Cargo.toml" <<'EOF'
[workspace.package]
version = "3.1.0"
EOF
cat > "$TMP/wsver/vendored/crates/widget/Cargo.toml" <<'EOF'
[package]
name = "widget"
version.workspace = true
edition = "2021"
EOF
printf '[[package]]\nname = "widget"\nversion = "3.1.0"\n' > "$TMP/wsver/Cargo.lock"
expect 0 "version.workspace = true resolves upward" "$TMP/wsver" "1 path-redirecting"

# 5b. ...and is judged, not waved through, when it disagrees.
printf '[[package]]\nname = "widget"\nversion = "1.0.0"\n' > "$TMP/wsver/Cargo.lock"
expect 1 "an inherited version still gets judged" "$TMP/wsver" "3.1.0"

# 6. a patch path with no manifest is MISSING -- a patch that points at nothing
#    -- unless it lies inside a gitlink whose submodule worktree is absent (6c).
#    Until 2026-09-27 every missing manifest was "skipped: submodule not checked
#    out", so a typo'd path outside any submodule printed OK for a false reason.
scaffold "$TMP/typo" 'version = "1.5.0"' "$LOCK_ONE"
sed -i.bak 's#vendored/crates/widget" }#vendored/crates/widgt" }#' "$TMP/typo/Cargo.toml"
expect 1 "a typo'd patch path outside any submodule is MISSING" "$TMP/typo" "MISSING"

# 7. a [dependencies] version must never be mistaken for the package version.
scaffold "$TMP/depver" 'version = "1.5.0"' "$LOCK_ONE"
cat >> "$TMP/depver/vendored/crates/widget/Cargo.toml" <<'EOF'

[dependencies]
serde = { version = "9.9.9" }
EOF
expect 0 "a dependency version is not the package version" "$TMP/depver" "1 path-redirecting"

# ---------------------------------------------------------------------------
# Git fixtures. widget is a real submodule at first-party/widget with
# `version.workspace = true`, like first-party/clean:
#   W150  workspace.package 1.5.0
#   W200  workspace.package 2.0.0      (the 8dddf6c755 bump)
#   WMOVE crates/widget -> crates/widget-core (the patched dir is gone)
G="$TMP/git"
mkdir -p "$G"
git init -q -b main "$G/widget"
mkdir -p "$G/widget/crates/widget"
printf '[workspace]\nmembers = ["crates/widget"]\n\n[workspace.package]\nversion = "1.5.0"\n' > "$G/widget/Cargo.toml"
printf '[package]\nname = "widget"\nversion.workspace = true\nedition = "2021"\n' > "$G/widget/crates/widget/Cargo.toml"
git -C "$G/widget" add -A && git -C "$G/widget" commit -qm v1.5.0
W150="$(git -C "$G/widget" rev-parse HEAD)"
sed -i.bak 's/1.5.0/2.0.0/' "$G/widget/Cargo.toml" && rm "$G/widget/Cargo.toml.bak"
git -C "$G/widget" commit -qam v2.0.0
W200="$(git -C "$G/widget" rev-parse HEAD)"
git -C "$G/widget" mv crates/widget crates/widget-core
git -C "$G/widget" commit -qm "move the crate dir"
WMOVE="$(git -C "$G/widget" rev-parse HEAD)"

LOCK_150='[[package]]
name = "widget"
version = "1.5.0"
'
LOCK_200='[[package]]
name = "widget"
version = "2.0.0"
'
LOCK_SPLIT='[[package]]
name = "widget"
version = "1.5.0"

[[package]]
name = "widget"
version = "2.0.0"
source = "git+https://example.invalid/widget.git#deadbeef"
'

S="$G/super"
git init -q -b main "$S"
git clone -q "$G/widget" "$S/first-party/widget"
git -C "$S/first-party/widget" checkout -q "$W150"
cat > "$S/Cargo.toml" <<'EOF'
[workspace]
members = []

[patch."https://example.invalid/widget.git"]
widget = { path = "first-party/widget/crates/widget" }
EOF
printf '[submodule "first-party/widget"]\n\tpath = first-party/widget\n\turl = ../widget\n' > "$S/.gitmodules"
printf '%s' "$LOCK_150" > "$S/Cargo.lock"
git -C "$S" add Cargo.toml Cargo.lock .gitmodules
git -C "$S" update-index --add --cacheinfo "160000,$W150,first-party/widget"
git -C "$S" commit -qm "pin widget 1.5.0"
MAIN="$(git -C "$S" rev-parse HEAD)"
Z=0000000000000000000000000000000000000000

# commit_on BRANCH MESSAGE [PIN] [LOCK]: a commit on BRANCH (from main) that sets
# the widget gitlink and/or Cargo.lock, WITHOUT touching the checkout's files:
# the working tree and submodule checkout stay at main's healthy state.
commit_on() {
  local branch="$1" msg="$2" pin="${3:-}" lock="${4:-}" idx="$TMP/idx.$1" blob
  rm -f "$idx"
  GIT_INDEX_FILE="$idx" git -C "$S" read-tree "$MAIN"
  if [ -n "$pin" ]; then
    GIT_INDEX_FILE="$idx" git -C "$S" update-index --cacheinfo "160000,$pin,first-party/widget"
  fi
  if [ -n "$lock" ]; then
    blob="$(printf '%s' "$lock" | git -C "$S" hash-object -w --stdin)"
    GIT_INDEX_FILE="$idx" git -C "$S" update-index --cacheinfo "100644,$blob,Cargo.lock"
  fi
  local tree commit
  tree="$(GIT_INDEX_FILE="$idx" git -C "$S" write-tree)"
  commit="$(git -C "$S" commit-tree "$tree" -p "$MAIN" -m "$msg")"
  git -C "$S" update-ref "refs/heads/$branch" "$commit"
  printf '%s' "$commit"
}

# 6b. The checked-out pin (== HEAD's gitlink, so pin-coherent) moved the patched
#     crate's directory away: the submodule IS checked out, so this is MISSING,
#     not "skipped: submodule not checked out".
cp -R "$S" "$G/moved"
git -C "$G/moved" update-index --cacheinfo "160000,$WMOVE,first-party/widget"
git -C "$G/moved" commit -qm "pin the rev that moved the crate"
git -C "$G/moved/first-party/widget" checkout -q "$WMOVE"
expect 1 "a checked-out pin without the patched crate is MISSING" "$G/moved" "MISSING"
expect_push 1 "...and the pushed tree pinning it is MISSING too" "$G/moved" \
  "refs/heads/main $(git -C "$G/moved" rev-parse HEAD) refs/heads/main $MAIN" "MISSING"

# 6c. ...but a gitlink whose submodule worktree is genuinely absent (no .git)
#     is still skipped in the working-tree reading: check_pin_coherence.sh's.
git clone -q "$S" "$G/noinit"
expect 0 "a gitlink with no submodule worktree is skipped" "$G/noinit" "skipped: submodule not checked out"

# 8. Healthy working tree and HEAD: the no-push reading and a push of HEAD agree.
expect 0 "the healthy fixture binds (no push)" "$S" "1 path-redirecting"
expect_push 0 "pushing the healthy HEAD binds" "$S" "refs/heads/main $MAIN refs/heads/main $Z" "SUBJECT: the pushed trees"

# 9. [patch-binds-1] a SPLIT lock COMMITTED, the healthy lock only on disk:
#    the push publishes the SPLIT, so it must fail though the disk is fine.
cp -R "$S" "$G/dirty-good"
printf '%s' "$LOCK_SPLIT" > "$G/dirty-good/Cargo.lock"
git -C "$G/dirty-good" commit -qam "split the lock"
printf '%s' "$LOCK_150" > "$G/dirty-good/Cargo.lock"
expect 0 "(control) the healthy uncommitted lock binds on disk" "$G/dirty-good" "1 path-redirecting"
expect_push 1 "a committed SPLIT lock fails though the working tree is healthy" "$G/dirty-good" \
  "refs/heads/main $(git -C "$G/dirty-good" rev-parse HEAD) refs/heads/main $MAIN" "SPLIT"

# 10. [patch-binds-1] `git push origin topic:main` from a healthy HEAD: the
#     pushed ref is not the checkout, and its tree is what is published.
TOPIC_SPLIT="$(commit_on topic-split "split the lock" "" "$LOCK_SPLIT")"
expect_push 1 "a SPLIT topic pushed as main fails from a healthy HEAD" "$S" \
  "refs/heads/topic-split $TOPIC_SPLIT refs/heads/main $MAIN" "refs/heads/topic-split"

# 11. [patch-binds-2] the founding shape: a topic moves the gitlink across
#     1.5.0 -> 2.0.0 and leaves Cargo.lock; the submodule is checked out at
#     main's pin (pin-coherent), so only the pinned manifests can see it.
TOPIC_BUMP="$(commit_on topic-bump "bump the widget pin, not the lock" "$W200" "")"
expect_push 1 "a pushed gitlink moved across a bump without the lock is UNBOUND" "$S" \
  "refs/heads/topic-bump $TOPIC_BUMP refs/heads/main $MAIN" "UNBOUND"
# ...control: the pin and the lock moved in the SAME commit binds.
TOPIC_BOTH="$(commit_on topic-both "bump the pin and the lock" "$W200" "$LOCK_200")"
expect_push 0 "a pushed gitlink moved WITH its lock binds" "$S" \
  "refs/heads/topic-both $TOPIC_BOTH refs/heads/main $MAIN" "1 path-redirecting"
# ...a pin the submodule's object store does not hold is an error, not a pass.
TOPIC_GHOST="$(commit_on topic-ghost "pin an unfetched rev" "1234567890123456789012345678901234567890" "")"
expect_push 1 "a pushed pin missing from the submodule store fails closed" "$S" \
  "refs/heads/topic-ghost $TOPIC_GHOST refs/heads/main $MAIN" "not in its object store"
# ...and so is a pushed pin whose submodule is not initialized here.
git -C "$G/noinit" fetch -q "$S" "refs/heads/topic-both:refs/heads/topic-both"
expect_push 1 "a push with an uninitialized submodule fails closed" "$G/noinit" \
  "refs/heads/topic-both $TOPIC_BOTH refs/heads/main $MAIN" "not initialized"
# ...and a moved-away crate dir in a pushed pin is MISSING (6b's pushed form).
TOPIC_MOVE="$(commit_on topic-move "pin the rev that moved the crate" "$WMOVE" "")"
expect_push 1 "a pushed pin without the patched crate is MISSING" "$S" \
  "refs/heads/topic-move $TOPIC_MOVE refs/heads/main $MAIN" "MISSING"

# 12. [patch-binds-3] the inverse: uncommitted WIP must not block a push whose
#     committed tree is healthy, nor a deletion that publishes no tree.
cp -R "$S" "$G/wip"
printf '%s' "$LOCK_SPLIT" > "$G/wip/Cargo.lock"
expect 1 "(control) the SPLIT WIP fails the no-push reading" "$G/wip" "SPLIT"
expect_push 0 "SPLIT WIP does not block a push of the healthy HEAD" "$G/wip" \
  "refs/heads/main $MAIN refs/heads/main $Z" "1 path-redirecting"
expect_push 0 "a deletion-only push judges nothing and says SKIPPED" "$G/wip" \
  "(delete) $Z refs/heads/scratch $MAIN" "^SKIPPED: "
expect_push 1 "a deletion beside a SPLIT push still fails" "$G/wip" \
  "(delete) $Z refs/heads/scratch $MAIN
refs/heads/topic-split $TOPIC_SPLIT refs/heads/main $MAIN" "SPLIT"

# 13. Push input the gate cannot read fails closed.
expect_push 1 "a malformed TRUST_PUSHED_REFS line fails closed" "$S" \
  "refs/heads/main not-a-sha refs/heads/main $MAIN" "malformed"
expect_push 1 "an unresolvable pushed sha fails closed" "$S" \
  "refs/heads/main 1234567890123456789012345678901234567890 refs/heads/main $MAIN" "UNRESOLVED"

if [ "$FAILED" -eq 0 ]; then
  echo "check_patch_binds tests: PASS"
  exit 0
fi
echo "check_patch_binds tests: FAIL" >&2
exit 1
