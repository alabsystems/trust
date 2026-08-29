#!/usr/bin/env bash
# Self-test for scripts/check_patch_binds.py.
#
# The gate's whole value is that it distinguishes states that look alike in a
# build log, so each gets a case here: BINDS, UNBOUND (the version moved out
# from under the lock), DUPLICATED (the source named by the patch also
# resolved), compatible coexistence at another version or unrelated source,
# and SKIPPED (the submodule is simply not checked out, which is a different
# gate's problem and must not be reported as this one's).
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
GATE="$REPO_ROOT/scripts/check_patch_binds.py"
[ -f "$GATE" ] || { echo "check_patch_binds tests: no $GATE" >&2; exit 2; }

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
  if [ "$rc" != "$want" ]; then
    fail "$label (exit $rc, wanted $want)"; printf '%s\n' "$out" | sed 's/^/       /'
    return
  fi
  if [ -n "$needle" ] && ! printf '%s' "$out" | grep -q "$needle"; then
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

# 3. Another version is a distinct Cargo package identity and may coexist when
#    its dependency requirement cannot accept the patched version.
scaffold "$TMP/coexist" 'version = "1.5.0"' '[[package]]
name = "widget"
version = "1.5.0"

[[package]]
name = "widget"
version = "2.0.0"
source = "git+https://example.invalid/widget.git#deadbeef"
'
expect 0 "another package version may coexist" "$TMP/coexist" "other-version"

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

# 6. an un-checked-out submodule is SKIPPED, not failed: that is
#    check_pin_coherence.sh's finding, and duplicating it here would only teach
#    lanes to ignore this gate in every fresh worktree.
scaffold "$TMP/skip" 'version = "1.5.0"' "$LOCK_ONE"
rm -rf "$TMP/skip/vendored"
expect 0 "missing submodule worktree is skipped" "$TMP/skip" "skipped"

# 7. a [dependencies] version must never be mistaken for the package version.
scaffold "$TMP/depver" 'version = "1.5.0"' "$LOCK_ONE"
cat >> "$TMP/depver/vendored/crates/widget/Cargo.toml" <<'EOF'

[dependencies]
serde = { version = "9.9.9" }
EOF
expect 0 "a dependency version is not the package version" "$TMP/depver" "1 path-redirecting"

if [ "$FAILED" -eq 0 ]; then
  echo "check_patch_binds tests: PASS"
  exit 0
fi
echo "check_patch_binds tests: FAIL" >&2
exit 1
