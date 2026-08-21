#!/usr/bin/env bash
# Self-test for scripts/check_patch_binds.py.
#
# The gate's whole value is that it distinguishes four states that look alike in
# a build log, so each one gets a case here: BINDS, UNBOUND (the version moved
# out from under the lock), DUPLICATED (a second instance already resolved), and
# SKIPPED (the submodule is simply not checked out, which is a different gate's
# problem and must not be reported as this one's).
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
# patched crate's manifest, $3 = the Cargo.lock body.
scaffold() {
  local dir="$1" crate_version="$2" lock="$3"
  mkdir -p "$dir/vendored/crates/widget"
  cat > "$dir/Cargo.toml" <<EOF
[workspace]
members = ["vendored/crates/widget"]

[patch."https://example.invalid/widget.git"]
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

# 3. two copies already in the lock -> the patch failed to prevent an instance.
scaffold "$TMP/dup" 'version = "1.5.0"' '[[package]]
name = "widget"
version = "1.5.0"

[[package]]
name = "widget"
version = "2.0.0"
source = "git+https://example.invalid/widget.git#deadbeef"
'
expect 1 "two lock entries are DUPLICATED" "$TMP/dup" "DUPLICATED"

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
