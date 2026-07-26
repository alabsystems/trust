#!/bin/bash
# End-to-end test: canonical `targo trust` resolves configuration and
# observational-cache roots from the intended crate or file target, not from
# the caller's shell cwd.
#
# This exercises the standalone local public CLI baseline through:
#   - crate-root invocation
#   - subdirectory invocation under a crate
#   - repo-external invocation with --manifest-path
#   - repo-external single-file invocation
#   - repo-external invocation against a non-root workspace member manifest

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

echo "=== Trust E2E Test: targo trust root resolution ==="
echo

fail_setup() {
    echo "ERROR: $1"
    exit 2
}

fail_test() {
    echo "FAIL: $1"
    exit 1
}

run_public_cli() {
    env -u TRUSTC -u RUSTUP_TOOLCHAIN -u RUSTC -u RUSTDOC \
        -u RUSTFLAGS -u CARGO_ENCODED_RUSTFLAGS \
        -u RUSTC_WRAPPER -u RUSTC_WORKSPACE_WRAPPER \
        -u CARGO_BUILD_RUSTC -u CARGO_BUILD_RUSTDOC \
        -u CARGO_BUILD_RUSTC_WRAPPER -u CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER \
        "$TRUST_TARGO" trust "$@"
}

require_command() {
    local cmd="$1"
    local install_hint="$2"
    if ! command -v "$cmd" >/dev/null 2>&1; then
        fail_setup "$cmd not found on PATH. $install_hint"
    fi
}

assert_terminal_report() {
    local stderr_file="$1"
    local expected_symbol="$2"
    local expected_level="$3"

    local output
    output="$(cat "$stderr_file")"

    if grep -q "falling back to standalone source analysis" <<<"$output"; then
        fail_setup "standalone Trust toolchain is visible, but targo trust fell back to source inventory"
    fi
    if ! grep -q "using native compiler" <<<"$output"; then
        fail_setup "standalone Trust toolchain is visible, but targo trust did not use a native compiler"
    fi
    if ! grep -q "=== Trust Verification Report ===" <<<"$output"; then
        fail_test "terminal mode did not render the human report"
    fi
    if ! grep -q "Level: $expected_level" <<<"$output"; then
        fail_test "terminal mode did not use the expected $expected_level configuration"
    fi
    if ! grep -q "$expected_symbol" <<<"$output"; then
        fail_test "terminal mode did not report the expected symbol $expected_symbol"
    fi
    if grep -q "TRUST_JSON:" <<<"$output"; then
        fail_test "terminal mode leaked raw TRUST_JSON transport"
    fi
}

assert_persisted_verification_cache() {
    local root="$1"
    local cache="$root/target/trust-cache/verification.json"

    if [ ! -f "$cache" ] || [ -L "$cache" ]; then
        fail_test "verification-result snapshot is missing or not an exact regular file: $cache"
    fi
}

assert_no_persisted_verification_cache() {
    local root cache
    for root in "$@"; do
        cache="$root/target/trust-cache/verification.json"
        # `-e` catches all live entries and `-L` also catches dangling
        # symlinks at an incorrectly selected root.
        if [ -e "$cache" ] || [ -L "$cache" ]; then
            fail_test "verification-result snapshot was persisted at the wrong root: $cache"
        fi
    done
}

run_check_case() {
    local workdir="$1"
    local stderr_file="$2"
    shift 2

    local stdout_file="${stderr_file%.stderr}.stdout"
    local exit_code=0
    (
        cd "$workdir"
        run_public_cli check "$@" >"$stdout_file" 2>"$stderr_file"
    ) || exit_code=$?

    if [ "$exit_code" -gt 1 ]; then
        fail_test "terminal mode exited with unexpected status $exit_code for args: $*"
    fi
}

find_standalone_targo() {
    local candidate
    while IFS= read -r candidate; do
        if [ -x "$candidate" ] && [ -x "$(dirname "$candidate")/trustc" ]; then
            printf '%s\n' "$candidate"
            return 0
        fi
    done < <(find "$TRUST_ROOT/build" -path "*/stage2/bin/targo" -type f -perm -111 -print 2>/dev/null | sort -r)

    return 1
}

if ! TRUST_TARGO="$(find_standalone_targo)"; then
    fail_setup "repo-local stage2 Trust targo/trustc not found under build/*/stage2/bin. Run ./x.py build --stage 2."
fi
TRUSTC_BIN="$(dirname "$TRUST_TARGO")/trustc"
if ! run_public_cli --help >/dev/null 2>&1; then
    fail_setup "standalone targo does not expose the canonical \`targo trust\` subcommand"
fi

echo "Using targo:       $TRUST_TARGO"
echo "Using trustc:       $TRUSTC_BIN"
echo

TMP_DIR="$(mktemp -d /tmp/targo_trust_root_resolution_XXXXXX)"
trap 'rm -rf "$TMP_DIR"' EXIT

CRATE_DIR="$TMP_DIR/rooted-crate"
SUBDIR="$CRATE_DIR/src/nested/deeper"
UNRELATED_CWD="$TMP_DIR/unrelated"
SINGLE_DIR="$TMP_DIR/single-file"
WORKSPACE_DIR="$TMP_DIR/workspace"
MEMBER_DIR="$WORKSPACE_DIR/member-crate"

mkdir -p "$CRATE_DIR/src" "$SUBDIR" "$UNRELATED_CWD" "$SINGLE_DIR" "$MEMBER_DIR/src"

cat > "$CRATE_DIR/Cargo.toml" <<'TOML'
[package]
name = "rooted-crate"
version = "0.1.0"
edition = "2021"
TOML

cat > "$CRATE_DIR/trust.toml" <<'TOML'
level = "L2"
TOML

cat > "$CRATE_DIR/src/lib.rs" <<'RUST'
pub fn midpoint(a: i32, b: i32) -> i32 {
    a + (b - a) / 2
}

#[cfg(test)]
mod tests {
    use super::midpoint;

    #[test]
    fn computes_midpoint() {
        assert_eq!(midpoint(2, 6), 4);
    }
}
RUST

cat > "$SINGLE_DIR/trust.toml" <<'TOML'
level = "L2"
TOML

cat > "$SINGLE_DIR/demo.rs" <<'RUST'
pub fn demo_value(x: i32) -> i32 {
    x + 1
}

fn main() {
    println!("{}", demo_value(4));
}
RUST

cat > "$WORKSPACE_DIR/Cargo.toml" <<'TOML'
[workspace]
members = ["member-crate"]
resolver = "2"
TOML

cat > "$WORKSPACE_DIR/trust.toml" <<'TOML'
level = "L0"
TOML

cat > "$MEMBER_DIR/Cargo.toml" <<'TOML'
[package]
name = "member-crate"
version = "0.1.0"
edition = "2021"
TOML

cat > "$MEMBER_DIR/trust.toml" <<'TOML'
level = "L2"
TOML

cat > "$MEMBER_DIR/src/lib.rs" <<'RUST'
pub fn member_value(x: i32) -> i32 {
    x * 2
}

#[cfg(test)]
mod tests {
    use super::member_value;

    #[test]
    fn doubles_value() {
        assert_eq!(member_value(4), 8);
    }
}
RUST

echo "Using targo:       $TRUST_TARGO"
echo "Using trustc:       $TRUSTC_BIN"
echo

echo "--- crate root"
rm -rf "$CRATE_DIR/target"
ROOT_STDERR="$TMP_DIR/root.stderr"
run_check_case "$CRATE_DIR" "$ROOT_STDERR"
assert_terminal_report "$ROOT_STDERR" "midpoint" "L2"
assert_persisted_verification_cache "$CRATE_DIR"

echo "--- crate subdirectory"
rm -rf "$CRATE_DIR/target" "$SUBDIR/target"
SUBDIR_STDERR="$TMP_DIR/subdir.stderr"
run_check_case "$SUBDIR" "$SUBDIR_STDERR"
assert_terminal_report "$SUBDIR_STDERR" "midpoint" "L2"
assert_persisted_verification_cache "$CRATE_DIR"
assert_no_persisted_verification_cache "$SUBDIR"

echo "--- unrelated cwd with --manifest-path"
rm -rf "$CRATE_DIR/target" "$UNRELATED_CWD/target"
MANIFEST_STDERR="$TMP_DIR/manifest.stderr"
run_check_case "$UNRELATED_CWD" "$MANIFEST_STDERR" --manifest-path "$CRATE_DIR/Cargo.toml"
assert_terminal_report "$MANIFEST_STDERR" "midpoint" "L2"
assert_persisted_verification_cache "$CRATE_DIR"
assert_no_persisted_verification_cache "$UNRELATED_CWD"

echo "--- unrelated cwd single-file mode"
rm -rf "$SINGLE_DIR/target" "$UNRELATED_CWD/target"
SINGLE_STDERR="$TMP_DIR/single.stderr"
run_check_case "$UNRELATED_CWD" "$SINGLE_STDERR" "$SINGLE_DIR/demo.rs"
assert_terminal_report "$SINGLE_STDERR" "demo_value" "L2"
assert_persisted_verification_cache "$SINGLE_DIR"
assert_no_persisted_verification_cache "$UNRELATED_CWD"

echo "--- unrelated cwd with non-root workspace member --manifest-path"
rm -rf "$MEMBER_DIR/target" "$WORKSPACE_DIR/target" "$UNRELATED_CWD/target"
MEMBER_STDERR="$TMP_DIR/member.stderr"
run_check_case "$UNRELATED_CWD" "$MEMBER_STDERR" --manifest-path "$MEMBER_DIR/Cargo.toml"
assert_terminal_report "$MEMBER_STDERR" "member_value" "L2"
assert_persisted_verification_cache "$MEMBER_DIR"
assert_no_persisted_verification_cache "$WORKSPACE_DIR" "$UNRELATED_CWD"

echo
echo "=== targo trust root resolution test: PASS ==="
