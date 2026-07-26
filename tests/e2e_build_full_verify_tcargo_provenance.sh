#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/trust-full-verify-targo.XXXXXX")"
trap 'rm -rf "$TMP_DIR"' EXIT

fail() {
    echo "FAIL: $*" >&2
    exit 1
}

write_exe() {
    local path="$1"
    local body="$2"
    mkdir -p "$(dirname "$path")"
    printf '%s\n' "$body" >"$path"
    chmod +x "$path"
}

write_fake_sysroot() {
    local sysroot="$1"
    local targo_log="$2"

    mkdir -p "$sysroot/bin"

    local tool
    # Trust: produced stage2 sysroot exposes the targo/tippy bin surface.
    for tool in \
        trustc trustdoc targo-trust trustd trustfmt targo-fmt tippy targo-tippy tippy-driver trust-analyzer
    do
        write_exe "$sysroot/bin/$tool" '#!/usr/bin/env sh
if [ "${1:-}" = "--version" ] || [ "${1:-}" = "-Vv" ]; then
    echo "$(basename "$0") 0.1.0 (trust-test)"
fi
exit 0'
    done

    write_exe "$sysroot/bin/targo" "#!/usr/bin/env sh
if [ \"\${1:-}\" = \"--version\" ] || [ \"\${1:-}\" = \"-Vv\" ]; then
    echo \"cargo 0.1.0 (trust-test)\"
    echo \"binary: targo\"
    exit 0
fi
printf '%s\n' \"\$*\" >> '$targo_log'
exit 0"

    # Trust: the Rust-compatible aliases must be the same artifact as their
    # canonical Trust tools (hardened same-artifact alias gate).
    cp "$sysroot/bin/trustc" "$sysroot/bin/rustc"
    cp "$sysroot/bin/targo" "$sysroot/bin/cargo"
    chmod +x "$sysroot/bin/rustc" "$sysroot/bin/cargo"
}

write_fixture_repo() {
    local repo="$1"
    local targo_log="$2"

    mkdir -p "$repo/scripts"
    mkdir -p "$repo/scripts/lib"
    cp "$ROOT/scripts/build.sh" "$repo/scripts/build.sh"
    cp "$ROOT/scripts/lib/trust_toolchain_surface.sh" \
        "$repo/scripts/lib/trust_toolchain_surface.sh"
    chmod +x "$repo/scripts/build.sh"
    write_fake_sysroot "$repo/build/host/stage2" "$targo_log"
}

write_ambient_targo() {
    local path="$1"
    local marker="$2"

    write_exe "$path" "#!/usr/bin/env sh
touch '$marker'
exit 99"
}

assert_contains() {
    local file="$1"
    local needle="$2"

    if ! grep -qF -- "$needle" "$file"; then
        echo "--- $file ---" >&2
        cat "$file" >&2
        echo "--------------" >&2
        fail "expected $file to contain: $needle"
    fi
}

assert_not_contains_regex() {
    local file="$1"
    local pattern="$2"

    if grep -Eq -- "$pattern" "$file"; then
        echo "--- $file ---" >&2
        cat "$file" >&2
        echo "--------------" >&2
        fail "did not expect $file to match: $pattern"
    fi
}

echo "--- full-verify command plan uses canonical stage2 targo"
GOOD_REPO="$TMP_DIR/good"
GOOD_LOG="$GOOD_REPO/stub.log"
GOOD_OUT="$GOOD_REPO/output.log"
GOOD_TARGO_LOG="$GOOD_REPO/targo.log"
GOOD_AMBIENT_MARKER="$GOOD_REPO/ambient-targo-used"
GOOD_AMBIENT_BIN="$GOOD_REPO/fake-bin"
write_fixture_repo "$GOOD_REPO" "$GOOD_TARGO_LOG"
mkdir -p "$GOOD_AMBIENT_BIN"
write_ambient_targo "$GOOD_AMBIENT_BIN/targo" "$GOOD_AMBIENT_MARKER"

PATH="$GOOD_AMBIENT_BIN:$PATH" \
    TRUST_BUILD_STUB=1 \
    TRUST_BUILD_ALLOW_NON_RELEASE_STUBS=1 \
    TRUST_BUILD_STUB_LOG="$GOOD_LOG" \
    bash "$GOOD_REPO/scripts/build.sh" full-verify >"$GOOD_OUT" 2>&1 \
    || {
        cat "$GOOD_OUT" >&2
        fail "stubbed full-verify should pass with canonical stage2 targo"
    }

GOOD_REPO_ROOT="$(cd "$GOOD_REPO" && pwd)"
GOOD_REPO_REAL="$(cd "$GOOD_REPO" && pwd -P)"
GOOD_TARGO="$GOOD_REPO_REAL/build/host/stage2/bin/targo"
GOOD_BOOTSTRAP_TARGET="$GOOD_REPO_ROOT/build/full-verify/bootstrap-target"
GOOD_BOOTSTRAP_MANIFEST="$GOOD_REPO_ROOT/src/bootstrap/Cargo.toml"
assert_contains "$GOOD_OUT" "Using canonical full-verify targo: $GOOD_TARGO"
assert_contains "$GOOD_LOG" "$GOOD_TARGO trust verify self"
assert_contains "$GOOD_LOG" "TRUST_VERIFY_WORKER_THREADS=2 $GOOD_TARGO trust verify self"
assert_contains "$GOOD_LOG" "--stage-command env -u CARGO_TARGET_DIR $GOOD_TARGO --unverified run --locked --offline --target-dir $GOOD_BOOTSTRAP_TARGET --manifest-path $GOOD_BOOTSTRAP_MANIFEST -- --src $GOOD_REPO_ROOT build"
assert_contains "$GOOD_LOG" "--set build.full-bootstrap=true"
assert_contains "$GOOD_LOG" "$GOOD_TARGO trust domination upstream-tests --release"
assert_contains "$GOOD_LOG" "$GOOD_TARGO trust deps validate"
assert_not_contains_regex "$GOOD_LOG" $'\ttargo trust'
assert_not_contains_regex "$GOOD_LOG" '--stage-command \./x\.py'
assert_not_contains_regex "$GOOD_LOG" 'python'
assert_not_contains_regex "$GOOD_LOG" 'src/bootstrap/target'
if [[ -e "$GOOD_AMBIENT_MARKER" ]]; then
    fail "ambient PATH targo was invoked during full-verify command planning"
fi

echo "--- missing canonical stage2 targo rejects ambient PATH targo"
MISSING_REPO="$TMP_DIR/missing"
MISSING_LOG="$MISSING_REPO/stub.log"
MISSING_OUT="$MISSING_REPO/output.log"
MISSING_TARGO_LOG="$MISSING_REPO/targo.log"
MISSING_AMBIENT_MARKER="$MISSING_REPO/ambient-targo-used"
MISSING_AMBIENT_BIN="$MISSING_REPO/fake-bin"
write_fixture_repo "$MISSING_REPO" "$MISSING_TARGO_LOG"
rm -f "$MISSING_REPO/build/host/stage2/bin/targo"
mkdir -p "$MISSING_AMBIENT_BIN"
write_ambient_targo "$MISSING_AMBIENT_BIN/targo" "$MISSING_AMBIENT_MARKER"

missing_rc=0
PATH="$MISSING_AMBIENT_BIN:$PATH" \
    TRUST_BUILD_STUB=1 \
    TRUST_BUILD_ALLOW_NON_RELEASE_STUBS=1 \
    TRUST_BUILD_STUB_LOG="$MISSING_LOG" \
    bash "$MISSING_REPO/scripts/build.sh" full-verify >"$MISSING_OUT" 2>&1 \
    || missing_rc=$?
if [[ "$missing_rc" -eq 0 ]]; then
    fail "stubbed full-verify should fail when canonical stage2 targo is missing"
fi
assert_contains "$MISSING_OUT" "fresh Trust sysroot with canonical Trust tools not found"
if [[ -e "$MISSING_AMBIENT_MARKER" ]]; then
    fail "ambient PATH targo was invoked despite missing canonical stage2 targo"
fi
if [[ -e "$MISSING_LOG" ]]; then
    fail "full-verify should not emit a command plan after targo provenance fails"
fi

echo "--- external configured sysroot is rejected"
EXTERNAL_REPO="$TMP_DIR/external-override"
EXTERNAL_LOG="$EXTERNAL_REPO/stub.log"
EXTERNAL_OUT="$EXTERNAL_REPO/output.log"
EXTERNAL_TARGO_LOG="$EXTERNAL_REPO/targo.log"
EXTERNAL_AMBIENT_MARKER="$EXTERNAL_REPO/ambient-targo-used"
EXTERNAL_AMBIENT_BIN="$EXTERNAL_REPO/fake-bin"
EXTERNAL_SYSROOT="$TMP_DIR/outside-stage2"
write_fixture_repo "$EXTERNAL_REPO" "$EXTERNAL_TARGO_LOG"
write_fake_sysroot "$EXTERNAL_SYSROOT" "$EXTERNAL_TARGO_LOG"
mkdir -p "$EXTERNAL_AMBIENT_BIN"
write_ambient_targo "$EXTERNAL_AMBIENT_BIN/targo" "$EXTERNAL_AMBIENT_MARKER"

external_rc=0
PATH="$EXTERNAL_AMBIENT_BIN:$PATH" \
    TRUST_BUILD_STUB=1 \
    TRUST_BUILD_ALLOW_NON_RELEASE_STUBS=1 \
    TRUST_FULL_VERIFY_TRUST_SYSROOT="$EXTERNAL_SYSROOT" \
    TRUST_BUILD_STUB_LOG="$EXTERNAL_LOG" \
    bash "$EXTERNAL_REPO/scripts/build.sh" full-verify >"$EXTERNAL_OUT" 2>&1 \
    || external_rc=$?
if [[ "$external_rc" -eq 0 ]]; then
    fail "stubbed full-verify should fail when configured sysroot is outside the repo"
fi
assert_contains "$EXTERNAL_OUT" "TRUST_FULL_VERIFY_TRUST_SYSROOT must resolve to a repo-local build/<host>/stage2 sysroot"
if [[ -e "$EXTERNAL_AMBIENT_MARKER" ]]; then
    fail "ambient PATH targo was invoked while rejecting external configured sysroot"
fi
if [[ -e "$EXTERNAL_LOG" ]]; then
    fail "full-verify should not emit a command plan after external sysroot provenance fails"
fi

echo "--- configured repo-local sysroot without trustd is rejected"
MISSING_TRUSTD_REPO="$TMP_DIR/configured-missing-trustd"
MISSING_TRUSTD_LOG="$MISSING_TRUSTD_REPO/stub.log"
MISSING_TRUSTD_OUT="$MISSING_TRUSTD_REPO/output.log"
MISSING_TRUSTD_TARGO_LOG="$MISSING_TRUSTD_REPO/targo.log"
write_fixture_repo "$MISSING_TRUSTD_REPO" "$MISSING_TRUSTD_TARGO_LOG"
rm -f "$MISSING_TRUSTD_REPO/build/host/stage2/bin/trustd"

missing_trustd_rc=0
TRUST_BUILD_STUB=1 \
    TRUST_BUILD_ALLOW_NON_RELEASE_STUBS=1 \
    TRUST_FULL_VERIFY_TRUST_SYSROOT="$MISSING_TRUSTD_REPO/build/host/stage2" \
    TRUST_BUILD_STUB_LOG="$MISSING_TRUSTD_LOG" \
    bash "$MISSING_TRUSTD_REPO/scripts/build.sh" full-verify \
        >"$MISSING_TRUSTD_OUT" 2>&1 \
    || missing_trustd_rc=$?
if [[ "$missing_trustd_rc" -eq 0 ]]; then
    fail "stubbed full-verify should fail when configured stage2 trustd is missing"
fi
assert_contains \
    "$MISSING_TRUSTD_OUT" \
    "TRUST_FULL_VERIFY_TRUST_SYSROOT rejected its canonical tool surface: canonical trustd is not an exact regular executable"
if [[ -e "$MISSING_TRUSTD_LOG" ]]; then
    fail "full-verify should not emit a command plan after configured trustd validation fails"
fi

echo "--- configured canonical leaves reject symlinks and executable directories"
ln -s targo "$MISSING_TRUSTD_REPO/build/host/stage2/bin/trustd"
symlink_trustd_rc=0
TRUST_BUILD_STUB=1 \
    TRUST_BUILD_ALLOW_NON_RELEASE_STUBS=1 \
    TRUST_FULL_VERIFY_TRUST_SYSROOT="$MISSING_TRUSTD_REPO/build/host/stage2" \
    bash "$MISSING_TRUSTD_REPO/scripts/build.sh" full-verify \
        >"$MISSING_TRUSTD_OUT" 2>&1 \
    || symlink_trustd_rc=$?
if [[ "$symlink_trustd_rc" -eq 0 ]]; then
    fail "stubbed full-verify should reject a symlinked canonical trustd"
fi
assert_contains "$MISSING_TRUSTD_OUT" "canonical trustd is not an exact regular executable"

rm -f "$MISSING_TRUSTD_REPO/build/host/stage2/bin/trustd"
mkdir "$MISSING_TRUSTD_REPO/build/host/stage2/bin/trustd"
chmod +x "$MISSING_TRUSTD_REPO/build/host/stage2/bin/trustd"
directory_trustd_rc=0
TRUST_BUILD_STUB=1 \
    TRUST_BUILD_ALLOW_NON_RELEASE_STUBS=1 \
    TRUST_FULL_VERIFY_TRUST_SYSROOT="$MISSING_TRUSTD_REPO/build/host/stage2" \
    bash "$MISSING_TRUSTD_REPO/scripts/build.sh" full-verify \
        >"$MISSING_TRUSTD_OUT" 2>&1 \
    || directory_trustd_rc=$?
if [[ "$directory_trustd_rc" -eq 0 ]]; then
    fail "stubbed full-verify should reject an executable directory as canonical trustd"
fi
assert_contains "$MISSING_TRUSTD_OUT" "canonical trustd is not an exact regular executable"

echo "build full-verify targo provenance regressions passed"
