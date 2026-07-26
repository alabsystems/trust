#!/bin/bash
# Differential parity test: inherited upstream rustc vs trustc with verification explicitly disabled.
#
# This is the baseline compiler-correctness contract:
# when trust verification is OFF, trustc should behave like the inherited upstream compiler.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

echo "=== Trust E2E Test: semantic parity with inherited upstream ==="
echo

find_trustc() {
    local candidates=(
        "$TRUST_ROOT/build/host/stage2/bin/trustc"
        "$TRUST_ROOT/build/host/stage1/bin/trustc"
        "$TRUST_ROOT/build/aarch64-apple-darwin/stage2/bin/trustc"
        "$TRUST_ROOT/build/aarch64-apple-darwin/stage1/bin/trustc"
        "$TRUST_ROOT/build/x86_64-unknown-linux-gnu/stage2/bin/trustc"
        "$TRUST_ROOT/build/x86_64-unknown-linux-gnu/stage1/bin/trustc"
        "$TRUST_ROOT/build/x86_64-apple-darwin/stage2/bin/trustc"
        "$TRUST_ROOT/build/x86_64-apple-darwin/stage1/bin/trustc"
    )
    local candidate
    for candidate in "${candidates[@]}"; do
        if [ -x "$candidate" ]; then
            echo "$candidate"
            return 0
        fi
    done
    return 1
}

if ! TRUSTC_BIN="$(find_trustc)"; then
    echo "SKIP: built trustc compiler not found (run ./x.py build first)"
    exit 0
fi

# The e2e harness prepends the stage2 bin dir to PATH, so a bare `rustc`
# lookup can resolve to the Trust toolchain's same-sysroot compatibility
# alias. That is not an upstream compiler; reject it below.
HOST_RUSTUP_BIN="$(command -v rustup 2>/dev/null || true)"
if [ -z "$HOST_RUSTUP_BIN" ] && [ -x "${CARGO_HOME:-$HOME/.cargo}/bin/rustup" ]; then
    HOST_RUSTUP_BIN="${CARGO_HOME:-$HOME/.cargo}/bin/rustup"
fi

if [ -n "${UPSTREAM_RUSTC:-}" ]; then
    UPSTREAM_BIN=("$UPSTREAM_RUSTC")
elif [ -n "$HOST_RUSTUP_BIN" ] && "$HOST_RUSTUP_BIN" which --toolchain stable rustc >/dev/null 2>&1; then
    UPSTREAM_BIN=("$HOST_RUSTUP_BIN" run stable rustc)
elif command -v rustc >/dev/null 2>&1; then
    UPSTREAM_BIN=(rustc)
else
    echo "SKIP: no external upstream rustc found (set UPSTREAM_RUSTC or install stable)"
    exit 0
fi

UPSTREAM_IDENTITY="$("${UPSTREAM_BIN[@]}" --version 2>/dev/null || true)"
case "$UPSTREAM_IDENTITY" in
    *trustc*)
        echo "SKIP: discovered rustc is the Trust toolchain alias, not an upstream compiler (set UPSTREAM_RUSTC or install stable)"
        exit 0
        ;;
    rustc\ *) ;;
    *)
        echo "SKIP: discovered upstream rustc did not report a usable identity: ${UPSTREAM_IDENTITY:-<none>}"
        exit 0
        ;;
esac

echo "trust compiler: $TRUSTC_BIN"
echo "upstream rustc: ${UPSTREAM_BIN[*]}"
echo
TRUSTC_PARITY_CMD=("$TRUSTC_BIN" -Z trust-verify=off)

TMP_DIR="$(mktemp -d /tmp/trust_parity_XXXXXX)"
trap 'rm -rf "$TMP_DIR"' EXIT

SUCCESS_RS="$TMP_DIR/parity_success.rs"
LIB_RS="$TMP_DIR/parity_lib.rs"
FAIL_RS="$TMP_DIR/parity_fail.rs"

cat > "$SUCCESS_RS" <<'RUST'
fn midpoint(a: i64, b: i64) -> i64 {
    a + (b - a) / 2
}

fn checksum(xs: &[i64]) -> i64 {
    xs.iter().enumerate().map(|(i, x)| *x * i as i64).sum()
}

fn main() {
    let xs = [2, 4, 6, 8];
    println!("{} {}", midpoint(10, 14), checksum(&xs));
}
RUST

cat > "$LIB_RS" <<'RUST'
pub enum Maybe<T> {
    Some(T),
    None,
}

pub fn map_or<T, U>(value: Maybe<T>, default: U, f: impl FnOnce(T) -> U) -> U {
    match value {
        Maybe::Some(v) => f(v),
        Maybe::None => default,
    }
}
RUST

cat > "$FAIL_RS" <<'RUST'
fn main() {
    let _x: u32 = "not a u32";
}
RUST

PASS=0
FAIL=0

pass() {
    echo "  PASS: $1"
    PASS=$((PASS + 1))
}

fail() {
    echo "  FAIL: $1"
    FAIL=$((FAIL + 1))
}

run_capture() {
    local stdout_file="$1"
    local stderr_file="$2"
    shift 2
    local exit_code=0
    "$@" >"$stdout_file" 2>"$stderr_file" || exit_code=$?
    echo "$exit_code"
}

require_empty_stderr() {
    local label="$1"
    local file="$2"
    if [ ! -s "$file" ]; then
        pass "$label stderr is empty"
    else
        echo "--- $label stderr ---"
        cat "$file"
        echo "--- end stderr ---"
        fail "$label emitted unexpected stderr"
    fi
}

check_no_trust_output() {
    local label="$1"
    local file="$2"
    if grep -q 'TRUST_JSON:\|Trust Verification Report' "$file"; then
        fail "$label emitted trust verification output with verification disabled"
    else
        pass "$label emitted no trust verification output with -Z trust-verify=off"
    fi
}

echo "[1] Run-and-compare successful binary"
UP_SUCCESS_BIN="$TMP_DIR/up_success"
TR_SUCCESS_BIN="$TMP_DIR/tr_success"
UP_SUCCESS_STDOUT="$TMP_DIR/up_success.stdout"
UP_SUCCESS_STDERR="$TMP_DIR/up_success.stderr"
TR_SUCCESS_STDOUT="$TMP_DIR/tr_success.stdout"
TR_SUCCESS_STDERR="$TMP_DIR/tr_success.stderr"

up_exit=$(run_capture "$UP_SUCCESS_STDOUT" "$UP_SUCCESS_STDERR" "${UPSTREAM_BIN[@]}" --edition 2021 "$SUCCESS_RS" -o "$UP_SUCCESS_BIN")
tr_exit=$(run_capture "$TR_SUCCESS_STDOUT" "$TR_SUCCESS_STDERR" "${TRUSTC_PARITY_CMD[@]}" --edition 2021 "$SUCCESS_RS" -o "$TR_SUCCESS_BIN")

if [ "$up_exit" -eq 0 ] && [ "$tr_exit" -eq 0 ]; then
    pass "Both compilers build parity_success.rs"
else
    fail "Compile exits differ for parity_success.rs (upstream=$up_exit, trust=$tr_exit)"
fi

require_empty_stderr "upstream compile success" "$UP_SUCCESS_STDERR"
require_empty_stderr "Trust compile success" "$TR_SUCCESS_STDERR"
check_no_trust_output "Trust compile success" "$TR_SUCCESS_STDERR"

UP_RUN_STDOUT="$TMP_DIR/up_run.stdout"
UP_RUN_STDERR="$TMP_DIR/up_run.stderr"
TR_RUN_STDOUT="$TMP_DIR/tr_run.stdout"
TR_RUN_STDERR="$TMP_DIR/tr_run.stderr"

up_run_exit=$(run_capture "$UP_RUN_STDOUT" "$UP_RUN_STDERR" "$UP_SUCCESS_BIN")
tr_run_exit=$(run_capture "$TR_RUN_STDOUT" "$TR_RUN_STDERR" "$TR_SUCCESS_BIN")

if [ "$up_run_exit" -eq 0 ] && [ "$tr_run_exit" -eq 0 ]; then
    pass "Both binaries run successfully"
else
    fail "Runtime exits differ (upstream=$up_run_exit, trust=$tr_run_exit)"
fi

if cmp -s "$UP_RUN_STDOUT" "$TR_RUN_STDOUT"; then
    pass "Runtime stdout matches"
else
    echo "--- upstream stdout ---"
    cat "$UP_RUN_STDOUT"
    echo "--- Trust stdout ---"
    cat "$TR_RUN_STDOUT"
    fail "Runtime stdout differs"
fi

require_empty_stderr "upstream runtime" "$UP_RUN_STDERR"
require_empty_stderr "Trust runtime" "$TR_RUN_STDERR"

echo
echo "[2] Compile library metadata without behavioral drift"
UP_LIB_STDOUT="$TMP_DIR/up_lib.stdout"
UP_LIB_STDERR="$TMP_DIR/up_lib.stderr"
TR_LIB_STDOUT="$TMP_DIR/tr_lib.stdout"
TR_LIB_STDERR="$TMP_DIR/tr_lib.stderr"

up_lib_exit=$(run_capture "$UP_LIB_STDOUT" "$UP_LIB_STDERR" "${UPSTREAM_BIN[@]}" --edition 2021 --crate-type lib --emit metadata "$LIB_RS" -o "$TMP_DIR/up_lib.rmeta")
tr_lib_exit=$(run_capture "$TR_LIB_STDOUT" "$TR_LIB_STDERR" "${TRUSTC_PARITY_CMD[@]}" --edition 2021 --crate-type lib --emit metadata "$LIB_RS" -o "$TMP_DIR/tr_lib.rmeta")

if [ "$up_lib_exit" -eq 0 ] && [ "$tr_lib_exit" -eq 0 ]; then
    pass "Both compilers build parity_lib.rs metadata"
else
    fail "Library metadata exits differ (upstream=$up_lib_exit, trust=$tr_lib_exit)"
fi

require_empty_stderr "upstream lib metadata" "$UP_LIB_STDERR"
require_empty_stderr "Trust lib metadata" "$TR_LIB_STDERR"
check_no_trust_output "Trust lib metadata" "$TR_LIB_STDERR"

echo
echo "[3] Compare compile-fail behavior"
UP_FAIL_STDOUT="$TMP_DIR/up_fail.stdout"
UP_FAIL_STDERR="$TMP_DIR/up_fail.stderr"
TR_FAIL_STDOUT="$TMP_DIR/tr_fail.stdout"
TR_FAIL_STDERR="$TMP_DIR/tr_fail.stderr"

up_fail_exit=$(run_capture "$UP_FAIL_STDOUT" "$UP_FAIL_STDERR" "${UPSTREAM_BIN[@]}" --edition 2021 "$FAIL_RS" -o "$TMP_DIR/up_fail_bin")
tr_fail_exit=$(run_capture "$TR_FAIL_STDOUT" "$TR_FAIL_STDERR" "${TRUSTC_PARITY_CMD[@]}" --edition 2021 "$FAIL_RS" -o "$TMP_DIR/tr_fail_bin")

if [ "$up_fail_exit" -ne 0 ] && [ "$tr_fail_exit" -ne 0 ]; then
    pass "Both compilers reject parity_fail.rs"
else
    fail "Compile-fail parity broken (upstream=$up_fail_exit, trust=$tr_fail_exit)"
fi

if grep -q 'E0308' "$UP_FAIL_STDERR" && grep -q 'E0308' "$TR_FAIL_STDERR"; then
    pass "Both compilers report E0308 for parity_fail.rs"
else
    echo "--- upstream compile-fail stderr ---"
    cat "$UP_FAIL_STDERR"
    echo "--- Trust compile-fail stderr ---"
    cat "$TR_FAIL_STDERR"
    fail "Expected E0308 in both compilers"
fi

check_no_trust_output "Trust compile-fail" "$TR_FAIL_STDERR"

echo
echo "=== Results: $PASS passed, $FAIL failed ==="

if [ "$FAIL" -gt 0 ]; then
    exit 1
fi

echo
echo "Semantic parity checks passed."
