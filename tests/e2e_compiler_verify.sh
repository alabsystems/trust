#!/bin/bash
# End-to-end test: built Trust compiler emits verification transport
#
# Tests that the compiler-integrated verification pipeline (trust_verify.rs)
# is wired into the built compiler and emits machine-readable verification
# transport for real Rust code when `-Z trust-verify-output=json` is set.
#
# This tests the native Trust compiler path (MIR pass).
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache 2.0

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
INPUT="$TRUST_ROOT/examples/midpoint.rs"

echo "=== Trust E2E Test: compiler-integrated verification ==="
echo

# --- Locate built Trust compiler ---
# Daily-driver/public gates require a stage2 compiler. Stage1 remains useful
# for bootstrap debugging, but accepting it here would let raw bootstrap
# layouts pass as a replacement toolchain.
TRUSTC_BIN=""

runtime_library_path_var() {
    case "$(uname -s)" in
        Darwin) echo "DYLD_LIBRARY_PATH" ;;
        Linux) echo "LD_LIBRARY_PATH" ;;
        *) echo "" ;;
    esac
}

runtime_library_path_for_trustc() {
    local trustc="$1"
    local bin_dir sysroot stage_name build_dir deps_root rustlib_root
    local -a paths=()

    bin_dir="$(cd "$(dirname "$trustc")" && pwd -P)"
    sysroot="$(cd "$bin_dir/.." && pwd -P)"
    stage_name="$(basename "$sysroot")"
    build_dir="$(dirname "$sysroot")"
    deps_root="$build_dir/${stage_name}-rustc"
    rustlib_root="$sysroot/lib/rustlib"

    [ -d "$sysroot/lib" ] && paths+=("$sysroot/lib")

    for libdir in "$rustlib_root"/*/lib; do
        [ -d "$libdir" ] && paths+=("$libdir")
    done

    for depsdir in "$deps_root"/*/release/deps; do
        [ -d "$depsdir" ] && paths+=("$depsdir")
    done

    local joined=""
    local path
    for path in "${paths[@]}"; do
        if [ -z "$joined" ]; then
            joined="$path"
        else
            joined="$joined:$path"
        fi
    done

    printf '%s' "$joined"
}

run_trustc_with_runtime_env() {
    local trustc="$1"
    shift

    local path_var
    local path_value
    local existing=""

    path_var="$(runtime_library_path_var)"
    path_value="$(runtime_library_path_for_trustc "$trustc")"

    if [ -n "$path_var" ] && [ -n "$path_value" ]; then
        existing="${!path_var:-}"
        if [ -n "$existing" ]; then
            env "$path_var=$path_value:$existing" "$trustc" "$@"
        else
            env "$path_var=$path_value" "$trustc" "$@"
        fi
    else
        "$trustc" "$@"
    fi
}

# The probe program must be PROVABLE under the default strict fail-closed
# verification: unproved Level 0 obligations are build errors, so a probe
# like `(a + b) / 2` (a genuine overflow refutation) would reject every
# working trustc. `a / 2 + b / 2` is kernel-certified overflow-free.
supports_trust_verify() {
    local trustc="$1"
    local metadata_out
    metadata_out=$(mktemp /tmp/trust_verify_probe.XXXXXX)
    printf 'pub fn trust_verify_probe(a: usize, b: usize) -> usize { a / 2 + b / 2 }\n' | \
        run_trustc_with_runtime_env "$trustc" --edition 2021 --crate-name trust_verify_probe \
            --crate-type lib --emit metadata -o "$metadata_out" - >/dev/null 2>&1
    local rc=$?
    rm -f "$metadata_out"
    return $rc
}

supports_json_output() {
    local trustc="$1"
    local metadata_out
    local stderr_file
    metadata_out=$(mktemp /tmp/trust_verify_probe_json.XXXXXX)
    stderr_file=$(mktemp /tmp/trust_verify_probe_stderr.XXXXXX)
    printf 'pub fn trust_verify_probe(a: usize, b: usize) -> usize { a / 2 + b / 2 }\n' | \
        run_trustc_with_runtime_env "$trustc" -Z trust-verify-output=json \
            --edition 2021 --crate-name trust_verify_probe --crate-type lib --emit metadata \
            -o "$metadata_out" - 2>"$stderr_file" >/dev/null
    local rc=$?
    if [ $rc -eq 0 ] && grep -q 'TRUST_JSON:' "$stderr_file"; then
        rm -f "$metadata_out" "$stderr_file"
        return 0
    fi
    rm -f "$metadata_out" "$stderr_file"
    return 1
}

if [ -n "${TRUSTC:-}" ] && [ -x "${TRUSTC}" ]; then
    if supports_trust_verify "${TRUSTC}"; then
        TRUSTC_BIN="${TRUSTC}"
    else
        echo "WARN: TRUSTC is set but does not provide a usable native verification path: ${TRUSTC}"
    fi
fi

CANDIDATES=(
    "$TRUST_ROOT/build/host/stage2/bin/trustc"
    "$TRUST_ROOT/build/aarch64-unknown-linux-gnu/stage2/bin/trustc"
    "$TRUST_ROOT/build/aarch64-apple-darwin/stage2/bin/trustc"
    "$TRUST_ROOT/build/x86_64-unknown-linux-gnu/stage2/bin/trustc"
    "$TRUST_ROOT/build/x86_64-apple-darwin/stage2/bin/trustc"
)

if [ -z "$TRUSTC_BIN" ]; then
    for candidate in "${CANDIDATES[@]}"; do
        if [ -x "$candidate" ] && supports_trust_verify "$candidate"; then
            TRUSTC_BIN="$candidate"
            break
        fi
    done
fi

if [ -z "$TRUSTC_BIN" ]; then
    echo "ERROR: built stage2 Trust compiler with a usable native verification path not found."
    echo
    echo "Checked paths:"
    for candidate in "${CANDIDATES[@]}"; do
        if [ -x "$candidate" ]; then
            if supports_trust_verify "$candidate"; then
                echo "  $candidate (usable native verification path)"
            else
                echo "  $candidate (native verification unavailable)"
            fi
        else
            echo "  $candidate (not found)"
        fi
    done
    echo
    echo "Build it with:"
    echo "  cd $TRUST_ROOT && ./x.py build --stage 2 compiler/rustc library/std"
    echo
    echo "This builds the full compiler with the trust_verify MIR pass."
    exit 2
fi

echo "Using trustc: $TRUSTC_BIN"
echo "Input file:  $INPUT"
echo

if ! supports_trust_verify "$TRUSTC_BIN"; then
    echo "ERROR: selected trustc does not provide a usable native verification path"
    exit 2
fi

SUPPORTS_JSON_OUTPUT=0
if supports_json_output "$TRUSTC_BIN"; then
    SUPPORTS_JSON_OUTPUT=1
fi

# --- Verify input file exists ---
if [ ! -f "$INPUT" ]; then
    echo "ERROR: Test input not found: $INPUT"
    exit 2
fi

# --- Run compilation with JSON transport enabled ---
# The trust_verify pass writes verification output to stderr. We capture it
# separately from stdout. midpoint.rs contains a REAL overflow bug, and
# strict Trust verification is fail-closed: unproved Level 0 obligations
# are build errors, so this compilation MUST fail (exit 1) while still
# emitting the machine-readable verification transport.
if [ "$SUPPORTS_JSON_OUTPUT" -eq 1 ]; then
    CMD=(
        "$TRUSTC_BIN" -Z trust-verify-output=json --edition 2021 "$INPUT"
    )
    echo "Running: $TRUSTC_BIN -Z trust-verify-output=json --edition 2021 $INPUT"
else
    CMD=("$TRUSTC_BIN" --edition 2021 "$INPUT")
    echo "Running: $TRUSTC_BIN --edition 2021 $INPUT"
    echo "Note: selected trustc does not provide live JSON transport on the native path; falling back to note-based verification checks."
fi
echo

STDERR_FILE=$(mktemp /tmp/trust_verify_stderr.XXXXXX)
OUTPUT_FILE=$(mktemp /tmp/trust_verify_output.XXXXXX)
SCALAR_CONST_SRC=$(mktemp /tmp/trust_verify_scalar_const.XXXXXX.rs)
SCALAR_CONST_OUT=$(mktemp /tmp/trust_verify_scalar_const.XXXXXX.rmeta)
SCALAR_CONST_STDERR=$(mktemp /tmp/trust_verify_scalar_const_stderr.XXXXXX)
THREAD_LOCAL_SRC=$(mktemp /tmp/trust_verify_thread_local.XXXXXX.rs)
THREAD_LOCAL_OUT=$(mktemp /tmp/trust_verify_thread_local.XXXXXX.rmeta)
THREAD_LOCAL_STDERR=$(mktemp /tmp/trust_verify_thread_local_stderr.XXXXXX)
FAKE_METADATA_SRC=$(mktemp /tmp/trust_verify_fake_metadata.XXXXXX.rs)
FAKE_METADATA_OUT=$(mktemp /tmp/trust_verify_fake_metadata.XXXXXX.rmeta)
FAKE_METADATA_STDERR=$(mktemp /tmp/trust_verify_fake_metadata_stderr.XXXXXX)
ASSOC_CONST_SRC=$(mktemp /tmp/trust_verify_assoc_const.XXXXXX.rs)
ASSOC_CONST_OUT_DIR=$(mktemp -d /tmp/trust_verify_assoc_const.XXXXXX)
ASSOC_CONST_STDERR=$(mktemp /tmp/trust_verify_assoc_const_stderr.XXXXXX)
GENERIC_SWIZZLE_SRC=$(mktemp /tmp/trust_verify_generic_swizzle.XXXXXX.rs)
GENERIC_SWIZZLE_OUT_DIR=$(mktemp -d /tmp/trust_verify_generic_swizzle.XXXXXX)
GENERIC_SWIZZLE_STDERR=$(mktemp /tmp/trust_verify_generic_swizzle_stderr.XXXXXX)
trap "rm -f '$STDERR_FILE' '$OUTPUT_FILE' '$SCALAR_CONST_SRC' '$SCALAR_CONST_OUT' '$SCALAR_CONST_STDERR' '$THREAD_LOCAL_SRC' '$THREAD_LOCAL_OUT' '$THREAD_LOCAL_STDERR' '$FAKE_METADATA_SRC' '$FAKE_METADATA_OUT' '$FAKE_METADATA_STDERR' '$ASSOC_CONST_SRC' '$ASSOC_CONST_STDERR' '$GENERIC_SWIZZLE_SRC' '$GENERIC_SWIZZLE_STDERR'; rm -rf '$ASSOC_CONST_OUT_DIR' '$GENERIC_SWIZZLE_OUT_DIR'" EXIT

COMPILE_EXIT=0
if [ "$SUPPORTS_JSON_OUTPUT" -eq 1 ]; then
    run_trustc_with_runtime_env "$TRUSTC_BIN" -Z trust-verify-output=json --edition 2021 "$INPUT" -o "$OUTPUT_FILE" 2>"$STDERR_FILE" || COMPILE_EXIT=$?
else
    run_trustc_with_runtime_env "$TRUSTC_BIN" --edition 2021 "$INPUT" -o "$OUTPUT_FILE" 2>"$STDERR_FILE" || COMPILE_EXIT=$?
fi

OUTPUT=$(cat "$STDERR_FILE")

echo "--- stderr output ---"
echo "$OUTPUT"
echo "--- end stderr ---"
echo

# --- Check the strict verification gate fired without an ICE ---
# midpoint.rs is the golden buggy example: strict fail-closed verification
# must reject it as a normal compile error (exit 1), never an ICE/abort.
if [ $COMPILE_EXIT -eq 0 ]; then
    echo "FAILED: strict verification accepted the intentionally buggy midpoint example"
    exit 1
fi
if [ $COMPILE_EXIT -gt 1 ]; then
    echo "FAILED: trustc exited with unexpected status $COMPILE_EXIT (expected the strict verification build error)"
    exit 1
fi

# --- Verify expected transport contract ---
PASS=0
FAIL=0

check() {
    local pattern="$1"
    local description="${2:-$1}"
    if echo "$OUTPUT" | grep -q "$pattern"; then
        echo "  PASS: $description"
        PASS=$((PASS + 1))
    else
        echo "  FAIL: $description"
        echo "        Expected pattern: $pattern"
        FAIL=$((FAIL + 1))
    fi
}

if [ "$SUPPORTS_JSON_OUTPUT" -eq 1 ]; then
    # 1. Machine-readable transport lines are emitted
    check "TRUST_JSON:" "Transport: TRUST_JSON lines emitted"

    # 2. main function is reported
    check '"function":"main"' "Transport: main function reported"

    # 3. get_midpoint function is reported
    check '"function":"get_midpoint"' "Transport: get_midpoint function reported"

    # 4. Summary counters are present
    check '"proved":[0-9]' "Transport: proved counter present"
    check '"failed":[0-9]' "Transport: failed counter present"
    check '"unknown":[0-9]' "Transport: unknown counter present"
    check '"runtime_checked":[0-9]' "Transport: runtime_checked counter present"
    check '"total":[0-9]' "Transport: total counter present"
else
    # Fallback for compilers that support native verification but not JSON transport.
    check "=== Trust Verification Report" "Report header emitted"
    check "Trust \\[" "Verification note emitted"
    check "PROVED\\|FAILED\\|UNKNOWN\\|TIMEOUT\\|RUNTIME-CHECKED" "Verification outcome emitted"
fi

echo

# --- Negative checks: things that should NOT appear ---
check_absent() {
    local pattern="$1"
    local description="${2:-No false positive: $1}"
    if echo "$OUTPUT" | grep -q "$pattern"; then
        echo "  FAIL: $description (unexpected pattern found)"
        FAIL=$((FAIL + 1))
    else
        echo "  PASS: $description"
        PASS=$((PASS + 1))
    fi
}

check_absent "divzero" "No division-by-zero false positive on midpoint / 2"

cat >"$SCALAR_CONST_SRC" <<'RUST'
pub fn scalar_const_probe(input: usize) -> usize {
    let scalar = 7usize;
    input + scalar
}

pub fn bool_const_probe(input: bool) -> bool {
    let flag = true;
    input && flag
}
RUST

SCALAR_CONST_EXIT=0
if [ "$SUPPORTS_JSON_OUTPUT" -eq 1 ]; then
    run_trustc_with_runtime_env "$TRUSTC_BIN" \
        -Z trust-verify-level=1 \
        -Z trust-verify-output=json \
        --edition 2021 \
        --crate-name trust_verify_scalar_const_probe \
        --crate-type lib \
        --emit metadata \
        -o "$SCALAR_CONST_OUT" \
        "$SCALAR_CONST_SRC" \
        2>"$SCALAR_CONST_STDERR" || SCALAR_CONST_EXIT=$?
else
    run_trustc_with_runtime_env "$TRUSTC_BIN" \
        -Z trust-verify-level=1 \
        --edition 2021 \
        --crate-name trust_verify_scalar_const_probe \
        --crate-type lib \
        --emit metadata \
        -o "$SCALAR_CONST_OUT" \
        "$SCALAR_CONST_SRC" \
        2>"$SCALAR_CONST_STDERR" || SCALAR_CONST_EXIT=$?
fi

if [ "$SCALAR_CONST_EXIT" -gt 1 ]; then
    echo "  FAIL: Scalar-constant native verification no-ICE regression"
    cat "$SCALAR_CONST_STDERR"
    FAIL=$((FAIL + 1))
else
    echo "  PASS: Scalar-constant native verification no-ICE regression"
    PASS=$((PASS + 1))
fi

if grep -q "internal compiler error\|cannot destructure mir constant" "$SCALAR_CONST_STDERR"; then
    echo "  FAIL: Scalar-constant regression emitted const-destructure ICE text"
    cat "$SCALAR_CONST_STDERR"
    FAIL=$((FAIL + 1))
else
    echo "  PASS: Scalar-constant regression did not emit const-destructure ICE text"
    PASS=$((PASS + 1))
fi

cat >"$THREAD_LOCAL_SRC" <<'RUST'
std::thread_local! {
    static TLS_COUNTER: usize = 7;
}

pub fn thread_local_probe() -> usize {
    TLS_COUNTER.with(|value| *value)
}
RUST

THREAD_LOCAL_EXIT=0
if [ "$SUPPORTS_JSON_OUTPUT" -eq 1 ]; then
    run_trustc_with_runtime_env "$TRUSTC_BIN" \
        -Z trust-verify-level=1 \
        -Z trust-verify-output=json \
        --edition 2021 \
        --crate-name trust_verify_thread_local_probe \
        --crate-type lib \
        --emit metadata \
        -o "$THREAD_LOCAL_OUT" \
        "$THREAD_LOCAL_SRC" \
        2>"$THREAD_LOCAL_STDERR" || THREAD_LOCAL_EXIT=$?
else
    run_trustc_with_runtime_env "$TRUSTC_BIN" \
        -Z trust-verify-level=1 \
        --edition 2021 \
        --crate-name trust_verify_thread_local_probe \
        --crate-type lib \
        --emit metadata \
        -o "$THREAD_LOCAL_OUT" \
        "$THREAD_LOCAL_SRC" \
        2>"$THREAD_LOCAL_STDERR" || THREAD_LOCAL_EXIT=$?
fi

if [ "$THREAD_LOCAL_EXIT" -gt 1 ]; then
    echo "  FAIL: Thread-local MIR native verification no-panic regression"
    cat "$THREAD_LOCAL_STDERR"
    FAIL=$((FAIL + 1))
else
    echo "  PASS: Thread-local MIR native verification no-panic regression"
    PASS=$((PASS + 1))
fi

if grep -q "ThreadLocalRef\|does not support MIR rvalue\|thread 'rustc'.*panicked" "$THREAD_LOCAL_STDERR"; then
    echo "  FAIL: Thread-local regression emitted unsupported-rvalue panic text"
    cat "$THREAD_LOCAL_STDERR"
    FAIL=$((FAIL + 1))
else
    echo "  PASS: Thread-local regression did not emit unsupported-rvalue panic text"
    PASS=$((PASS + 1))
fi

cat >"$FAKE_METADATA_SRC" <<'RUST'
pub fn slice_metadata_probe(values: &mut [u8]) -> usize {
    values.len()
}
RUST

FAKE_METADATA_EXIT=0
if [ "$SUPPORTS_JSON_OUTPUT" -eq 1 ]; then
    run_trustc_with_runtime_env "$TRUSTC_BIN" \
        -Z trust-verify-level=1 \
        -Z trust-verify-output=json \
        --edition 2021 \
        --crate-name trust_verify_fake_metadata_probe \
        --crate-type lib \
        --emit metadata \
        -o "$FAKE_METADATA_OUT" \
        "$FAKE_METADATA_SRC" \
        2>"$FAKE_METADATA_STDERR" || FAKE_METADATA_EXIT=$?
else
    run_trustc_with_runtime_env "$TRUSTC_BIN" \
        -Z trust-verify-level=1 \
        --edition 2021 \
        --crate-name trust_verify_fake_metadata_probe \
        --crate-type lib \
        --emit metadata \
        -o "$FAKE_METADATA_OUT" \
        "$FAKE_METADATA_SRC" \
        2>"$FAKE_METADATA_STDERR" || FAKE_METADATA_EXIT=$?
fi

if [ "$FAKE_METADATA_EXIT" -gt 1 ]; then
    echo "  FAIL: Fake pointer metadata native verification no-panic regression"
    cat "$FAKE_METADATA_STDERR"
    FAIL=$((FAIL + 1))
else
    echo "  PASS: Fake pointer metadata native verification no-panic regression"
    PASS=$((PASS + 1))
fi

if grep -q "RawPtrKind::FakeForPtrMetadata\|does not support RawPtrKind\|thread 'rustc'.*panicked" "$FAKE_METADATA_STDERR"; then
    echo "  FAIL: Fake pointer metadata regression emitted unsupported-raw-pointer panic text"
    cat "$FAKE_METADATA_STDERR"
    FAIL=$((FAIL + 1))
else
    echo "  PASS: Fake pointer metadata regression did not emit unsupported-raw-pointer panic text"
    PASS=$((PASS + 1))
fi

cat >"$ASSOC_CONST_SRC" <<'RUST'
pub trait Relr: Clone {
    type Word: Into<u64> + Default + Copy;
    const COUNT: u8;
    fn next(offset: &mut Self::Word, bits: &mut Self::Word) -> Option<Self::Word>;
}

pub trait FileHeader {
    type Word: Into<u64> + Default + Copy;
    type Relr: Relr<Word = Self::Word>;
}

pub struct RelrIterator<Elf: FileHeader> {
    offset: Elf::Word,
    bits: Elf::Word,
    count: u8,
    _marker: core::marker::PhantomData<Elf>,
}

impl<Elf: FileHeader> Iterator for RelrIterator<Elf> {
    type Item = Elf::Word;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            while self.count > 0 {
                self.count -= 1;
                let offset = Elf::Relr::next(&mut self.offset, &mut self.bits);
                if offset.is_some() {
                    return offset;
                }
            }
            self.count = Elf::Relr::COUNT;
            return None;
        }
    }
}
RUST

ASSOC_CONST_EXIT=0
if [ "$SUPPORTS_JSON_OUTPUT" -eq 1 ]; then
    run_trustc_with_runtime_env "$TRUSTC_BIN" \
        -Z trust-verify-level=1 \
        -Z trust-verify-output=json \
        --edition 2021 \
        --crate-name trust_verify_assoc_const_probe \
        --crate-type lib \
        --emit=dep-info,metadata,link \
        -C embed-bitcode=no \
        --out-dir "$ASSOC_CONST_OUT_DIR" \
        "$ASSOC_CONST_SRC" \
        2>"$ASSOC_CONST_STDERR" || ASSOC_CONST_EXIT=$?
else
    run_trustc_with_runtime_env "$TRUSTC_BIN" \
        -Z trust-verify-level=1 \
        --edition 2021 \
        --crate-name trust_verify_assoc_const_probe \
        --crate-type lib \
        --emit=dep-info,metadata,link \
        -C embed-bitcode=no \
        --out-dir "$ASSOC_CONST_OUT_DIR" \
        "$ASSOC_CONST_SRC" \
        2>"$ASSOC_CONST_STDERR" || ASSOC_CONST_EXIT=$?
fi

if [ "$ASSOC_CONST_EXIT" -gt 1 ]; then
    echo "  FAIL: Projected associated const native verification no-ICE regression"
    cat "$ASSOC_CONST_STDERR"
    FAIL=$((FAIL + 1))
else
    echo "  PASS: Projected associated const native verification no-ICE regression"
    PASS=$((PASS + 1))
fi

if grep -q "normalize_erasing_regions\|resolve_instance_raw\|internal compiler error\|thread 'rustc'.*panicked" "$ASSOC_CONST_STDERR"; then
    echo "  FAIL: Projected associated const regression emitted normalization ICE text"
    cat "$ASSOC_CONST_STDERR"
    FAIL=$((FAIL + 1))
else
    echo "  PASS: Projected associated const regression did not emit normalization ICE text"
    PASS=$((PASS + 1))
fi

cat >"$GENERIC_SWIZZLE_SRC" <<'RUST'
pub trait Swizzle<const M: usize> {
    const INDEX: [usize; M];

    fn first_index() -> usize {
        Self::INDEX[0]
    }
}

pub fn generic_swizzle_probe<const N: usize>() -> usize {
    struct Resize<const N: usize>;

    impl<const N: usize, const M: usize> Swizzle<M> for Resize<N> {
        const INDEX: [usize; M] = const {
            let mut index = [0; M];
            let mut i = 0;
            while i < M {
                index[i] = if i < N { i } else { N };
                i += 1;
            }
            index
        };
    }

    <Resize<N> as Swizzle<8>>::first_index()
}

pub fn instantiated_swizzle_probe() -> usize {
    generic_swizzle_probe::<4>()
}
RUST

GENERIC_SWIZZLE_EXIT=0
if [ "$SUPPORTS_JSON_OUTPUT" -eq 1 ]; then
    run_trustc_with_runtime_env "$TRUSTC_BIN" \
        -Z trust-verify-level=1 \
        -Z trust-verify-output=json \
        --edition 2021 \
        --crate-name trust_verify_generic_swizzle_probe \
        --crate-type lib \
        --emit=dep-info,metadata,link \
        -C embed-bitcode=no \
        --out-dir "$GENERIC_SWIZZLE_OUT_DIR" \
        "$GENERIC_SWIZZLE_SRC" \
        2>"$GENERIC_SWIZZLE_STDERR" || GENERIC_SWIZZLE_EXIT=$?
else
    run_trustc_with_runtime_env "$TRUSTC_BIN" \
        -Z trust-verify-level=1 \
        --edition 2021 \
        --crate-name trust_verify_generic_swizzle_probe \
        --crate-type lib \
        --emit=dep-info,metadata,link \
        -C embed-bitcode=no \
        --out-dir "$GENERIC_SWIZZLE_OUT_DIR" \
        "$GENERIC_SWIZZLE_SRC" \
        2>"$GENERIC_SWIZZLE_STDERR" || GENERIC_SWIZZLE_EXIT=$?
fi

if [ "$GENERIC_SWIZZLE_EXIT" -gt 1 ]; then
    echo "  FAIL: Generic associated const swizzle native verification no-ICE regression"
    cat "$GENERIC_SWIZZLE_STDERR"
    FAIL=$((FAIL + 1))
else
    echo "  PASS: Generic associated const swizzle native verification no-ICE regression"
    PASS=$((PASS + 1))
fi

if grep -q "find_const_ty_from_env\|resolve_instance_raw\|codegen_select_candidate\|internal compiler error\|thread 'rustc'.*panicked" "$GENERIC_SWIZZLE_STDERR"; then
    echo "  FAIL: Generic associated const swizzle regression emitted resolution ICE text"
    cat "$GENERIC_SWIZZLE_STDERR"
    FAIL=$((FAIL + 1))
else
    echo "  PASS: Generic associated const swizzle regression did not emit resolution ICE text"
    PASS=$((PASS + 1))
fi

echo

# --- Summary ---
echo "=== Results: $PASS passed, $FAIL failed ==="

if [ $FAIL -gt 0 ]; then
    echo
    echo "FAILED: $FAIL check(s) did not pass."
    exit 1
fi

echo
echo "All checks passed."
exit 0
