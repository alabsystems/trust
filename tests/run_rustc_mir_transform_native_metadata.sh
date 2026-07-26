#!/usr/bin/env bash
# Run the focused compiler-side native TrustIr metadata tests for
# rustc_mir_transform with a repo-local stage2 Trust toolchain.

set -u -o pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

HOST_TRIPLE="$(uname -m)-$(uname -s | tr '[:upper:]' '[:lower:]')"
case "$HOST_TRIPLE" in
    arm64-darwin) HOST_TRIPLE="aarch64-apple-darwin" ;;
esac

TARGET_DIR="${TRUST_NATIVE_METADATA_TARGET_DIR:-$TRUST_ROOT/build/wave-s3-lane-d-rustc-mir-transform-target}"
OUTPUT_DIR="${TRUST_NATIVE_METADATA_OUTPUT_DIR:-$TRUST_ROOT/build/wave-s3-lane-d-native-metadata}"
REPORT_TSV="$OUTPUT_DIR/status.tsv"

fail_setup() {
    printf 'SETUP/BLOCKED: %s\n' "$*" >&2
    exit 2
}

first_sysroot() {
    local candidate

    for candidate in \
        "${TRUST_NATIVE_METADATA_SYSROOT:-}" \
        "$TRUST_ROOT/build/host/stage2" \
        "$TRUST_ROOT/build/$HOST_TRIPLE/stage2" \
        "$TRUST_ROOT/build/aarch64-apple-darwin/stage2"
    do
        [ -n "$candidate" ] || continue
        [ -x "$candidate/bin/targo" ] || continue
        [ -x "$candidate/bin/trustc" ] || continue
        printf '%s\n' "$candidate"
        return 0
    done
    return 1
}

rustc_vv_field() {
    local field="$1"
    "$TRUSTC_BIN" -Vv | awk -F': ' -v field="$field" '$1 == field { print $2; exit }'
}

append_flag_once() {
    local flags="$1"
    local flag="$2"
    case " $flags " in
        *" $flag "*) printf '%s' "$flags" ;;
        *) printf '%s %s' "$flags" "$flag" ;;
    esac
}

run_filter() {
    local label="$1"
    local filter="$2"
    local log="$OUTPUT_DIR/$label.log"
    local status="passed"

    printf '\n=== rustc_mir_transform native metadata: %s ===\n' "$filter"
    printf 'log: %s\n' "$log"

    set +e
    env -u RUSTUP_TOOLCHAIN \
        RUSTC="$TRUSTC_BIN" \
        RUSTC_BOOTSTRAP=1 \
        RUSTFLAGS="$RUSTFLAGS_FOR_TEST" \
        CFG_RELEASE="$CFG_RELEASE" \
        CFG_RELEASE_CHANNEL="$CFG_RELEASE_CHANNEL" \
        CFG_VERSION="$CFG_VERSION" \
        CFG_COMPILER_HOST_TRIPLE="$CFG_COMPILER_HOST_TRIPLE" \
        CFG_COMPILER_BUILD_TRIPLE="$CFG_COMPILER_BUILD_TRIPLE" \
        CFG_DEFAULT_CODEGEN_BACKEND="$CFG_DEFAULT_CODEGEN_BACKEND" \
        CFG_LIBDIR_RELATIVE="$CFG_LIBDIR_RELATIVE" \
        CARGO_TARGET_DIR="$TARGET_DIR" \
        "$TARGO_BIN" --unverified test -p rustc_mir_transform "$filter" --lib -- --nocapture \
        >"$log" 2>&1
    local rc=$?
    set -u

    if [ "$rc" -ne 0 ]; then
        status="failed"
    elif ! grep -Eq 'running [1-9][0-9]* tests?' "$log"; then
        status="blocked-zero-tests"
    fi

    printf '%s\t%s\t%s\t%s\n' "$label" "$status" "$rc" "$log" >> "$REPORT_TSV"
    if [ "$status" = "passed" ]; then
        printf 'PASS: %s\n' "$filter"
    else
        printf '%s: %s\n' "$(printf '%s' "$status" | tr '[:lower:]' '[:upper:]')" "$filter" >&2
        tail -n 40 "$log" >&2 || true
    fi
}

main() {
    cd "$TRUST_ROOT"

    SYSROOT="$(first_sysroot)" || fail_setup "repo-local stage2 sysroot with bin/targo and bin/trustc not found"
    TARGO_BIN="$SYSROOT/bin/targo"
    TRUSTC_BIN="$SYSROOT/bin/trustc"

    CFG_RELEASE="${CFG_RELEASE:-$(rustc_vv_field release)}"
    CFG_RELEASE_CHANNEL="${CFG_RELEASE_CHANNEL:-trust}"
    CFG_VERSION="${CFG_VERSION:-$CFG_RELEASE}"
    CFG_COMPILER_HOST_TRIPLE="${CFG_COMPILER_HOST_TRIPLE:-$(rustc_vv_field host)}"
    CFG_COMPILER_BUILD_TRIPLE="${CFG_COMPILER_BUILD_TRIPLE:-$CFG_COMPILER_HOST_TRIPLE}"
    CFG_DEFAULT_CODEGEN_BACKEND="${CFG_DEFAULT_CODEGEN_BACKEND:-llvm}"
    CFG_LIBDIR_RELATIVE="${CFG_LIBDIR_RELATIVE:-lib}"
    CFG_DEFAULT_LINKER="${CFG_DEFAULT_LINKER:-}"

    RUSTFLAGS_FOR_TEST="${TRUST_NATIVE_METADATA_RUSTFLAGS:-${RUSTFLAGS:-}}"
    RUSTFLAGS_FOR_TEST="$(append_flag_once "$RUSTFLAGS_FOR_TEST" "--cfg bootstrap")"
    RUSTFLAGS_FOR_TEST="$(append_flag_once "$RUSTFLAGS_FOR_TEST" "-Ztrust-verify=off")"

    mkdir -p "$OUTPUT_DIR" "$TARGET_DIR"
    : > "$REPORT_TSV"

    printf 'Using stage2 sysroot: %s\n' "$SYSROOT"
    printf '  targo: %s\n' "$TARGO_BIN"
    printf '  trustc: %s\n' "$TRUSTC_BIN"
    printf '  target: %s\n' "$TARGET_DIR"
    printf '  output: %s\n' "$OUTPUT_DIR"
    printf '  RUSTFLAGS: %s\n' "$RUSTFLAGS_FOR_TEST"
    printf '  CFG_RELEASE: %s\n' "$CFG_RELEASE"
    printf '  CFG_RELEASE_CHANNEL: %s\n' "$CFG_RELEASE_CHANNEL"
    printf '  CFG_COMPILER_HOST_TRIPLE: %s\n' "$CFG_COMPILER_HOST_TRIPLE"

    run_filter \
        native-bundle \
        full_verification_compiler_input_defers_direct_trust_vc_proof_unit
    run_filter \
        missing-native-bundle \
        full_verification_compiler_input_classifies_missing_native_bundle_and_direct_rejection
    run_filter \
        trust-vc-metadata-only-negative \
        proof_unit_metadata_alone_does_not_synthesize_trust_vc_certificate

    if awk -F '\t' '$2 != "passed" { found = 1 } END { exit found ? 0 : 1 }' "$REPORT_TSV"; then
        printf '\nFocused native metadata compiler tests completed with failures. Report: %s\n' "$REPORT_TSV" >&2
        exit 1
    fi

    printf '\nFocused native metadata compiler tests passed. Report: %s\n' "$REPORT_TSV"
}

main "$@"
