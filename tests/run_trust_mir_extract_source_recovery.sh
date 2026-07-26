#!/usr/bin/env bash
# Run the focused trust-mir-extract source-recovery evidence tests with a
# bootstrap-built Trust toolchain. This intentionally avoids plain host Cargo:
# trust-mir-extract depends on rustc_private crates and must be compiled with a
# matching Trust trustc/sysroot.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
MANIFEST="$TRUST_ROOT/crates/trust-mir-extract/Cargo.toml"
TARGET_DIR="${TRUST_SOURCE_RECOVERY_TARGET_DIR:-$TRUST_ROOT/build/trust-mir-extract-source-recovery-target}"

DEFAULT_FILTERS=(
    default_contract_extraction_policy_is_native_only
    convert_trust_contract_bundle
    current_rustc_contract_query_unsupported_payload_fails_closed
    compat_source_recovery
    compiler_contract_attrs_extract_into_pre_and_postconditions
    native_no_contract_bundle_fails_closed_without_source_scraping
)

fail() {
    printf 'FAIL: %s\n' "$*" >&2
    exit 1
}

blocked() {
    printf 'SETUP/BLOCKED: %s\n' "$*" >&2
    exit 2
}

have_std_libs() {
    local sysroot="$1"
    local trustc="$sysroot/bin/trustc"
    local host
    local libdir

    [ -x "$trustc" ] || return 1
    host="$("$trustc" -vV 2>/dev/null | awk '/^host:/ { print $2; exit }')"
    [ -n "$host" ] || return 1
    libdir="$sysroot/lib/rustlib/$host/lib"
    [ -d "$libdir" ] || return 1

    set -- "$libdir"/libcore-*.rlib
    [ -e "$1" ] || return 1
    set -- "$libdir"/libstd-*.rlib
    [ -e "$1" ] || return 1
}

select_toolchain() {
    local candidate

    for candidate in \
        "$TRUST_ROOT"/build/host/stage2 \
        "$TRUST_ROOT"/build/*/stage2
    do
        [ -d "$candidate" ] || continue
        [ -x "$candidate/bin/targo" ] || continue
        have_std_libs "$candidate" || continue
        printf 'stage2\n%s\n%s\n' "$candidate/bin/targo" "$candidate/bin/trustc"
        return 0
    done

    return 1
}

run_one_filter() {
    local kind="$1"
    local cargo_bin="$2"
    local rustc_bin="$3"
    local filter="$4"

    printf '\n=== trust-mir-extract source-recovery: %s ===\n' "$filter"
    case "$kind" in
        stage2)
            env -u RUSTUP_TOOLCHAIN \
                RUSTC="$rustc_bin" \
                RUSTC_BOOTSTRAP=1 \
                RUSTFLAGS="--cfg bootstrap" \
                CARGO_TARGET_DIR="$TARGET_DIR" \
                "$cargo_bin" test \
                    --manifest-path "$MANIFEST" "$filter" --lib -- --nocapture
            ;;
        *)
            fail "unknown toolchain kind: $kind"
            ;;
    esac
}

main() {
    local selected
    local kind
    local cargo_bin
    local rustc_bin
    local filters
    local filter

    cd "$TRUST_ROOT"

    if ! selected="$(select_toolchain)"; then
        blocked "no complete repo-local stage2 Trust targo/trustc sysroot found. Build one with ./x.py build --stage 2; then rerun $0. Plain host Cargo and rustup selectors are intentionally not used."
    fi

    kind="$(printf '%s\n' "$selected" | sed -n '1p')"
    cargo_bin="$(printf '%s\n' "$selected" | sed -n '2p')"
    rustc_bin="$(printf '%s\n' "$selected" | sed -n '3p')"

    printf 'Using Trust toolchain: %s\n' "$kind"
    printf '  targo: %s\n' "$cargo_bin"
    printf '  trustc: %s\n' "$rustc_bin"
    printf '  target: %s\n' "$TARGET_DIR"

    if [ -n "${TRUST_SOURCE_RECOVERY_FILTERS:-}" ]; then
        filters="$TRUST_SOURCE_RECOVERY_FILTERS"
        for filter in $filters; do
            run_one_filter "$kind" "$cargo_bin" "$rustc_bin" "$filter"
        done
    else
        for filter in "${DEFAULT_FILTERS[@]}"; do
            run_one_filter "$kind" "$cargo_bin" "$rustc_bin" "$filter"
        done
    fi
}

main "$@"
