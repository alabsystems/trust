#!/bin/sh

# Shared fail-closed checks for Trust toolchain compatibility entrypoints.
# Callers may set TRUST_TOOLCHAIN_PYTHON3 to a specific Python 3 interpreter.

# Keep this inventory coherent with bootstrap's stage0 contract and
# targo-trust's linked/release surface. Optional canonical trust-miri and
# targo-miri are deliberately not forbidden in complete stage2 roots.
TRUST_TOOLCHAIN_FORBIDDEN_PUBLIC_BINS='cargo-trust tcargo tcargo-trust tcargo-fmt rustdoc rustfmt cargo-fmt cargo-clippy clippy-driver targo-clippy trust-clippy trust-clippy-driver rust-analyzer miri cargo-miri rust-gdb rust-gdbgui rust-lldb rust-windbg.cmd'
TRUST_TOOLCHAIN_FORBIDDEN_PUBLIC_LIBEXEC_BINS='rust-analyzer-proc-macro-srv'

trust_toolchain_resolve_path() {
    "${TRUST_TOOLCHAIN_PYTHON3:-python3}" - "$1" <<'PY'
import pathlib
import sys

try:
    print(pathlib.Path(sys.argv[1]).resolve(strict=True))
except (OSError, RuntimeError):
    raise SystemExit(1)
PY
}

# Print an error and return success when a canonical tool leaf is not one exact
# regular non-symlink executable confined directly beneath an exact bin
# directory. Return failure when the complete list is valid. Compatibility
# aliases are checked separately because rustc/cargo may intentionally be
# same-surface links or copies of trustc/targo.
trust_toolchain_exact_executable_error() (
    bin_dir="$1"
    shift

    if [ ! -d "$bin_dir" ] || [ -L "$bin_dir" ]; then
        printf 'canonical bin path is not an exact directory: %s\n' "$bin_dir"
        return 0
    fi
    resolved_bin="$(trust_toolchain_resolve_path "$bin_dir")" || {
        printf 'canonical bin directory cannot be resolved: %s\n' "$bin_dir"
        return 0
    }

    for name in "$@"; do
        path="$bin_dir/$name"
        if [ ! -f "$path" ] || [ -L "$path" ] || [ ! -x "$path" ]; then
            printf 'canonical %s is not an exact regular executable: %s\n' "$name" "$path"
            return 0
        fi
        resolved_path="$(trust_toolchain_resolve_path "$path")" || {
            printf 'canonical %s cannot be resolved: %s\n' "$name" "$path"
            return 0
        }
        if [ "${resolved_path%/*}" != "$resolved_bin" ]; then
            printf 'canonical %s resolves outside selected bin directory: %s\n' \
                "$name" "$resolved_path"
            return 0
        fi
    done

    return 1
)

trust_toolchain_exact_executables_valid() {
    ! trust_toolchain_exact_executable_error "$@" >/dev/null
}

# Resolve a candidate Stage2 and print it only when it is an exact
# `<repo>/build/<single-host>/stage2` directory. This prevents a repo-shaped
# lexical path from escaping through a symlinked stage2/host ancestor.
trust_toolchain_resolve_repo_stage2() (
    repo_root="$(trust_toolchain_resolve_path "$1")" || return 1
    stage2="$(trust_toolchain_resolve_path "$2")" || return 1
    [ -d "$stage2" ] || return 1

    case "$stage2" in
        "$repo_root"/build/*/stage2)
            host_part="${stage2#"$repo_root"/build/}"
            host_part="${host_part%/stage2}"
            case "$host_part" in
                ''|*/*) return 1 ;;
            esac
            printf '%s\n' "$stage2"
            ;;
        *) return 1 ;;
    esac
)

trust_toolchain_alias_pair_error() (
    bin_dir="$1"
    canonical_name="$2"
    alias_name="$3"
    canonical_path="$bin_dir/$canonical_name"
    alias_path="$bin_dir/$alias_name"

    if [ ! -x "$canonical_path" ]; then
        printf 'canonical %s is missing or not executable at %s\n' "$canonical_name" "$canonical_path"
        return 0
    fi
    if [ ! -x "$alias_path" ]; then
        printf 'compatibility alias %s is missing or not executable at %s\n' "$alias_name" "$alias_path"
        return 0
    fi

    resolved_bin="$(trust_toolchain_resolve_path "$bin_dir")" || {
        printf 'selected bin directory cannot be canonicalized: %s\n' "$bin_dir"
        return 0
    }
    resolved_canonical="$(trust_toolchain_resolve_path "$canonical_path")" || {
        printf 'canonical %s cannot be canonicalized at %s\n' "$canonical_name" "$canonical_path"
        return 0
    }
    resolved_alias="$(trust_toolchain_resolve_path "$alias_path")" || {
        printf 'compatibility alias %s cannot be canonicalized at %s\n' "$alias_name" "$alias_path"
        return 0
    }

    if [ "${resolved_canonical%/*}" != "$resolved_bin" ]; then
        printf 'canonical %s resolves outside selected bin directory: %s\n' \
            "$canonical_name" "$resolved_canonical"
        return 0
    fi
    if [ "${resolved_alias%/*}" != "$resolved_bin" ]; then
        printf 'compatibility alias %s resolves outside selected bin directory: %s\n' \
            "$alias_name" "$resolved_alias"
        return 0
    fi
    if ! command -p cmp -s "$canonical_path" "$alias_path"; then
        printf '%s and %s are not byte-identical same-surface artifacts\n' \
            "$canonical_name" "$alias_name"
        return 0
    fi

    return 1
)

trust_toolchain_alias_pair_valid() {
    ! trust_toolchain_alias_pair_error "$@" >/dev/null
}

trust_toolchain_forbidden_entry_error() (
    bin_dir="$1"
    for name in $TRUST_TOOLCHAIN_FORBIDDEN_PUBLIC_BINS; do
        path="$bin_dir/$name"
        if [ -e "$path" ] || [ -L "$path" ]; then
            printf 'forbidden stock or retired public entrypoint is present: %s\n' "$path"
            return 0
        fi
    done

    sysroot_dir="${bin_dir%/bin}"
    for name in $TRUST_TOOLCHAIN_FORBIDDEN_PUBLIC_LIBEXEC_BINS; do
        path="$sysroot_dir/libexec/$name"
        if [ -e "$path" ] || [ -L "$path" ]; then
            printf 'forbidden stock or retired public entrypoint is present: %s\n' "$path"
            return 0
        fi
    done

    return 1
)

trust_toolchain_forbidden_entries_absent() {
    ! trust_toolchain_forbidden_entry_error "$@" >/dev/null
}
