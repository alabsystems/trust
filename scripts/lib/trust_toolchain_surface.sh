#!/bin/sh

# Shared fail-closed checks for Trust toolchain compatibility entrypoints.
# Callers may set TRUST_TOOLCHAIN_PYTHON3 to a specific Python 3 interpreter.

# Keep this inventory coherent with bootstrap's stage0 contract and
# targo-trust's linked/release surface. This list governs COMPLETE roots, so it
# is bootstrap.py's STAGE0_FORBIDDEN_BINS minus two deliberate carve-outs;
# scripts/check_toolchain_coherence.py derives exactly that difference and fails
# if these mirrors drift.
#   trust-miri, targo-miri  optional canonical Trust tools. A complete stage2
#                           root may ship them.
#   rustdoc                 a deliberate same-surface ALIAS of trustdoc since
#                           76d408e1cd: cargo spawns a binary named `rustdoc`
#                           for its doctest phase and rustup's proxy refuses a
#                           linked toolchain without it, so bootstrap installs
#                           both names at every stage >= 1
#                           (tool.rs:1676 rustdoc_sysroot_bins) and dist ships
#                           both. It is admitted exactly the way `rustc` and
#                           `cargo` are -- as an alias whose byte-identity with
#                           its canonical Trust tool is enforced separately by
#                           trust_toolchain_alias_pair_error -- never as a stock
#                           entrypoint standing on its own. A stage0 SEED still
#                           forbids the name; that list stays in bootstrap.py.
TRUST_TOOLCHAIN_FORBIDDEN_PUBLIC_BINS='cargo-trust tcargo tcargo-trust tcargo-fmt rustfmt cargo-fmt cargo-clippy clippy-driver targo-clippy trust-clippy trust-clippy-driver rust-analyzer miri cargo-miri rust-gdb rust-gdbgui rust-lldb rust-windbg.cmd'
TRUST_TOOLCHAIN_FORBIDDEN_PUBLIC_LIBEXEC_BINS='rust-analyzer-proc-macro-srv'

trust_toolchain_resolve_path() {
    # The path contract needs only the standard library. Ambient site hooks
    # and PYTHONPATH must not run before checking the selected tool root.
    "${TRUST_TOOLCHAIN_PYTHON3:-python3}" -I -S - "$1" <<'PY'
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

# Trust tools that descend from a stock Rust program with the same job, and so
# could be confused with it: a stock build under the Trust name (a stale
# tools-directory artifact that bootstrap restored, a hand copy) is a regular,
# runnable executable that answers `--version`, so existence-and-runs cannot tell
# the two apart. Each Trust build names itself in its `--version` output, where
# the stock program names itself (measured on seal trust-7d5533b2, 2026-09-30):
#
#   trustc          rustc 1.99.0-dev (7d5533b2b 2026-09-23) (trustc 0.1.0)
#   trustdoc        rustc 1.99.0-dev (7d5533b2b 2026-09-23) (trustdoc 0.1.0)
#   targo           targo 1.99.0-dev (7d5533b2b 2026-09-23) (targo 0.1.0)
#   trustfmt        trustfmt 1.9.0-trust (7d5533b2bb 2026-09-23)
#   targo-fmt       trustfmt 1.9.0-trust (7d5533b2bb 2026-09-23)
#   tippy           tippy 0.1.0 (7d5533b2bb 2026-09-23)
#   targo-tippy     tippy 0.1.0 (7d5533b2bb 2026-09-23)
#   tippy-driver    tippy 0.1.98 (7d5533b2bb 2026-09-23)
#   trust-analyzer  trust-analyzer 1.99.0-dev (7d5533b2bb 2026-09-23)
#
# and, from source (neither is built by default): `trust-miri <version>`
# (src/tools/miri/src/bin/miri.rs) and `targo-miri <version> (...)`
# (src/tools/miri/cargo-miri/src/phases.rs). The stock programs print `rustc
# <version> (...)` with no Trust parenthetical, `rustdoc`, `cargo`, `rustfmt`,
# `clippy`, `rust-analyzer` and `miri`. The three compatibility aliases (rustc,
# cargo, rustdoc) are not listed: each is held byte-identical to its canonical
# tool here, which is. First-party tools with no stock ancestor (ay, ty, clean,
# targo-trust, trustd, trustup) are not listed either.
#
# The banner is self-reported. This check refuses a stock program that reports
# its own identity under a Trust name (a stale or copied artifact, unmodified).
# It does not refuse a wrapper that runs a stock program and rewrites its first
# line. The local genesis stage0 adapter (scripts/create_local_genesis_stage0.py)
# is such a wrapper, and its trustfmt, tippy, targo-tippy, tippy-driver,
# trust-analyzer and targo pass this check (docs/trust-naming.md, "What The
# Banner Check Does Not Establish").
TRUST_TOOLCHAIN_BRANDED_PUBLIC_BINS='trustc trustdoc targo trustfmt targo-fmt tippy targo-tippy tippy-driver trust-analyzer trust-miri targo-miri'

# Print an error and return success when VERSION_OUTPUT, the STANDARD OUTPUT of
# `NAME --version` for the public tool NAME, does not identify the Trust build of
# NAME. Return failure when it does. NAME must be one of
# TRUST_TOOLCHAIN_BRANDED_PUBLIC_BINS; any other name is an error, never a pass.
# Only the first line counts: that is the version line, and a later line must
# not be able to vouch for it. Callers pass stdout alone, never stdout merged
# with stderr: every banner above is printed on stdout, and Cargo prints its
# configuration warnings (an unused .cargo/config.toml key, a CARGO_HOME with
# both `config` and `config.toml`) on stderr BEFORE its banner, so a merged
# first line refuses the genuine targo.
trust_toolchain_identity_error() (
    name="$1"
    version_output="$2"
    first_line="$(printf '%s\n' "$version_output" | sed -n '1p')"

    case "$name" in
        trustc|trustdoc)
            # rustc-derived banners keep the leading `rustc` token (build
            # scripts across the ecosystem sniff it) and carry the Trust
            # identity in a trailing parenthetical: `(trustc)` without
            # CFG_TRUST_VERSION, `(trustc <version>)` with it
            # (compiler/rustc_driver_impl/src/lib.rs). Accept exactly those two
            # shapes and nothing looser. Matching only the literal `(trustc)`
            # once refused every real toolchain built after CFG_TRUST_VERSION
            # was threaded through bootstrap (a81c07e1d6; measured 2026-08-22:
            # `rustc 1.99.0-dev (52e0a7031 2026-08-22) (trustc 0.1.0)`), while
            # recorded banners from before it carry the bare shape. A stock
            # rustc prints no parenthetical and fails either way.
            case "$first_line" in
                *"($name)"*|*"($name "*) return 1 ;;
            esac
            printf '%s --version does not carry the Trust brand "(%s)" or "(%s <version>)": %s\n' \
                "$name" "$name" "$name" "$first_line"
            return 0
            ;;
        targo|trustfmt|tippy|trust-analyzer|trust-miri|targo-miri) brand="$name" ;;
        targo-fmt) brand=trustfmt ;;
        targo-tippy|tippy-driver) brand=tippy ;;
        *)
            printf 'no Trust version brand is defined for %s\n' "$name"
            return 0
            ;;
    esac

    case "$first_line" in
        "$brand "*) return 1 ;;
    esac
    printf '%s --version does not identify the Trust build (expected a first stdout line beginning "%s "): %s\n' \
        "$name" "$brand" "$first_line"
    return 0
)

trust_toolchain_identity_valid() {
    ! trust_toolchain_identity_error "$@" >/dev/null
}
