#!/usr/bin/env bash
# Check, and on supported hosts execution-audit, a self-hosted Trust build.
#
# Default mode is deliberately only a static preflight.  It validates the
# pinned seed, both supported bootstrap configuration filenames, compiler
# selection environment variables, and every Rust-family command reachable on
# PATH.  It does not run a build and therefore must not claim that a build was
# free of stock Rust.
#
# --build performs a fresh stage2 build under a minimal environment and a
# kernel exec audit.  Today the supported audit backend is Linux strace.  Other
# hosts fail unsupported; merely deleting rustup from PATH is not exec proof.
#
# Usage: scripts/prove_rust_free_build.sh [--build]
set -uo pipefail

usage() {
    printf 'usage: %s [--build]\n' "${0##*/}" >&2
}

note() {
    printf '  %s\n' "$*"
}

bad() {
    printf 'FAIL: %s\n' "$*" >&2
    FAIL=1
}

AUDIT_BUILD_PID=
AUDIT_COLLECTOR_PID=
AUDIT_SENTINEL_OPEN=0
AUDIT_HANDSHAKE_OPEN=0

cleanup_audit_children() {
    # GNU timeout normally owns a separate process group.  Address that group
    # first, then the direct process as a conservative fallback.  strace's
    # EXITKILL option provides the kernel-side descendant cleanup.
    if [ -n "${AUDIT_BUILD_PID:-}" ]; then
        kill -TERM -- "-$AUDIT_BUILD_PID" 2>/dev/null || true
        kill -TERM "$AUDIT_BUILD_PID" 2>/dev/null || true
        kill -KILL -- "-$AUDIT_BUILD_PID" 2>/dev/null || true
        kill -KILL "$AUDIT_BUILD_PID" 2>/dev/null || true
        wait "$AUDIT_BUILD_PID" 2>/dev/null || true
        AUDIT_BUILD_PID=
    fi
    if [ "${AUDIT_SENTINEL_OPEN:-0}" -eq 1 ]; then
        exec 9>&-
        AUDIT_SENTINEL_OPEN=0
    fi
    if [ "${AUDIT_HANDSHAKE_OPEN:-0}" -eq 1 ]; then
        exec 8>&-
        AUDIT_HANDSHAKE_OPEN=0
    fi
    if [ -n "${AUDIT_COLLECTOR_PID:-}" ]; then
        kill -TERM "$AUDIT_COLLECTOR_PID" 2>/dev/null || true
        wait "$AUDIT_COLLECTOR_PID" 2>/dev/null || true
        AUDIT_COLLECTOR_PID=
    fi
}

audit_exit_cleanup() {
    local status=$?
    trap - EXIT HUP INT TERM
    cleanup_audit_children
    exit "$status"
}

audit_signal_cleanup() {
    local signal=$1
    trap - EXIT HUP INT TERM
    cleanup_audit_children
    trap - "$signal"
    kill -s "$signal" "$$"
}

canonical_file() {
    "$PYTHON_BIN" -I -S -c \
        'import os,sys; print(os.path.realpath(sys.argv[1]))' "$1"
}

control_path_is_forbidden() {
    case "$1" in
        *'/.rustup/'*|*'/rustup/toolchains/'*|*'/genesis-stage0/'*) return 0 ;;
        *) return 1 ;;
    esac
}

consume_check_output() {
    local output=$1
    local helper_status=$2
    local saw_error=0
    local kind message

    while IFS=$'\t' read -r kind message; do
        case "$kind" in
            NOTE) note "$message" ;;
            ERROR)
                bad "$message"
                saw_error=1
                ;;
            FINGERPRINT) PREFLIGHT_FINGERPRINT=$message ;;
            '') ;;
            *)
                bad "audit helper emitted an unrecognized record"
                saw_error=1
                ;;
        esac
    done <<< "$output"

    if [ "$helper_status" -ne 0 ] && [ "$saw_error" -eq 0 ]; then
        bad "audit helper failed without a diagnostic (status $helper_status)"
    fi
}

run_preflight() {
    local output status
    PREFLIGHT_FINGERPRINT=
    output=$("$PYTHON_BIN" -I -S "$AUDIT_HELPER" preflight "$ROOT")
    status=$?
    consume_check_output "$output" "$status"
}

audit_trace_file() {
    local trace=$1
    local build_root=$2
    "$PYTHON_BIN" -I -S "$AUDIT_HELPER" trace "$ROOT" "$build_root" "$trace"
}

check_stage2_output() {
    local build_root=$1
    "$PYTHON_BIN" -I -S "$AUDIT_HELPER" stage2-output "$ROOT" "$build_root"
}

main() {
    local mode=preflight
    local helper_output helper_status
    local platform strace_bin strace_real strace_help env_bin timeout_bin timeout_real
    local python_identity strace_identity timeout_identity env_identity current_identity
    local audit_dir trace_file trace_pipe trace_ready trace_identity audited_build_dir build_status
    local collector_pid collector_status
    local trace_output trace_status output_check output_status
    local post_output post_status post_fingerprint

    case $# in
        0) ;;
        1)
            if [ "$1" = "--build" ]; then
                mode=build
            else
                usage
                printf 'FAIL: unknown argument: %s\n' "$1" >&2
                return 2
            fi
            ;;
        *)
            usage
            printf 'FAIL: expected zero arguments or exactly --build\n' >&2
            return 2
            ;;
    esac

    local script_dir=${BASH_SOURCE[0]%/*}
    if [ "$script_dir" = "${BASH_SOURCE[0]}" ]; then
        script_dir=.
    fi
    ROOT=$(cd -P "$script_dir/.." && pwd -P) || {
        printf 'FAIL: cannot resolve repository root\n' >&2
        return 2
    }
    AUDIT_HELPER="$ROOT/scripts/off_stock_rust_audit.py"
    FAIL=0

    # `type -P` ignores inherited shell functions and aliases.  Isolated mode
    # keeps PYTHONPATH/PYTHONHOME and user site hooks out of the helper.
    PYTHON_BIN=$(type -P python3 || true)
    if [ -z "$PYTHON_BIN" ] || [ ! -x "$PYTHON_BIN" ]; then
        printf 'FAIL: python3 executable is required for fail-closed auditing\n' >&2
        return 1
    fi
    PYTHON_BIN=$(canonical_file "$PYTHON_BIN") || {
        printf 'FAIL: cannot canonicalize python3\n' >&2
        return 1
    }
    if control_path_is_forbidden "$PYTHON_BIN"; then
        printf 'FAIL: python3 resolves through a forbidden stock-Rust tree\n' >&2
        return 1
    fi
    if [ ! -f "$AUDIT_HELPER" ] || [ -L "$AUDIT_HELPER" ]; then
        printf 'FAIL: audit helper must be a regular, repository-owned file: %s\n' \
            "$AUDIT_HELPER" >&2
        return 1
    fi
    cd -P "$ROOT" || {
        printf 'FAIL: cannot enter authenticated repository root\n' >&2
        return 1
    }
    python_identity=$("$PYTHON_BIN" -I -S "$AUDIT_HELPER" executable-identity "$PYTHON_BIN") || {
        printf 'FAIL: cannot authenticate the selected python3 executable\n' >&2
        return 1
    }

    printf '== off-stock-Rust static preflight ==\n'
    run_preflight

    current_identity=$("$PYTHON_BIN" -I -S "$AUDIT_HELPER" executable-identity "$PYTHON_BIN" 2>/dev/null || true)
    if [ "$current_identity" != "$python_identity" ]; then
        bad "the selected python3 executable changed during preflight"
    fi

    if [ "$FAIL" -ne 0 ]; then
        printf '\nNOT READY: static preflight failed; no build was run.\n' >&2
        return 1
    fi

    if [ "$mode" = preflight ]; then
        printf '\nPREFLIGHT OK: static inputs are ready. No build was run and no execution claim is made.\n'
        return 0
    fi

    platform=$("$PYTHON_BIN" -I -S -c 'import platform; print(platform.system())') || {
        bad "cannot identify the host platform"
        return 1
    }
    if [ "$platform" != Linux ]; then
        printf '\nFAIL: --build requires a supported kernel exec-audit backend; %s is unsupported.\n' \
            "$platform" >&2
        printf '      Run this gate in Linux CI/a stock-Rust-free VM with strace installed.\n' >&2
        return 1
    fi

    strace_bin=$(type -P strace || true)
    if [ -z "$strace_bin" ] || [ ! -x "$strace_bin" ]; then
        printf '\nFAIL: --build requires Linux strace; PATH scrubbing alone is not execution proof.\n' >&2
        return 1
    fi
    strace_real=$(canonical_file "$strace_bin") || {
        bad "cannot canonicalize strace"
        return 1
    }
    if control_path_is_forbidden "$strace_real"; then
        bad "strace resolves through a forbidden stock-Rust tree"
        return 1
    fi
    strace_identity=$("$PYTHON_BIN" -I -S "$AUDIT_HELPER" executable-identity "$strace_real") || {
        bad "cannot authenticate strace identity"
        return 1
    }
    strace_help=$(LC_ALL=C "$strace_real" --help 2>&1) || {
        bad "cannot inspect strace capabilities"
        return 1
    }
    case "$strace_help" in
        *--kill-on-exit*) ;;
        *)
            bad "strace lacks --kill-on-exit; tracees could outlive a failed/limited auditor"
            return 1
            ;;
    esac

    timeout_bin=$(type -P timeout || true)
    if [ -z "$timeout_bin" ] || [ ! -x "$timeout_bin" ]; then
        bad "GNU timeout is required to bound the audited build"
        return 1
    fi
    timeout_real=$(canonical_file "$timeout_bin") || {
        bad "cannot canonicalize timeout"
        return 1
    }
    if control_path_is_forbidden "$timeout_real"; then
        bad "timeout resolves through a forbidden stock-Rust tree"
        return 1
    fi
    timeout_identity=$("$PYTHON_BIN" -I -S "$AUDIT_HELPER" executable-identity "$timeout_real") || {
        bad "cannot authenticate timeout identity"
        return 1
    }

    env_bin=$(type -P env || true)
    if [ -z "$env_bin" ] || [ ! -x "$env_bin" ]; then
        bad "env executable is required to construct the minimal build environment"
        return 1
    fi
    env_bin=$(canonical_file "$env_bin") || {
        bad "cannot canonicalize env"
        return 1
    }
    if control_path_is_forbidden "$env_bin"; then
        bad "env resolves through a forbidden stock-Rust tree"
        return 1
    fi
    env_identity=$("$PYTHON_BIN" -I -S "$AUDIT_HELPER" executable-identity "$env_bin") || {
        bad "cannot authenticate env identity"
        return 1
    }

    audit_dir=$("$PYTHON_BIN" -I -S "$AUDIT_HELPER" make-audit-dir "$ROOT/build") || {
        bad "cannot create owner-private audit directory under build/"
        return 1
    }
    trace_file="$audit_dir/exec.trace"
    trace_pipe="$audit_dir/exec.trace.pipe"
    trace_ready="$audit_dir/collector.ready"
    trace_identity=$("$PYTHON_BIN" -I -S "$AUDIT_HELPER" file-identity "$trace_file") || {
        bad "cannot authenticate the pre-created trace inode"
        return 1
    }
    audited_build_dir="$audit_dir/fresh-build"
    note "audit evidence directory: $audit_dir"
    note "building a fresh stage2 under Linux strace (12-hour/512-MiB trace bounds)"

    # The collector opens a pre-created owner-private trace inode and drains a
    # FIFO even after the byte ceiling is reached.  Thus an exec storm cannot
    # fill the filesystem or deadlock strace; exceeding the ceiling makes the
    # final result fail.  strace's EXITKILL option terminates all tracees if the
    # tracer itself is killed or loses its output channel.
    # Open one temporary read/write handshake endpoint so neither side of the
    # FIFO can block before the collector has authenticated and opened both
    # evidence descriptors.  The collector does not inherit it.
    exec 8<>"$trace_pipe" || {
        bad "cannot open trace collector startup handshake"
        return 1
    }
    AUDIT_HANDSHAKE_OPEN=1
    "$PYTHON_BIN" -I -S "$AUDIT_HELPER" collect-trace \
        "$trace_pipe" "$trace_file" 536870912 "$trace_ready" 8>&- &
    collector_pid=$!
    AUDIT_COLLECTOR_PID=$collector_pid
    trap audit_exit_cleanup EXIT
    trap 'audit_signal_cleanup HUP' HUP
    trap 'audit_signal_cleanup INT' INT
    trap 'audit_signal_cleanup TERM' TERM
    # A parent-held writer keeps the authenticated collector alive if
    # timeout/strace rejects its arguments before opening the pipe.  It was
    # opened while fd 8 still supplied the FIFO's read side, so startup cannot
    # deadlock if the collector fails before its own open.
    exec 9>"$trace_pipe"
    AUDIT_SENTINEL_OPEN=1
    exec 8>&-
    AUDIT_HANDSHAKE_OPEN=0
    if ! "$PYTHON_BIN" -I -S "$AUDIT_HELPER" wait-ready \
        "$trace_ready" "$collector_pid" 5000; then
        bad "trace collector did not become ready within 5 seconds"
        return 1
    fi

    # `env -i` is intentional.  It closes inherited RUSTC/CARGO/wrapper,
    # RUST_BOOTSTRAP_CONFIG, Cargo target-runner, loader, shell-startup, and
    # Python import injection instead of trying to maintain an incomplete
    # unset list.  Cargo/rustup homes are empty and owner-private.
    "$timeout_real" --signal=TERM --kill-after=30s 12h \
      "$strace_real" --kill-on-exit -f -s 65535 -yy \
        -e trace=execve,execveat \
        -o "$trace_pipe" \
        "$env_bin" -i \
        HOME="$audit_dir/home" \
        USER="${USER:-trust-audit}" \
        LOGNAME="${LOGNAME:-${USER:-trust-audit}}" \
        PATH="$PATH" \
        LANG=C LC_ALL=C TZ=UTC \
        TMPDIR="$audit_dir/tmp" \
        CARGO_HOME="$audit_dir/cargo-home" \
        RUSTUP_HOME="$audit_dir/rustup-home" \
        XDG_CONFIG_HOME="$audit_dir/xdg-config" \
        GIT_CONFIG_NOSYSTEM=1 GIT_CONFIG_GLOBAL=/dev/null \
        "$PYTHON_BIN" -I -S "$ROOT/x.py" build \
        --build-dir "$audited_build_dir" \
        --stage 2 \
        --set build.submodules=false \
        compiler/rustc &
    AUDIT_BUILD_PID=$!
    wait "$AUDIT_BUILD_PID"
    build_status=$?
    AUDIT_BUILD_PID=

    exec 9>&-
    AUDIT_SENTINEL_OPEN=0
    wait "$collector_pid"
    collector_status=$?
    AUDIT_COLLECTOR_PID=
    trap - EXIT HUP INT TERM
    if [ "$collector_status" -ne 0 ]; then
        bad "exec trace exceeded 512 MiB or its bounded collector failed"
    fi
    if [ "$("$PYTHON_BIN" -I -S "$AUDIT_HELPER" file-identity "$trace_file" 2>/dev/null || true)" \
         != "$trace_identity" ]; then
        bad "the pre-created exec trace inode was replaced during the build"
    fi

    trace_output=$(audit_trace_file "$trace_file" "$audited_build_dir")
    trace_status=$?
    if [ -n "$trace_output" ]; then
        printf '%s\n' "$trace_output"
    fi
    if [ "$trace_status" -ne 0 ]; then
        bad "exec trace is incomplete or violates the off-stock policy"
    fi

    output_check=$(check_stage2_output "$audited_build_dir")
    output_status=$?
    if [ -n "$output_check" ]; then
        printf '%s\n' "$output_check"
    fi
    if [ "$output_status" -ne 0 ]; then
        bad "fresh stage2 output validation failed"
    fi

    if [ "$build_status" -ne 0 ]; then
        bad "fresh stage2 build failed under strace (status $build_status)"
    fi

    # Detect ordinary preflight/build races.  An adversarial host can always
    # mutate files between syscalls; the stronger claim belongs in an isolated
    # VM/image with no stock compiler installed.
    post_output=$("$PYTHON_BIN" -I -S "$AUDIT_HELPER" preflight "$ROOT")
    post_status=$?
    post_fingerprint=
    while IFS=$'\t' read -r kind message; do
        case "$kind" in
            FINGERPRINT) post_fingerprint=$message ;;
            ERROR) bad "post-build preflight: $message" ;;
        esac
    done <<< "$post_output"
    if [ "$post_status" -ne 0 ] && [ -z "$post_fingerprint" ]; then
        bad "post-build preflight failed without a complete fingerprint"
    fi
    if [ -z "$PREFLIGHT_FINGERPRINT" ] || \
       [ "$post_fingerprint" != "$PREFLIGHT_FINGERPRINT" ]; then
        bad "security-relevant seed/config/PATH inputs changed during the build"
    fi
    current_identity=$("$PYTHON_BIN" -I -S "$AUDIT_HELPER" executable-identity "$PYTHON_BIN" 2>/dev/null || true)
    if [ "$current_identity" != "$python_identity" ]; then
        bad "the selected python3 executable changed during the audited build"
    fi
    current_identity=$("$PYTHON_BIN" -I -S "$AUDIT_HELPER" executable-identity "$strace_real" 2>/dev/null || true)
    if [ "$current_identity" != "$strace_identity" ]; then
        bad "the selected strace executable changed during the audited build"
    fi
    current_identity=$("$PYTHON_BIN" -I -S "$AUDIT_HELPER" executable-identity "$timeout_real" 2>/dev/null || true)
    if [ "$current_identity" != "$timeout_identity" ]; then
        bad "the selected timeout executable changed during the audited build"
    fi
    current_identity=$("$PYTHON_BIN" -I -S "$AUDIT_HELPER" executable-identity "$env_bin" 2>/dev/null || true)
    if [ "$current_identity" != "$env_identity" ]; then
        bad "the selected env executable changed during the audited build"
    fi

    if [ "$FAIL" -ne 0 ]; then
        printf '\nAUDIT FAILED: no off-stock execution claim is made. Evidence retained at %s\n' \
            "$audit_dir" >&2
        return 1
    fi

    printf '\nPASS: fresh stage2 build satisfied the documented Linux exec-audit policy.\n'
    printf '      This is path/name/identity evidence, not a universal detector for deliberately renamed unknown binaries.\n'
    printf '      It assumes a trusted checkout; same-UID hostile-child resistance requires privilege separation/isolation.\n'
    printf '      Evidence retained at %s\n' "$audit_dir"
    return 0
}

if [ "${BASH_SOURCE[0]}" = "$0" ]; then
    main "$@"
fi
