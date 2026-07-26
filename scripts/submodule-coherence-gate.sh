#!/usr/bin/env bash
# submodule-coherence-gate.sh — fail if the recorded first-party submodule
# SHAs do not type-check together.
#
# WHY THIS EXISTS
#   Aligning each first-party repo to its own `main` does NOT guarantee a
#   buildable whole. A submodule can add an enum variant (e.g. trust-ir
#   `BinOp::FMin/FMax`) that its consumers (trust-cg / trust-mc / ty) do not
#   yet handle, producing a non-exhaustive-match build break that git-level
#   "alignment" cannot see. This gate runs `x.py check` (cargo check across
#   the workspace, no codegen — far faster than a full build) and fails
#   closed on any compile error, so a submodule pointer bump cannot land a
#   non-building tree.
#
#   CRITICAL ROBUSTNESS: we capture the REAL exit status. A `cmd | tee | tail`
#   pipeline returns tail's exit code (0), which silently masks build
#   failures — the exact trap that hid this class of break (bootstrap printed
#   "Build completed unsuccessfully" while the harness saw exit 0). We use
#   PIPESTATUS + a CR-normalized scan for bootstrap's own failure verdict.
#
# USAGE
#   scripts/submodule-coherence-gate.sh            # run the gate
#   Wire into CI and/or a pre-push hook:
#     ln -s ../../scripts/submodule-coherence-gate.sh .git/hooks/pre-push
set -uo pipefail

ROOT="$(git -C "$(dirname "${BASH_SOURCE[0]}")/.." rev-parse --show-toplevel)"
cd "$ROOT" || exit 1

LOG="$(mktemp -t coherence-gate.XXXXXX)"
trap 'rm -f "$LOG"' EXIT

echo "[coherence] recorded first-party submodule SHAs:"
git submodule status first-party 2>/dev/null | sed 's/^/    /'

check_args=(check --skip src/tools/tippy)
coherence_jobs="${TRUST_JOBS:-${CARGO_BUILD_JOBS:-}}"
if [[ -n "$coherence_jobs" ]]; then
    if [[ ! "$coherence_jobs" =~ ^[1-9][0-9]*$ ]]; then
        echo "[coherence] FAIL: TRUST_JOBS/CARGO_BUILD_JOBS must be a positive integer." >&2
        exit 2
    fi
    check_args+=(-j "$coherence_jobs")
fi

echo "[coherence] x.py check across compiler + Trust + first-party workspaces…"
# Tippy has no first-party dependency edge, and its integration-test targets
# intentionally require Cargo-provided CARGO_BIN_EXE_* paths. `x.py check`
# checks those targets without building their companion executables, so
# including Tippy here produces an unrelated compile-time failure and prevents
# this gate from answering its actual coherence question. Tippy remains covered
# by its dedicated build/test gates and by the stage2 toolchain build.
./x.py "${check_args[@]}" >"$LOG" 2>&1
rc=${PIPESTATUS[0]}

# Defense in depth: a build can fail two ways — a nonzero exit, OR bootstrap
# printing its own verdict while a wrapping pipeline masks the code. Scan the
# CR-normalized log for both compile errors and the bootstrap failure line.
norm="$(tr '\r' '\n' <"$LOG")"
if printf '%s\n' "$norm" | grep -aqE 'could not compile|Build completed unsuccessfully|^error\[E[0-9]+\]|^error: aborting'; then
    echo "[coherence] FAIL: compile errors / bootstrap failure detected:"
    printf '%s\n' "$norm" | grep -aE 'could not compile|Build completed unsuccessfully|^error' | head -20 | sed 's/^/    /'
    exit 1
fi
if [ "${rc:-1}" -ne 0 ]; then
    echo "[coherence] FAIL: x.py check exited ${rc}."
    exit "${rc:-1}"
fi

echo "[coherence] PASS: the recorded submodule SHAs type-check together."
