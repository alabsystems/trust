#!/usr/bin/env bash
# Cut the seed of a Trust pack: build the committed HEAD from the src/stage0
# pin, double-compile it against an independent seed (DDC; diverse only when
# that seed is lineage-disjoint), rebuild Trust from the minted archives, and
# emit the commit-bound re-pin (docs/DECISION_QUEUE.md D12; the runbook is
# docs/CUTTING-A-TOOLCHAIN.md section 3.9).
#
#   1. Build HEAD's compiler and std in a fresh build/pack-mint-* directory
#      from the src/stage0 pin alone: a configuration that overrides any stage0
#      tool is refused, and the extracted stage0 must be the pin. This first
#      build is also the measurement of whether the pin builds HEAD at all.
#   2. DDC: move that build aside, rebuild HEAD's compiler and std at the SAME
#      path with --ddc-seed as the compiler (the pinned seed's cargo still
#      drives), and require the two stage2 trees to be byte-identical. Then
#      finish the pinned-seed build (full stage2, dist archives) and require
#      every compared stage2 entry to be unchanged by it. The
#      receipt records how that seed relates to the pin (mint_seed_support.py
#      DDC_RELATIONS): lineage-disjoint (a stock compiler; the only DIVERSE
#      relation), same-lineage, pin-ancestor or reproducibility-control. The
#      default DDC seed is the newest atpkg trust pack whose compiler is not the
#      pin: once packs are cut from pins, the previous-but-one pack, which is
#      the seed that built the pin (pin-ancestor). A cut that anchors the chain
#      passes --ddc-seed with a stock-lineage sysroot.
#   3. Install the minted archives, require the compiler, driver and std they
#      ship to be the bytes the DDC compared, and rebuild HEAD's stage2 from them.
#   4. Write build/pack-mint-*/trust-seed-mint, which scripts/promote-toolchain.sh
#      copies into the toolchain as SEED-MINT, and the re-pin: src/stage0, the
#      seed ledger and the channel metadata as ONE commit whose parent is HEAD,
#      on branch seed/repin-<HEAD>. The checkout is never modified.
#
# What the DDC establishes: the stage2 compiler and std that ship are the bytes
# HEAD's source compiles to when the pinned seed's compiler (trustc and its std)
# is replaced by another one. A subversion carried by the pinned seed's
# compiler and not by the DDC seed cannot reach the pack. It does not cover
# what both builds share (the pinned seed's cargo as build driver, LLVM and the
# host C/C++ toolchain and linker, python, the source), a subversion present in
# both seeds (every Trust compiler shares the Trust lineage, and the pin's own
# ancestors can have passed anything to it; only a stock-lineage seed is
# disjoint from it), or the other programs stage2 ships beside the compiler,
# which stage1 builds and nothing compares. A --ddc-seed at the pin's own
# commit is a reproducibility control: it stops after the comparison and writes
# no receipt and no re-pin.
#
# The workflow records its exact inputs. It does not call PATH scrubbing a
# kernel execution proof; the stronger execution claim belongs to
# `scripts/prove_rust_free_build.sh --build`, which currently requires Linux
# strace and a materialized release-grade pinned seed.
set -Eeuo pipefail
umask 077

usage() {
    printf '%s\n' \
        'usage: scripts/mint_and_prove_seed.sh [options]' \
        '' \
        'Options:' \
        '  --ddc-seed DIR            Compiler sysroot for the DDC build (default: the newest' \
        '                            atpkg trust pack whose compiler is not the pin). Only a' \
        '                            stock-lineage sysroot makes the double compile diverse:' \
        '                            a rustup toolchain directory (STOCK-AS-ORACLE, D16).' \
        '  --host TARGET             Build host triple (auto-detected on macOS/Linux).' \
        '  --jobs N                  Parallel build/archive jobs (capped by build-slot admission).' \
        '  --config FILE             Bootstrap config used for the sanctioned mint.' \
        '  --resume-after-provenance DIR  Continue a retained failed mint from audited evidence.' \
        '  --resume-at-provenance DIR  Re-audit a failed provenance boundary with its original' \
        '                            retained WORK, then run the remaining archive/self-host tail.' \
        '  --source-root DIR         Frozen product checkout for continuation; orchestration' \
        '                            source stays in this script checkout. Both flags required.' \
        '  --clean-lean-lib DIR      Exact repository-pinned Clean lib/lean input; required,' \
        '                            content-bound and shared by pinned, DDC and self-host builds.' \
        '  --seed-dir DIR            Final seed sysroot (must not already exist).' \
        '  --proof-build-dir DIR     Fresh stage2 build directory (must not exist).' \
        '  --library-path DIR        Explicit native link directory (repeatable).' \
        '  --cargo-home DIR          A cargo home a networked build of this commit filled: its' \
        '                            registry/index, registry/cache and git/db (never bin/ or' \
        '                            config.toml) seed this phase private offline cargo home;' \
        '                            continuation inputs are freshly content-bound.' \
        '  --seed-dylib-path DIR     A directory first on DYLD_LIBRARY_PATH for every run, providing' \
        '                            a library a seed names by a foreign absolute path (repeatable;' \
        '                            bound by content). A seed with an unprovided foreign load is' \
        '                            refused.' \
        '  --drop-host TRIPLE        Let the re-pin drop a host the committed seed ledger records' \
        '                            (repeatable, one host each). A cut re-pins its own host only,' \
        '                            so without it a cut that would drop a recorded host stops' \
        '                            before it builds.' \
        '  --check-only              Validate the inputs and print the exact plan; build nothing.' \
        '  -h, --help                Show this help.' \
        '' \
        'The source tree and submodules must be clean. Output directories are restricted' \
        'to build/, are never overwritten, and partial temporary seed state is removed' \
        'on failure. The fresh proof build is retained as evidence if a build starts.' >&2
}

HOST=
DDC_SEED=
CONFIG_SOURCE=
RESUME_EVIDENCE=
RESUME_AT_PROVENANCE=0
SOURCE_ROOT=
CONTINUATION_RECORD=
CONTINUATION_RECORD_SHA256=
CLEAN_LEAN_LIB=
SEED_FINAL=
PROOF_BUILD=
CHECK_ONLY=0
BUILD_JOBS=
LIBRARY_PATHS=()
CARGO_HOME_SOURCE=
SEED_DYLIB_PATHS=()
DROP_HOSTS=()
while [ "$#" -gt 0 ]; do
    case "$1" in
        --host|--jobs|--ddc-seed|--config|--clean-lean-lib|--seed-dir|--proof-build-dir|--library-path|--cargo-home|--seed-dylib-path|--resume-after-provenance|--resume-at-provenance|--source-root|--drop-host)
            if [ "$#" -lt 2 ]; then
                printf 'error: %s requires a value\n' "$1" >&2
                usage
                exit 2
            fi
            case "$1" in
                --host) HOST=$2 ;;
                --jobs)
                    if [ -z "$2" ]; then
                        printf 'error: --jobs requires a nonempty positive count\n' >&2
                        exit 2
                    fi
                    BUILD_JOBS=$2
                    ;;
                --ddc-seed) DDC_SEED=$2 ;;
                --config) CONFIG_SOURCE=$2 ;;
                --resume-after-provenance|--resume-at-provenance)
                    if [ -n "$RESUME_EVIDENCE" ] || [ -z "$2" ]; then
                        printf 'error: continuation evidence must be supplied exactly once\n' >&2
                        exit 2
                    fi
                    RESUME_EVIDENCE=$2
                    if [ "$1" = --resume-at-provenance ]; then
                        RESUME_AT_PROVENANCE=1
                    fi
                    ;;
                --source-root)
                    if [ -n "$SOURCE_ROOT" ] || [ -z "$2" ]; then
                        printf 'error: continuation source root must be supplied exactly once\n' >&2
                        exit 2
                    fi
                    SOURCE_ROOT=$2
                    ;;
                --clean-lean-lib) CLEAN_LEAN_LIB=$2 ;;
                --seed-dir) SEED_FINAL=$2 ;;
                --proof-build-dir) PROOF_BUILD=$2 ;;
                --library-path) LIBRARY_PATHS+=("$2") ;;
                --cargo-home) CARGO_HOME_SOURCE=$2 ;;
                --seed-dylib-path) SEED_DYLIB_PATHS+=("$2") ;;
                --drop-host)
                    if [ -z "$2" ]; then
                        printf 'error: --drop-host requires a host triple\n' >&2
                        exit 2
                    fi
                    DROP_HOSTS+=("$2")
                    ;;
            esac
            shift 2
            ;;
        --check-only)
            CHECK_ONLY=1
            shift
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        *)
            printf 'error: unknown argument: %s\n' "$1" >&2
            usage
            exit 2
            ;;
    esac
done

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
if [ "$SCRIPT_DIR" = "${BASH_SOURCE[0]}" ]; then
    SCRIPT_DIR=.
fi
ORCHESTRATION_ROOT=$(cd -P "$SCRIPT_DIR/.." && pwd -P) || {
    printf 'error: cannot resolve repository root\n' >&2
    exit 1
}
ROOT=$ORCHESTRATION_ROOT
if [ -n "$RESUME_EVIDENCE" ] || [ -n "$SOURCE_ROOT" ]; then
    if [ -z "$RESUME_EVIDENCE" ] || [ -z "$SOURCE_ROOT" ] || [ -z "$DDC_SEED" ]; then
        printf 'error: continuation requires one resume mode, --source-root and the original --ddc-seed\n' >&2
        exit 2
    fi
    ROOT=$(cd -P "$SOURCE_ROOT" && pwd -P) || {
        printf 'error: cannot resolve the frozen product source root\n' >&2
        exit 1
    }
fi
cd -P "$ROOT"

# Trust: the helper parses TOML with the stdlib `tomllib` (3.11+) under
# `-I -S`, where no user-site `tomli` backport can stand in. A bare `python3`
# is 3.9 on macOS CommandLineTools, so select the interpreter by version, the
# same candidate order prove_rust_free_build.sh and the pre-push hook use.
PYTHON_BIN=
for candidate in python3.14 python3.13 python3.12 python3.11 python3; do
    PYTHON_BIN=$(type -P "$candidate" || true)
    if [ -n "$PYTHON_BIN" ] && [ -x "$PYTHON_BIN" ] \
        && "$PYTHON_BIN" -I -S -c 'import sys; raise SystemExit(sys.version_info < (3, 11))'; then
        break
    fi
    PYTHON_BIN=
done
if [ -z "$PYTHON_BIN" ]; then
    printf 'error: python >= 3.11 is required (tomllib); tried python3.14 python3.13 python3.12 python3.11 python3\n' >&2
    exit 1
fi
PYTHON_BIN=$(
    "$PYTHON_BIN" -I -S -c 'import os,sys; print(os.path.realpath(sys.executable))'
) || {
    printf 'error: cannot canonicalize python3\n' >&2
    exit 1
}
HELPER="$ORCHESTRATION_ROOT/scripts/mint_seed_support.py"
if [ ! -f "$HELPER" ] || [ -L "$HELPER" ]; then
    printf 'error: seed helper must be a repository-owned regular file: %s\n' "$HELPER" >&2
    exit 1
fi
# Only the explicit CLI input configures Clean. Ambient selectors cannot enter
# a mint, and a directory label alone is not an Oracle-world identity.
if [ "${CLEAN_OLEAN_PINNED_LEAN_LIB+x}" = x ] || [ "${CLEAN_OLEAN_REQUIRE_PINNED_LEAN+x}" = x ]; then
    printf 'error: undeclared ambient Clean Lean selectors; use --clean-lean-lib\n' >&2
    exit 1
fi
if [ -z "$CLEAN_LEAN_LIB" ]; then
    printf 'error: --clean-lean-lib is required for the pinned Clean input\n' >&2
    exit 1
fi
CLEAN_LEAN_LIB=$("$PYTHON_BIN" -I -S "$HELPER" clean-lean-inputs \
    --root "$ROOT" --library "$CLEAN_LEAN_LIB" --path-only)
# Trust: consume the admission before run_clean removes ambient build controls.
# The explicit override is shared by all pinned, DDC and self-host x.py calls,
# and by both observations of the effective mint configuration.
BUILD_JOB_ARGS=()
if [ -n "$BUILD_JOBS" ]; then
    BUILD_JOB_ARGS=(--jobs "$BUILD_JOBS")
fi
BUILD_JOBS=$("$PYTHON_BIN" -I -S "$HELPER" build-jobs ${BUILD_JOB_ARGS[@]+"${BUILD_JOB_ARGS[@]}"})
if [ -n "${RESUME_EVIDENCE:-}" ] && [ -z "$BUILD_JOBS" ]; then
    printf 'error: continuation requires an explicit admitted --jobs count\n' >&2
    exit 2
fi
BUILD_JOB_ARGS=()
if [ -n "$BUILD_JOBS" ]; then
    BUILD_JOB_ARGS=(--jobs "$BUILD_JOBS")
fi
ENV_BIN=$(type -P env || true)
MKDIR_BIN=$(type -P mkdir || true)
if [ -z "$ENV_BIN" ] || [ -z "$MKDIR_BIN" ]; then
    printf 'error: env and mkdir executables are required\n' >&2
    exit 1
fi
ENV_BIN=$("$PYTHON_BIN" -I -S "$HELPER" canonical-file "$ENV_BIN" "env executable")
MKDIR_BIN=$(
    "$PYTHON_BIN" -I -S "$HELPER" canonical-file "$MKDIR_BIN" "mkdir executable"
)

if [ -z "$CONFIG_SOURCE" ]; then
    if [ -f "$ROOT/bootstrap.toml" ] && [ ! -L "$ROOT/bootstrap.toml" ]; then
        CONFIG_SOURCE="$ROOT/bootstrap.toml"
    elif [ -f "$ROOT/config.toml" ] && [ ! -L "$ROOT/config.toml" ]; then
        CONFIG_SOURCE="$ROOT/config.toml"
    else
        printf 'error: --config is required when no regular bootstrap.toml/config.toml exists\n' >&2
        exit 1
    fi
elif [[ "$CONFIG_SOURCE" != /* ]]; then
    CONFIG_SOURCE="$ROOT/$CONFIG_SOURCE"
fi
CONFIG_SOURCE=$(
    "$PYTHON_BIN" -I -S "$HELPER" canonical-file \
        "$CONFIG_SOURCE" "bootstrap source configuration"
)
case "$CONFIG_SOURCE" in
    "$ROOT"/*) ;;
    *)
        printf 'error: bootstrap config must be inside the authenticated checkout: %s\n' \
            "$CONFIG_SOURCE" >&2
        exit 1
        ;;
esac
# The pin is the only seed: no stage0 tool may be configured (D12).
"$PYTHON_BIN" -I -S "$HELPER" require-pinned-seed "$ROOT" "$CONFIG_SOURCE"
CONFIG_SHA256=$("$PYTHON_BIN" -I -S "$HELPER" file-sha256 "$CONFIG_SOURCE")
CONFIG_CLOSURE_FINGERPRINT=$(
    "$PYTHON_BIN" -I -S "$HELPER" config-fingerprint "$ROOT" "$CONFIG_SOURCE"
)
CANONICAL_LIBRARY_PATHS=()
# ${a[@]+"${a[@]}"}: bash 3.2 (macOS /bin/bash) treats an empty array as unbound under set -u.
for library_path in ${LIBRARY_PATHS[@]+"${LIBRARY_PATHS[@]}"}; do
    if [[ "$library_path" != /* ]]; then
        library_path="$ROOT/$library_path"
    fi
    CANONICAL_LIBRARY_PATHS+=(
        "$("$PYTHON_BIN" -I -S "$HELPER" canonical-directory \
            "$library_path" "explicit native library directory")"
    )
done
NATIVE_LIBRARY_PATH=
if [ "${#CANONICAL_LIBRARY_PATHS[@]}" -gt 0 ]; then
    NATIVE_LIBRARY_PATH=$(IFS=:; printf '%s' "${CANONICAL_LIBRARY_PATHS[*]}")
fi
CANONICAL_SEED_DYLIB_PATHS=()
SEED_DYLIB_ARGS=()
for seed_dylib_path in ${SEED_DYLIB_PATHS[@]+"${SEED_DYLIB_PATHS[@]}"}; do
    if [[ "$seed_dylib_path" != /* ]]; then
        seed_dylib_path="$ROOT/$seed_dylib_path"
    fi
    seed_dylib_path=$("$PYTHON_BIN" -I -S "$HELPER" canonical-directory \
        "$seed_dylib_path" "seed dylib directory")
    CANONICAL_SEED_DYLIB_PATHS+=("$seed_dylib_path")
    SEED_DYLIB_ARGS+=(--seed-dylib-path "$seed_dylib_path")
done
SEED_DYLIB_PATH=
if [ "${#CANONICAL_SEED_DYLIB_PATHS[@]}" -gt 0 ]; then
    SEED_DYLIB_PATH=$(IFS=:; printf '%s' "${CANONICAL_SEED_DYLIB_PATHS[*]}")
fi
CARGO_HOME_ARGS=()
if [ -n "$CARGO_HOME_SOURCE" ]; then
    if [[ "$CARGO_HOME_SOURCE" != /* ]]; then
        CARGO_HOME_SOURCE="$ROOT/$CARGO_HOME_SOURCE"
    fi
    CARGO_HOME_SOURCE=$("$PYTHON_BIN" -I -S "$HELPER" canonical-directory \
        "$CARGO_HOME_SOURCE" "cargo home input")
    CARGO_HOME_ARGS=(--source "$CARGO_HOME_SOURCE")
fi

VERSION=$("$PYTHON_BIN" -I -S "$HELPER" version "$ROOT")
if [ -n "$HOST" ]; then
    HOST=$("$PYTHON_BIN" -I -S "$HELPER" host --value "$HOST")
else
    HOST=$("$PYTHON_BIN" -I -S "$HELPER" host)
fi
case "$HOST" in
    *-apple-darwin|*-unknown-linux-gnu|*-unknown-linux-musl) ;;
    *)
        printf 'error: executable self-host workflow is unsupported for %s\n' "$HOST" >&2
        printf '       use a native macOS/Linux host or extend the audited launcher first\n' >&2
        exit 1
        ;;
esac
# A cut re-pins its own host only. Every other host the committed seed ledger
# records leaves the pin only by a typed --drop-host, and a host whose record
# carries root_disclosure (a fixed point, docs/PLAN.md PKG-S6) cannot be cut by
# the mint at all: stop here, in seconds, before anything is built.
# ${a[@]+"${a[@]}"}: bash 3.2 (macOS /bin/bash) treats an empty array as unbound under set -u.
DROP_HOST_ARGS=()
for drop_host in ${DROP_HOSTS[@]+"${DROP_HOSTS[@]}"}; do
    DROP_HOST_ARGS+=(--drop-host "$drop_host")
done
"$PYTHON_BIN" -I -S "$HELPER" recorded-hosts --root "$ROOT" --host "$HOST" \
    ${DROP_HOST_ARGS[@]+"${DROP_HOST_ARGS[@]}"}
IFS=$'\t' read -r COMMIT SOURCE_DATE_EPOCH COMMIT_DATE < <(
    "$PYTHON_BIN" -I -S "$HELPER" repo-state "$ROOT"
)
if [ -z "$COMMIT" ] || [ -z "$SOURCE_DATE_EPOCH" ] || [ -z "$COMMIT_DATE" ]; then
    printf 'error: repository metadata helper returned an incomplete record\n' >&2
    exit 1
fi
IFS=$'\t' read -r PIN_COMMIT PIN_DATE PIN_VERSION PIN_DIST_SERVER < <(
    "$PYTHON_BIN" -I -S "$HELPER" pin "$ROOT"
)
if [ -z "$PIN_COMMIT" ] || [ -z "$PIN_DIST_SERVER" ]; then
    printf 'error: cannot read the src/stage0 pin\n' >&2
    exit 1
fi
"$PYTHON_BIN" -I -S "$HELPER" check-repin-date "$ROOT" "$COMMIT_DATE"
if [ -z "$DDC_SEED" ]; then
    DDC_SEED=$("$PYTHON_BIN" -I -S "$HELPER" default-ddc-seed "$ROOT")
elif [[ "$DDC_SEED" != /* ]]; then
    DDC_SEED="$ROOT/$DDC_SEED"
fi
DDC_LINE=$("$PYTHON_BIN" -I -S "$HELPER" ddc-seed --root "$ROOT" --seed "$DDC_SEED" --host "$HOST" \
    ${SEED_DYLIB_ARGS[@]+"${SEED_DYLIB_ARGS[@]}"})
IFS=$'\t' read -r DDC_RELATION DDC_COMMIT DDC_DATE DDC_LINEAGE DDC_COMPILER DDC_SEED <<< "$DDC_LINE"
REPIN_BRANCH="seed/repin-${COMMIT:0:12}"
if git -C "$ROOT" rev-parse --verify --quiet "refs/heads/$REPIN_BRANCH" >/dev/null; then
    printf 'error: branch %s already exists; a re-pin is never moved\n' "$REPIN_BRANCH" >&2
    exit 1
fi
IDENTITY=$(git -C "$ROOT" var GIT_COMMITTER_IDENT) || {
    printf 'error: git has no committer identity for the re-pin commit\n' >&2
    exit 1
}
IDENTITY=${IDENTITY% * *}

if [ -z "$SEED_FINAL" ]; then
    SEED_FINAL="$ROOT/build/trust-seed-$VERSION-$HOST-${COMMIT:0:12}"
elif [[ "$SEED_FINAL" != /* ]]; then
    SEED_FINAL="$ROOT/$SEED_FINAL"
fi
if [ -z "$PROOF_BUILD" ]; then
    PROOF_BUILD="$ROOT/build/self-host-proof-$VERSION-$HOST-${COMMIT:0:12}"
elif [[ "$PROOF_BUILD" != /* ]]; then
    PROOF_BUILD="$ROOT/$PROOF_BUILD"
fi
"$PYTHON_BIN" -I -S "$HELPER" check-output \
    "$ROOT" "$SEED_FINAL" "final seed sysroot"
"$PYTHON_BIN" -I -S "$HELPER" check-output \
    "$ROOT" "$PROOF_BUILD" "fresh proof build directory"
MINT_BUILD="$ROOT/build/pack-mint-$VERSION-$HOST-${COMMIT:0:12}"
if [ -z "$RESUME_EVIDENCE" ]; then
    "$PYTHON_BIN" -I -S "$HELPER" check-output \
        "$ROOT" "$MINT_BUILD" "fresh pack-mint build directory"
elif [ ! -d "$MINT_BUILD" ] || [ -L "$MINT_BUILD" ]; then
    printf 'error: continuation requires its retained regular MINT directory: %s\n' "$MINT_BUILD" >&2
    exit 1
fi
"$PYTHON_BIN" -I -S "$HELPER" check-output \
    "$ROOT" "$MINT_BUILD.pinned" "DDC staging directory"

# The pin's archives are materialized and digest-bound, and the configuration
# this cut reads names no seed of its own.
RUST_BOOTSTRAP_CONFIG="$CONFIG_SOURCE" "$PYTHON_BIN" -I \
    "$ROOT/scripts/check_seed_freshness.py" --require-payloads --host "$HOST"

DIST="$MINT_BUILD/dist"
COMPONENTS=(trust-std trustc trustc-dev targo trustfmt)
DIST_PATHS=()
for component in "${COMPONENTS[@]}"; do
    DIST_PATHS+=("$component-$VERSION-trust-$HOST.tar.xz")
done

printf '== pack-cut seed plan ==\n'
printf '  source:       %s (%s, %s)\n' "$VERSION" "$COMMIT" "$COMMIT_DATE"
printf '  host:         %s\n' "$HOST"
printf '  build jobs:   %s\n' "${BUILD_JOBS:-bootstrap configuration default}"
printf '  config:       %s\n' "$CONFIG_SOURCE"
printf '  pinned seed:  %s (%s, %s)\n' "$PIN_COMMIT" "$PIN_DATE" "$PIN_VERSION"
printf '  DDC seed:     %s (%s, %s lineage, %s) at %s\n' "$DDC_COMMIT" "$DDC_DATE" "$DDC_LINEAGE" "$DDC_RELATION" "$DDC_COMPILER"
printf '  mint build:   %s\n' "$MINT_BUILD"
printf '  seed output:  %s\n' "$SEED_FINAL"
printf '  proof output: %s\n' "$PROOF_BUILD"
printf '  re-pin:       branch %s, committed as %s\n' "$REPIN_BRANCH" "$IDENTITY"
case "$DDC_RELATION" in
    lineage-disjoint) ;;
    reproducibility-control)
        printf '  NOTE: the DDC seed is the pin'"'"'s own commit: this run is a reproducibility\n'
        printf '        control, not a DDC. It stops after the comparison and writes no\n'
        printf '        receipt and no re-pin.\n'
        ;;
    *)
        printf '  NOTE: a %s DDC seed makes this a double compile, not a diverse one; pass\n' "$DDC_RELATION"
        printf '        --ddc-seed with a stock-lineage sysroot to anchor the seed chain.\n'
        ;;
esac
if [ -n "$NATIVE_LIBRARY_PATH" ]; then
    printf '  library path: %s\n' "$NATIVE_LIBRARY_PATH"
fi
printf '  cargo home:   %s\n' "${CARGO_HOME_SOURCE:-none (a fresh, empty, offline cargo home)}"
if [ -n "$SEED_DYLIB_PATH" ]; then
    printf '  seed dylibs:  %s (first on DYLD_LIBRARY_PATH)\n' "$SEED_DYLIB_PATH"
fi
printf '  exact archives:\n'
printf '    %s\n' "${DIST_PATHS[@]}"
if [ -n "$RESUME_EVIDENCE" ]; then
    RECOVERY_HELPER="$ORCHESTRATION_ROOT/scripts/mint_seed_recovery.py"
    if [ ! -f "$RECOVERY_HELPER" ] || [ -L "$RECOVERY_HELPER" ]; then
        printf 'error: continuation requires its repository-owned recovery verifier\n' >&2
        exit 1
    fi
    RESUME_EVIDENCE=$("$PYTHON_BIN" -I -S "$HELPER" canonical-directory \
        "$RESUME_EVIDENCE" "retained mint evidence")
    CONTINUATION_RECORD_ROOT="$MINT_BUILD"
    if [ "$RESUME_AT_PROVENANCE" -eq 1 ]; then
        CONTINUATION_RECORD_ROOT="$RESUME_EVIDENCE"
    fi
    CONTINUATION_RECORD=$("$PYTHON_BIN" -I -S -c \
        'import pathlib,sys,uuid; print(pathlib.Path(sys.argv[1]) / ("mint-continuation-" + uuid.uuid4().hex + ".json"))' \
        "$CONTINUATION_RECORD_ROOT")
    RECOVERY_MODE=prepare
    if [ "$CHECK_ONLY" -eq 1 ]; then
        RECOVERY_MODE=inspect
    fi
    if [ "$RESUME_AT_PROVENANCE" -eq 1 ]; then
        RECOVERY_MODE="$RECOVERY_MODE-at-provenance"
    fi
    "$PYTHON_BIN" -I -S "$RECOVERY_HELPER" "$RECOVERY_MODE" \
        --root "$ROOT" --build "$MINT_BUILD" --evidence "$RESUME_EVIDENCE" \
        --output "$CONTINUATION_RECORD"
    if [ "$CHECK_ONLY" -eq 1 ]; then
        printf '\nCONTINUATION INPUTS INSPECTED: %s\n' "$CONTINUATION_RECORD"
        printf 'No operational namespace or self-host result was created.\n'
        exit 0
    fi
    CONTINUATION_RECORD_SHA256=$("$PYTHON_BIN" -I -S "$HELPER" file-sha256 "$CONTINUATION_RECORD")
    WORK=$("$PYTHON_BIN" -I -S "$HELPER" continuation-context \
        --root "$ROOT" --record "$CONTINUATION_RECORD" \
        --sha256 "$CONTINUATION_RECORD_SHA256" --work-only)
elif [ "$CHECK_ONLY" -eq 1 ]; then
    printf '\nCHECK OK: the pin is materialized, the inputs are committed and the output\n'
    printf '          paths are new; no build was run.\n'
    exit 0
else
    WORK=$("$PYTHON_BIN" -I -S "$HELPER" make-work "$ROOT")
fi
CHILD_PID=
REPIN_COMMIT=
# A run that stops after writing the re-pin must not leave it to be landed.
drop_repin() {
    if [ -n "$REPIN_COMMIT" ]; then
        git -C "$ROOT" update-ref -d "refs/heads/$REPIN_BRANCH" "$REPIN_COMMIT" 2>/dev/null || true
    fi
}
finish_work() {
    local status=$1
    if [ -n "${WORK:-}" ] && [ -d "$WORK" ]; then
        if [ "$status" -eq 0 ] && [ "${RESUME_AT_PROVENANCE:-0}" -eq 0 ]; then
            "$PYTHON_BIN" -I -S "$HELPER" cleanup-work "$ROOT" "$WORK" || true
        else
            printf 'Retained failed mint work and evidence: %s\n' "$WORK" >&2
        fi
    fi
}
cleanup() {
    local status=$?
    trap - EXIT HUP INT TERM
    if [ "$status" -ne 0 ]; then
        drop_repin
    fi
    if [ -n "${CHILD_PID:-}" ]; then
        kill -TERM "$CHILD_PID" 2>/dev/null || true
        wait "$CHILD_PID" 2>/dev/null || true
        kill -KILL "$CHILD_PID" 2>/dev/null || true
        CHILD_PID=
    fi
    "$PYTHON_BIN" -I -S "$HELPER" ddc-restore --root "$ROOT" --build "$MINT_BUILD" || true
    finish_work "$status"
    exit "$status"
}
signal_exit() {
    local signal=$1
    local status=$2
    trap - EXIT HUP INT TERM
    drop_repin
    if [ -n "${CHILD_PID:-}" ]; then
        kill -TERM "$CHILD_PID" 2>/dev/null || true
        wait "$CHILD_PID" 2>/dev/null || true
        kill -KILL "$CHILD_PID" 2>/dev/null || true
        CHILD_PID=
    fi
    "$PYTHON_BIN" -I -S "$HELPER" ddc-restore --root "$ROOT" --build "$MINT_BUILD" || true
    finish_work "$status"
    printf 'error: interrupted by %s\n' "$signal" >&2
    exit "$status"
}
trap cleanup EXIT
trap 'signal_exit HUP 129' HUP
trap 'signal_exit INT 130' INT
trap 'signal_exit TERM 143' TERM

if [ -n "$CONTINUATION_RECORD" ]; then
    "$PYTHON_BIN" -I -S "$HELPER" continuation-context \
        --root "$ROOT" --record "$CONTINUATION_RECORD" \
        --sha256 "$CONTINUATION_RECORD_SHA256" --config "$CONFIG_SOURCE" \
        --host "$HOST" --clean-lean-lib "$CLEAN_LEAN_LIB" \
        --library-path "$NATIVE_LIBRARY_PATH" --seed-dylib-path "$SEED_DYLIB_PATH" \
        --ddc-seed "$DDC_SEED" --cargo-source "$CARGO_HOME_SOURCE" \
        --python "$PYTHON_BIN" >/dev/null
    ENV_BIN="$WORK/safe-bin/env"
    MKDIR_BIN="$WORK/safe-bin/mkdir"
fi

CONFIG_MANIFEST="$WORK/bootstrap-config-closure.json"
if [ "$RESUME_AT_PROVENANCE" -eq 0 ]; then
"$PYTHON_BIN" -I -S "$HELPER" config-manifest \
    "$ROOT" "$CONFIG_SOURCE" "$CONFIG_MANIFEST"
fi
CONFIG_MANIFEST_SHA256=$("$PYTHON_BIN" -I -S "$HELPER" file-sha256 "$CONFIG_MANIFEST")
CLEAN_LEAN_MANIFEST="$WORK/clean-lean-inputs.json"
if [ "$RESUME_AT_PROVENANCE" -eq 0 ]; then
"$PYTHON_BIN" -I -S "$HELPER" clean-lean-inputs \
    --root "$ROOT" --library "$CLEAN_LEAN_LIB" --output "$CLEAN_LEAN_MANIFEST"
fi
CLEAN_LEAN_MANIFEST_SHA256=$("$PYTHON_BIN" -I -S "$HELPER" file-sha256 "$CLEAN_LEAN_MANIFEST")
LIBRARY_MANIFEST="$WORK/native-library-inputs.json"
if [ "$RESUME_AT_PROVENANCE" -eq 0 ]; then
"$PYTHON_BIN" -I -S "$HELPER" library-manifest \
    "$LIBRARY_MANIFEST" ${CANONICAL_LIBRARY_PATHS[@]+"${CANONICAL_LIBRARY_PATHS[@]}"}
fi
LIBRARY_MANIFEST_SHA256=$("$PYTHON_BIN" -I -S "$HELPER" file-sha256 "$LIBRARY_MANIFEST")
MINT_TOOLS_MANIFEST="$WORK/mint-toolchain-inputs.json"
if [ "$RESUME_AT_PROVENANCE" -eq 0 ]; then
"$PYTHON_BIN" -I -S "$HELPER" mint-tools-manifest \
    "$ROOT" "$CONFIG_SOURCE" "$MINT_TOOLS_MANIFEST"
fi
MINT_TOOLS_MANIFEST_SHA256=$(
    "$PYTHON_BIN" -I -S "$HELPER" file-sha256 "$MINT_TOOLS_MANIFEST"
)
SEED_DYLIB_MANIFEST="$WORK/seed-dylib-inputs.json"
if [ "$RESUME_AT_PROVENANCE" -eq 0 ]; then
"$PYTHON_BIN" -I -S "$HELPER" library-manifest \
    "$SEED_DYLIB_MANIFEST" ${CANONICAL_SEED_DYLIB_PATHS[@]+"${CANONICAL_SEED_DYLIB_PATHS[@]}"}
fi
SEED_DYLIB_MANIFEST_SHA256=$("$PYTHON_BIN" -I -S "$HELPER" file-sha256 "$SEED_DYLIB_MANIFEST")
# ONE private cargo home for every x.py run of the cut (offline): the crate
# sources come from --cargo-home, and one path keeps the two builds of the
# double compile alike.
CARGO_HOME_SHARED="$WORK/cargo-home"
CARGO_HOME_MANIFEST="$WORK/cargo-home-inputs.json"
if [ "$RESUME_AT_PROVENANCE" -eq 0 ]; then
"$PYTHON_BIN" -I -S "$HELPER" cargo-home-inputs ${CARGO_HOME_ARGS[@]+"${CARGO_HOME_ARGS[@]}"} \
    --destination "$CARGO_HOME_SHARED" --output "$CARGO_HOME_MANIFEST"
fi

SAFE_BIN="$WORK/safe-bin"
PATH_MANIFEST="$WORK/safe-path.json"
# Only the reviewed native build-helper profile enters PATH. In particular an
# unrelated app's aliases are neither executable build inputs nor revalidated
# after the hours-long mint. Every declared helper still binds its exact bytes
# and identity at its original location; missing/unreadable helpers refuse.
if [ -n "$CONTINUATION_RECORD" ]; then
    "$PYTHON_BIN" -I -S "$HELPER" revalidate-path \
        --path "$SAFE_BIN" --manifest "$PATH_MANIFEST"
else
    "$PYTHON_BIN" -I -S "$HELPER" safe-path \
        --input "$PATH" --output "$SAFE_BIN" --manifest "$PATH_MANIFEST" \
        --host "$HOST" --python "$PYTHON_BIN"
fi
PATH_MANIFEST_SHA256=$("$PYTHON_BIN" -I -S "$HELPER" file-sha256 "$PATH_MANIFEST")

run_clean() {
    local path_value=$1
    local environment_name=$2
    shift 2
    local environment_root="$WORK/environment-$environment_name"
    "$MKDIR_BIN" -p "$environment_root/home" "$environment_root/tmp" \
        "$environment_root/rustup-home" "$environment_root/xdg-config"
    local environment=(
        HOME="$environment_root/home"
        USER=trust-seed
        LOGNAME=trust-seed
        PATH="$path_value"
        LANG=C LC_ALL=C TZ=UTC
        TMPDIR="$environment_root/tmp"
        CARGO_HOME="$CARGO_HOME_SHARED"
        RUSTUP_HOME="$environment_root/rustup-home"
        XDG_CONFIG_HOME="$environment_root/xdg-config"
        CARGO_NET_OFFLINE=true
        GIT_CONFIG_NOSYSTEM=1 GIT_CONFIG_GLOBAL=/dev/null
        SOURCE_DATE_EPOCH="$SOURCE_DATE_EPOCH"
        CLEAN_OLEAN_PINNED_LEAN_LIB="$CLEAN_LEAN_LIB"
        CLEAN_OLEAN_REQUIRE_PINNED_LEAN=1
    )
    if [ -n "$NATIVE_LIBRARY_PATH" ]; then
        environment+=(LIBRARY_PATH="$NATIVE_LIBRARY_PATH")
    fi
    if [ -n "$SEED_DYLIB_PATH" ]; then
        # dyld searches DYLD_LIBRARY_PATH by leaf name BEFORE a load command's
        # absolute path: a seed's foreign library comes from the declared copy.
        environment+=(DYLD_LIBRARY_PATH="$SEED_DYLIB_PATH")
    fi
    "$ENV_BIN" -i "${environment[@]}" \
        "$PYTHON_BIN" -I -S "$HELPER" supervise \
        --timeout-seconds 43200 -- "$@" &
    CHILD_PID=$!
    set +e
    wait "$CHILD_PID"
    local status=$?
    set -e
    CHILD_PID=
    return "$status"
}

step() {
    printf '\n== %s ==\n' "$*"
}

# Every x.py run of the cut: <PATH> <environment> <config> <build dir> <verb> [paths].
xpy() {
    local path_value=$1
    local environment_name=$2
    local config=$3
    local build_dir=$4
    local verb=$5
    shift 5
    "$PYTHON_BIN" -I -S "$HELPER" verify-clean-lean-inputs "$ROOT" "$CLEAN_LEAN_MANIFEST" \
        --library "$CLEAN_LEAN_LIB" --sha256 "$CLEAN_LEAN_MANIFEST_SHA256"
    run_clean "$path_value" "$environment_name" \
        "$PYTHON_BIN" -I -S "$ROOT/x.py" \
        --config "$config" \
        "$verb" \
        --build-dir "$build_dir" \
        --build "$HOST" \
        --host "$HOST" \
        --target "$HOST" \
        --stage 2 \
        ${BUILD_JOB_ARGS[@]+"${BUILD_JOB_ARGS[@]}"} \
        --set build.submodules=false \
        --set rust.channel=trust \
        --set rust.download-rustc=false \
        --set llvm.download-ci-llvm=false \
        "$@"
    "$PYTHON_BIN" -I -S "$HELPER" verify-clean-lean-inputs "$ROOT" "$CLEAN_LEAN_MANIFEST" \
        --library "$CLEAN_LEAN_LIB" --sha256 "$CLEAN_LEAN_MANIFEST_SHA256"
}

if [ -z "$CONTINUATION_RECORD" ]; then
step "observe source, seed, native authority and the absent LLVM before the mint starts"
STAGE_OBSERVATION="$WORK/mint-stage-observation.json"
run_clean "$SAFE_BIN" mint "$PYTHON_BIN" -I -S "$HELPER" stage-evidence-before \
    --root "$ROOT" --build "$MINT_BUILD" --config "$CONFIG_SOURCE" --host "$HOST" \
    --observation "$STAGE_OBSERVATION" ${BUILD_JOB_ARGS[@]+"${BUILD_JOB_ARGS[@]}"}

step "build HEAD's compiler and std from the src/stage0 pin"
xpy "$SAFE_BIN" mint "$CONFIG_SOURCE" "$MINT_BUILD" build compiler/rustc library/std
"$PYTHON_BIN" -I -S "$HELPER" pinned-stage0 --root "$ROOT" --build "$MINT_BUILD" \
    --host "$HOST" --output "$WORK/pinned-seed.json" ${SEED_DYLIB_ARGS[@]+"${SEED_DYLIB_ARGS[@]}"}
"$PYTHON_BIN" -I -S "$HELPER" stage2-manifest "$MINT_BUILD/$HOST/stage2" \
    "$WORK/stage2-pinned-seed.json"

step "double compile ($DDC_RELATION): HEAD's compiler and std from $DDC_COMMIT, at the same path"
"$PYTHON_BIN" -I -S "$HELPER" ddc-seed --root "$ROOT" --seed "$DDC_SEED" --host "$HOST" \
    --output "$WORK/ddc-seed.json" ${SEED_DYLIB_ARGS[@]+"${SEED_DYLIB_ARGS[@]}"} >/dev/null
"$PYTHON_BIN" -I -S "$HELPER" ddc-stage --root "$ROOT" --build "$MINT_BUILD" --host "$HOST"
DDC_CONFIG="$WORK/bootstrap.ddc.toml"
"$PYTHON_BIN" -I -S "$HELPER" write-ddc-config \
    --source "$CONFIG_SOURCE" \
    --output "$DDC_CONFIG" \
    --rustc "$DDC_COMPILER" \
    --cargo "$MINT_BUILD.pinned/$HOST/stage0/bin/cargo" \
    --fail-tool "$WORK/bin/ddc-unavailable-tippy"
# The same environment as the pinned-seed build (HOME, TMPDIR, cargo home): the
# two builds differ in the compiler and nothing else.
xpy "$SAFE_BIN" mint "$DDC_CONFIG" "$MINT_BUILD" build compiler/rustc library/std
"$PYTHON_BIN" -I -S "$HELPER" stage2-manifest "$MINT_BUILD/$HOST/stage2" \
    "$WORK/stage2-ddc-seed.json"
# ddc-restore deletes the DDC build: keep both seeds' copies of every entry the
# trees disagree on first, in the pinned build that the restore puts back, so a
# failed comparison can be diffed instead of rebuilt.
DDC_EVIDENCE_ENTRIES=$("$PYTHON_BIN" -I -S "$HELPER" ddc-evidence \
    --pinned-manifest "$WORK/stage2-pinned-seed.json" \
    --ddc-manifest "$WORK/stage2-ddc-seed.json" \
    --pinned-stage2 "$MINT_BUILD.pinned/$HOST/stage2" \
    --ddc-stage2 "$MINT_BUILD/$HOST/stage2" \
    --output "$MINT_BUILD.pinned/ddc-evidence")
"$PYTHON_BIN" -I -S "$HELPER" ddc-restore --root "$ROOT" --build "$MINT_BUILD"
if [ "$DDC_EVIDENCE_ENTRIES" != 0 ]; then
    printf 'DDC evidence: both seeds'"'"' copies of the %s differing entries are in %s\n' \
        "$DDC_EVIDENCE_ENTRIES" "$MINT_BUILD/ddc-evidence" >&2
fi
"$PYTHON_BIN" -I -S "$HELPER" ddc-seed --root "$ROOT" --seed "$DDC_SEED" --host "$HOST" \
    --output "$WORK/ddc-seed-post-build.json" ${SEED_DYLIB_ARGS[@]+"${SEED_DYLIB_ARGS[@]}"} >/dev/null
if [ "$("$PYTHON_BIN" -I -S "$HELPER" file-sha256 "$WORK/ddc-seed.json")" \
    != "$("$PYTHON_BIN" -I -S "$HELPER" file-sha256 "$WORK/ddc-seed-post-build.json")" ]; then
    printf 'error: the DDC seed changed during the DDC build\n' >&2
    exit 1
fi
STAGE2_TREE_SHA256=$(
    "$PYTHON_BIN" -I -S "$HELPER" ddc-compare \
        "$WORK/stage2-pinned-seed.json" "$WORK/stage2-ddc-seed.json"
)
printf '  identical stage2 trees from both seeds: %s\n' "$STAGE2_TREE_SHA256"
if [ "$DDC_RELATION" = reproducibility-control ]; then
    printf '\nCONTROL: HEAD built byte-identically from the pin and from the pin'"'"'s own\n'
    printf '         commit, so this build is reproducible. No receipt, no re-pin.\n'
    exit 0
fi

step "build the dist archives, the full stage2 and their channel manifest"
# dist BEFORE the full build. `x.py dist` re-assembles stage2 as Kind::Dist,
# and that Assemble prunes every rustc_private crate from the stage2 target
# libdir (compile.rs, `prune_public_sysroot_compiler_artifacts`; the rustc-dev
# top-up is Kind::Build only). The DDC compared a Kind::Build stage2 that has
# them, and scripts/promote-toolchain.sh promotes this stage2 and refuses one
# without them. Measured 2026-10-06: build --stage 2 then dist trustc took the
# target libdir's librustc_* from 88 to 10 (librustc_public among those lost).
# The full build afterwards re-assembles as Kind::Build from the same stamp,
# so stage2 ends in the shape the DDC compared; verify-stage2-unchanged below
# is what holds that. The archives ship rustc-dev as `trustc-dev` either way.
DIST_COMPONENT_LINE=$("$PYTHON_BIN" -I -S "$HELPER" dist-components "$ROOT")
read -r -a DIST_COMPONENTS <<< "$DIST_COMPONENT_LINE"
xpy "$SAFE_BIN" mint "$CONFIG_SOURCE" "$MINT_BUILD" dist "${DIST_COMPONENTS[@]}"
xpy "$SAFE_BIN" mint "$CONFIG_SOURCE" "$MINT_BUILD" build
xpy "$SAFE_BIN" mint "$CONFIG_SOURCE" "$MINT_BUILD" build src/tools/build-manifest
BUILD_MANIFEST=$(
    "$PYTHON_BIN" -I -S "$HELPER" build-manifest-tool --build "$MINT_BUILD" --host "$HOST"
)
# build-manifest's address argument is inert: prepare.py rewrites every URL
# from the pin's dist_server.
run_clean "$SAFE_BIN" mint "$BUILD_MANIFEST" "$DIST" "$DIST" "$COMMIT_DATE" \
    https://trust.invalid trust
# The full build and dist ran over the compiler and std the DDC compared.
"$PYTHON_BIN" -I -S "$HELPER" verify-stage2-unchanged \
    "$WORK/stage2-pinned-seed.json" "$MINT_BUILD/$HOST/stage2"

step "bind and re-verify the minted stage's actual build-time provenance"
run_clean "$SAFE_BIN" mint "$PYTHON_BIN" -I -S "$HELPER" stage-evidence-after \
    --root "$ROOT" --build "$MINT_BUILD" --config "$CONFIG_SOURCE" --host "$HOST" \
    --observation "$STAGE_OBSERVATION" ${BUILD_JOB_ARGS[@]+"${BUILD_JOB_ARGS[@]}"}
else
    step "re-observe the retained pinned stage0 after audited continuation admission"
    PINNED_OBSERVATION="$WORK/pinned-seed.json"
    if [ "$RESUME_AT_PROVENANCE" -eq 1 ]; then
        PINNED_OBSERVATION="$WORK/pinned-seed-recovery.json"
    fi
    "$PYTHON_BIN" -I -S "$HELPER" pinned-stage0 --root "$ROOT" --build "$MINT_BUILD" \
        --host "$HOST" --output "$PINNED_OBSERVATION" ${SEED_DYLIB_ARGS[@]+"${SEED_DYLIB_ARGS[@]}"}
    if [ "$RESUME_AT_PROVENANCE" -eq 1 ] && \
        [ "$("$PYTHON_BIN" -I -S "$HELPER" file-sha256 "$PINNED_OBSERVATION")" != \
          "$("$PYTHON_BIN" -I -S "$HELPER" file-sha256 "$WORK/pinned-seed.json")" ]; then
        printf 'error: retained pinned stage0 differs from its fresh recovery observation\n' >&2
        exit 1
    fi
fi

step "admit only exact version/host archives and bind them to HEAD"
INPUT_MANIFEST="$WORK/seed-inputs.json"
run_clean "$SAFE_BIN" artifact-admission \
    "$PYTHON_BIN" -I -S "$HELPER" stage-artifacts \
    --dist "$DIST" \
    --work "$WORK" \
    --version "$VERSION" \
    --host "$HOST" \
    --commit "$COMMIT" \
    --manifest "$INPUT_MANIFEST"
INPUT_MANIFEST_SHA256=$("$PYTHON_BIN" -I -S "$HELPER" file-sha256 "$INPUT_MANIFEST")

step "install admitted archives into a private candidate sysroot"
SEED_WORK="$WORK/seed"
"$MKDIR_BIN" -p "$SEED_WORK"
for component in "${COMPONENTS[@]}"; do
    package="$component-$VERSION-trust-$HOST"
    installer="$WORK/unpack/$component/$package/install.sh"
    run_clean "$SAFE_BIN" install \
        "$installer" --prefix="$SEED_WORK" --disable-ldconfig
    printf '  installed %s\n' "$component"
done

SEED_SURFACE="$WORK/seed-surface.json"
run_clean "$SEED_WORK/bin:$SAFE_BIN" seed-validation \
    "$PYTHON_BIN" -I -S "$HELPER" validate-seed \
    --seed "$SEED_WORK" --version "$VERSION" --host "$HOST" \
    --output "$SEED_SURFACE"
SEED_SURFACE_SHA256=$("$PYTHON_BIN" -I -S "$HELPER" file-sha256 "$SEED_SURFACE")
CARRIED=$(
    "$PYTHON_BIN" -I -S "$HELPER" verify-archives-carry-compared \
        --seed "$SEED_WORK" --manifest "$WORK/stage2-pinned-seed.json" --host "$HOST"
)
printf '  the archives ship %s compared stage2 files, byte for byte\n' "$CARRIED"

step "generate an owner-private seed override (the checkout remains untouched)"
SEED_CONFIG="$WORK/bootstrap.seed.toml"
FAIL_TIPPY="$WORK/bin/unavailable-tippy"
"$PYTHON_BIN" -I -S "$HELPER" write-config \
    --source "$CONFIG_SOURCE" \
    --output "$SEED_CONFIG" \
    --seed "$SEED_WORK" \
    --fail-tool "$FAIL_TIPPY"
SEED_CONFIG_SHA256=$("$PYTHON_BIN" -I -S "$HELPER" file-sha256 "$SEED_CONFIG")

step "fresh stage2 rebuild under a minimal, offline environment"
xpy "$SEED_WORK/bin:$SAFE_BIN" proof "$SEED_CONFIG" "$PROOF_BUILD" build compiler/rustc

STAGE2="$PROOF_BUILD/$HOST/stage2/bin/trustc"
if [ ! -x "$STAGE2" ] || [ -L "$STAGE2" ]; then
    printf 'error: fresh build did not produce a regular stage2 trustc: %s\n' "$STAGE2" >&2
    exit 1
fi

step "sanity-check the exact fresh stage2"
SANITY_SOURCE="$WORK/self-host-sanity.rs"
SANITY_BINARY="$WORK/self-host-sanity"
printf 'fn main() { println!("Trust self-host sanity: {}", 6 * 7); }\n' > "$SANITY_SOURCE"
run_clean "$SEED_WORK/bin:$SAFE_BIN" sanity "$STAGE2" --version
run_clean "$SEED_WORK/bin:$SAFE_BIN" sanity \
    "$STAGE2" -Z trust-verify=off -o "$SANITY_BINARY" "$SANITY_SOURCE"
run_clean "$SEED_WORK/bin:$SAFE_BIN" sanity "$SANITY_BINARY"

step "write the seed-mint receipt and the commit-bound re-pin"
RECEIPT="$MINT_BUILD/trust-seed-mint"
"$PYTHON_BIN" -I -S "$HELPER" write-receipt \
    --root "$ROOT" \
    --version "$VERSION" \
    --host "$HOST" \
    --pinned-seed "$WORK/pinned-seed.json" \
    --ddc-seed "$WORK/ddc-seed.json" \
    --pinned-manifest "$WORK/stage2-pinned-seed.json" \
    --ddc-manifest "$WORK/stage2-ddc-seed.json" \
    --output "$RECEIPT"
PREPARED="$MINT_BUILD/repin"
# prepare.py writes a seed only over a materialized trustc-dev handoff under its
# artifact roots; this output root is new, so the cut lays the handoff out from
# the admitted archive (gitignored there: the re-pin commits none of it).
"$PYTHON_BIN" -I -S "$HELPER" rustc-dev-handoff \
    --root "$ROOT" \
    --input-manifest "$INPUT_MANIFEST" \
    --work "$WORK" \
    --output-root "$PREPARED/bootstrap/trust-stage0"
run_clean "$SAFE_BIN" repin \
    "$PYTHON_BIN" -I "$ROOT/src/tools/trust-stage0-dist/prepare.py" \
    --input-dist "$DIST" \
    --source-channel trust \
    --owned-channel trust \
    --archive-format xz \
    ${BUILD_JOB_ARGS[@]+"${BUILD_JOB_ARGS[@]}"} \
    --stage0-seed-only \
    --git-commit-hash "$COMMIT" \
    --date "$COMMIT_DATE" \
    --dist-server "$PIN_DIST_SERVER" \
    --output-root "$PREPARED/bootstrap/trust-stage0" \
    --stage0-output "$PREPARED/src-stage0"
REPIN_LINE=$(
    "$PYTHON_BIN" -I -S "$HELPER" repin \
        --root "$ROOT" \
        --prepared "$PREPARED" \
        --commit "$COMMIT" \
        --host "$HOST" \
        --branch "$REPIN_BRANCH" \
        --identity "$IDENTITY" \
        --receipt "$RECEIPT" \
        --surface "$SEED_SURFACE" \
        --work "$WORK" \
        ${DROP_HOST_ARGS[@]+"${DROP_HOST_ARGS[@]}"}
)
IFS=$'\t' read -r REPIN_COMMIT REPIN_TAG REPIN_STAGE0_SHA256 <<< "$REPIN_LINE"

step "revalidate source identity and publish immutable provenance"
"$PYTHON_BIN" -I -S "$HELPER" repo-state "$ROOT" --expect-commit "$COMMIT" >/dev/null
POST_INPUT_MANIFEST_SHA256=$(
    "$PYTHON_BIN" -I -S "$HELPER" file-sha256 "$INPUT_MANIFEST"
)
if [ "$POST_INPUT_MANIFEST_SHA256" != "$INPUT_MANIFEST_SHA256" ]; then
    printf 'error: admitted seed-input manifest changed during the workflow\n' >&2
    exit 1
fi
POST_SEED_CONFIG_SHA256=$("$PYTHON_BIN" -I -S "$HELPER" file-sha256 "$SEED_CONFIG")
if [ "$POST_SEED_CONFIG_SHA256" != "$SEED_CONFIG_SHA256" ]; then
    printf 'error: generated seed configuration changed during the workflow\n' >&2
    exit 1
fi
POST_SEED_SURFACE="$WORK/seed-surface-post-build.json"
run_clean "$SEED_WORK/bin:$SAFE_BIN" post-seed-validation \
    "$PYTHON_BIN" -I -S "$HELPER" validate-seed \
    --seed "$SEED_WORK" --version "$VERSION" --host "$HOST" \
    --output "$POST_SEED_SURFACE"
POST_SEED_SURFACE_SHA256=$(
    "$PYTHON_BIN" -I -S "$HELPER" file-sha256 "$POST_SEED_SURFACE"
)
if [ "$POST_SEED_SURFACE_SHA256" != "$SEED_SURFACE_SHA256" ]; then
    printf 'error: installed seed sysroot changed during the proof build\n' >&2
    exit 1
fi
POST_CONFIG_SHA256=$("$PYTHON_BIN" -I -S "$HELPER" file-sha256 "$CONFIG_SOURCE")
if [ "$POST_CONFIG_SHA256" != "$CONFIG_SHA256" ]; then
    printf 'error: bootstrap source configuration changed during the workflow\n' >&2
    exit 1
fi
POST_CONFIG_CLOSURE_FINGERPRINT=$(
    "$PYTHON_BIN" -I -S "$HELPER" config-fingerprint "$ROOT" "$CONFIG_SOURCE"
)
if [ "$POST_CONFIG_CLOSURE_FINGERPRINT" != "$CONFIG_CLOSURE_FINGERPRINT" ]; then
    printf 'error: bootstrap configuration closure changed during the workflow\n' >&2
    exit 1
fi
POST_CONFIG_MANIFEST_SHA256=$(
    "$PYTHON_BIN" -I -S "$HELPER" file-sha256 "$CONFIG_MANIFEST"
)
if [ "$POST_CONFIG_MANIFEST_SHA256" != "$CONFIG_MANIFEST_SHA256" ]; then
    printf 'error: bootstrap configuration manifest changed during the workflow\n' >&2
    exit 1
fi
POST_LIBRARY_MANIFEST="$WORK/native-library-inputs-post-build.json"
"$PYTHON_BIN" -I -S "$HELPER" library-manifest \
    "$POST_LIBRARY_MANIFEST" ${CANONICAL_LIBRARY_PATHS[@]+"${CANONICAL_LIBRARY_PATHS[@]}"}
POST_LIBRARY_MANIFEST_SHA256=$(
    "$PYTHON_BIN" -I -S "$HELPER" file-sha256 "$POST_LIBRARY_MANIFEST"
)
if [ "$POST_LIBRARY_MANIFEST_SHA256" != "$LIBRARY_MANIFEST_SHA256" ]; then
    printf 'error: explicit native library inputs changed during the workflow\n' >&2
    exit 1
fi
POST_SEED_DYLIB_MANIFEST="$WORK/seed-dylib-inputs-post-build.json"
"$PYTHON_BIN" -I -S "$HELPER" library-manifest \
    "$POST_SEED_DYLIB_MANIFEST" ${CANONICAL_SEED_DYLIB_PATHS[@]+"${CANONICAL_SEED_DYLIB_PATHS[@]}"}
if [ "$("$PYTHON_BIN" -I -S "$HELPER" file-sha256 "$POST_SEED_DYLIB_MANIFEST")" \
    != "$SEED_DYLIB_MANIFEST_SHA256" ]; then
    printf 'error: seed dylib inputs changed during the workflow\n' >&2
    exit 1
fi
"$PYTHON_BIN" -I -S "$HELPER" verify-cargo-home-inputs "$CARGO_HOME_MANIFEST"
POST_MINT_TOOLS_MANIFEST="$WORK/mint-toolchain-inputs-post-build.json"
"$PYTHON_BIN" -I -S "$HELPER" mint-tools-manifest \
    "$ROOT" "$CONFIG_SOURCE" "$POST_MINT_TOOLS_MANIFEST"
POST_MINT_TOOLS_MANIFEST_SHA256=$(
    "$PYTHON_BIN" -I -S "$HELPER" file-sha256 "$POST_MINT_TOOLS_MANIFEST"
)
if [ "$POST_MINT_TOOLS_MANIFEST_SHA256" != "$MINT_TOOLS_MANIFEST_SHA256" ]; then
    printf 'error: configured seed-mint toolchain changed during the workflow\n' >&2
    exit 1
fi
POST_PATH_MANIFEST_SHA256=$(
    "$PYTHON_BIN" -I -S "$HELPER" file-sha256 "$PATH_MANIFEST"
)
if [ "$POST_PATH_MANIFEST_SHA256" != "$PATH_MANIFEST_SHA256" ]; then
    printf 'error: sanitized PATH manifest changed during the workflow\n' >&2
    exit 1
fi
"$PYTHON_BIN" -I -S "$HELPER" revalidate-path \
    --path "$SAFE_BIN" --manifest "$PATH_MANIFEST"
PROVENANCE="$SEED_WORK/share/trust/self-host-provenance.json"
CONTINUATION_ARGS=()
if [ -n "$CONTINUATION_RECORD" ]; then
    CONTINUATION_ARGS=(--continuation-record "$CONTINUATION_RECORD" \
        --continuation-record-sha256 "$CONTINUATION_RECORD_SHA256" \
        --continuation-build-jobs "$BUILD_JOBS")
fi
"$PYTHON_BIN" -I -S "$HELPER" finalize \
    --root "$ROOT" \
    --input "$INPUT_MANIFEST" \
    --output "$PROVENANCE" \
    --config "$SEED_CONFIG" \
    --source-config "$CONFIG_SOURCE" \
    --stage2 "$STAGE2" \
    --source-date-epoch "$SOURCE_DATE_EPOCH" \
    --path-manifest "$PATH_MANIFEST" \
    --surface-manifest "$SEED_SURFACE" \
    --library-path "$NATIVE_LIBRARY_PATH" \
    --config-manifest "$CONFIG_MANIFEST" \
    --library-manifest "$LIBRARY_MANIFEST" \
    --mint-tools-manifest "$MINT_TOOLS_MANIFEST" \
    --mint-receipt "$RECEIPT" \
    --cargo-home-manifest "$CARGO_HOME_MANIFEST" \
    --seed-dylib-path "$SEED_DYLIB_PATH" \
    --seed-dylib-manifest "$SEED_DYLIB_MANIFEST" \
    --clean-lean-manifest "$CLEAN_LEAN_MANIFEST" \
    --clean-lean-lib "$CLEAN_LEAN_LIB" \
    --clean-lean-manifest-sha256 "$CLEAN_LEAN_MANIFEST_SHA256" \
    ${CONTINUATION_ARGS[@]+"${CONTINUATION_ARGS[@]}"}
"$PYTHON_BIN" -I -S "$HELPER" publish \
    "$ROOT" "$SEED_WORK" "$SEED_FINAL" "final seed sysroot"

printf '\nPASS: Trust %s (%s) was built from the pin %s, double-compiled\n' "$VERSION" "${COMMIT:0:12}" "${PIN_COMMIT:0:12}"
printf '      identically from %s (%s), and rebuilt itself from its %s archives.\n' "${DDC_COMMIT:0:12}" "$DDC_RELATION" "$HOST"
printf '      Pack source:  %s (receipt: %s)\n' "$MINT_BUILD/$HOST/stage2" "$RECEIPT"
printf '      Re-pin:       %s = %s (src/stage0 sha256 %s)\n' "$REPIN_BRANCH" "$REPIN_COMMIT" "$REPIN_STAGE0_SHA256"
printf '      Archives:     %s -> release %s\n' "$PREPARED/bootstrap/trust-stage0/dist/$COMMIT_DATE" "$REPIN_TAG"
printf '      Seed: %s\n' "$SEED_FINAL"
printf '      Fresh stage2: %s\n' "$STAGE2"
printf '      Provenance: %s\n' "$SEED_FINAL/share/trust/self-host-provenance.json"
printf '      Next: seal the pack source, stage the trust-wp drivers into a copy of the\n'
printf '      seal, and pass the gates docs/CUTTING-A-TOOLCHAIN.md section 3.9 runs on\n'
printf '      that copy. Then scripts/publish_seed_cut.sh releases the archives and pushes\n'
printf '      the re-pin, then the pack (section 3.9).\n'
printf '      The environment inherited no ambient variables and exposed no ambient\n'
printf '      Rust-family command names. This is self-hosting evidence, not a kernel\n'
printf '      execution trace. Use scripts/prove_rust_free_build.sh --build on Linux\n'
printf '      for the stronger execution-audit claim.\n'
