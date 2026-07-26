#!/usr/bin/env bash
# Mint an exact, commit-bound Trust seed and rebuild Trust from it.
#
# This workflow establishes self-hosting and records its exact inputs.  It does
# not call PATH scrubbing a kernel execution proof.  The stronger execution
# claim belongs to `scripts/prove_rust_free_build.sh --build`, which currently
# requires Linux strace and a materialized release-grade pinned seed.
set -Eeuo pipefail
umask 077

usage() {
    printf '%s\n' \
        'usage: scripts/mint_and_prove_seed.sh [options]' \
        '' \
        'Options:' \
        '  --host TARGET             Build host triple (auto-detected on macOS/Linux).' \
        '  --config FILE             Bootstrap config used for the sanctioned mint.' \
        '  --seed-dir DIR            Final seed sysroot (must not already exist).' \
        '  --proof-build-dir DIR     Fresh stage2 build directory (must not exist).' \
        '  --library-path DIR        Explicit native link directory (repeatable).' \
        '  --check-only              Validate immutable inputs and print the exact plan.' \
        '  -h, --help                Show this help.' \
        '' \
        'The source tree and submodules must be clean. Output directories are restricted' \
        'to build/, are never overwritten, and partial temporary seed state is removed' \
        'on failure. The fresh proof build is retained as evidence if a build starts.' >&2
}

HOST=
CONFIG_SOURCE=
SEED_FINAL=
PROOF_BUILD=
CHECK_ONLY=0
LIBRARY_PATHS=()
while [ "$#" -gt 0 ]; do
    case "$1" in
        --host|--config|--seed-dir|--proof-build-dir|--library-path)
            if [ "$#" -lt 2 ]; then
                printf 'error: %s requires a value\n' "$1" >&2
                usage
                exit 2
            fi
            case "$1" in
                --host) HOST=$2 ;;
                --config) CONFIG_SOURCE=$2 ;;
                --seed-dir) SEED_FINAL=$2 ;;
                --proof-build-dir) PROOF_BUILD=$2 ;;
                --library-path) LIBRARY_PATHS+=("$2") ;;
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
ROOT=$(cd -P "$SCRIPT_DIR/.." && pwd -P) || {
    printf 'error: cannot resolve repository root\n' >&2
    exit 1
}
cd -P "$ROOT"

PYTHON_BIN=$(type -P python3 || true)
if [ -z "$PYTHON_BIN" ] || [ ! -x "$PYTHON_BIN" ]; then
    printf 'error: python3 is required\n' >&2
    exit 1
fi
PYTHON_BIN=$(
    "$PYTHON_BIN" -I -S -c 'import os,sys; print(os.path.realpath(sys.executable))'
) || {
    printf 'error: cannot canonicalize python3\n' >&2
    exit 1
}
HELPER="$ROOT/scripts/mint_seed_support.py"
if [ ! -f "$HELPER" ] || [ -L "$HELPER" ]; then
    printf 'error: seed helper must be a repository-owned regular file: %s\n' "$HELPER" >&2
    exit 1
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
CONFIG_SHA256=$("$PYTHON_BIN" -I -S "$HELPER" file-sha256 "$CONFIG_SOURCE")
CONFIG_CLOSURE_FINGERPRINT=$(
    "$PYTHON_BIN" -I -S "$HELPER" config-fingerprint "$ROOT" "$CONFIG_SOURCE"
)
CANONICAL_LIBRARY_PATHS=()
for library_path in "${LIBRARY_PATHS[@]}"; do
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
IFS=$'\t' read -r COMMIT SOURCE_DATE_EPOCH < <(
    "$PYTHON_BIN" -I -S "$HELPER" repo-state "$ROOT"
)
if [ -z "$COMMIT" ] || [ -z "$SOURCE_DATE_EPOCH" ]; then
    printf 'error: repository metadata helper returned an incomplete record\n' >&2
    exit 1
fi

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

DIST="$ROOT/build/dist"
COMPONENTS=(trust-std trustc trustc-dev targo trustfmt)
DIST_PATHS=()
for component in "${COMPONENTS[@]}"; do
    DIST_PATHS+=("$component-$VERSION-trust-$HOST.tar.xz")
done

printf '== exact self-host seed plan ==\n'
printf '  source:       %s (%s)\n' "$VERSION" "$COMMIT"
printf '  host:         %s\n' "$HOST"
printf '  config:       %s\n' "$CONFIG_SOURCE"
printf '  seed output:  %s\n' "$SEED_FINAL"
printf '  proof output: %s\n' "$PROOF_BUILD"
if [ -n "$NATIVE_LIBRARY_PATH" ]; then
    printf '  library path: %s\n' "$NATIVE_LIBRARY_PATH"
fi
printf '  exact archives:\n'
printf '    %s\n' "${DIST_PATHS[@]}"
if [ "$CHECK_ONLY" -eq 1 ]; then
    printf '\nCHECK OK: inputs are committed and output paths are new; no build was run.\n'
    exit 0
fi

WORK=$("$PYTHON_BIN" -I -S "$HELPER" make-work "$ROOT")
CHILD_PID=
cleanup() {
    local status=$?
    trap - EXIT HUP INT TERM
    if [ -n "${CHILD_PID:-}" ]; then
        kill -TERM "$CHILD_PID" 2>/dev/null || true
        wait "$CHILD_PID" 2>/dev/null || true
        kill -KILL "$CHILD_PID" 2>/dev/null || true
        CHILD_PID=
    fi
    if [ -n "${WORK:-}" ] && [ -d "$WORK" ]; then
        "$PYTHON_BIN" -I -S "$HELPER" cleanup-work "$ROOT" "$WORK" || true
    fi
    exit "$status"
}
signal_exit() {
    local signal=$1
    local status=$2
    trap - EXIT HUP INT TERM
    if [ -n "${CHILD_PID:-}" ]; then
        kill -TERM "$CHILD_PID" 2>/dev/null || true
        wait "$CHILD_PID" 2>/dev/null || true
        kill -KILL "$CHILD_PID" 2>/dev/null || true
        CHILD_PID=
    fi
    if [ -n "${WORK:-}" ] && [ -d "$WORK" ]; then
        "$PYTHON_BIN" -I -S "$HELPER" cleanup-work "$ROOT" "$WORK" || true
    fi
    printf 'error: interrupted by %s\n' "$signal" >&2
    exit "$status"
}
trap cleanup EXIT
trap 'signal_exit HUP 129' HUP
trap 'signal_exit INT 130' INT
trap 'signal_exit TERM 143' TERM

CONFIG_MANIFEST="$WORK/bootstrap-config-closure.json"
"$PYTHON_BIN" -I -S "$HELPER" config-manifest \
    "$ROOT" "$CONFIG_SOURCE" "$CONFIG_MANIFEST"
CONFIG_MANIFEST_SHA256=$("$PYTHON_BIN" -I -S "$HELPER" file-sha256 "$CONFIG_MANIFEST")
LIBRARY_MANIFEST="$WORK/native-library-inputs.json"
"$PYTHON_BIN" -I -S "$HELPER" library-manifest \
    "$LIBRARY_MANIFEST" "${CANONICAL_LIBRARY_PATHS[@]}"
LIBRARY_MANIFEST_SHA256=$("$PYTHON_BIN" -I -S "$HELPER" file-sha256 "$LIBRARY_MANIFEST")
MINT_TOOLS_MANIFEST="$WORK/mint-toolchain-inputs.json"
"$PYTHON_BIN" -I -S "$HELPER" mint-tools-manifest \
    "$ROOT" "$CONFIG_SOURCE" "$MINT_TOOLS_MANIFEST"
MINT_TOOLS_MANIFEST_SHA256=$(
    "$PYTHON_BIN" -I -S "$HELPER" file-sha256 "$MINT_TOOLS_MANIFEST"
)

SAFE_BIN="$WORK/safe-bin"
PATH_MANIFEST="$WORK/safe-path.json"
"$PYTHON_BIN" -I -S "$HELPER" safe-path \
    --input "$PATH" --output "$SAFE_BIN" --manifest "$PATH_MANIFEST"
PATH_MANIFEST_SHA256=$("$PYTHON_BIN" -I -S "$HELPER" file-sha256 "$PATH_MANIFEST")

run_clean() {
    local path_value=$1
    local environment_name=$2
    shift 2
    local environment_root="$WORK/environment-$environment_name"
    "$MKDIR_BIN" -p "$environment_root/home" "$environment_root/tmp" \
        "$environment_root/cargo-home" "$environment_root/rustup-home" \
        "$environment_root/xdg-config"
    local environment=(
        HOME="$environment_root/home"
        USER=trust-seed
        LOGNAME=trust-seed
        PATH="$path_value"
        LANG=C LC_ALL=C TZ=UTC
        TMPDIR="$environment_root/tmp"
        CARGO_HOME="$environment_root/cargo-home"
        RUSTUP_HOME="$environment_root/rustup-home"
        XDG_CONFIG_HOME="$environment_root/xdg-config"
        CARGO_NET_OFFLINE=true
        GIT_CONFIG_NOSYSTEM=1 GIT_CONFIG_GLOBAL=/dev/null
        SOURCE_DATE_EPOCH="$SOURCE_DATE_EPOCH"
    )
    if [ -n "$NATIVE_LIBRARY_PATH" ]; then
        environment+=(LIBRARY_PATH="$NATIVE_LIBRARY_PATH")
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

step "mint the five minimal self-host components from committed HEAD"
run_clean "$SAFE_BIN" mint \
    "$PYTHON_BIN" -I -S "$ROOT/x.py" \
    --config "$CONFIG_SOURCE" \
    dist \
    --build-dir "$ROOT/build" \
    --build "$HOST" \
    --host "$HOST" \
    --target "$HOST" \
    --stage 2 \
    --set build.submodules=false \
    --set rust.channel=trust \
    --set rust.download-rustc=false \
    --set llvm.download-ci-llvm=false \
    trust-std trustc trustc-dev targo trustfmt

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
run_clean "$SEED_WORK/bin:$SAFE_BIN" proof \
    "$PYTHON_BIN" -I -S "$ROOT/x.py" \
    --config "$SEED_CONFIG" \
    build \
    --build-dir "$PROOF_BUILD" \
    --build "$HOST" \
    --host "$HOST" \
    --target "$HOST" \
    --stage 2 \
    --set build.submodules=false \
    --set rust.channel=trust \
    --set rust.download-rustc=false \
    --set llvm.download-ci-llvm=false \
    compiler/rustc

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
    "$POST_LIBRARY_MANIFEST" "${CANONICAL_LIBRARY_PATHS[@]}"
POST_LIBRARY_MANIFEST_SHA256=$(
    "$PYTHON_BIN" -I -S "$HELPER" file-sha256 "$POST_LIBRARY_MANIFEST"
)
if [ "$POST_LIBRARY_MANIFEST_SHA256" != "$LIBRARY_MANIFEST_SHA256" ]; then
    printf 'error: explicit native library inputs changed during the workflow\n' >&2
    exit 1
fi
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
    --mint-tools-manifest "$MINT_TOOLS_MANIFEST"
"$PYTHON_BIN" -I -S "$HELPER" publish \
    "$ROOT" "$SEED_WORK" "$SEED_FINAL" "final seed sysroot"

printf '\nPASS: Trust %s rebuilt itself from exact %s seed archives.\n' "$VERSION" "$HOST"
printf '      Seed: %s\n' "$SEED_FINAL"
printf '      Fresh stage2: %s\n' "$STAGE2"
printf '      Provenance: %s\n' "$SEED_FINAL/share/trust/self-host-provenance.json"
printf '      The environment inherited no ambient variables and exposed no ambient\n'
printf '      Rust-family command names. This is self-hosting evidence, not a kernel\n'
printf '      execution trace. Use scripts/prove_rust_free_build.sh --build on Linux\n'
printf '      for the stronger execution-audit claim.\n'
