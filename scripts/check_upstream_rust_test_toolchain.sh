#!/usr/bin/env bash
# Preflight for running upstream Rust tests through the self-contained Trust toolchain.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

ALLOW_REBUILD="${TRUST_UPSTREAM_TEST_ALLOW_REBUILD:-}"
TOOLCHAIN_DEGRADED=0
TOOLCHAIN_MATCH=unknown
POST_STAGE2_DELTA_STATUS=unknown
POST_STAGE2_DELTA_DETAIL=""
POST_STAGE2_DELTA_FILES=()
COMMAND=()
REQUIRED_STAGE2_EXECUTABLES=(
    targo trustc targo-trust trustd trustdoc trustfmt targo-fmt
    tippy targo-tippy tippy-driver trust-analyzer
)

fail() {
    echo "ERROR: $*" >&2
    exit 1
}

warn() {
    echo "WARNING: $*" >&2
}

usage() {
    cat <<'EOF'
Usage:
  scripts/check_upstream_rust_test_toolchain.sh [--allow-rebuild]
  scripts/check_upstream_rust_test_toolchain.sh [--allow-rebuild] -- ./x.py test ...

Without a command, validate that a coherent repo-local Trust stage2 toolchain is
available for upstream Rust tests. With a command, validate the toolchain, run an
`x.py test --dry-run` rebuild guard, then execute the explicit command.

Set TRUST_UPSTREAM_TEST_ALLOW_REBUILD=1 or pass --allow-rebuild to execute the
command even when the dry-run says it would rebuild stage/tool artifacts.
EOF
}

is_truthy() {
    case "${1:-}" in
        1|true|TRUE|yes|YES|on|ON) return 0 ;;
        *) return 1 ;;
    esac
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        --allow-rebuild)
            ALLOW_REBUILD=1
            shift
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        --)
            shift
            COMMAND=("$@")
            break
            ;;
        *)
            fail "unknown argument: $1"
            ;;
    esac
done

candidate_sysroots() {
    if [[ -n "${TRUST_STAGE2_SYSROOT:-}" ]]; then
        printf '%s\n' "$TRUST_STAGE2_SYSROOT"
        return
    fi

    printf '%s\n' "$ROOT/build/host/stage2"
    local candidate
    for candidate in "$ROOT"/build/*/stage2; do
        [[ -e "$candidate" ]] || continue
        printf '%s\n' "$candidate"
    done
}

complete_sysroot() {
    local sysroot="$1"
    [[ ${#REQUIRED_STAGE2_EXECUTABLES[@]} -gt 0 ]] || return 1
    local tool
    for tool in "${REQUIRED_STAGE2_EXECUTABLES[@]}"; do
        [[ -x "$sysroot/bin/$tool" ]] || return 1
    done
}

find_stage2_sysroot() {
    local sysroot
    local first_partial=""
    while IFS= read -r sysroot; do
        if complete_sysroot "$sysroot"; then
            printf '%s\n' "$sysroot"
            return
        fi
        [[ -z "$first_partial" ]] && sysroot_has_any_required_tool "$sysroot" && first_partial="$sysroot"
    done < <(candidate_sysroots)
    if [[ -n "$first_partial" ]]; then
        printf '%s\n' "$first_partial"
        return 2
    fi
    return 1
}

sysroot_has_any_required_tool() {
    local sysroot="$1"
    local tool
    for tool in "${REQUIRED_STAGE2_EXECUTABLES[@]}"; do
        [[ -x "$sysroot/bin/$tool" ]] && return 0
    done
    return 1
}

missing_required_tools() {
    local sysroot="$1"
    local missing=()
    local tool
    for tool in "${REQUIRED_STAGE2_EXECUTABLES[@]}"; do
        [[ -x "$sysroot/bin/$tool" ]] || missing+=("bin/$tool")
    done
    [[ ${#missing[@]} -gt 0 ]] || return 0
    printf '%s\n' "${missing[@]}"
}

repo_local_stage2_sysroot() {
    local sysroot="$1"
    local resolved_root
    local resolved_sysroot
    resolved_root="$(cd "$ROOT" && pwd -P)"
    resolved_sysroot="$(cd "$sysroot" 2>/dev/null && pwd -P)" || return 1
    case "$resolved_sysroot" in
        "$resolved_root"/build/*/stage2) return 0 ;;
        *) return 1 ;;
    esac
}

format_command() {
    local quoted=()
    local arg
    for arg in "$@"; do
        printf -v arg '%q' "$arg"
        quoted+=("$arg")
    done
    printf '%s\n' "${quoted[*]}"
}

is_allowed_post_stage2_delta_path() {
    case "$1" in
        reports/*) return 0 ;;
        *) return 1 ;;
    esac
}

account_post_stage2_delta() {
    local toolchain_commit="$1"
    local repo_head="$2"

    TOOLCHAIN_MATCH=false
    POST_STAGE2_DELTA_STATUS=rejected
    POST_STAGE2_DELTA_DETAIL="stage2 trustc commit does not match checkout"
    POST_STAGE2_DELTA_FILES=()

    if ! git -C "$ROOT" cat-file -e "${toolchain_commit}^{commit}" 2>/dev/null; then
        POST_STAGE2_DELTA_DETAIL="stage2 trustc commit is not present in this checkout"
        return 1
    fi

    if ! git -C "$ROOT" merge-base --is-ancestor "$toolchain_commit" "$repo_head"; then
        POST_STAGE2_DELTA_DETAIL="stage2 trustc commit is not an ancestor of checkout"
        return 1
    fi

    local path
    while IFS= read -r path; do
        [[ -n "$path" ]] || continue
        POST_STAGE2_DELTA_FILES+=("$path")
        if ! is_allowed_post_stage2_delta_path "$path"; then
            POST_STAGE2_DELTA_DETAIL="non-evidence file changed after stage2 build: $path"
            return 1
        fi
    done < <(git -C "$ROOT" diff --name-only "$toolchain_commit..$repo_head" --)

    POST_STAGE2_DELTA_STATUS=accepted_reports_only
    POST_STAGE2_DELTA_DETAIL="checkout differs from stage2 only by generated report evidence"
    return 0
}

validate_stage2_toolchain() {
    local sysroot="$1"
    BIN="$sysroot/bin"
    LIB="$sysroot/lib"
    TARGO="$BIN/targo"
    TRUSTC="$BIN/trustc"
    CARGO_TRUST="$BIN/targo-trust"
    local trustdoc="$BIN/trustdoc"
    local trustfmt="$BIN/trustfmt"
    local targo_fmt="$BIN/targo-fmt"
    local tippy="$BIN/tippy"
    local targo_tippy="$BIN/targo-tippy"
    local tippy_driver="$BIN/tippy-driver"
    local trust_analyzer="$BIN/trust-analyzer"

    [[ -d "$sysroot" ]] || fail "stage2 sysroot candidate does not exist: $sysroot"
    repo_local_stage2_sysroot "$sysroot" \
        || fail "stage2 sysroot must be repo-local under build/<host>/stage2: $sysroot"

    local missing_tools
    missing_tools="$(missing_required_tools "$sysroot")"
    if [[ -n "$missing_tools" ]]; then
        fail "stage2 sysroot is incomplete: $sysroot missing executable(s): $(printf '%s' "$missing_tools" | paste -sd ', ' -)"
    fi

    [[ -x "$TARGO" ]] || fail "missing canonical stage2 targo: $TARGO"
    [[ -x "$TRUSTC" ]] || fail "missing canonical stage2 trustc: $TRUSTC"
    [[ -x "$CARGO_TRUST" ]] || fail "missing stage2 targo-trust subcommand: $CARGO_TRUST"
    [[ -x "$trustdoc" ]] || fail "missing canonical stage2 trustdoc: $trustdoc"
    [[ -x "$trustfmt" ]] || fail "missing canonical stage2 trustfmt: $trustfmt"
    [[ -x "$targo_fmt" ]] || fail "missing canonical stage2 targo-fmt: $targo_fmt"
    [[ -x "$tippy" ]] || fail "missing canonical stage2 tippy: $tippy"
    [[ -x "$targo_tippy" ]] || fail "missing canonical stage2 targo-tippy: $targo_tippy"
    [[ -x "$tippy_driver" ]] \
        || fail "missing canonical stage2 tippy-driver: $tippy_driver"
    [[ -x "$trust_analyzer" ]] || fail "missing canonical stage2 trust-analyzer: $trust_analyzer"

    case "$(basename "$TARGO")" in
        targo) ;;
        *) fail "canonical Cargo driver must be named targo: $TARGO" ;;
    esac
    case "$(basename "$TRUSTC")" in
        trustc) ;;
        *) fail "canonical compiler must be named trustc: $TRUSTC" ;;
    esac

    case "$(uname -s)" in
        Darwin) export DYLD_LIBRARY_PATH="$LIB${DYLD_LIBRARY_PATH:+:$DYLD_LIBRARY_PATH}" ;;
        Linux) export LD_LIBRARY_PATH="$LIB${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}" ;;
    esac
    export PATH="$BIN:$PATH"

    local trustc_vv
    trustc_vv="$("$TRUSTC" -Vv 2>&1)" \
        || fail "stage2 trustc does not run -Vv: $TRUSTC"
    case "$trustc_vv" in
        *"(trustc)"*|*"binary: trustc"*) ;;
        *) fail "stage2 compiler identity is not canonical trustc: $TRUSTC" ;;
    esac
    local trustdoc_vv
    trustdoc_vv="$("$trustdoc" -Vv 2>&1)" \
        || fail "stage2 trustdoc does not run -Vv: $trustdoc"
    case "$trustdoc_vv" in
        *"(trustdoc)"*|*"binary: trustdoc"*) ;;
        *) fail "stage2 trustdoc identity is not canonical trustdoc: $trustdoc" ;;
    esac
    "$trustfmt" -V >/dev/null 2>&1 \
        || fail "stage2 trustfmt does not run -V: $trustfmt"
    "$tippy" -V >/dev/null 2>&1 \
        || fail "stage2 tippy does not run -V: $tippy"
    "$TARGO" tippy -V >/dev/null 2>&1 \
        || fail "stage2 targo tippy dispatch does not run -V via: $targo_tippy"
    "$tippy_driver" -Vv >/dev/null 2>&1 \
        || fail "stage2 tippy-driver does not run -Vv: $tippy_driver"
    "$trust_analyzer" --version >/dev/null 2>&1 \
        || fail "stage2 trust-analyzer does not run --version: $trust_analyzer"

    local repo_head
    repo_head="$(git -C "$ROOT" rev-parse HEAD 2>/dev/null || true)"
    local trustc_commit
    trustc_commit="$(
        printf '%s\n' "$trustc_vv" | awk -F': ' '$1 == "commit-hash" { print $2; exit }'
    )"
    if [[ ! "$trustc_commit" =~ ^[0-9a-fA-F]{40}$ ]]; then
        fail "stage2 trustc -Vv did not report a full 40-hex commit-hash: $TRUSTC"
    fi
    if [[ -n "$repo_head" && "$trustc_commit" == "$repo_head" ]]; then
        TOOLCHAIN_MATCH=true
        POST_STAGE2_DELTA_STATUS=none
        POST_STAGE2_DELTA_DETAIL="stage2 trustc commit matches checkout"
    elif [[ -n "$repo_head" && "$trustc_commit" != "$repo_head" ]]; then
        account_post_stage2_delta "$trustc_commit" "$repo_head" || true
        if [[ ${#COMMAND[@]} -gt 0 ]] && is_truthy "$ALLOW_REBUILD"; then
            TOOLCHAIN_DEGRADED=1
            warn "stage2 trustc commit $trustc_commit does not match checkout $repo_head; continuing because rebuild opt-in is set"
        elif [[ "$POST_STAGE2_DELTA_STATUS" == "accepted_reports_only" ]]; then
            :
        else
            fail "stage2 trustc commit $trustc_commit does not match checkout $repo_head (${POST_STAGE2_DELTA_DETAIL}); sysroot=$sysroot trustc=$TRUSTC; rebuild with ./x.py build --stage 2 compiler/rustc or pass --allow-rebuild for an explicit rebuilding run"
        fi
    fi

    [[ -d "$LIB/rustlib" ]] || fail "stage2 rustlib is missing: $LIB/rustlib"
    find "$LIB/rustlib" -type f -name 'libstd-*.rlib' -print -quit | grep -q . \
        || fail "stage2 libstd artifact is missing under $LIB/rustlib"

    "$TRUSTC" -Ztrust-verify=off --version >/dev/null 2>&1 \
        || fail "stage2 trustc does not run with -Ztrust-verify=off: $TRUSTC"

    "$CARGO_TRUST" --version >/dev/null 2>&1 \
        || fail "stage2 targo-trust does not run: $CARGO_TRUST"

    UPSTREAM_HELP="$("$TARGO" trust domination upstream-tests --help 2>&1)" \
        || fail "stage2 targo does not expose \`targo trust domination upstream-tests\`"

    case "$UPSTREAM_HELP" in
        *"trust-upstream-compat port"*) ;;
        *) fail "upstream-tests help did not identify the Rust trust-upstream-compat port engine" ;;
    esac
}

dry_run_command() {
    if [[ ${#COMMAND[@]} -eq 0 ]]; then
        return
    fi
    if [[ "$(basename "${COMMAND[0]}")" != "x.py" || "${COMMAND[1]:-}" != "test" ]]; then
        fail "guarded upstream test command must start with x.py test"
    fi

    local dry=()
    local arg
    local has_dry_run=0
    for arg in "${COMMAND[@]}"; do
        if [[ "$arg" == "--dry-run" ]]; then
            has_dry_run=1
            break
        fi
    done
    if [[ "$has_dry_run" == 1 ]]; then
        dry=("${COMMAND[@]}")
    else
        dry=("${COMMAND[0]}" "${COMMAND[1]}" "--dry-run")
        if [[ ${#COMMAND[@]} -gt 2 ]]; then
            dry+=("${COMMAND[@]:2}")
        fi
    fi

    local dry_log
    dry_log="$(mktemp "${TMPDIR:-/tmp}/trust-upstream-xpy-dry-run.XXXXXX")"
    if ! "${dry[@]}" >"$dry_log" 2>&1; then
        sed -n '1,120p' "$dry_log" >&2
        rm -f "$dry_log"
        fail "x.py dry-run failed for guarded upstream test command"
    fi

    local rebuild_lines
    rebuild_lines="$(
        grep -E '^(Building LLVM|Building stage[0-9]+|Creating a sysroot for stage[0-9]+|Uplifting library \(stage[0-9]+ -> stage[0-9]+\))' "$dry_log" || true
    )"
    if [[ -n "$rebuild_lines" ]]; then
        if is_truthy "$ALLOW_REBUILD"; then
            warn "x.py dry-run plans stage/tool rebuild work; continuing because rebuild opt-in is set"
            printf '%s\n' "$rebuild_lines" | sed -n '1,20p' >&2
        else
            {
                echo "x.py dry-run says this scoped upstream test would rebuild stage/tool artifacts:"
                printf '%s\n' "$rebuild_lines" | sed -n '1,20p'
                echo
                echo "Refusing to run unbounded rebuild/log growth from a smoke test."
                echo "Rebuild a coherent stage2 sysroot first, or pass --allow-rebuild / set TRUST_UPSTREAM_TEST_ALLOW_REBUILD=1 for an explicit rebuilding run."
            } >&2
            rm -f "$dry_log"
            exit 1
        fi
    fi
    rm -f "$dry_log"
}

SYSROOT_STATUS=0
SYSROOT="$(find_stage2_sysroot)" || SYSROOT_STATUS=$?
if [[ "$SYSROOT_STATUS" != 0 ]]; then
    if [[ ${#COMMAND[@]} -gt 0 ]] && is_truthy "$ALLOW_REBUILD"; then
        TOOLCHAIN_DEGRADED=1
        warn "complete Trust stage2 sysroot not found; continuing because rebuild opt-in is set"
    elif [[ "$SYSROOT_STATUS" == 2 ]]; then
        validate_stage2_toolchain "$SYSROOT"
    else
        fail "Trust stage2 sysroot not found under build/host/stage2 or build/<host>/stage2; build with ./x.py build --stage 2 compiler/rustc and include targo-trust before upstream tests"
    fi
else
    validate_stage2_toolchain "$SYSROOT"
fi

dry_run_command

if [[ "$TOOLCHAIN_DEGRADED" == 1 ]]; then
    cat <<EOF
WARNING: upstream Rust test command accepted with explicit rebuild opt-in
sysroot: ${SYSROOT:-<not proven>}
targo:   ${TARGO:-<not proven>}
trustc:  ${TRUSTC:-<not proven>}
toolchain_checkout_match: ${TOOLCHAIN_MATCH}
post_stage2_delta_status: ${POST_STAGE2_DELTA_STATUS}
post_stage2_delta_detail: ${POST_STAGE2_DELTA_DETAIL}
EOF
else
    cat <<EOF
OK: upstream Rust test toolchain is self-contained
sysroot: ${SYSROOT:-<rebuild opt-in>}
targo:   ${TARGO:-<rebuild opt-in>}
trustc:  ${TRUSTC:-<rebuild opt-in>}
toolchain_checkout_match: ${TOOLCHAIN_MATCH}
post_stage2_delta_status: ${POST_STAGE2_DELTA_STATUS}
post_stage2_delta_detail: ${POST_STAGE2_DELTA_DETAIL}
EOF
fi

if [[ ${#POST_STAGE2_DELTA_FILES[@]} -gt 0 ]]; then
    printf 'post_stage2_delta_files:\n'
    printf '  %s\n' "${POST_STAGE2_DELTA_FILES[@]}"
fi

cat <<EOF
Representative scoped upstream test command:
  ./scripts/check_upstream_rust_test_toolchain.sh -- ./x.py test --stage 2 --trust-vanilla --no-fail-fast tests/ui/entry-point/hello-world.rs tests/codegen-llvm/array-codegen.rs tests/incremental/hello_world.rs
EOF

if [[ ${#COMMAND[@]} -gt 0 ]]; then
    printf '\nExecuting guarded upstream test command:\n  %s\n' "$(format_command "${COMMAND[@]}")"
    exec "${COMMAND[@]}"
fi
