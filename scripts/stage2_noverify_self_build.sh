#!/usr/bin/env bash
# Run the canonical bounded no-verification stage2 self-build evidence gate.
#
# This harness builds the Trust-owned stage2 surface that matters for local
# self-host evidence: Trust-preferred tools plus same-sysroot Rust-compatible
# aliases.
# Host/upstream Cargo is only involved indirectly inside bootstrap/x.py;
# post-build proof commands use the freshly built Trust tools.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
PYTHON3="${PYTHON3:-python3}"
TRUST_TOOLCHAIN_PYTHON3="$PYTHON3"
. "$SCRIPT_DIR/lib/trust_toolchain_surface.sh"
cd "$TRUST_ROOT"

JOBS="${TRUST_JOBS:-4}"
RUN_ID="${TRUST_NOVERIFY_RUN_ID:-stage2-noverify-$(date -u '+%Y%m%dT%H%M%SZ')}"
REPORT_DIR="${TRUST_NOVERIFY_REPORT_DIR:-$TRUST_ROOT/reports/build/$RUN_ID}"
LOG_DIR="$REPORT_DIR/logs"
BUILD_LOG="$LOG_DIR/stage2-noverify-build.log"
PREFLIGHT_LOG="$LOG_DIR/source-manifest-preflight.log"
VERSIONS_LOG="$LOG_DIR/trust-tool-versions.log"
SCAN_LOG="$LOG_DIR/noverify-log-scan.log"
ARTIFACTS_LOG="$LOG_DIR/stage2-artifacts.log"
SOURCE_WATCH_LOG="$LOG_DIR/source-watch.log"
SUMMARY="$REPORT_DIR/summary.md"
REPORT_JSON="$REPORT_DIR/report.json"
DRY_RUN="${TRUST_NOVERIFY_DRY_RUN:-0}"
SOURCE_WATCH_INTERVAL="${TRUST_NOVERIFY_SOURCE_WATCH_INTERVAL:-15}"
RUN_START_UTC="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
RUN_START_EPOCH="$(date -u '+%s')"
START_HEAD="$(git rev-parse HEAD)"
REQUIRED_SOURCE_MANIFESTS=(
    "src/tools/targo/Cargo.toml"
    "targo-trust/Cargo.toml"
    "first-party/trust-cg/crates/trust-cg-ir/Cargo.toml"
    "first-party/trust-ir/crates/trust-ir/Cargo.toml"
    "first-party/ay/crates/ay/Cargo.toml"
    "first-party/ay/crates/ay-bindings/Cargo.toml"
    "first-party/ay/crates/ay-core/Cargo.toml"
)
SELF_CONTAINED_LOCKFILES=(
    "Cargo.lock"
    "crates/Cargo.lock"
    "targo-trust/Cargo.lock"
    "library/Cargo.lock"
    "src/bootstrap/Cargo.lock"
    "src/tools/targo/Cargo.lock"
    "first-party/trust-vc/Cargo.lock"
    "first-party/trust-ir/Cargo.lock"
    "first-party/ay/Cargo.lock"
)
STAGE2_REQUIRED_TOOLS=(
    "trustc"
    "targo"
    "targo-trust"
    "trustd"
    "trustdoc"
    "trustfmt"
    "targo-fmt"
    "tippy"
    "targo-tippy"
    "tippy-driver"
    "trust-analyzer"
)
# Rust tooling requires these two same-sysroot compatibility entrypoints. All
# stock secondary aliases remain forbidden.
STAGE2_REQUIRED_COMPAT_ALIASES=("rustc" "cargo")
STAGE2_REQUIRED_ALIAS_PAIRS=("trustc:rustc" "targo:cargo")
# Keep no-verification bootstrap evidence independent of caller-local wrappers.
# A stale bootstrap rustc shim here breaks the initial Cargo build of bootstrap.
BOOTSTRAP_WRAPPER_ENV_UNSET=(
    "RUSTC_WRAPPER"
    "RUSTC_WORKSPACE_WRAPPER"
    "RUSTC_WRAPPER_REAL"
    "CARGO_BUILD_RUSTC_WRAPPER"
    "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER"
)

usage() {
    cat <<'USAGE'
stage2_noverify_self_build.sh -- bounded no-verification Trust self-build gate

USAGE:
  bash scripts/stage2_noverify_self_build.sh

ENVIRONMENT:
  TRUST_JOBS=N                 Parallel x.py jobs; defaults to 4.
  TRUST_NOVERIFY_RUN_ID=ID     Report id; defaults to stage2-noverify-<UTC>.
  TRUST_NOVERIFY_REPORT_DIR=P  Report directory; defaults to reports/build/<id>.
  TRUST_NOVERIFY_DRY_RUN=1     Print the canonical command without executing it.

OUTPUT:
  reports/build/<run-id>/summary.md
  reports/build/<run-id>/logs/source-manifest-preflight.log
  reports/build/<run-id>/logs/stage2-noverify-build.log
  reports/build/<run-id>/logs/trust-tool-versions.log
  reports/build/<run-id>/logs/noverify-log-scan.log
  reports/build/<run-id>/logs/stage2-artifacts.log
  reports/build/<run-id>/logs/source-watch.log
  reports/build/<run-id>/report.json
USAGE
}

append_shell_word() {
    local current="$1"
    local word="$2"

    if [[ -z "$current" ]]; then
        printf '%s\n' "$word"
    elif [[ " $current " == *" $word "* ]]; then
        printf '%s\n' "$current"
    else
        printf '%s %s\n' "$current" "$word"
    fi
}

format_command() {
    local out=""
    local arg

    for arg in "$@"; do
        if [[ -n "$out" ]]; then
            out+=" "
        fi
        printf -v out "%s%q" "$out" "$arg"
    done
    printf '%s\n' "$out"
}

find_stage2_sysroot() {
    local candidate
    local resolved
    while IFS= read -r candidate; do
        if resolved="$(
            trust_toolchain_resolve_repo_stage2 "$TRUST_ROOT" "$candidate"
        )" \
            && stage2_has_required_tools "$resolved" \
            && stage2_has_required_compat_aliases "$resolved"; then
            printf '%s\n' "$resolved"
            return 0
        fi
    done < <(stage2_sysroot_candidates)

    return 1
}

stage2_has_required_tools() {
    local candidate="$1"
    local tool

    trust_toolchain_forbidden_entries_absent "$candidate/bin" || return 1
    trust_toolchain_exact_executables_valid \
        "$candidate/bin" "${STAGE2_REQUIRED_TOOLS[@]}" || return 1

    return 0
}

stage2_required_tool_name() {
    local wanted="$1"
    local tool

    for tool in "${STAGE2_REQUIRED_TOOLS[@]}"; do
        [[ "$tool" == "$wanted" ]] && return 0
    done

    return 1
}

stage2_required_alias_name() {
    local wanted="$1"
    local tool

    for tool in "${STAGE2_REQUIRED_COMPAT_ALIASES[@]}"; do
        [[ "$tool" == "$wanted" ]] && return 0
    done

    return 1
}

stage2_has_required_compat_aliases() {
    local candidate="$1"
    local tool

    for tool in "${STAGE2_REQUIRED_COMPAT_ALIASES[@]}"; do
        [[ -x "$candidate/bin/$tool" ]] || return 1
    done

    local pair canonical alias
    for pair in "${STAGE2_REQUIRED_ALIAS_PAIRS[@]}"; do
        canonical="${pair%%:*}"
        alias="${pair#*:}"
        trust_toolchain_alias_pair_valid "$candidate/bin" "$canonical" "$alias" || return 1
    done
    return 0
}

stage2_sysroot_candidates() {
    shopt -s nullglob
    local candidates=("$TRUST_ROOT/build/host/stage2")
    local candidate
    local seen=" "

    for candidate in "$TRUST_ROOT"/build/*/stage2; do
        candidates+=("$candidate")
    done
    shopt -u nullglob

    for candidate in "${candidates[@]}"; do
        [[ -n "$candidate" ]] || continue
        if [[ " $seen " == *" $candidate "* ]]; then
            continue
        fi
        seen+="$candidate "
        printf '%s\n' "$candidate"
    done
}

tracked_dirty_report() {
    git status --porcelain=v1 --untracked-files=no
}

untracked_source_report() {
    local line
    local path

    while IFS= read -r line; do
        case "$line" in
            "?? "*)
                path="${line#?? }"
                path="${path%/}"
                case "$path" in
                    build/*|target/*|reports/*|.claude/*|.git/*)
                        ;;
                    *)
                        printf '%s\n' "$path"
                        ;;
                esac
                ;;
        esac
    done < <(git status --porcelain=v1 --untracked-files=all)
}

source_dirty_report() {
    local tracked
    local untracked
    tracked="$(tracked_dirty_report)"
    untracked="$(untracked_source_report)"
    if [[ -n "$tracked" ]]; then
        printf '%s\n' "$tracked"
    fi
    if [[ -n "$untracked" ]]; then
        printf '?? %s\n' "$untracked"
    fi
}

tracked_dirty_count() {
    local dirty
    dirty="$(tracked_dirty_report)"
    if [[ -z "$dirty" ]]; then
        echo 0
    else
        printf '%s\n' "$dirty" | wc -l | tr -d ' '
    fi
}

preflight_clean_tracked_worktree() {
    local dirty
    dirty="$(tracked_dirty_report)"

    if [[ -z "$dirty" ]]; then
        return 0
    fi

    {
        echo "tracked source worktree is dirty before no-verification Trust self-build:"
        printf '%s\n' "$dirty"
        echo
        echo "Commit or otherwise resolve tracked source changes before using this"
        echo "harness as bootstrap evidence. Untracked report/log artifacts are ignored."
    } >&2
    return 1
}

preflight_clean_untracked_sources() {
    local dirty
    dirty="$(untracked_source_report)"

    if [[ -z "$dirty" ]]; then
        return 0
    fi

    {
        echo "untracked source inputs are present before no-verification Trust self-build:"
        printf '?? %s\n' "$dirty"
        echo
        echo "Move, commit, or intentionally ignore these files before collecting"
        echo "bootstrap evidence. Untracked build/, target/, reports/, and .claude/"
        echo "artifacts are ignored."
    } >&2
    return 1
}

preflight_source_manifests() {
    local missing=()
    local manifest

    for manifest in "${REQUIRED_SOURCE_MANIFESTS[@]}"; do
        if [[ ! -f "$TRUST_ROOT/$manifest" ]]; then
            missing+=("$manifest")
        fi
    done

    if [[ "${#missing[@]}" -eq 0 ]]; then
        return 0
    fi

    {
        echo "missing required local source manifest(s) for no-verification Trust self-build:"
        for manifest in "${missing[@]}"; do
            echo "  - $manifest"
        done
        echo
        echo "These are Trust-owned local path dependencies. The no-verification gate"
        echo "does not fall back to host/upstream Cargo registry or Git sources."
    } >&2
    return 1
}

preflight_self_contained_lockfiles() {
    local lockfile
    local findings=()
    local line

    for lockfile in "${SELF_CONTAINED_LOCKFILES[@]}"; do
        if [[ ! -f "$TRUST_ROOT/$lockfile" ]]; then
            continue
        fi
        while IFS= read -r line; do
            findings+=("$lockfile:$line")
        done < <(grep -n 'source = "git+' "$TRUST_ROOT/$lockfile" || true)
    done

    if [[ "${#findings[@]}" -eq 0 ]]; then
        return 0
    fi

    {
        echo "forbidden Git dependency source(s) in no-verification Trust self-build lockfile closure:"
        printf '  - %s\n' "${findings[@]}"
        echo
        echo "The no-verification self-build gate runs offline from local Trust-owned"
        echo "source snapshots. Refresh these lockfiles to local path sources before"
        echo "using this harness as bootstrap/control evidence."
    } >&2
    return 1
}

stage0_dist_server() {
    awk -F= '$1 == "dist_server" { print $2; exit }' "$TRUST_ROOT/src/stage0"
}

stage0_dist_payload_mode() {
    awk -F= '$1 == "dist_payload_mode" { print $2; exit }' "$TRUST_ROOT/src/stage0"
}

stage0_local_dist_root() {
    local dist_server="$1"
    local root

    case "$dist_server" in
        file://*)
            root="${dist_server#file://}"
            root="${root//\{trust-root\}/$TRUST_ROOT}"
            printf '%s\n' "$root"
            return 0
            ;;
        *)
            return 1
            ;;
    esac
}

preflight_stage0_payloads() {
    local stage0_file="$TRUST_ROOT/src/stage0"
    local payload_mode
    local dist_server
    local dist_root
    local rel
    local expected
    local path
    local actual
    local rel_path
    local missing=()
    local mismatched=()
    local untracked_repo_local=()

    if [[ ! -f "$stage0_file" ]]; then
        echo "missing Trust stage0 metadata file: src/stage0" >&2
        return 1
    fi

    payload_mode="$(stage0_dist_payload_mode)"
    dist_server="$(stage0_dist_server)"
    if [[ -z "$dist_server" ]]; then
        echo "src/stage0 does not define a Trust stage0 dist_server" >&2
        return 1
    fi

    if ! dist_root="$(stage0_local_dist_root "$dist_server")"; then
        return 0
    fi

    while IFS='=' read -r rel expected; do
        case "$rel" in
            dist/*.tar|dist/*.tar.gz|dist/*.tar.xz)
                path="$dist_root/$rel"
                if [[ ! -f "$path" ]]; then
                    missing+=("$rel")
                    continue
                fi
                case "$path" in
                    "$TRUST_ROOT"/*)
                        rel_path="${path#"$TRUST_ROOT"/}"
                        if ! git -C "$TRUST_ROOT" ls-files --error-unmatch "$rel_path" >/dev/null 2>&1; then
                            untracked_repo_local+=("$rel")
                            continue
                        fi
                        ;;
                esac
                actual="$(file_sha256 "$path")"
                if [[ "$actual" != "$expected" ]]; then
                    mismatched+=("$rel expected=$expected actual=$actual")
                fi
                ;;
        esac
    done <"$stage0_file"

    if [[ "${#missing[@]}" -eq 0 && "${#mismatched[@]}" -eq 0 && "${#untracked_repo_local[@]}" -eq 0 ]]; then
        return 0
    fi

    {
        echo "Trust stage0 payload preflight failed before no-verification self-build."
        echo "stage0=src/stage0"
        echo "dist_server=$dist_server"
        echo "dist_payload_mode=${payload_mode:-<unset>}"
        echo "resolved_dist_root=$dist_root"
        echo
        if [[ "${#missing[@]}" -ne 0 ]]; then
            echo "missing checksum-pinned stage0 payload(s):"
            printf '  - %s\n' "${missing[@]}"
            echo
        fi
        if [[ "${#mismatched[@]}" -ne 0 ]]; then
            echo "checksum mismatch in stage0 payload(s):"
            printf '  - %s\n' "${mismatched[@]}"
            echo
        fi
        if [[ "${#untracked_repo_local[@]}" -ne 0 ]]; then
            echo "repo-local stage0 payload(s) are not tracked by Git:"
            printf '  - %s\n' "${untracked_repo_local[@]}"
            echo
            echo "Ignored or otherwise untracked repo-local tarballs are not clean-clone"
            echo "release evidence. Track the local Trust stage0 payloads with the"
            echo "matching manifests and checksum pins."
            echo
        fi
        echo "Materialize the Trust-owned stage0 artifact root from src/stage0 before collecting"
        echo "stage2 no-verification bootstrap evidence. This gate does not fall back"
        echo "to inherited upstream Rust stage0 downloads."
        echo
        echo "To check whether existing Trust metadata declares fetchable canonical"
        echo "payload URLs, run:"
        echo "  python3 scripts/fetch_trust_stage0_payloads.py"
        echo "Add --fetch only when that audit reports fetchable payloads. The helper"
        echo "refuses undeclared URLs and validates the src/stage0 SHA-256 pins before"
        echo "writing any archive."
    } >&2
    return 1
}

run_preflight_checks() {
    preflight_clean_tracked_worktree || return "$?"
    preflight_clean_untracked_sources || return "$?"
    preflight_source_manifests || return "$?"
    preflight_stage0_payloads || return "$?"
    preflight_self_contained_lockfiles || return "$?"
}

scan_noverify_log() {
    local log_path="$1"
    local stage2_sysroot="$2"
    local stage2_targo="$stage2_sysroot/bin/targo"
    local stage2_trustc="$stage2_sysroot/bin/trustc"
    local stage2_targo_trust="$stage2_sysroot/bin/targo-trust"
    local stage2_trustd="$stage2_sysroot/bin/trustd"
    local stage2_trustdoc="$stage2_sysroot/bin/trustdoc"
    local stage2_trustfmt="$stage2_sysroot/bin/trustfmt"
    local stage2_targo_fmt="$stage2_sysroot/bin/targo-fmt"
    local stage2_tippy="$stage2_sysroot/bin/tippy"
    local stage2_targo_tippy="$stage2_sysroot/bin/targo-tippy"
    local stage2_tippy_driver="$stage2_sysroot/bin/tippy-driver"
    local stage2_trust_analyzer="$stage2_sysroot/bin/trust-analyzer"
    local stage2_alias="$TRUST_ROOT/build/host/stage2"
    local stage2_targo_alias="$stage2_alias/bin/targo"
    local stage2_trustc_alias="$stage2_alias/bin/trustc"
    local stage2_targo_trust_alias="$stage2_alias/bin/targo-trust"
    local stage2_trustd_alias="$stage2_alias/bin/trustd"
    local stage2_trustdoc_alias="$stage2_alias/bin/trustdoc"
    local stage2_trustfmt_alias="$stage2_alias/bin/trustfmt"
    local stage2_targo_fmt_alias="$stage2_alias/bin/targo-fmt"
    local stage2_tippy_alias="$stage2_alias/bin/tippy"
    local stage2_targo_tippy_alias="$stage2_alias/bin/targo-tippy"
    local stage2_tippy_driver_alias="$stage2_alias/bin/tippy-driver"
    local stage2_trust_analyzer_alias="$stage2_alias/bin/trust-analyzer"
    local host_cargo
    local host_rustc

    host_cargo="$(command -v cargo 2>/dev/null || true)"
    host_rustc="$(command -v rustc 2>/dev/null || true)"

    {
        echo "log=$log_path"
        echo "stage2_targo=$stage2_targo"
        echo "stage2_trustc=$stage2_trustc"
        echo "stage2_targo_trust=$stage2_targo_trust"
        echo "stage2_trustd=$stage2_trustd"
        echo "stage2_trustdoc=$stage2_trustdoc"
        echo "stage2_trustfmt=$stage2_trustfmt"
        echo "stage2_targo_fmt=$stage2_targo_fmt"
        echo "stage2_tippy=$stage2_tippy"
        echo "stage2_targo_tippy=$stage2_targo_tippy"
        echo "stage2_tippy_driver=$stage2_tippy_driver"
        echo "stage2_trust_analyzer=$stage2_trust_analyzer"
        echo "stage2_sysroot_alias=$stage2_alias"
        echo "host_or_upstream_cargo=${host_cargo:-<not-found>}"
        echo "host_or_upstream_rustc=${host_rustc:-<not-found>}"
        echo
        echo "trust_verification_report_count=$(grep -c 'Trust Verification Report\\|TRUST_JSON:' "$log_path" || true)"
        echo "stage2_targo_path_count=$(grep -cF "$stage2_targo" "$log_path" || true)"
        echo "stage2_trustc_path_count=$(grep -cF "$stage2_trustc" "$log_path" || true)"
        echo "stage2_targo_trust_path_count=$(grep -cF "$stage2_targo_trust" "$log_path" || true)"
        echo "stage2_trustd_path_count=$(grep -cF "$stage2_trustd" "$log_path" || true)"
        echo "stage2_trustdoc_path_count=$(grep -cF "$stage2_trustdoc" "$log_path" || true)"
        echo "stage2_trustfmt_path_count=$(grep -cF "$stage2_trustfmt" "$log_path" || true)"
        echo "stage2_targo_fmt_path_count=$(grep -cF "$stage2_targo_fmt" "$log_path" || true)"
        echo "stage2_tippy_path_count=$(grep -cF "$stage2_tippy" "$log_path" || true)"
        echo "stage2_targo_tippy_path_count=$(grep -cF "$stage2_targo_tippy" "$log_path" || true)"
        echo "stage2_tippy_driver_path_count=$(grep -cF "$stage2_tippy_driver" "$log_path" || true)"
        echo "stage2_trust_analyzer_path_count=$(grep -cF "$stage2_trust_analyzer" "$log_path" || true)"
        if [[ "$stage2_targo_alias" != "$stage2_targo" ]]; then
            echo "stage2_targo_alias_path_count=$(grep -cF "$stage2_targo_alias" "$log_path" || true)"
        fi
        if [[ "$stage2_trustc_alias" != "$stage2_trustc" ]]; then
            echo "stage2_trustc_alias_path_count=$(grep -cF "$stage2_trustc_alias" "$log_path" || true)"
        fi
        if [[ "$stage2_targo_trust_alias" != "$stage2_targo_trust" ]]; then
            echo "stage2_targo_trust_alias_path_count=$(grep -cF "$stage2_targo_trust_alias" "$log_path" || true)"
        fi
        if [[ "$stage2_trustd_alias" != "$stage2_trustd" ]]; then
            echo "stage2_trustd_alias_path_count=$(grep -cF "$stage2_trustd_alias" "$log_path" || true)"
        fi
        if [[ "$stage2_trustdoc_alias" != "$stage2_trustdoc" ]]; then
            echo "stage2_trustdoc_alias_path_count=$(grep -cF "$stage2_trustdoc_alias" "$log_path" || true)"
        fi
        if [[ "$stage2_trustfmt_alias" != "$stage2_trustfmt" ]]; then
            echo "stage2_trustfmt_alias_path_count=$(grep -cF "$stage2_trustfmt_alias" "$log_path" || true)"
        fi
        if [[ "$stage2_targo_fmt_alias" != "$stage2_targo_fmt" ]]; then
            echo "stage2_targo_fmt_alias_path_count=$(grep -cF "$stage2_targo_fmt_alias" "$log_path" || true)"
        fi
        if [[ "$stage2_tippy_alias" != "$stage2_tippy" ]]; then
            echo "stage2_tippy_alias_path_count=$(grep -cF "$stage2_tippy_alias" "$log_path" || true)"
        fi
        if [[ "$stage2_targo_tippy_alias" != "$stage2_targo_tippy" ]]; then
            echo "stage2_targo_tippy_alias_path_count=$(grep -cF "$stage2_targo_tippy_alias" "$log_path" || true)"
        fi
        if [[ "$stage2_tippy_driver_alias" != "$stage2_tippy_driver" ]]; then
            echo "stage2_tippy_driver_alias_path_count=$(grep -cF "$stage2_tippy_driver_alias" "$log_path" || true)"
        fi
        if [[ "$stage2_trust_analyzer_alias" != "$stage2_trust_analyzer" ]]; then
            echo "stage2_trust_analyzer_alias_path_count=$(grep -cF "$stage2_trust_analyzer_alias" "$log_path" || true)"
        fi
        if [[ -n "$host_cargo" ]]; then
            echo "host_or_upstream_cargo_path_count=$(grep -cF "$host_cargo" "$log_path" || true)"
        fi
        if [[ -n "$host_rustc" ]]; then
            echo "host_or_upstream_rustc_path_count=$(grep -cF "$host_rustc" "$log_path" || true)"
        fi
    } >"$SCAN_LOG"
}

file_mtime_epoch() {
    local path="$1"

    if stat -f '%m' "$path" >/dev/null 2>&1; then
        stat -f '%m' "$path"
    else
        stat -c '%Y' "$path"
    fi
}

file_sha256() {
    shasum -a 256 "$1" | awk '{print $1}'
}

write_stage2_tool_surface_diagnostic() {
    local reason="$1"
    local selected_sysroot="${2:-}"
    local candidate
    local tool
    local path
    local status
    local found_rustc_main=0

    {
        echo "reason=$reason"
        echo "selected_stage2_sysroot=${selected_sysroot:-<none>}"
        echo "expected_canonical_tools=${STAGE2_REQUIRED_TOOLS[*]}"
        echo "expected_compat_aliases=${STAGE2_REQUIRED_COMPAT_ALIASES[*]}"
        echo "responsibility=bootstrap compiler/sysroot install must materialize Trust-preferred tools and same-sysroot Rust-compatible aliases"
        echo

        while IFS= read -r candidate; do
            local missing_tools=""
            local missing_aliases=""
            local invalid_aliases=""
            echo "candidate=$candidate"
            if [[ ! -d "$candidate" ]]; then
                echo "status=missing-stage2-sysroot"
                echo
                continue
            fi

            local forbidden_error=""
            if forbidden_error="$(trust_toolchain_forbidden_entry_error "$candidate/bin")"; then
                echo "forbidden_public_surface=$forbidden_error"
            fi

            for tool in "${STAGE2_REQUIRED_TOOLS[@]}" "${STAGE2_REQUIRED_COMPAT_ALIASES[@]}"; do
                path="$candidate/bin/$tool"
                if stage2_required_tool_name "$tool" \
                    && trust_toolchain_exact_executables_valid "$candidate/bin" "$tool"; then
                    status="exact-executable"
                elif stage2_required_alias_name "$tool" && [[ -x "$path" ]]; then
                    status="executable"
                elif [[ -e "$path" ]]; then
                    status="present-noncanonical"
                    if stage2_required_tool_name "$tool"; then
                        missing_tools="$missing_tools $tool"
                    elif stage2_required_alias_name "$tool"; then
                        missing_aliases="$missing_aliases $tool"
                    fi
                else
                    status="missing"
                    if stage2_required_tool_name "$tool"; then
                        missing_tools="$missing_tools $tool"
                    elif stage2_required_alias_name "$tool"; then
                        missing_aliases="$missing_aliases $tool"
                    fi
                fi
                echo "$tool=$status path=$path"
                if [[ "$status" == "exact-executable" || "$status" == "executable" ]]; then
                    echo "${tool}_sha256=$(file_sha256 "$path")"
                    echo "${tool}_mtime_epoch=$(file_mtime_epoch "$path")"
                fi
            done
            local pair canonical alias alias_error
            for pair in "${STAGE2_REQUIRED_ALIAS_PAIRS[@]}"; do
                canonical="${pair%%:*}"
                alias="${pair#*:}"
                if [[ -x "$candidate/bin/$canonical" && -x "$candidate/bin/$alias" ]] \
                    && alias_error="$(
                        trust_toolchain_alias_pair_error "$candidate/bin" "$canonical" "$alias"
                    )"; then
                    invalid_aliases+=" $canonical:$alias"
                    echo "invalid_alias_pair=$canonical:$alias reason=$alias_error"
                fi
            done
            if [[ -n "$forbidden_error" ]]; then
                echo "diagnosis=invalid stage2 sysroot: forbidden stock or retired public entrypoint is present"
                echo "next_measurement=remove inherited secondary aliases and rebuild the canonical Trust-only secondary surface"
            elif [[ -x "$candidate/bin/targo" && ! -x "$candidate/bin/trustc" ]]; then
                echo "diagnosis=partial stage2 sysroot: targo exists but canonical trustc is missing"
                echo "next_measurement=inspect the compiler install/link step that should copy rustc-main to stage2/bin/trustc"
            elif [[ -x "$candidate/bin/trustc" && ! -x "$candidate/bin/targo" ]]; then
                echo "diagnosis=partial stage2 sysroot: trustc exists but canonical targo is missing"
                echo "next_measurement=inspect the bootstrap tool install step for src/tools/targo -> stage2/bin/targo"
            elif [[ -n "$missing_tools" ]]; then
                echo "diagnosis=partial stage2 sysroot: missing required canonical Trust tool(s):$missing_tools"
                echo "next_measurement=inspect the bootstrap install/link step for the missing Trust-owned entrypoint(s)"
            elif [[ -n "$missing_aliases" ]]; then
                echo "diagnosis=partial stage2 sysroot: missing required Rust-compatible alias(es):$missing_aliases"
                echo "next_measurement=inspect the bootstrap install/link step for same-sysroot compatibility aliases"
            elif [[ -n "$invalid_aliases" ]]; then
                echo "diagnosis=partial stage2 sysroot: invalid same-sysroot alias binding(s):$invalid_aliases"
                echo "next_measurement=replace outward or mismatched aliases with same-bin bindings to canonical Trust artifacts"
            elif stage2_has_required_tools "$candidate" && stage2_has_required_compat_aliases "$candidate"; then
                echo "diagnosis=complete tool names are present; version probes determine runtime and identity health"
            fi
            echo
        done < <(stage2_sysroot_candidates)

        echo "stage2_rustc_main_outputs="
        while IFS= read -r path; do
            found_rustc_main=1
            echo "  - $path"
        done < <(find "$TRUST_ROOT/build" -path '*/stage2-rustc/*/release/rustc-main' -type f -print 2>/dev/null | sort)
        if [[ "$found_rustc_main" -eq 0 ]]; then
            echo "  - <none>"
        fi
    } >"$ARTIFACTS_LOG"
}

record_stage2_tool_versions() {
    local stage2_sysroot="$1"
    local status=0
    local runtime_lib_dir="$stage2_sysroot/lib"
    local runtime_lib_var
    local runtime_lib_value

    case "$(uname -s)" in
        Darwin)
            runtime_lib_var="DYLD_LIBRARY_PATH"
            ;;
        *)
            runtime_lib_var="LD_LIBRARY_PATH"
            ;;
    esac
    runtime_lib_value="$runtime_lib_dir"
    if [[ -n "${!runtime_lib_var-}" ]]; then
        runtime_lib_value="$runtime_lib_value:${!runtime_lib_var}"
    fi

    : >"$VERSIONS_LOG"

    record_one_stage2_tool_version() {
        local label="$1"
        shift
        local rc=0

        {
            echo "## $label"
            echo "command=$(format_command "$@")"
            if [[ -d "$runtime_lib_dir" ]]; then
                echo "runtime_library_env=$runtime_lib_var=$runtime_lib_value"
            fi
        } >>"$VERSIONS_LOG"

        set +e
        if [[ -d "$runtime_lib_dir" ]]; then
            env "$runtime_lib_var=$runtime_lib_value" "$@" >>"$VERSIONS_LOG" 2>&1
        else
            "$@" >>"$VERSIONS_LOG" 2>&1
        fi
        rc=$?
        set -e
        if [[ "$rc" -ne 0 ]]; then
            status=1
        fi

        {
            echo "exit_code=$rc"
            echo
        } >>"$VERSIONS_LOG"
    }

    record_one_stage2_tool_version trustc "$stage2_sysroot/bin/trustc" -Vv
    record_one_stage2_tool_version targo "$stage2_sysroot/bin/targo" -Vv
    record_one_stage2_tool_version targo-trust "$stage2_sysroot/bin/targo-trust" --version
    record_one_stage2_tool_version trustd "$stage2_sysroot/bin/trustd" --version
    record_one_stage2_tool_version trustdoc "$stage2_sysroot/bin/trustdoc" --version
    record_one_stage2_tool_version trustfmt "$stage2_sysroot/bin/trustfmt" --version
    record_one_stage2_tool_version targo-fmt "$stage2_sysroot/bin/targo-fmt" --version
    record_one_stage2_tool_version tippy "$stage2_sysroot/bin/tippy" --version
    record_one_stage2_tool_version targo-tippy "$stage2_sysroot/bin/targo-tippy" --version
    record_one_stage2_tool_version tippy-driver "$stage2_sysroot/bin/tippy-driver" --version
    record_one_stage2_tool_version trust-analyzer "$stage2_sysroot/bin/trust-analyzer" --version

    return "$status"
}

validate_stage2_artifacts_fresh() {
    local stage2_sysroot="$1"
    local tool
    local path
    local mtime
    local sha
    local status=0

    {
        echo "run_start_utc=$RUN_START_UTC"
        echo "run_start_epoch=$RUN_START_EPOCH"
        echo "stage2_sysroot=$stage2_sysroot"
        echo
    } >"$ARTIFACTS_LOG"

    for tool in "${STAGE2_REQUIRED_TOOLS[@]}"; do
        path="$stage2_sysroot/bin/$tool"
        if [[ ! -x "$path" ]]; then
            echo "error: missing executable stage2 tool: $path" | tee -a "$ARTIFACTS_LOG" >&2
            status=1
            continue
        fi
        mtime="$(file_mtime_epoch "$path")"
        sha="$(file_sha256 "$path")"
        {
            echo "tool=$tool"
            echo "path=$path"
            echo "mtime_epoch=$mtime"
            echo "sha256=$sha"
            echo
        } >>"$ARTIFACTS_LOG"
        if [[ "$mtime" -lt "$RUN_START_EPOCH" ]]; then
            echo "error: stage2 $tool is older than this no-verification run start: $path" >&2
            status=1
        fi
    done

    return "$status"
}

stage2_tool_version_line() {
    local label="$1"
    local prefix="$2"
    awk -v heading="## $label" -v prefix="$prefix" '
        $0 == heading { in_section = 1; next }
        in_section && /^## / { exit }
        in_section && index($0, prefix) == 1 { print; exit }
    ' "$VERSIONS_LOG"
}

validate_stage2_tool_identity() {
    local trustc_binary
    local trustc_commit
    local targo_version_line
    local targo_trust_identity
    local trustd_version_line
    local trustdoc_version_line
    local trustfmt_version_line
    local targo_fmt_version_line
    local tippy_version_line
    local targo_tippy_version_line
    local tippy_driver_version_line
    local trust_analyzer_version_line
    local status=0

    trustc_binary="$(awk -F': ' '/^binary:/{print $2; exit}' "$VERSIONS_LOG")"
    trustc_commit="$(awk -F': ' '/^commit-hash:/{print $2; exit}' "$VERSIONS_LOG")"
    targo_version_line="$(grep -m1 '^targo ' "$VERSIONS_LOG" || true)"
    targo_trust_identity="$(awk -F= '/^trust.identity=/{print $2; exit}' "$VERSIONS_LOG")"
    trustd_version_line="$(stage2_tool_version_line trustd 'trustd ' || true)"
    trustdoc_version_line="$(grep -m1 '(trustdoc)\|^trustdoc ' "$VERSIONS_LOG" || true)"
    trustfmt_version_line="$(grep -m1 '^trustfmt ' "$VERSIONS_LOG" || true)"
    targo_fmt_version_line="$(stage2_tool_version_line targo-fmt 'trustfmt ' || true)"
    tippy_version_line="$(stage2_tool_version_line tippy 'tippy ' || true)"
    targo_tippy_version_line="$(stage2_tool_version_line targo-tippy 'tippy ' || true)"
    tippy_driver_version_line="$(stage2_tool_version_line tippy-driver 'tippy ' || true)"
    trust_analyzer_version_line="$(grep -m1 '^trust-analyzer ' "$VERSIONS_LOG" || true)"

    if [[ "$trustc_binary" != "trustc" ]]; then
        echo "error: stage2 trustc identity reported binary '$trustc_binary', expected 'trustc'" >&2
        status=1
    fi
    if [[ "$trustc_commit" != "$START_HEAD" ]]; then
        echo "error: stage2 trustc commit-hash '$trustc_commit' does not match source HEAD '$START_HEAD'" >&2
        status=1
    fi
    if [[ "$targo_version_line" != targo\ * ]]; then
        echo "error: stage2 targo version line is not canonical targo identity: ${targo_version_line:-<missing>}" >&2
        status=1
    fi
    if [[ "$targo_trust_identity" != "targo trust" ]]; then
        echo "error: targo-trust identity '$targo_trust_identity' does not match 'targo trust'" >&2
        status=1
    fi
    if [[ "$trustd_version_line" != trustd\ * ]]; then
        echo "error: stage2 trustd version line is not canonical trustd identity: ${trustd_version_line:-<missing>}" >&2
        status=1
    fi
    if [[ -z "$trustdoc_version_line" ]]; then
        echo "error: stage2 trustdoc version line is not canonical trustdoc identity: <missing>" >&2
        status=1
    fi
    if [[ "$trustfmt_version_line" != trustfmt\ * ]]; then
        echo "error: stage2 trustfmt version line is not canonical trustfmt identity: ${trustfmt_version_line:-<missing>}" >&2
        status=1
    fi
    if [[ "$targo_fmt_version_line" != trustfmt\ * ]]; then
        echo "error: stage2 targo-fmt version line is not canonical Trust formatter identity: ${targo_fmt_version_line:-<missing>}" >&2
        status=1
    fi
    if [[ "$tippy_version_line" != tippy\ * ]]; then
        echo "error: stage2 tippy version line is not canonical tippy identity: ${tippy_version_line:-<missing>}" >&2
        status=1
    fi
    if [[ "$targo_tippy_version_line" != tippy\ * ]]; then
        echo "error: stage2 targo-tippy version line is not canonical tippy identity: ${targo_tippy_version_line:-<missing>}" >&2
        status=1
    fi
    if [[ "$tippy_driver_version_line" != tippy\ * ]]; then
        echo "error: stage2 tippy-driver version line is not canonical tippy identity: ${tippy_driver_version_line:-<missing>}" >&2
        status=1
    fi
    if [[ "$trust_analyzer_version_line" != trust-analyzer\ * ]]; then
        echo "error: stage2 trust-analyzer version line is not canonical trust-analyzer identity: ${trust_analyzer_version_line:-<missing>}" >&2
        status=1
    fi

    return "$status"
}

source_watch_loop() {
    while :; do
        echo "sample_utc=$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
        if dirty="$(source_dirty_report)"; then
            if [[ -n "$dirty" ]]; then
                echo "DIRTY:"
                printf '%s\n' "$dirty"
            else
                echo "clean"
            fi
        else
            echo "ERROR: git source status failed"
        fi
        echo
        sleep "$SOURCE_WATCH_INTERVAL"
    done
}

source_dirty_sample_count() {
    if [[ ! -f "$SOURCE_WATCH_LOG" ]]; then
        echo 0
        return 0
    fi
    grep -c '^DIRTY:\|^ERROR: git source status failed' "$SOURCE_WATCH_LOG" || true
}

write_report_json() {
    local status="$1"
    local exit_code="$2"
    local stage2_sysroot="$3"
    local trustc_commit="${4:-}"
    local targo_version_line="${5:-}"
    local targo_trust_identity="${6:-}"
    local trustdoc_version_line="${7:-}"
    local trustfmt_version_line="${8:-}"
    local tippy_version_line="${9:-}"
    local targo_tippy_version_line="${10:-}"
    local tippy_driver_version_line="${11:-}"
    local trust_analyzer_version_line="${12:-}"
    local trustd_version_line
    local targo_fmt_version_line
    local end_head
    local dirty_entries
    local dirty_samples
    local head_changed="false"

    end_head="$(git rev-parse HEAD)"
    dirty_entries="$(tracked_dirty_count)"
    dirty_samples="$(source_dirty_sample_count)"
    if [[ "$START_HEAD" != "$end_head" ]]; then
        head_changed="true"
    fi
    trustd_version_line="$(stage2_tool_version_line trustd 'trustd ' || true)"
    targo_fmt_version_line="$(stage2_tool_version_line targo-fmt 'trustfmt ' || true)"

    cat >"$REPORT_JSON" <<JSON
{
  "schema": "trust.stage2-noverify.self-build.v1",
  "run_id": "$RUN_ID",
  "status": "$status",
  "exit_code": $exit_code,
  "run_start_utc": "$RUN_START_UTC",
  "run_start_epoch": $RUN_START_EPOCH,
  "source": {
    "start_head": "$START_HEAD",
    "end_head": "$end_head",
    "head_changed": $head_changed,
    "tracked_dirty_entries": $dirty_entries,
    "source_dirty_samples": $dirty_samples
  },
  "stage2": {
    "sysroot": "$stage2_sysroot",
    "trustc_commit_hash": "$trustc_commit",
    "targo_version_line": "$targo_version_line",
    "targo_trust_identity": "$targo_trust_identity",
    "trustd_version_line": "$trustd_version_line",
    "trustdoc_version_line": "$trustdoc_version_line",
    "trustfmt_version_line": "$trustfmt_version_line",
    "targo_fmt_version_line": "$targo_fmt_version_line",
    "tippy_version_line": "$tippy_version_line",
    "targo_tippy_version_line": "$targo_tippy_version_line",
    "tippy_driver_version_line": "$tippy_driver_version_line",
    "trust_analyzer_version_line": "$trust_analyzer_version_line",
    "required_tools": [
      "trustc",
      "targo",
      "targo-trust",
      "trustd",
      "trustdoc",
      "trustfmt",
      "targo-fmt",
      "tippy",
      "targo-tippy",
      "tippy-driver",
      "trust-analyzer"
    ]
  },
  "logs": {
    "build": "$BUILD_LOG",
    "preflight": "$PREFLIGHT_LOG",
    "versions": "$VERSIONS_LOG",
    "scan": "$SCAN_LOG",
    "artifacts": "$ARTIFACTS_LOG",
    "source_watch": "$SOURCE_WATCH_LOG"
  }
}
JSON
}

write_summary() {
    local status="$1"
    local exit_code="$2"
    local command_line="$3"
    local end_head
    local head_changed="false"
    local dirty_entries
    end_head="$(git rev-parse HEAD 2>/dev/null || echo unknown)"
    dirty_entries="$(tracked_dirty_count)"
    if [[ "$START_HEAD" != "$end_head" ]]; then
        head_changed="true"
    fi

    {
        echo "# Stage2 No-Verification Self-Build"
        echo
        echo "- run_id: \`$RUN_ID\`"
        echo "- status: \`$status\`"
        echo "- exit_code: \`$exit_code\`"
        echo "- start_head: \`$START_HEAD\`"
        echo "- end_head: \`$end_head\`"
        echo "- head_changed: \`$head_changed\`"
        echo "- tracked_dirty_entries: \`$dirty_entries\`"
        echo "- jobs: \`$JOBS\`"
        echo "- report_json: \`$REPORT_JSON\`"
        echo "- build_log: \`$BUILD_LOG\`"
        echo "- preflight_log: \`$PREFLIGHT_LOG\`"
        echo "- versions_log: \`$VERSIONS_LOG\`"
        echo "- scan_log: \`$SCAN_LOG\`"
        echo "- artifacts_log: \`$ARTIFACTS_LOG\`"
        echo "- source_watch_log: \`$SOURCE_WATCH_LOG\`"
        echo
        echo "## Canonical Command"
        echo
        echo '```sh'
        echo "$command_line"
        echo '```'
    } >"$SUMMARY"
}

main() {
    case "${1:-}" in
        --help|-h)
            usage
            return 0
            ;;
        "")
            ;;
        *)
            echo "error: unknown argument: $1" >&2
            usage >&2
            return 2
            ;;
    esac

    mkdir -p "$LOG_DIR"

    local offline_cargoflags
    local wrapper_env_unsets=()
    local wrapper_env
    offline_cargoflags="$(append_shell_word "${CARGOFLAGS:-}" "--offline")"
    for wrapper_env in "${BOOTSTRAP_WRAPPER_ENV_UNSET[@]}"; do
        wrapper_env_unsets+=("-u" "$wrapper_env")
    done

    local command=(
        env
        "${wrapper_env_unsets[@]}"
        CARGO_NET_OFFLINE=true
        TRUST_JOBS="$JOBS"
        CARGOFLAGS="$offline_cargoflags"
        ./x.py build
        --set llvm.ninja=false
        --set build.extended=true
        --set 'build.tools=["targo","targo-trust","trustdoc","trustfmt","tippy","trust-analyzer"]'
        --set rust.debuginfo-level-tools=0
        --set rust.debug-assertions-tools=false
        -j "$JOBS"
        --stage 2
        compiler/rustc
        library/std
    )
    local command_line
    command_line="$(format_command "${command[@]}")"

    if [[ "$DRY_RUN" == "1" ]]; then
        echo "$command_line"
        write_summary planned 0 "$command_line"
        write_report_json planned 0 "" "" "" "" "" "" "" ""
        return 0
    fi

    if ! run_preflight_checks 2> >(tee "$PREFLIGHT_LOG" >&2); then
        write_summary failed 1 "$command_line"
        write_report_json failed 1 "" "" "" ""
        return 1
    fi

    local status=0
    : >"$SOURCE_WATCH_LOG"
    source_watch_loop >"$SOURCE_WATCH_LOG" 2>&1 &
    local source_watch_pid="$!"
    "${command[@]}" 2>&1 | tee "$BUILD_LOG" || status=${PIPESTATUS[0]}
    kill "$source_watch_pid" 2>/dev/null || true
    wait "$source_watch_pid" 2>/dev/null || true

    local stage2_sysroot=""
    local version_status=0
    local trustc_commit=""
    local targo_version_line=""
    local targo_trust_identity=""
    local trustdoc_version_line=""
    local trustfmt_version_line=""
    local tippy_version_line=""
    local targo_tippy_version_line=""
    local tippy_driver_version_line=""
    local trust_analyzer_version_line=""
    if stage2_sysroot="$(find_stage2_sysroot)"; then
        record_stage2_tool_versions "$stage2_sysroot" || version_status=$?
        scan_noverify_log "$BUILD_LOG" "$stage2_sysroot"
        trustc_commit="$(awk -F': ' '/^commit-hash:/{print $2; exit}' "$VERSIONS_LOG")"
        targo_version_line="$(grep -m1 '^targo ' "$VERSIONS_LOG" || true)"
        targo_trust_identity="$(awk -F= '/^trust.identity=/{print $2; exit}' "$VERSIONS_LOG")"
        trustdoc_version_line="$(grep -m1 '(trustdoc)\|^trustdoc ' "$VERSIONS_LOG" || true)"
        trustfmt_version_line="$(grep -m1 '^trustfmt ' "$VERSIONS_LOG" || true)"
        tippy_version_line="$(stage2_tool_version_line tippy 'tippy ' || true)"
        targo_tippy_version_line="$(stage2_tool_version_line targo-tippy 'tippy ' || true)"
        tippy_driver_version_line="$(stage2_tool_version_line tippy-driver 'tippy ' || true)"
        trust_analyzer_version_line="$(grep -m1 '^trust-analyzer ' "$VERSIONS_LOG" || true)"
    else
        write_stage2_tool_surface_diagnostic "no-complete-stage2-sysroot" ""
        echo "stage2 tool surface diagnostic: $ARTIFACTS_LOG" >&2
    fi

    if [[ "$status" -eq 0 && -z "$stage2_sysroot" ]]; then
        echo "error: build exited 0 but no stage2 sysroot with canonical trustc/targo/targo-trust/trustd/trustdoc/trustfmt/targo-fmt/tippy/targo-tippy/tippy-driver/trust-analyzer was found" >&2
        status=1
    fi

    if [[ "$status" -eq 0 && "$version_status" -ne 0 ]]; then
        write_stage2_tool_surface_diagnostic "stage2-tool-version-proof-failed" "$stage2_sysroot"
        echo "stage2 tool surface diagnostic: $ARTIFACTS_LOG" >&2
        echo "error: stage2 Trust tool version proof failed; see $VERSIONS_LOG" >&2
        status="$version_status"
    fi

    if [[ "$status" -eq 0 ]] && ! validate_stage2_artifacts_fresh "$stage2_sysroot"; then
        status=1
    fi

    if [[ "$status" -eq 0 ]] && ! validate_stage2_tool_identity; then
        status=1
    fi

    local end_head
    end_head="$(git rev-parse HEAD)"
    if [[ "$status" -eq 0 && "$START_HEAD" != "$end_head" ]]; then
        echo "error: repository HEAD changed during no-verification self-build: $START_HEAD -> $end_head" >&2
        status=1
    fi
    local dirty_entries_after
    dirty_entries_after="$(tracked_dirty_count)"
    if [[ "$status" -eq 0 && "$dirty_entries_after" -ne 0 ]]; then
        echo "error: tracked source worktree became dirty during no-verification self-build:" >&2
        tracked_dirty_report >&2
        status=1
    fi
    local dirty_samples
    dirty_samples="$(source_dirty_sample_count)"
    if [[ "$status" -eq 0 && "$dirty_samples" -ne 0 ]]; then
        echo "error: source worktree was dirty during no-verification self-build; see $SOURCE_WATCH_LOG" >&2
        status=1
    fi

    if [[ "$status" -eq 0 ]]; then
        write_summary passed "$status" "$command_line"
        write_report_json passed "$status" "$stage2_sysroot" "$trustc_commit" "$targo_version_line" "$targo_trust_identity" "$trustdoc_version_line" "$trustfmt_version_line" "$tippy_version_line" "$targo_tippy_version_line" "$tippy_driver_version_line" "$trust_analyzer_version_line"
    else
        write_summary failed "$status" "$command_line"
        write_report_json failed "$status" "$stage2_sysroot" "$trustc_commit" "$targo_version_line" "$targo_trust_identity" "$trustdoc_version_line" "$trustfmt_version_line" "$tippy_version_line" "$targo_tippy_version_line" "$tippy_driver_version_line" "$trust_analyzer_version_line"
    fi
    return "$status"
}

main "$@"
