#!/usr/bin/env bash
# Run a bounded verification-on self-build step with explicit stage2 Trust tools.
#
# This wrapper is intentionally small and fail-closed. It proves that a
# canonical repo-local stage2 sysroot exposes Trust-preferred tools, records
# timing for each preflight/build step, performs a separate bootstrap rebuild
# for provenance, then delegates one direct Cargo JSON evidence build to
# `targo trust verify self`. Bootstrap stdout is never proof input. A
# successful process without compiler TRUST_JSON obligation rows is still an
# incomplete proof.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
DEFAULT_TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

TRUST_ROOT="${TRUST_STAGE2_VERIFY_REPO_ROOT:-$DEFAULT_TRUST_ROOT}"
RUN_ID="${TRUST_STAGE2_VERIFY_RUN_ID:-stage2-verify-self-build-$(date -u '+%Y%m%dT%H%M%SZ')}"
REPORT_DIR="${TRUST_STAGE2_VERIFY_REPORT_DIR:-}"
PYTHON3="${PYTHON3:-python3}"
TRUST_TOOLCHAIN_PYTHON3="$PYTHON3"
. "$SCRIPT_DIR/lib/trust_toolchain_surface.sh"
JOBS="${TRUST_STAGE2_VERIFY_JOBS:-${TRUST_JOBS:-2}}"
TIMEOUT_SEC="${TRUST_STAGE2_VERIFY_TIMEOUT_SEC:-300}"
TARGET="${TRUST_STAGE2_VERIFY_TARGET:-stage2 full-bootstrap compiler/rustc library/std}"
EVIDENCE_MANIFEST="${TRUST_STAGE2_VERIFY_EVIDENCE_MANIFEST:-targo-trust/Cargo.toml}"
INCLUDE_DEPENDENCIES_RAW="${TRUST_STAGE2_VERIFY_INCLUDE_DEPENDENCIES:-yes}"
WORKER_THREADS="${TRUST_VERIFY_WORKER_THREADS:-2}"
OFFLINE="${TRUST_STAGE2_VERIFY_OFFLINE:-1}"
DRY_RUN="${TRUST_STAGE2_VERIFY_DRY_RUN:-0}"
PERF_BUDGET_MODE="${TRUST_STAGE2_VERIFY_PERF_BUDGET_MODE:-report}"
MAX_VERIFICATION_WALL_TIME_SEC="${TRUST_STAGE2_VERIFY_MAX_VERIFICATION_WALL_TIME_SEC:-${TRUST_STAGE2_VERIFY_MAX_WALL_TIME_SEC:-}}"
MAX_REPORTED_SOLVER_TIME_MS="${TRUST_STAGE2_VERIFY_MAX_REPORTED_SOLVER_TIME_MS:-${TRUST_STAGE2_VERIFY_MAX_SOLVER_TIME_MS:-}}"
MAX_OBLIGATION_ROWS="${TRUST_STAGE2_VERIFY_MAX_OBLIGATION_ROWS:-}"
MAX_CACHE_MISS_OBLIGATIONS="${TRUST_STAGE2_VERIFY_MAX_CACHE_MISS_OBLIGATIONS:-}"
COMPARE_REPORT="${TRUST_STAGE2_VERIFY_COMPARE_REPORT:-}"
STAGE_LABEL="stage2-explicit-trust-tools-verification-on"
STAGE_DESCRIPTION="Direct stage2 Targo Cargo JSON evidence build for the explicit evidence manifest; the default wrapper performs bootstrap rebuild/provenance separately and never parses bootstrap stdout as proof."
REQUIRED_STAGE2_TOOLS=(
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
REQUIRED_STAGE2_COMPAT_ALIASES=("rustc" "cargo")
REQUIRED_STAGE2_ALIAS_PAIRS=("trustc:rustc" "targo:cargo")
CUSTOM_STAGE_COMMAND=()

usage() {
    cat <<'USAGE'
stage2_verify_self_build.sh -- bounded verification-on stage2 self-build harness

USAGE:
  bash scripts/stage2_verify_self_build.sh [options]
  bash scripts/stage2_verify_self_build.sh [options] -- <custom stage command>

OPTIONS:
  --repo-root PATH      Trust repo root. Defaults to this script's parent.
  --report-dir PATH    Evidence directory. Defaults to reports/build/<run-id>.
  --run-id ID          Evidence run id.
  --timeout SEC        Bounded stage timeout. Defaults to 300.
  --jobs N             Job count passed to the Rust self-verify metadata.
  --target TEXT        Logical release/composition label; never interpreted as a path.
  --evidence-manifest PATH
                      Cargo manifest selecting the authenticated proof package.
  --perf-budget-mode MODE
                      Harness perf budget mode: report or enforce. Defaults to report.
  --max-verification-wall-time-sec SEC
                      Report/enforce bounded verification wall time.
  --max-reported-solver-time-ms MS
                      Report/enforce summed TRUST_JSON solver time.
  --max-obligation-rows N
                      Report/enforce maximum TRUST_JSON obligation rows.
  --max-cache-miss-obligations N
                      Report/enforce maximum cache-miss obligation rows.
  --compare-report PATH
                      Add report-only performance deltas against a previous harness report.
  --dry-run            Write a planned report without invoking toolchain commands.
  -h, --help           Show this help.

ENVIRONMENT:
  TRUST_STAGE2_SYSROOT=/repo/build/<host>/stage2
      Optional explicit repo-local stage2 sysroot. Must contain bin/trustc,
      bin/targo, bin/targo-trust, bin/trustd, bin/trustdoc, bin/trustfmt,
      bin/targo-fmt,
      bin/tippy, bin/targo-tippy, bin/tippy-driver, and bin/trust-analyzer. Non-repo sysroots are refused
      for self-build evidence.
  TRUST_STAGE2_VERIFY_INCLUDE_DEPENDENCIES=yes|no
      Forward dependency verification policy to the evidence harness. Defaults to yes.

OUTPUT:
  <report-dir>/stage2-verify-self-build.report.json
  <report-dir>/summary.md
  <report-dir>/timings.tsv
  <report-dir>/logs/*
  <report-dir>/self-verify-harness/self-verify-harness.report.json when run
USAGE
}

while [[ "$#" -gt 0 ]]; do
    case "$1" in
        --repo-root)
            [[ "$#" -ge 2 ]] || { echo "error: --repo-root requires a value" >&2; exit 2; }
            TRUST_ROOT="$2"
            shift 2
            ;;
        --report-dir)
            [[ "$#" -ge 2 ]] || { echo "error: --report-dir requires a value" >&2; exit 2; }
            REPORT_DIR="$2"
            shift 2
            ;;
        --run-id)
            [[ "$#" -ge 2 ]] || { echo "error: --run-id requires a value" >&2; exit 2; }
            RUN_ID="$2"
            shift 2
            ;;
        --timeout)
            [[ "$#" -ge 2 ]] || { echo "error: --timeout requires a value" >&2; exit 2; }
            TIMEOUT_SEC="$2"
            shift 2
            ;;
        --jobs)
            [[ "$#" -ge 2 ]] || { echo "error: --jobs requires a value" >&2; exit 2; }
            JOBS="$2"
            shift 2
            ;;
        --target)
            [[ "$#" -ge 2 ]] || { echo "error: --target requires a value" >&2; exit 2; }
            TARGET="$2"
            shift 2
            ;;
        --evidence-manifest)
            [[ "$#" -ge 2 ]] || { echo "error: --evidence-manifest requires a value" >&2; exit 2; }
            EVIDENCE_MANIFEST="$2"
            shift 2
            ;;
        --manifest)
            echo "error: --manifest was replaced by --evidence-manifest" >&2
            exit 2
            ;;
        --perf-budget-mode)
            [[ "$#" -ge 2 ]] || { echo "error: --perf-budget-mode requires a value" >&2; exit 2; }
            PERF_BUDGET_MODE="$2"
            shift 2
            ;;
        --max-verification-wall-time-sec)
            [[ "$#" -ge 2 ]] || { echo "error: --max-verification-wall-time-sec requires a value" >&2; exit 2; }
            MAX_VERIFICATION_WALL_TIME_SEC="$2"
            shift 2
            ;;
        --max-reported-solver-time-ms)
            [[ "$#" -ge 2 ]] || { echo "error: --max-reported-solver-time-ms requires a value" >&2; exit 2; }
            MAX_REPORTED_SOLVER_TIME_MS="$2"
            shift 2
            ;;
        --max-obligation-rows)
            [[ "$#" -ge 2 ]] || { echo "error: --max-obligation-rows requires a value" >&2; exit 2; }
            MAX_OBLIGATION_ROWS="$2"
            shift 2
            ;;
        --max-cache-miss-obligations)
            [[ "$#" -ge 2 ]] || { echo "error: --max-cache-miss-obligations requires a value" >&2; exit 2; }
            MAX_CACHE_MISS_OBLIGATIONS="$2"
            shift 2
            ;;
        --compare-report)
            [[ "$#" -ge 2 ]] || { echo "error: --compare-report requires a value" >&2; exit 2; }
            COMPARE_REPORT="$2"
            shift 2
            ;;
        --dry-run)
            DRY_RUN=1
            shift
            ;;
        --help|-h)
            usage
            exit 0
            ;;
        --)
            shift
            CUSTOM_STAGE_COMMAND=("$@")
            break
            ;;
        *)
            echo "error: unknown argument: $1" >&2
            usage >&2
            exit 2
            ;;
    esac
done

case "$PERF_BUDGET_MODE" in
    report|enforce)
        ;;
    *)
        echo "error: --perf-budget-mode must be report or enforce" >&2
        exit 2
        ;;
esac

INCLUDE_DEPENDENCIES_NORMALIZED="$(printf '%s' "$INCLUDE_DEPENDENCIES_RAW" | tr '[:upper:]' '[:lower:]')"
case "$INCLUDE_DEPENDENCIES_NORMALIZED" in
    1|y|yes|on|true)
        INCLUDE_DEPENDENCIES=yes
        ;;
    0|n|no|off|false)
        INCLUDE_DEPENDENCIES=no
        ;;
    *)
        echo "error: TRUST_STAGE2_VERIFY_INCLUDE_DEPENDENCIES requires a boolean value (0/1, yes/no, on/off, or true/false)" >&2
        exit 2
        ;;
esac

TRUST_ROOT="$(cd "$TRUST_ROOT" && pwd -P)"

requested_evidence_manifest_path() {
    if [[ "$EVIDENCE_MANIFEST" == /* ]]; then
        printf '%s\n' "$EVIDENCE_MANIFEST"
    else
        printf '%s\n' "$TRUST_ROOT/$EVIDENCE_MANIFEST"
    fi
}

# Resolve the proof subject before creating a report attempt or running the
# provenance-only bootstrap. The inner Rust harness repeats this check as the
# authority boundary; this early check prevents an invalid/out-of-repository
# manifest from consuming a full bootstrap build first.
if ! EVIDENCE_MANIFEST_PATH="$("$PYTHON3" - "$TRUST_ROOT" "$(requested_evidence_manifest_path)" <<'PY'
from pathlib import Path
import sys

repo = Path(sys.argv[1]).resolve(strict=True)
requested = Path(sys.argv[2])
try:
    manifest = requested.resolve(strict=True)
except OSError as error:
    raise SystemExit(f"error: could not resolve evidence manifest {requested}: {error}")
try:
    manifest.relative_to(repo)
except ValueError:
    raise SystemExit(
        f"error: evidence manifest {manifest} escapes repository root {repo}"
    )
if not manifest.is_file():
    raise SystemExit(f"error: evidence manifest is not a regular file: {manifest}")
print(manifest)
PY
)"; then
    exit 2
fi

evidence_manifest_path() {
    printf '%s\n' "$EVIDENCE_MANIFEST_PATH"
}

if [[ -z "$REPORT_DIR" ]]; then
    REPORT_DIR="$TRUST_ROOT/reports/build/$RUN_ID"
elif [[ "$REPORT_DIR" != /* ]]; then
    REPORT_DIR="$TRUST_ROOT/$REPORT_DIR"
fi
if [[ -n "$COMPARE_REPORT" && "$COMPARE_REPORT" != /* ]]; then
    COMPARE_REPORT="$TRUST_ROOT/$COMPARE_REPORT"
fi
BOOTSTRAP_TARGET_DIR="${TRUST_STAGE2_VERIFY_BOOTSTRAP_TARGET_DIR:-$TRUST_ROOT/build/full-verify/bootstrap-target}"

LOG_DIR="$REPORT_DIR/logs"
TIMINGS_TSV="$REPORT_DIR/timings.tsv"
REPORT_JSON="$REPORT_DIR/stage2-verify-self-build.report.json"
SUMMARY="$REPORT_DIR/summary.md"
PREFLIGHT_LOG="$LOG_DIR/toolchain-preflight.log"
TARGO_VERSION_LOG="$LOG_DIR/targo-version.log"
TRUSTC_VERSION_LOG="$LOG_DIR/trustc-version.log"
TARGO_TRUST_VERSION_LOG="$LOG_DIR/targo-trust-version.log"
TRUSTD_VERSION_LOG="$LOG_DIR/trustd-version.log"
TRUSTDOC_VERSION_LOG="$LOG_DIR/trustdoc-version.log"
TRUSTFMT_VERSION_LOG="$LOG_DIR/trustfmt-version.log"
TARGO_FMT_VERSION_LOG="$LOG_DIR/targo-fmt-version.log"
TIPPY_VERSION_LOG="$LOG_DIR/tippy-version.log"
TARGO_TIPPY_VERSION_LOG="$LOG_DIR/targo-tippy-version.log"
TIPPY_DRIVER_VERSION_LOG="$LOG_DIR/tippy-driver-version.log"
TRUST_ANALYZER_VERSION_LOG="$LOG_DIR/trust-analyzer-version.log"
HARNESS_STDOUT="$LOG_DIR/self-verify-harness.stdout.log"
HARNESS_STDERR="$LOG_DIR/self-verify-harness.stderr.log"
BOOTSTRAP_STDOUT="$LOG_DIR/stage2-bootstrap-rebuild.stdout.log"
BOOTSTRAP_STDERR="$LOG_DIR/stage2-bootstrap-rebuild.stderr.log"
HARNESS_REPORT_DIR="$REPORT_DIR/self-verify-harness"
HARNESS_REPORT="$HARNESS_REPORT_DIR/self-verify-harness.report.json"
# stage-command.argv is retained as the evidence-command compatibility name.
# It must never contain the separate bootstrap/provenance command.
STAGE_ARGV_FILE="$REPORT_DIR/stage-command.argv"
BOOTSTRAP_ARGV_FILE="$REPORT_DIR/bootstrap-command.argv"
STARTED_UTC="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
RUN_ATTEMPT_ID="${TRUST_STAGE2_VERIFY_ATTEMPT_ID:-$(date -u '+%Y%m%dT%H%M%SZ')-$$}"
LOCK_DIR="$REPORT_DIR/.stage2-verify-self-build.lock"
PREVIOUS_ATTEMPTS_DIR="$REPORT_DIR/previous-attempts"
PREVIOUS_ATTEMPT_DIR=""
RECOVERED_PREVIOUS_ARTIFACTS=0
RECOVERED_STALE_LOCK=0
LOCK_HELD=0

acquire_report_lock() {
    mkdir -p "$REPORT_DIR"
    while true; do
        if mkdir "$LOCK_DIR" 2>/dev/null; then
            LOCK_HELD=1
            printf '%s\n' "$$" >"$LOCK_DIR/pid"
            printf '%s\n' "$RUN_ATTEMPT_ID" >"$LOCK_DIR/attempt-id"
            return 0
        fi

        local existing_pid=""
        if [[ -f "$LOCK_DIR/pid" ]]; then
            existing_pid="$(tr -dc '0-9' <"$LOCK_DIR/pid" | head -c 20 || true)"
        fi
        if [[ -n "$existing_pid" ]] && kill -0 "$existing_pid" 2>/dev/null; then
            echo "error: report directory is locked by active stage2 verify run pid $existing_pid: $REPORT_DIR" >&2
            exit 2
        fi

        rm -rf "$LOCK_DIR"
        RECOVERED_STALE_LOCK=1
    done
}

release_report_lock() {
    if [[ "$LOCK_HELD" == "1" && -d "$LOCK_DIR" ]]; then
        rm -rf "$LOCK_DIR"
    fi
}

recover_previous_artifacts() {
    local artifacts=(
        "$TIMINGS_TSV"
        "$REPORT_JSON"
        "$SUMMARY"
        "$STAGE_ARGV_FILE"
        "$BOOTSTRAP_ARGV_FILE"
        "$LOG_DIR"
        "$HARNESS_REPORT_DIR"
    )
    local existing=()
    local artifact

    for artifact in "${artifacts[@]}"; do
        if [[ -e "$artifact" ]]; then
            existing+=("$artifact")
        fi
    done
    if [[ "${#existing[@]}" -eq 0 ]]; then
        return 0
    fi

    PREVIOUS_ATTEMPT_DIR="$PREVIOUS_ATTEMPTS_DIR/$RUN_ATTEMPT_ID"
    mkdir -p "$PREVIOUS_ATTEMPT_DIR"
    for artifact in "${existing[@]}"; do
        local destination="$PREVIOUS_ATTEMPT_DIR/$(basename "$artifact")"
        if [[ -e "$destination" ]]; then
            destination="$destination.$RANDOM"
        fi
        mv "$artifact" "$destination"
    done
    RECOVERED_PREVIOUS_ARTIFACTS=1
}

acquire_report_lock
trap release_report_lock EXIT
recover_previous_artifacts
mkdir -p "$LOG_DIR"
: >"$TIMINGS_TSV"
: >"$STAGE_ARGV_FILE"
: >"$BOOTSTRAP_ARGV_FILE"

now_epoch() {
    "$PYTHON3" -c 'import time; print(f"{time.time():.6f}")'
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

write_argv_file() {
    local path="$1"
    shift
    : >"$path"
    local arg
    for arg in "$@"; do
        printf '%s\n' "$arg" >>"$path"
    done
}

record_timing() {
    local name="$1"
    local status="$2"
    local started="$3"
    local ended="$4"
    local exit_code="$5"
    local detail="$6"

    printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$name" "$status" "$started" "$ended" "$exit_code" "$detail" >>"$TIMINGS_TSV"
}

run_timed() {
    local name="$1"
    local stdout_path="$2"
    local stderr_path="$3"
    shift 3

    local started
    local ended
    local restore_errexit=0
    local status
    local rc
    if [[ "$-" == *e* ]]; then
        restore_errexit=1
    fi
    started="$(now_epoch)"
    set +e
    "$@" >"$stdout_path" 2>"$stderr_path"
    rc=$?
    ended="$(now_epoch)"
    if [[ "$rc" -eq 0 ]]; then
        status="passed"
    else
        status="failed"
    fi
    record_timing "$name" "$status" "$started" "$ended" "$rc" "$stdout_path $stderr_path"
    if [[ "$restore_errexit" -eq 1 ]]; then
        set -e
    else
        set +e
    fi
    return "$rc"
}

find_stage2_sysroot() {
    local candidates=()
    local candidate
    local raw_candidate

    if [[ -n "${TRUST_STAGE2_SYSROOT:-}" ]]; then
        candidates+=("$TRUST_STAGE2_SYSROOT")
    fi
    candidates+=("$TRUST_ROOT/build/host/stage2")
    shopt -s nullglob
    for candidate in "$TRUST_ROOT"/build/*/stage2; do
        candidates+=("$candidate")
    done
    shopt -u nullglob

    local seen=" "
    for raw_candidate in "${candidates[@]}"; do
        [[ -n "$raw_candidate" ]] || continue
        if ! candidate="$(
            trust_toolchain_resolve_repo_stage2 "$TRUST_ROOT" "$raw_candidate"
        )"; then
            echo "refusing non-repo stage2 sysroot for self-build evidence: $raw_candidate" >&2
            continue
        fi
        if [[ " $seen " == *" $candidate "* ]]; then
            continue
        fi
        seen+="$candidate "
        local forbidden_error
        if forbidden_error="$(trust_toolchain_forbidden_entry_error "$candidate/bin")"; then
            echo "invalid Trust stage2 public surface at $candidate: $forbidden_error" >&2
            continue
        fi
        local missing_tools=""
        local missing_aliases=""
        local invalid_aliases=""
        local tool
        for tool in "${REQUIRED_STAGE2_TOOLS[@]}"; do
            if ! trust_toolchain_exact_executables_valid "$candidate/bin" "$tool"; then
                missing_tools="$missing_tools $tool"
            fi
        done
        for tool in "${REQUIRED_STAGE2_COMPAT_ALIASES[@]}"; do
            if [[ ! -x "$candidate/bin/$tool" ]]; then
                missing_aliases="$missing_aliases $tool"
            fi
        done
        local pair canonical alias alias_error
        for pair in "${REQUIRED_STAGE2_ALIAS_PAIRS[@]}"; do
            canonical="${pair%%:*}"
            alias="${pair#*:}"
            if [[ -x "$candidate/bin/$canonical" && -x "$candidate/bin/$alias" ]] \
                && alias_error="$(
                    trust_toolchain_alias_pair_error "$candidate/bin" "$canonical" "$alias"
                )"; then
                invalid_aliases+=" $canonical:$alias"
                echo "invalid compatibility alias pair $canonical:$alias: $alias_error" >&2
            fi
        done
        if [[ -z "$missing_tools" && -z "$missing_aliases" && -z "$invalid_aliases" ]]; then
            printf '%s\n' "$candidate"
            return 0
        fi
        if [[ -d "$candidate/bin" ]]; then
            echo "stage2 sysroot is missing Trust-preferred tool(s) or Rust-compatible alias(es): $candidate" >&2
            for tool in $missing_tools; do
                echo "  missing executable bin/$tool" >&2
            done
            for tool in $missing_aliases; do
                echo "  missing compatibility alias bin/$tool" >&2
            done
            for pair in $invalid_aliases; do
                canonical="${pair%%:*}"
                alias="${pair#*:}"
                alias_error="$(
                    trust_toolchain_alias_pair_error "$candidate/bin" "$canonical" "$alias"
                )" || true
                echo "  invalid compatibility alias $pair: $alias_error" >&2
            done
        fi
    done

    echo "canonical Trust stage2 sysroot not found under $TRUST_ROOT/build/*/stage2" >&2
    echo "required executables: bin/trustc bin/targo bin/targo-trust bin/trustd bin/trustdoc bin/trustfmt bin/targo-fmt bin/tippy bin/targo-tippy bin/tippy-driver bin/trust-analyzer" >&2
    if command -v rustup >/dev/null 2>&1; then
        local tool
        for tool in "${REQUIRED_STAGE2_TOOLS[@]}"; do
            echo "rustup trust $tool: $(rustup which --toolchain trust "$tool" 2>&1 || true)" >&2
        done
    fi
    return 1
}

write_report() {
    local status="$1"
    local exit_code="$2"
    local reason="$3"

    STATUS="$status" \
    EXIT_CODE="$exit_code" \
    REASON="$reason" \
    RUN_ID="$RUN_ID" \
    REPO_ROOT="$TRUST_ROOT" \
    REPORT_DIR="$REPORT_DIR" \
    LOG_DIR="$LOG_DIR" \
    TIMINGS_TSV="$TIMINGS_TSV" \
    REPORT_JSON="$REPORT_JSON" \
    SUMMARY="$SUMMARY" \
    STAGE_ARGV_FILE="$STAGE_ARGV_FILE" \
    BOOTSTRAP_ARGV_FILE="$BOOTSTRAP_ARGV_FILE" \
    SYSROOT="${STAGE2_SYSROOT:-}" \
    TARGO="${TARGO:-}" \
    TRUSTC="${TRUSTC:-}" \
    TARGO_TRUST="${TARGO_TRUST:-}" \
    TRUSTD="${TRUSTD:-}" \
    TRUSTDOC="${TRUSTDOC:-}" \
    TRUSTFMT="${TRUSTFMT:-}" \
    TARGO_FMT="${TARGO_FMT:-}" \
    TIPPY="${TIPPY:-}" \
    TARGO_TIPPY="${TARGO_TIPPY:-}" \
    TIPPY_DRIVER="${TIPPY_DRIVER:-}" \
    TRUST_ANALYZER="${TRUST_ANALYZER:-}" \
    TARGET="$TARGET" \
    EVIDENCE_MANIFEST_PATH="$(evidence_manifest_path)" \
    INCLUDE_DEPENDENCIES="$INCLUDE_DEPENDENCIES" \
    JOBS="$JOBS" \
    TIMEOUT_SEC="$TIMEOUT_SEC" \
    WORKER_THREADS="$WORKER_THREADS" \
    OFFLINE="$OFFLINE" \
    DRY_RUN="$DRY_RUN" \
    PERF_BUDGET_MODE="$PERF_BUDGET_MODE" \
    MAX_VERIFICATION_WALL_TIME_SEC="$MAX_VERIFICATION_WALL_TIME_SEC" \
    MAX_REPORTED_SOLVER_TIME_MS="$MAX_REPORTED_SOLVER_TIME_MS" \
    MAX_OBLIGATION_ROWS="$MAX_OBLIGATION_ROWS" \
    MAX_CACHE_MISS_OBLIGATIONS="$MAX_CACHE_MISS_OBLIGATIONS" \
    COMPARE_REPORT="$COMPARE_REPORT" \
    STAGE_LABEL="$STAGE_LABEL" \
    STAGE_DESCRIPTION="$STAGE_DESCRIPTION" \
    STARTED_UTC="$STARTED_UTC" \
    RUN_ATTEMPT_ID="$RUN_ATTEMPT_ID" \
    RECOVERED_PREVIOUS_ARTIFACTS="$RECOVERED_PREVIOUS_ARTIFACTS" \
    RECOVERED_STALE_LOCK="$RECOVERED_STALE_LOCK" \
    PREVIOUS_ATTEMPT_DIR="$PREVIOUS_ATTEMPT_DIR" \
    LOCK_DIR="$LOCK_DIR" \
    HARNESS_REPORT="$HARNESS_REPORT" \
    PREFLIGHT_LOG="$PREFLIGHT_LOG" \
    TARGO_VERSION_LOG="$TARGO_VERSION_LOG" \
    TRUSTC_VERSION_LOG="$TRUSTC_VERSION_LOG" \
    TARGO_TRUST_VERSION_LOG="$TARGO_TRUST_VERSION_LOG" \
    TRUSTD_VERSION_LOG="$TRUSTD_VERSION_LOG" \
    TRUSTDOC_VERSION_LOG="$TRUSTDOC_VERSION_LOG" \
    TRUSTFMT_VERSION_LOG="$TRUSTFMT_VERSION_LOG" \
    TARGO_FMT_VERSION_LOG="$TARGO_FMT_VERSION_LOG" \
    TIPPY_VERSION_LOG="$TIPPY_VERSION_LOG" \
    TARGO_TIPPY_VERSION_LOG="$TARGO_TIPPY_VERSION_LOG" \
    TIPPY_DRIVER_VERSION_LOG="$TIPPY_DRIVER_VERSION_LOG" \
    TRUST_ANALYZER_VERSION_LOG="$TRUST_ANALYZER_VERSION_LOG" \
    HARNESS_STDOUT="$HARNESS_STDOUT" \
    HARNESS_STDERR="$HARNESS_STDERR" \
    BOOTSTRAP_STDOUT="$BOOTSTRAP_STDOUT" \
    BOOTSTRAP_STDERR="$BOOTSTRAP_STDERR" \
    "$PYTHON3" - <<'PY'
from __future__ import annotations

import json
import os
import platform
import subprocess
import time
from datetime import datetime, timezone
from pathlib import Path


def env(name: str, default: str = "") -> str:
    return os.environ.get(name, default)


repo_root = Path(env("REPO_ROOT"))
report_dir = Path(env("REPORT_DIR"))
report_json = Path(env("REPORT_JSON"))
summary = Path(env("SUMMARY"))
timings_tsv = Path(env("TIMINGS_TSV"))
argv_file = Path(env("STAGE_ARGV_FILE"))
bootstrap_argv_file = Path(env("BOOTSTRAP_ARGV_FILE"))
harness_report_path = Path(env("HARNESS_REPORT"))


def rel(path: Path) -> str:
    try:
        return str(path.relative_to(repo_root))
    except ValueError:
        return str(path)


def atomic_write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp_path = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    try:
        tmp_path.write_text(text, encoding="utf-8")
        tmp_path.replace(path)
    finally:
        try:
            tmp_path.unlink()
        except FileNotFoundError:
            pass


def optional_number(name: str) -> int | float | None:
    value = env(name).strip()
    if not value:
        return None
    try:
        parsed = float(value) if "." in value else int(value)
    except ValueError:
        return None
    return parsed


def read_argv(path: Path) -> list[str]:
    try:
        return path.read_text(encoding="utf-8").splitlines()
    except OSError:
        return []


def parse_timings() -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    if not timings_tsv.exists():
        return rows
    for line in timings_tsv.read_text(encoding="utf-8").splitlines():
        parts = line.split("\t", 5)
        if len(parts) != 6:
            continue
        name, status, started, ended, exit_code, detail = parts
        try:
            started_f = float(started)
            ended_f = float(ended)
        except ValueError:
            started_f = 0.0
            ended_f = 0.0
        try:
            parsed_exit: int | None = int(exit_code)
        except ValueError:
            parsed_exit = None
        rows.append(
            {
                "name": name,
                "status": status,
                "started_epoch": started_f,
                "ended_epoch": ended_f,
                "duration_sec": round(max(0.0, ended_f - started_f), 3),
                "exit_code": parsed_exit,
                "detail": detail,
            }
        )
    return rows


def git_head() -> str | None:
    try:
        result = subprocess.run(
            ["git", "-C", str(repo_root), "rev-parse", "HEAD"],
            capture_output=True,
            text=True,
            timeout=10,
            check=False,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if result.returncode != 0:
        return None
    return result.stdout.strip()


def read_harness_report() -> dict[str, object] | None:
    try:
        payload = json.loads(harness_report_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    return payload if isinstance(payload, dict) else None


def shell_join(argv: list[str]) -> str:
    return " ".join(subprocess.list2cmdline([arg]) for arg in argv)


def unwrap_env_argv(argv: list[str]) -> list[str]:
    if not argv or Path(argv[0]).name != "env":
        return argv
    index = 1
    while index < len(argv):
        arg = argv[index]
        if arg == "--":
            index += 1
            break
        if arg == "-u" and index + 1 < len(argv):
            index += 2
            continue
        if arg.startswith("-u") and arg != "-u":
            index += 1
            continue
        if arg.startswith("--unset=") or arg in {"-", "-i", "--ignore-environment"}:
            index += 1
            continue
        if "=" in arg and not arg.startswith("="):
            index += 1
            continue
        break
    return argv[index:]


def flag_value(argv: list[str], flag: str) -> str | None:
    for index, arg in enumerate(argv[:-1]):
        if arg == flag:
            return argv[index + 1]
    return None


def is_xpy_bootstrap_runner(argv: list[str]) -> bool:
    return "build" in argv and any(Path(arg).name == "x.py" for arg in argv)


def is_rust_native_bootstrap_runner(argv: list[str]) -> bool:
    if (
        len(argv) < 3
        or Path(argv[0]).name != "targo"
        or argv[1:3] != ["--unverified", "run"]
    ):
        return False
    manifest = flag_value(argv, "--manifest-path")
    if manifest != str(repo_root / "src/bootstrap/Cargo.toml"):
        return False
    try:
        separator = argv.index("--")
    except ValueError:
        return False
    bootstrap_args = argv[separator + 1 :]
    return (
        "--locked" in argv
        and "--offline" in argv
        and flag_value(argv, "--target-dir") is not None
        and flag_value(bootstrap_args, "--src") == str(repo_root)
        and "build" in bootstrap_args
        and flag_value(bootstrap_args, "--stage") == "2"
    )


timings = parse_timings()
argv = read_argv(argv_file)
bootstrap_argv = read_argv(bootstrap_argv_file)
bootstrap_utility_argv = unwrap_env_argv(bootstrap_argv)
bootstrap_runner_detected = is_xpy_bootstrap_runner(bootstrap_utility_argv) or is_rust_native_bootstrap_runner(bootstrap_utility_argv)
bootstrap_timing = next(
    (row for row in timings if row.get("name") == "stage2-bootstrap-rebuild"),
    None,
)
bootstrap_completed = (
    isinstance(bootstrap_timing, dict)
    and bootstrap_timing.get("status") == "passed"
    and bootstrap_timing.get("exit_code") == 0
)
harness_report = read_harness_report()
status = env("STATUS")
exit_code = int(env("EXIT_CODE", "1"))
reason = env("REASON")
errors = [] if status in {"planned", "passed"} else [reason]
if harness_report and isinstance(harness_report.get("proof"), dict):
    proof = harness_report["proof"]
else:
    proof = {
        "status": "not_run" if status == "planned" else "failed",
        "complete": False,
        "timeout_is_incomplete_proof": True,
        "obligation_summary": {
            "status": "unsupported",
            "obligation_rows": 0,
            "unknown_obligations": 0,
            "timeout_obligations": 0,
            "summary": "no per-obligation solver evidence rows were observed",
        },
        "reasons": [] if status == "planned" else [reason],
    }
if isinstance(proof, dict) and not isinstance(proof.get("obligation_summary"), dict):
    solver_suite = harness_report.get("solver_suite") if harness_report else None
    if isinstance(solver_suite, dict) and isinstance(solver_suite.get("outcome_summary"), dict):
        proof["obligation_summary"] = solver_suite["outcome_summary"]
outcome_summary = proof.get("obligation_summary") if isinstance(proof, dict) else None
if not isinstance(outcome_summary, dict):
    outcome_summary = {
        "status": "unsupported",
        "obligation_rows": 0,
        "unknown_obligations": 0,
        "timeout_obligations": 0,
        "summary": "no per-obligation solver evidence rows were observed",
    }
coverage_blocker_summary = None
coverage_blockers = []
all_unknown_routing = None
compiler_self_verification = None
if harness_report and isinstance(harness_report.get("solver_suite"), dict):
    solver_suite = harness_report["solver_suite"]
    coverage_blocker_summary = solver_suite.get("coverage_blocker_summary")
    coverage_blockers_raw = solver_suite.get("coverage_blockers")
    if isinstance(coverage_blockers_raw, list):
        coverage_blockers = coverage_blockers_raw
    all_unknown_routing = solver_suite.get("all_unknown_routing")
    compiler_self_verification = solver_suite.get("compiler_self_verification")
if harness_report and isinstance(harness_report.get("compiler_self_verification"), dict):
    compiler_self_verification = harness_report["compiler_self_verification"]
if isinstance(proof, dict):
    coverage_blocker_summary = proof.get("coverage_blocker_summary", coverage_blocker_summary)
    coverage_blockers_raw = proof.get("coverage_blockers")
    if isinstance(coverage_blockers_raw, list):
        coverage_blockers = coverage_blockers_raw
    all_unknown_routing = proof.get("all_unknown_routing", all_unknown_routing)

perf_thresholds = {
    "max_verification_wall_time_sec": optional_number("MAX_VERIFICATION_WALL_TIME_SEC"),
    "max_reported_solver_time_ms": optional_number("MAX_REPORTED_SOLVER_TIME_MS"),
    "max_obligation_rows": optional_number("MAX_OBLIGATION_ROWS"),
    "max_cache_miss_obligations": optional_number("MAX_CACHE_MISS_OBLIGATIONS"),
}
perf_thresholds = {key: value for key, value in perf_thresholds.items() if value is not None}

payload: dict[str, object] = {
    "schema": "trust.stage2-verify-self-build.v1",
    "issue": "#1149",
    "run_id": env("RUN_ID"),
    "status": status,
    "exit_code": exit_code,
    "created_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
    "started_at": env("STARTED_UTC"),
    "repo_root": str(repo_root),
    "report_dir": rel(report_dir),
    "git": {"head": git_head()},
    "host": {
        "platform": platform.platform(),
        "machine": platform.machine(),
        "python": platform.python_version(),
    },
    "configuration": {
        "target": env("TARGET"),
        "evidence_manifest_path": env("EVIDENCE_MANIFEST_PATH"),
        "include_dependencies": env("INCLUDE_DEPENDENCIES") == "yes",
        "jobs": env("JOBS"),
        "timeout_sec": float(env("TIMEOUT_SEC", "0")),
        "worker_threads": env("WORKER_THREADS"),
        "offline": env("OFFLINE") == "1",
        "dry_run": env("DRY_RUN") == "1",
        "stage_label": env("STAGE_LABEL"),
        "stage_description": env("STAGE_DESCRIPTION"),
        "perf_budget_mode": env("PERF_BUDGET_MODE"),
        "perf_budget_thresholds": perf_thresholds,
        "compare_report": rel(Path(env("COMPARE_REPORT")))
        if env("COMPARE_REPORT")
        else None,
    },
    "evidence_controls": {
        "bounded_timeout_sec": float(env("TIMEOUT_SEC", "0")),
        "compiler_trust_json_required": True,
        "per_obligation_rows_required": True,
        "unknown_outcomes_complete_proof": False,
        "timeout_outcomes_complete_proof": False,
        "coverage_blockers_complete_proof": False,
        "all_unknown_routing_complete_proof": False,
        "fail_closed_on_all_unknown_routing": True,
        "perf_budget_mode": env("PERF_BUDGET_MODE"),
        "perf_budget_thresholds": perf_thresholds,
        "stale_harness_report_reused": False,
        "include_dependencies": env("INCLUDE_DEPENDENCIES") == "yes",
        "bootstrap_stdout_is_proof_input": False,
        "evidence_stream": "self-verify harness direct stage2 Targo Cargo JSON stdout only",
    },
    "stage2_bootstrap_semantics": {
        "stage2_source": (
            "separate repo-local stage2 Targo bootstrap rebuild/provenance phase"
            if bootstrap_argv
            else "explicit custom evidence command; no bootstrap rebuild/provenance phase claimed"
        ),
        "two_phase_claim": bool(bootstrap_argv) and bool(argv),
        "custom_evidence_command": not bool(bootstrap_argv),
        "bootstrap_rebuild_planned": bootstrap_runner_detected,
        "bootstrap_rebuild_completed": bootstrap_completed,
        "rebuild_claimed": bootstrap_completed and bootstrap_runner_detected,
        "full_bootstrap_requested": any(
            arg == "build.full-bootstrap=true" for arg in bootstrap_argv
        ),
        "bootstrap_stdout_parsed_as_evidence": False,
        "evidence_command_is_separate": bool(argv),
        "evidence_manifest_path": env("EVIDENCE_MANIFEST_PATH"),
        "independent_std_rebuild_claimed": False,
        "independent_std_rebuild_claim_requires_log_evidence": True,
    },
    "crash_recovery": {
        "attempt_id": env("RUN_ATTEMPT_ID"),
        "lock_dir": rel(Path(env("LOCK_DIR"))),
        "recovered_stale_lock": env("RECOVERED_STALE_LOCK") == "1",
        "recovered_previous_artifacts": env("RECOVERED_PREVIOUS_ARTIFACTS") == "1",
        "previous_attempt_dir": rel(Path(env("PREVIOUS_ATTEMPT_DIR")))
        if env("PREVIOUS_ATTEMPT_DIR")
        else None,
    },
    "toolchain": {
        "sysroot": env("SYSROOT") or None,
        "targo": env("TARGO") or None,
        "trustc": env("TRUSTC") or None,
        "targo_trust": env("TARGO_TRUST") or None,
        "trustd": env("TRUSTD") or None,
        "trustdoc": env("TRUSTDOC") or None,
        "trustfmt": env("TRUSTFMT") or None,
        "targo_fmt": env("TARGO_FMT") or None,
        "tippy": env("TIPPY") or None,
        "targo_tippy": env("TARGO_TIPPY") or None,
        "tippy_driver": env("TIPPY_DRIVER") or None,
        "trust_analyzer": env("TRUST_ANALYZER") or None,
        "required": [
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
            "trust-analyzer",
        ],
        "repo_stage2_required": True,
    },
    "command": {
        "argv": argv,
        "command_line": shell_join(argv),
        "uses_explicit_targo": any(Path(arg).name == "targo" for arg in argv),
        "uses_explicit_trustc": any(
            arg.startswith("RUSTC=") and Path(arg.removeprefix("RUSTC=")).name == "trustc"
            for arg in argv
        ),
    },
    "phases": {
        "bootstrap_rebuild_provenance": {
            "argv": bootstrap_argv,
            "command_line": shell_join(bootstrap_argv),
            "planned": bool(bootstrap_argv),
            "completed": bootstrap_completed,
            "stdout_is_proof_input": False,
        },
        "cargo_json_evidence": {
            "argv": argv,
            "command_line": shell_join(argv),
            "manifest_path": env("EVIDENCE_MANIFEST_PATH"),
            "sole_proof_stdout": True,
        },
    },
    "timings": {
        "total_measured_sec": round(sum(float(row["duration_sec"]) for row in timings), 3),
        "steps": timings,
    },
    "logs": {
        "preflight": rel(Path(env("PREFLIGHT_LOG"))),
        "targo_version": rel(Path(env("TARGO_VERSION_LOG"))),
        "trustc_version": rel(Path(env("TRUSTC_VERSION_LOG"))),
        "targo_trust_version": rel(Path(env("TARGO_TRUST_VERSION_LOG"))),
        "trustd_version": rel(Path(env("TRUSTD_VERSION_LOG"))),
        "trustdoc_version": rel(Path(env("TRUSTDOC_VERSION_LOG"))),
        "trustfmt_version": rel(Path(env("TRUSTFMT_VERSION_LOG"))),
        "targo_fmt_version": rel(Path(env("TARGO_FMT_VERSION_LOG"))),
        "tippy_version": rel(Path(env("TIPPY_VERSION_LOG"))),
        "targo_tippy_version": rel(Path(env("TARGO_TIPPY_VERSION_LOG"))),
        "tippy_driver_version": rel(Path(env("TIPPY_DRIVER_VERSION_LOG"))),
        "trust_analyzer_version": rel(Path(env("TRUST_ANALYZER_VERSION_LOG"))),
        "harness_stdout": rel(Path(env("HARNESS_STDOUT"))),
        "harness_stderr": rel(Path(env("HARNESS_STDERR"))),
        "bootstrap_stdout": rel(Path(env("BOOTSTRAP_STDOUT"))),
        "bootstrap_stderr": rel(Path(env("BOOTSTRAP_STDERR"))),
    },
    "harness_report": rel(harness_report_path) if harness_report_path.exists() else None,
    "harness_status": harness_report.get("status") if harness_report else None,
    "harness_performance": harness_report.get("performance") if harness_report else None,
    "proof": proof,
    "obligation_outcome_summary": outcome_summary,
    "compiler_self_verification": compiler_self_verification,
    "coverage_blocker_summary": coverage_blocker_summary,
    "coverage_blockers": coverage_blockers,
    "all_unknown_routing": all_unknown_routing,
    "errors": errors,
}

atomic_write_text(report_json, json.dumps(payload, indent=2, sort_keys=True) + "\n")

lines = [
    "# Stage2 Verification-On Self-Build",
    "",
    f"- run_id: `{payload['run_id']}`",
    f"- status: `{status}`",
    f"- exit_code: `{exit_code}`",
    f"- repo_root: `{repo_root}`",
    f"- report_json: `{report_json}`",
    f"- harness_report: `{payload['harness_report']}`",
    f"- sysroot: `{payload['toolchain']['sysroot']}`",
    f"- targo: `{payload['toolchain']['targo']}`",
    f"- trustc: `{payload['toolchain']['trustc']}`",
    f"- targo_trust: `{payload['toolchain']['targo_trust']}`",
    f"- trustd: `{payload['toolchain']['trustd']}`",
    f"- trustdoc: `{payload['toolchain']['trustdoc']}`",
    f"- trustfmt: `{payload['toolchain']['trustfmt']}`",
    f"- targo_fmt: `{payload['toolchain']['targo_fmt']}`",
    f"- tippy: `{payload['toolchain']['tippy']}`",
    f"- targo_tippy: `{payload['toolchain']['targo_tippy']}`",
    f"- tippy_driver: `{payload['toolchain']['tippy_driver']}`",
    f"- trust_analyzer: `{payload['toolchain']['trust_analyzer']}`",
    f"- logical_target: `{payload['configuration']['target']}`",
    f"- evidence_manifest: `{payload['configuration']['evidence_manifest_path']}`",
    f"- include_dependencies: `{payload['configuration']['include_dependencies']}`",
    f"- recovered_previous_artifacts: `{payload['crash_recovery']['recovered_previous_artifacts']}`",
    "",
    "## Bootstrap Rebuild / Provenance Command",
    "",
    "```sh",
    str(payload["phases"]["bootstrap_rebuild_provenance"]["command_line"]),
    "```",
    "",
    "Bootstrap stdout is provenance-only and is never parsed as compiler proof evidence.",
    "",
    "## Cargo JSON Evidence Command",
    "",
    "```sh",
    str(payload["phases"]["cargo_json_evidence"]["command_line"]),
    "```",
    "",
    "## Timings",
    "",
]
for row in timings:
    lines.append(
        f"- {row['name']}: `{row['status']}` `{row['duration_sec']}` sec exit `{row['exit_code']}`"
    )
lines.extend(
    [
        "",
        "## Proof Summary",
        "",
        f"- proof_status: `{proof.get('status') if isinstance(proof, dict) else None}`",
        f"- complete: `{proof.get('complete') if isinstance(proof, dict) else None}`",
        f"- obligation_rows: `{outcome_summary.get('obligation_rows')}`",
        f"- unknown_obligations: `{outcome_summary.get('unknown_obligations')}`",
        f"- timeout_obligations: `{outcome_summary.get('timeout_obligations')}`",
        f"- coverage_blockers: `{len(coverage_blockers)}`",
        f"- all_unknown_routing: `{all_unknown_routing.get('detected') if isinstance(all_unknown_routing, dict) else None}`",
        f"- summary: {outcome_summary.get('summary')}",
        "",
        "## Performance Controls",
        "",
        f"- perf_budget_mode: `{env('PERF_BUDGET_MODE')}`",
        f"- perf_budget_thresholds: `{json.dumps(perf_thresholds, sort_keys=True)}`",
    ]
)
proof_reasons = proof.get("reasons") if isinstance(proof, dict) else None
verification_summary = (
    compiler_self_verification.get("summary")
    if isinstance(compiler_self_verification, dict)
    else None
)
if isinstance(verification_summary, dict):
    lines.extend(
        [
            "",
            "## Compiler Self-Verification Rows",
            "",
            f"- total_rows: `{verification_summary.get('total_rows')}`",
            f"- proof_rows: `{verification_summary.get('proof_rows')}`",
            f"- unsupported_rows: `{verification_summary.get('unsupported_rows')}`",
            f"- failure_rows: `{verification_summary.get('failure_rows')}`",
            f"- summary: {verification_summary.get('summary')}",
        ]
    )
if isinstance(proof_reasons, list) and proof_reasons:
    lines.extend(["", "## Proof Reasons", ""])
    lines.extend(f"- {item}" for item in proof_reasons)
if errors:
    lines.extend(["", "## Errors", ""])
    lines.extend(f"- {error}" for error in errors)
atomic_write_text(summary, "\n".join(lines) + "\n")
PY
}

finish() {
    local status="$1"
    local exit_code="$2"
    local reason="$3"

    write_report "$status" "$exit_code" "$reason"
    echo "stage2 verify self-build report: $REPORT_JSON"
    echo "stage2 verify self-build status: $status"
    return 0
}

preflight_started="$(now_epoch)"
STAGE2_SYSROOT=""
if STAGE2_SYSROOT="$(find_stage2_sysroot 2>"$PREFLIGHT_LOG")"; then
    preflight_ended="$(now_epoch)"
    record_timing "toolchain-preflight" "passed" "$preflight_started" "$preflight_ended" 0 "$PREFLIGHT_LOG"
else
    preflight_ended="$(now_epoch)"
    record_timing "toolchain-preflight" "failed" "$preflight_started" "$preflight_ended" 1 "$PREFLIGHT_LOG"
    if [[ "$DRY_RUN" == "1" ]]; then
        write_argv_file "$STAGE_ARGV_FILE"
        write_argv_file "$BOOTSTRAP_ARGV_FILE"
        finish "planned" 0 "dry run only; canonical stage2 Trust tools were not required"
        exit 0
    fi
    cat "$PREFLIGHT_LOG" >&2
    write_argv_file "$STAGE_ARGV_FILE"
    write_argv_file "$BOOTSTRAP_ARGV_FILE"
    finish "failed" 1 "canonical repo-local Trust stage2 tool preflight failed"
    exit 1
fi

TARGO="$STAGE2_SYSROOT/bin/targo"
TRUSTC="$STAGE2_SYSROOT/bin/trustc"
TARGO_TRUST="$STAGE2_SYSROOT/bin/targo-trust"
TRUSTD="$STAGE2_SYSROOT/bin/trustd"
TRUSTDOC="$STAGE2_SYSROOT/bin/trustdoc"
TRUSTFMT="$STAGE2_SYSROOT/bin/trustfmt"
TARGO_FMT="$STAGE2_SYSROOT/bin/targo-fmt"
TIPPY="$STAGE2_SYSROOT/bin/tippy"
TARGO_TIPPY="$STAGE2_SYSROOT/bin/targo-tippy"
TIPPY_DRIVER="$STAGE2_SYSROOT/bin/tippy-driver"
TRUST_ANALYZER="$STAGE2_SYSROOT/bin/trust-analyzer"

if [[ "$(basename "$TARGO")" != "targo" || "$(basename "$TRUSTC")" != "trustc" || "$(basename "$TARGO_TRUST")" != "targo-trust" || "$(basename "$TRUSTD")" != "trustd" || "$(basename "$TRUSTDOC")" != "trustdoc" || "$(basename "$TRUSTFMT")" != "trustfmt" || "$(basename "$TARGO_FMT")" != "targo-fmt" || "$(basename "$TIPPY")" != "tippy" || "$(basename "$TARGO_TIPPY")" != "targo-tippy" || "$(basename "$TIPPY_DRIVER")" != "tippy-driver" || "$(basename "$TRUST_ANALYZER")" != "trust-analyzer" ]]; then
    echo "canonical stage2 tool names are required: trustc=$TRUSTC targo=$TARGO targo-trust=$TARGO_TRUST trustd=$TRUSTD trustdoc=$TRUSTDOC trustfmt=$TRUSTFMT targo-fmt=$TARGO_FMT tippy=$TIPPY targo-tippy=$TARGO_TIPPY tippy-driver=$TIPPY_DRIVER trust-analyzer=$TRUST_ANALYZER" >"$PREFLIGHT_LOG"
    write_argv_file "$STAGE_ARGV_FILE"
    write_argv_file "$BOOTSTRAP_ARGV_FILE"
    finish "failed" 1 "canonical stage2 tool names are required"
    exit 1
fi

if [[ "${#CUSTOM_STAGE_COMMAND[@]}" -gt 0 ]]; then
    BOOTSTRAP_PLANNED=0
    EVIDENCE_COMMAND=("${CUSTOM_STAGE_COMMAND[@]}")
    STAGE_DESCRIPTION="Custom Trust-native Cargo JSON evidence command for the explicit evidence manifest; no bootstrap rebuild is claimed and its stdout is the sole proof stream."
else
    BOOTSTRAP_PLANNED=1
    BOOTSTRAP_COMMAND=(
        env
        -u
        CARGO_TARGET_DIR
        "$TARGO"
        --unverified
        run
        --locked
        --offline
        --target-dir
        "$BOOTSTRAP_TARGET_DIR"
        --manifest-path
        "$TRUST_ROOT/src/bootstrap/Cargo.toml"
        --
        --src
        "$TRUST_ROOT"
        build
        --set
        llvm.ninja=false
        --set
        build.full-bootstrap=true
        --set
        build.extended=true
        --set
        'build.tools=["targo","targo-trust","trustdoc","trustfmt","tippy","trust-analyzer"]'
        -j
        "$JOBS"
        --stage
        2
        compiler/rustc
        library/std
    )
    EVIDENCE_COMMAND=(
        "$TARGO"
        build
        --message-format=json-render-diagnostics
        --manifest-path
        "$(evidence_manifest_path)"
        -j
        "$JOBS"
    )
fi
write_argv_file "$STAGE_ARGV_FILE" "${EVIDENCE_COMMAND[@]}"
if [[ "$BOOTSTRAP_PLANNED" == "1" ]]; then
    write_argv_file "$BOOTSTRAP_ARGV_FILE" "${BOOTSTRAP_COMMAND[@]}"
else
    write_argv_file "$BOOTSTRAP_ARGV_FILE"
fi

if [[ "$DRY_RUN" == "1" ]]; then
    finish "planned" 0 "dry run only; no compiler or solver evidence was collected"
    exit 0
fi

if ! run_timed "targo-version" "$TARGO_VERSION_LOG" "$LOG_DIR/targo-version.stderr.log" "$TARGO" --version; then
    finish "failed" 1 "stage2 targo --version failed"
    exit 1
fi

if ! run_timed "trustc-version" "$TRUSTC_VERSION_LOG" "$LOG_DIR/trustc-version.stderr.log" "$TRUSTC" -Vv; then
    finish "failed" 1 "stage2 trustc -Vv failed"
    exit 1
fi

if ! run_timed "targo-trust-version" "$TARGO_TRUST_VERSION_LOG" "$LOG_DIR/targo-trust-version.stderr.log" "$TARGO_TRUST" --version; then
    finish "failed" 1 "stage2 targo-trust --version failed"
    exit 1
fi

if ! run_timed "trustd-version" "$TRUSTD_VERSION_LOG" "$LOG_DIR/trustd-version.stderr.log" "$TRUSTD" --version; then
    finish "failed" 1 "stage2 trustd --version failed"
    exit 1
fi

if ! run_timed "trustdoc-version" "$TRUSTDOC_VERSION_LOG" "$LOG_DIR/trustdoc-version.stderr.log" "$TRUSTDOC" --version; then
    finish "failed" 1 "stage2 trustdoc --version failed"
    exit 1
fi

if ! run_timed "trustfmt-version" "$TRUSTFMT_VERSION_LOG" "$LOG_DIR/trustfmt-version.stderr.log" "$TRUSTFMT" --version; then
    finish "failed" 1 "stage2 trustfmt --version failed"
    exit 1
fi

if ! run_timed "targo-fmt-version" "$TARGO_FMT_VERSION_LOG" "$LOG_DIR/targo-fmt-version.stderr.log" "$TARGO_FMT" --version; then
    finish "failed" 1 "stage2 targo-fmt --version failed"
    exit 1
fi

if ! run_timed "tippy-version" "$TIPPY_VERSION_LOG" "$LOG_DIR/tippy-version.stderr.log" "$TIPPY" --version; then
    finish "failed" 1 "stage2 tippy --version failed"
    exit 1
fi

if ! run_timed "targo-tippy-version" "$TARGO_TIPPY_VERSION_LOG" "$LOG_DIR/targo-tippy-version.stderr.log" "$TARGO_TIPPY" --version; then
    finish "failed" 1 "stage2 targo-tippy --version failed"
    exit 1
fi

if ! run_timed "tippy-driver-version" "$TIPPY_DRIVER_VERSION_LOG" "$LOG_DIR/tippy-driver-version.stderr.log" "$TIPPY_DRIVER" --version; then
    finish "failed" 1 "stage2 tippy-driver --version failed"
    exit 1
fi

if ! run_timed "trust-analyzer-version" "$TRUST_ANALYZER_VERSION_LOG" "$LOG_DIR/trust-analyzer-version.stderr.log" "$TRUST_ANALYZER" --version; then
    finish "failed" 1 "stage2 trust-analyzer --version failed"
    exit 1
fi

# Bootstrap is a rebuild/provenance phase only. Its output is deliberately
# captured by this wrapper and is never handed to the self-verification
# transport parser, which accepts only the direct Cargo JSON evidence command.
if [[ "$BOOTSTRAP_PLANNED" == "1" ]]; then
    if ! run_timed \
        "stage2-bootstrap-rebuild" \
        "$BOOTSTRAP_STDOUT" \
        "$BOOTSTRAP_STDERR" \
        "${BOOTSTRAP_COMMAND[@]}"; then
        finish "failed" 1 "separate stage2 bootstrap rebuild/provenance phase failed"
        exit 1
    fi
fi

HARNESS_CMD=(
    "$TARGO_TRUST"
    trust
    verify
    self
    --repo-root
    "$TRUST_ROOT"
    --report-dir
    "$HARNESS_REPORT_DIR"
    --jobs
    "$JOBS"
    --full-verifier
    --timeout
    "$TIMEOUT_SEC"
    --target
    "$TARGET"
    --evidence-manifest
    "$(evidence_manifest_path)"
    --stage-label
    "$STAGE_LABEL"
    --stage-description
    "$STAGE_DESCRIPTION"
)
if [[ "$OFFLINE" == "1" ]]; then
    HARNESS_CMD+=(--offline)
fi
HARNESS_CMD+=(--perf-budget-mode "$PERF_BUDGET_MODE")
if [[ -n "$MAX_VERIFICATION_WALL_TIME_SEC" ]]; then
    HARNESS_CMD+=(--max-verification-wall-time-sec "$MAX_VERIFICATION_WALL_TIME_SEC")
fi
if [[ -n "$MAX_REPORTED_SOLVER_TIME_MS" ]]; then
    HARNESS_CMD+=(--max-reported-solver-time-ms "$MAX_REPORTED_SOLVER_TIME_MS")
fi
if [[ -n "$MAX_OBLIGATION_ROWS" ]]; then
    HARNESS_CMD+=(--max-obligation-rows "$MAX_OBLIGATION_ROWS")
fi
if [[ -n "$MAX_CACHE_MISS_OBLIGATIONS" ]]; then
    HARNESS_CMD+=(--max-cache-miss-obligations "$MAX_CACHE_MISS_OBLIGATIONS")
fi
if [[ -n "$COMPARE_REPORT" ]]; then
    HARNESS_CMD+=(--compare-report "$COMPARE_REPORT")
fi
HARNESS_CMD+=(--stage-command "${EVIDENCE_COMMAND[@]}")

set +e
run_timed \
    "self-verify-harness" \
    "$HARNESS_STDOUT" \
    "$HARNESS_STDERR" \
    env \
    "TRUST_TARGO_BIN=$TARGO" \
    "TRUST_TRUSTC_BIN=$TRUSTC" \
    "TRUST_TARGO_TRUST_BIN=$TARGO_TRUST" \
    "TRUST_TRUSTDOC_BIN=$TRUSTDOC" \
    "RUSTC=$TRUSTC" \
    "TRUSTDOC=$TRUSTDOC" \
    "TRUST_VERIFY_WORKER_THREADS=$WORKER_THREADS" \
    "TRUST_VERIFY_INCLUDE_DEPENDENCIES=$INCLUDE_DEPENDENCIES" \
    "${HARNESS_CMD[@]}"
harness_rc=$?
set -e

if [[ "$harness_rc" -eq 0 ]]; then
    finish "passed" 0 "targo trust verify self completed with complete compiler TRUST_JSON proof"
    exit 0
fi

harness_status="$("$PYTHON3" - "$HARNESS_REPORT" <<'PY'
from __future__ import annotations

import json
import sys
from pathlib import Path

try:
    payload = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
except Exception:
    print("failed")
else:
    print(payload.get("status", "failed"))
PY
)"

case "$harness_status" in
    timed_out)
        finish "timed_out" "$harness_rc" "targo trust verify self timed out before complete proof evidence"
        ;;
    incomplete)
        finish "incomplete" "$harness_rc" "targo trust verify self produced incomplete proof evidence"
        ;;
    failed)
        finish "failed" "$harness_rc" "targo trust verify self failed"
        ;;
    *)
        finish "failed" "$harness_rc" "targo trust verify self exited $harness_rc with status $harness_status"
        ;;
esac
exit "$harness_rc"
