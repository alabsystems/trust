#!/usr/bin/env bash
# Trust build script
# Usage:
#   ./scripts/build.sh           # Full build (Stage 2 compiler + tools)
#   ./scripts/build.sh check     # Fast type-check only (no codegen)
#   ./scripts/build.sh stage1    # Stage 1 only (faster, for development)
#   ./scripts/build.sh test      # Run compiler test suite
#   ./scripts/build.sh full-verify  # Stage2 + bootstrap/dist + release gates
#   ./scripts/build.sh clean     # Clean build artifacts
#   ./scripts/build.sh install   # Install to ~/.Trust
#
# Environment:
#   TRUST_JOBS=N     Override x.py parallel job count (default: system cores)
#   TRUST_VERBOSE=1  Verbose output
#   TRUST_BUILD_DRY_RUN=1  Print full-verify command plan without executing
#   TRUST_BUILD_STUB=1     Emit full-verify commands but do not execute them
#   TRUST_BUILD_STUB_LOG=PATH  Optional tab-separated full-verify command log
#   TRUST_BUILD_ALLOW_NON_RELEASE_STUBS=1  Allow dry-run/stub full-verify for tests only
#   TRUST_FULL_VERIFY_TMPDIR=PATH  Isolated tmp dir for release full-verify
#   TRUST_FULL_VERIFY_CARGO_HOME=PATH  Isolated Cargo cache for release full-verify
#   TRUST_FULL_VERIFY_CARGO_SEED_HOME=PATH  Read-only Cargo cache used to seed isolated release cache
#   TRUST_FULL_VERIFY_MIN_FREE_GIB=N  Minimum free GiB required before release full-verify
#   TRUST_FULL_VERIFY_RELEASE_METADATA_REPORT=PATH  Preserve early Rust release metadata report
#   TRUST_FULL_VERIFY_POST_STAGE_RELEASE_METADATA_REPORT=PATH  Preserve post-stage Rust release metadata report
#   TRUST_FULL_VERIFY_SELF_VERIFY_HARNESS_REPORT_DIR=PATH  Preserve self-verify harness report directory
#   TRUST_FULL_VERIFY_RUN_ID=ID  Verifier run id for build/trust-verification/<run-id>
#   TRUST_FULL_VERIFY_LOG_DIR=PATH  Durable per-step full-verify logs
#   TRUST_FULL_VERIFY_REPORT_ROOT=PATH  Durable report root (default reports/full-verify)
#   TRUST_VERIFY_WORKER_THREADS=N  Full-verifier worker cap for self-verification (default 2)
#   TRUST_FULL_VERIFY_REPORT_DIR=PATH  Durable report directory for this run
# Trust: removed env docs for TRUST_SELF_VERIFY_TARGET / _TIMEOUT_SEC / _RUN_ID; use --target/--timeout/--run-id on `targo trust verify self`.
#   TRUST_FULL_VERIFY_STAGE2_BUILD_HARNESS_REPORT_DIR=PATH  Preserve stage2-build proof transport report
#   TRUST_FULL_VERIFY_STAGE2_BUILD_HARNESS_REPORT=PATH  Stage2-build self-verify harness report path recorded in status metrics
#   TRUST_FULL_VERIFY_STAGE2_BUILD_TIMEOUT_SEC=N  Stage2-build proof harness timeout (0 disables)
#   TRUST_GATE_STATUS_LOG_DIR=PATH  Preserve gate-status per-gate logs (default: report dir)

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

PYTHON3="${PYTHON3:-${PYTHON:-python3}}"
TRUST_TOOLCHAIN_PYTHON3="$PYTHON3"
. "$REPO_ROOT/scripts/lib/trust_toolchain_surface.sh"
# Default parallelism: cap by BOTH core count and RAM. A Trust build fans out
# parallel rustc codegen + multi-GB rustc/LLVM link steps, and stage0/verified
# compiles additionally spawn the in-process Z3/ay verifier (each ay process
# self-limits to RAM/2 with no cross-process coordination), so peak resident
# memory scales with -j. Defaulting to hw.ncpu (e.g. 14 on a 24 GB host)
# exhausted the VM compressor and triggered a userspace-watchdog kernel panic.
# Budget ~5 GB/job and never exceed the core count. Override with TRUST_JOBS.
_trust_ncpu="$(sysctl -n hw.ncpu 2>/dev/null || nproc 2>/dev/null || echo 8)"
_trust_mem_bytes="$(sysctl -n hw.memsize 2>/dev/null || awk '/MemTotal/ {print $2*1024; exit}' /proc/meminfo 2>/dev/null || echo $((16 * 1024 * 1024 * 1024)))"
_trust_mem_jobs=$(( _trust_mem_bytes / (5 * 1024 * 1024 * 1024) ))
[ "${_trust_mem_jobs}" -lt 1 ] && _trust_mem_jobs=1
if [ "${_trust_ncpu}" -lt "${_trust_mem_jobs}" ]; then
    _trust_default_jobs="${_trust_ncpu}"
else
    _trust_default_jobs="${_trust_mem_jobs}"
fi
JOBS="${TRUST_JOBS:-${_trust_default_jobs}}"

# byo-toolchain native-lib link path. Homebrew LLVM (our llvm-config) links
# Homebrew zstd (LLVM uses it for compression), which isn't on the default linker
# path, so tool links (rustdoc-tool, …) otherwise fail with `ld: library 'zstd'
# not found`. (LLVM's other keg dep, Z3, is filtered out in
# compiler/rustc_llvm/build.rs — Trust verifies with AY, not LLVM's Z3 solver.
# libxml2/zlib resolve from the macOS SDK.) Add Homebrew's main lib dir to the
# linker/runtime search paths. No-op for download-ci-llvm / non-Homebrew (no `brew`).
if command -v brew >/dev/null 2>&1; then
    _trust_brew_lib="$(brew --prefix 2>/dev/null)/lib"
    if [ -d "${_trust_brew_lib}" ]; then
        export LIBRARY_PATH="${_trust_brew_lib}${LIBRARY_PATH:+:${LIBRARY_PATH}}"
        export DYLD_FALLBACK_LIBRARY_PATH="${_trust_brew_lib}${DYLD_FALLBACK_LIBRARY_PATH:+:${DYLD_FALLBACK_LIBRARY_PATH}}"
    fi
fi

VERBOSE="${TRUST_VERBOSE:-0}"
DRY_RUN="${TRUST_BUILD_DRY_RUN:-0}"
STUB="${TRUST_BUILD_STUB:-0}"
STUB_LOG="${TRUST_BUILD_STUB_LOG:-}"
ALLOW_NON_RELEASE_STUBS="${TRUST_BUILD_ALLOW_NON_RELEASE_STUBS:-0}"
FULL_VERIFY_BUILD_ROOT="${TRUST_FULL_VERIFY_BUILD_ROOT:-$REPO_ROOT/build/full-verify}"
FULL_VERIFY_PYTHON="$PYTHON3"
FULL_VERIFY_LOG_DIR="${TRUST_FULL_VERIFY_LOG_DIR:-$FULL_VERIFY_BUILD_ROOT/logs}"
FULL_VERIFY_STATUS_LOG="$FULL_VERIFY_LOG_DIR/status.tsv"
FULL_VERIFY_REPORT_ROOT="${TRUST_FULL_VERIFY_REPORT_ROOT:-$REPO_ROOT/reports/full-verify}"
FULL_VERIFY_REPORT_DIR="${TRUST_FULL_VERIFY_REPORT_DIR:-}"
FULL_VERIFY_REPORT_LOG_DIR=""
FULL_VERIFY_REPORT_STATUS_LOG=""
FULL_VERIFY_TRANSCRIPT=""
FULL_VERIFY_METADATA=""
FULL_VERIFY_SUMMARY=""
FULL_VERIFY_FAILURE_TRIAGE=""
FULL_VERIFY_CAPACITY_REPORT=""
FULL_VERIFY_RELEASE_METADATA_REPORT=""
FULL_VERIFY_POST_STAGE_RELEASE_METADATA_REPORT=""
FULL_VERIFY_SELF_VERIFY_HARNESS_REPORT_DIR=""
FULL_VERIFY_TRUST_WP_VERIFY_BUNDLE_PERF_REPORT=""
FULL_VERIFY_TRUST_WP_VERIFY_BUNDLE_PERF_METRICS=""
FULL_VERIFY_ARTIFACTS_INITIALIZED=0
FULL_VERIFY_TRANSCRIPT_STARTED=0
FULL_VERIFY_TARGO=""

VERBOSE_FLAG=""
if [[ "$VERBOSE" == "1" ]]; then
    VERBOSE_FLAG="-v"
fi

log() {
    echo "[Trust build] $(date '+%H:%M:%S') $*"
}

die() {
    echo "[Trust build] ERROR: $*" >&2
    exit 2
}

require_bool() {
    local name="$1"
    local value="$2"

    case "$value" in
        0|1) ;;
        *) die "$name must be 0 or 1 (got: $value)" ;;
    esac
}

require_positive_u16() {
    local name="$1"
    local value="$2"

    if [[ ! "$value" =~ ^[0-9]+$ ]] || (( 10#$value < 1 || 10#$value > 65535 )); then
        die "$name must be an integer between 1 and 65535 (got: $value)"
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
    echo "$out"
}

full_verify_is_stubbed() {
    [[ "$DRY_RUN" == "1" || "$STUB" == "1" ]]
}

full_verify_expected_step_labels() {
    cat <<'EOF'
self-verify-harness
stage2-build
stage2-identity
dist-default-profile
post-stage-release-metadata
dist-source
gate-upstream-rust-porting
gate-owned-dependency-release-readiness
gate-status
EOF
}

prepare_full_verify_step_logs() {
    if full_verify_is_stubbed; then
        return 0
    fi

    mkdir -p "$FULL_VERIFY_LOG_DIR"
    : >"$FULL_VERIFY_STATUS_LOG"
    if [[ "$FULL_VERIFY_ARTIFACTS_INITIALIZED" == "1" ]]; then
        mkdir -p "$FULL_VERIFY_REPORT_LOG_DIR"
        : >"$FULL_VERIFY_REPORT_STATUS_LOG"
    fi
    log "Full-verify step logs: $FULL_VERIFY_LOG_DIR"
}

init_full_verify_artifacts() {
    if full_verify_is_stubbed || [[ "$FULL_VERIFY_ARTIFACTS_INITIALIZED" == "1" ]]; then
        return 0
    fi

    export TRUST_FULL_VERIFY_RUN_ID="${TRUST_FULL_VERIFY_RUN_ID:-$(date -u '+full-verify-%Y%m%dT%H%M%SZ')}"
    if [[ -z "$FULL_VERIFY_REPORT_DIR" ]]; then
        FULL_VERIFY_REPORT_DIR="$FULL_VERIFY_REPORT_ROOT/$TRUST_FULL_VERIFY_RUN_ID"
    fi
    export TRUST_FULL_VERIFY_REPORT_DIR="$FULL_VERIFY_REPORT_DIR"

    FULL_VERIFY_REPORT_LOG_DIR="$FULL_VERIFY_REPORT_DIR/logs"
    FULL_VERIFY_REPORT_STATUS_LOG="$FULL_VERIFY_REPORT_LOG_DIR/status.tsv"
    FULL_VERIFY_TRANSCRIPT="$FULL_VERIFY_REPORT_DIR/transcript.log"
    FULL_VERIFY_METADATA="$FULL_VERIFY_REPORT_DIR/run-metadata.json"
    FULL_VERIFY_SUMMARY="$FULL_VERIFY_REPORT_DIR/run-summary.json"
    FULL_VERIFY_FAILURE_TRIAGE="$FULL_VERIFY_REPORT_DIR/failure-triage.md"
    FULL_VERIFY_CAPACITY_REPORT="$FULL_VERIFY_REPORT_DIR/disk-capacity.txt"
    FULL_VERIFY_RELEASE_METADATA_REPORT="${TRUST_FULL_VERIFY_RELEASE_METADATA_REPORT:-$FULL_VERIFY_REPORT_DIR/release-metadata-report.json}"
    FULL_VERIFY_POST_STAGE_RELEASE_METADATA_REPORT="${TRUST_FULL_VERIFY_POST_STAGE_RELEASE_METADATA_REPORT:-$FULL_VERIFY_REPORT_DIR/post-stage-release-metadata-report.json}"
    FULL_VERIFY_SELF_VERIFY_HARNESS_REPORT_DIR="${TRUST_FULL_VERIFY_SELF_VERIFY_HARNESS_REPORT_DIR:-$FULL_VERIFY_REPORT_DIR/self-verify-harness}"
    export TRUST_FULL_VERIFY_RELEASE_METADATA_REPORT="$FULL_VERIFY_RELEASE_METADATA_REPORT"
    export TRUST_FULL_VERIFY_POST_STAGE_RELEASE_METADATA_REPORT="$FULL_VERIFY_POST_STAGE_RELEASE_METADATA_REPORT"
    export TRUST_FULL_VERIFY_SELF_VERIFY_HARNESS_REPORT_DIR="$FULL_VERIFY_SELF_VERIFY_HARNESS_REPORT_DIR"
    export TRUST_FULL_VERIFY_SELF_VERIFY_HARNESS_REPORT="$FULL_VERIFY_SELF_VERIFY_HARNESS_REPORT_DIR/self-verify-harness.report.json"
    mkdir -p "$FULL_VERIFY_REPORT_LOG_DIR" "$FULL_VERIFY_LOG_DIR"
    : >"$FULL_VERIFY_TRANSCRIPT"
    FULL_VERIFY_ARTIFACTS_INITIALIZED=1
}

start_full_verify_transcript() {
    if [[ "$FULL_VERIFY_ARTIFACTS_INITIALIZED" != "1" || "$FULL_VERIFY_TRANSCRIPT_STARTED" == "1" ]]; then
        return 0
    fi

    exec > >(tee -a "$FULL_VERIFY_TRANSCRIPT") 2>&1
    FULL_VERIFY_TRANSCRIPT_STARTED=1
}

write_full_verify_metadata() {
    if [[ "$FULL_VERIFY_ARTIFACTS_INITIALIZED" != "1" ]]; then
        return 0
    fi

    local path="$1"
    local status="${2:-running}"

    FULL_VERIFY_SUMMARY_STATUS="$status" \
    FULL_VERIFY_METADATA_PATH="$path" \
    FULL_VERIFY_REPO_ROOT="$REPO_ROOT" \
    FULL_VERIFY_STATUS_LOG_PATH="$FULL_VERIFY_STATUS_LOG" \
    FULL_VERIFY_REPORT_STATUS_LOG_PATH="$FULL_VERIFY_REPORT_STATUS_LOG" \
    FULL_VERIFY_TRANSCRIPT_PATH="$FULL_VERIFY_TRANSCRIPT" \
    FULL_VERIFY_RELEASE_METADATA_REPORT_PATH="$FULL_VERIFY_RELEASE_METADATA_REPORT" \
    FULL_VERIFY_POST_STAGE_RELEASE_METADATA_REPORT_PATH="$FULL_VERIFY_POST_STAGE_RELEASE_METADATA_REPORT" \
    FULL_VERIFY_CAPACITY_REPORT_PATH="$FULL_VERIFY_CAPACITY_REPORT" \
    "$FULL_VERIFY_PYTHON" - <<'PY'
import json
import hashlib
import os
import platform
import subprocess
from datetime import UTC, datetime
from pathlib import Path


def git(*args: str) -> str | None:
    try:
        result = subprocess.run(
            ["git", "-C", os.environ["FULL_VERIFY_REPO_ROOT"], *args],
            capture_output=True,
            text=True,
            timeout=5,
            check=False,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if result.returncode != 0:
        return None
    return result.stdout.strip()


def porcelain_status_path(line: str) -> str:
    path = line[3:] if len(line) > 3 else line
    if " -> " in path:
        path = path.rsplit(" -> ", 1)[1]
    return path.strip().strip('"')


def report_relative_prefix() -> str | None:
    report_dir = os.environ.get("TRUST_FULL_VERIFY_REPORT_DIR")
    if not report_dir:
        return None
    try:
        return str(Path(report_dir).resolve().relative_to(Path(os.environ["FULL_VERIFY_REPO_ROOT"]).resolve()))
    except ValueError:
        return None


def parse_status_entries(raw_path: str) -> list[dict]:
    path = Path(raw_path)
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError:
        return []

    entries = []
    for line in lines:
        parts = line.split("\t")
        if len(parts) < 3:
            continue
        entry = {
            "label": parts[0],
            "exit_status": parts[1],
            "log": parts[2],
        }
        if len(parts) >= 8:
            entry.update(
                {
                    "state": parts[3],
                    "started_at": parts[4],
                    "finished_at": parts[5],
                    "duration_sec": None,
                    "metrics": None,
                }
            )
            try:
                entry["duration_sec"] = float(parts[6])
            except ValueError:
                entry["duration_sec"] = None
            try:
                metrics = json.loads(parts[7])
            except json.JSONDecodeError:
                metrics = None
            if isinstance(metrics, dict):
                entry["metrics"] = metrics
        entries.append(entry)
    return entries


def status_performance(entries: list[dict]) -> dict:
    durations = [
        entry["duration_sec"]
        for entry in entries
        if isinstance(entry.get("duration_sec"), (int, float))
    ]
    state_counts: dict[str, int] = {}
    for entry in entries:
        state = entry.get("state")
        if isinstance(state, str):
            state_counts[state] = state_counts.get(state, 0) + 1
    return {
        "schema": "trust.full-verify.status-performance.v1",
        "total_wall_time_sec": round(sum(durations), 3) if durations else None,
        "state_counts": dict(sorted(state_counts.items())),
        "steps": entries,
    }


def tool_provenance(raw_path: str | None) -> dict | None:
    if not raw_path:
        return None

    path = Path(raw_path)
    item = {
        "path": str(path),
        "canonical_path": None,
        "sha256": None,
        "version": None,
    }
    try:
        resolved = path.resolve(strict=True)
        item["canonical_path"] = str(resolved)
        item["sha256"] = f"sha256:{hashlib.sha256(resolved.read_bytes()).hexdigest()}"
        version = subprocess.run(
            [str(resolved), "--version"],
            capture_output=True,
            text=True,
            timeout=10,
            check=False,
        )
        if version.returncode == 0:
            item["version"] = version.stdout.splitlines()[0] if version.stdout.splitlines() else ""
    except (OSError, subprocess.SubprocessError):
        pass
    return item


status_lines = (git("status", "--short") or "").splitlines()
ignored_prefix = report_relative_prefix()
filtered_status = []
ignored_status = []
for line in status_lines:
    path = porcelain_status_path(line)
    if ignored_prefix and (path == ignored_prefix or path.startswith(f"{ignored_prefix}/")):
        ignored_status.append(line)
    else:
        filtered_status.append(line)

status_entries = parse_status_entries(os.environ["FULL_VERIFY_STATUS_LOG_PATH"])
report_status_entries = parse_status_entries(os.environ["FULL_VERIFY_REPORT_STATUS_LOG_PATH"])

payload = {
    "schema": "trust.full-verify.run-artifacts.v1",
    "status": os.environ["FULL_VERIFY_SUMMARY_STATUS"],
    "checked_at": datetime.now(UTC).isoformat(timespec="seconds"),
    "run_id": os.environ.get("TRUST_FULL_VERIFY_RUN_ID"),
    "repo_root": os.environ["FULL_VERIFY_REPO_ROOT"],
    "report_dir": os.environ.get("TRUST_FULL_VERIFY_REPORT_DIR"),
    "head": git("rev-parse", "HEAD"),
    "branch": git("rev-parse", "--abbrev-ref", "HEAD"),
    "dirty": bool(filtered_status),
    "status_short": filtered_status,
    "ignored_status_short": ignored_status,
    "host": {
        "system": platform.system(),
        "release": platform.release(),
        "machine": platform.machine(),
        "node": platform.node(),
    },
    "tool_provenance": {
        "targo": tool_provenance(os.environ.get("TRUST_FULL_VERIFY_TARGO")),
    },
    "artifacts": {
        "transcript": os.environ["FULL_VERIFY_TRANSCRIPT_PATH"],
        "status_log": os.environ["FULL_VERIFY_STATUS_LOG_PATH"],
        "report_status_log": os.environ["FULL_VERIFY_REPORT_STATUS_LOG_PATH"],
        "release_metadata_report": os.environ["FULL_VERIFY_RELEASE_METADATA_REPORT_PATH"],
        "post_stage_release_metadata_report": os.environ["FULL_VERIFY_POST_STAGE_RELEASE_METADATA_REPORT_PATH"],
        "capacity_report": os.environ["FULL_VERIFY_CAPACITY_REPORT_PATH"],
        "self_verify_harness_report": os.environ.get("TRUST_FULL_VERIFY_SELF_VERIFY_HARNESS_REPORT"),
        "stage2_build_harness_report": os.environ.get("TRUST_FULL_VERIFY_STAGE2_BUILD_HARNESS_REPORT"),
    },
    "full_verify_status": {
        "build_log": status_performance(status_entries),
        "report_log": status_performance(report_status_entries),
    },
}

path = Path(os.environ["FULL_VERIFY_METADATA_PATH"])
path.parent.mkdir(parents=True, exist_ok=True)
path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
PY
}

capture_full_verify_capacity_report() {
    if [[ "$FULL_VERIFY_ARTIFACTS_INITIALIZED" != "1" ]]; then
        return 0
    fi

    mkdir -p "${TMPDIR:-$FULL_VERIFY_BUILD_ROOT/tmp}" "${CARGO_HOME:-$FULL_VERIFY_BUILD_ROOT/cargo-home}"
    {
        echo "# full-verify disk/capacity preflight"
        echo "captured_utc=$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
        echo "repo=$REPO_ROOT"
        echo "tmp=${TMPDIR:-}"
        echo "cargo_home=${CARGO_HOME:-}"
        echo
        echo "## df -h ."
        df -h .
        echo
        echo "## df -h tmp/cargo/report/build"
        df -h "${TMPDIR:-.}" "${CARGO_HOME:-.}" "$FULL_VERIFY_REPORT_DIR" "$FULL_VERIFY_BUILD_ROOT" 2>&1 || true
        echo
        echo "## du -sh selected paths"
        du -sh "$FULL_VERIFY_BUILD_ROOT" "$FULL_VERIFY_REPORT_ROOT" 2>&1 || true
        echo
        echo "## cleanup guidance"
        echo "Preserve any report directory needed as reviewer evidence before deleting files."
        echo "Suggested local cleanup targets when disk gates fail:"
        echo "- stale full-verify tmp/cache: rm -rf '$FULL_VERIFY_BUILD_ROOT/tmp' '$FULL_VERIFY_BUILD_ROOT/cargo-home'"
        echo "- stale build outputs: python3 x.py clean, or remove old noncurrent build/full-verify runs"
        echo "- larger volumes: set TRUST_FULL_VERIFY_TMPDIR, TRUST_FULL_VERIFY_CARGO_HOME, TRUST_FULL_VERIFY_BUILD_ROOT, or TRUST_FULL_VERIFY_REPORT_ROOT"
    } >"$FULL_VERIFY_CAPACITY_REPORT"
}

ensure_full_verify_python_env() {
    if full_verify_is_stubbed; then
        return 0
    fi

    FULL_VERIFY_PYTHON="$PYTHON3"
    export FULL_VERIFY_PYTHON

    "$FULL_VERIFY_PYTHON" - <<'PY' || die "full-verify Python helper is unavailable"
import json
import pathlib
PY
    log "Full-verify Python helper: $("$FULL_VERIFY_PYTHON" -c 'import sys; print(sys.executable)')"
}

full_verify_epoch_seconds() {
    "$FULL_VERIFY_PYTHON" - <<'PY'
import time

print(f"{time.time():.6f}")
PY
}

full_verify_step_state() {
    local status="$1"

    if [[ "$status" == "0" ]]; then
        echo "passed"
    elif [[ "$status" == "124" ]]; then
        echo "timed_out"
    else
        echo "failed"
    fi
}

full_verify_step_metrics_json() {
    local label="$1"
    local status="$2"
    local state="$3"
    local duration_sec="$4"

    FULL_VERIFY_STEP_LABEL="$label" \
    FULL_VERIFY_STEP_EXIT_STATUS="$status" \
    FULL_VERIFY_STEP_STATE="$state" \
    FULL_VERIFY_STEP_DURATION_SEC="$duration_sec" \
    "$FULL_VERIFY_PYTHON" - <<'PY'
import json
import os
from pathlib import Path


def load_json(path):
    if not path:
        return None
    try:
        raw = Path(path)
        if not raw.is_file():
            return None
        data = json.loads(raw.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    return data if isinstance(data, dict) else None


def harness_report_path(label):
    if label == "self-verify-harness":
        return os.environ.get("TRUST_FULL_VERIFY_SELF_VERIFY_HARNESS_REPORT")
    if label == "stage2-build":
        return os.environ.get("TRUST_FULL_VERIFY_STAGE2_BUILD_HARNESS_REPORT")
    return None


label = os.environ["FULL_VERIFY_STEP_LABEL"]
status = int(os.environ["FULL_VERIFY_STEP_EXIT_STATUS"])
duration_sec = float(os.environ["FULL_VERIFY_STEP_DURATION_SEC"])
report_path = harness_report_path(label)
report = load_json(report_path)

metrics = {
    "schema": "trust.full-verify.step-metrics.v1",
    "state": os.environ["FULL_VERIFY_STEP_STATE"],
    "exit_status": status,
    "wall_time_sec": duration_sec,
    "verification_scope": {
        "kind": "full-verify-step",
        "stage_label": label,
        "metrics_source": "status-log-wrapper",
    },
    "bundle_counts": {"available": False},
    "cache": {"available": False},
    "per_suite_timing": [],
    "outcome_counts": {},
    "self_verify_harness_report": report_path,
    "self_verify_harness_report_available": report is not None,
}

if report is not None:
    performance = report.get("performance") if isinstance(report.get("performance"), dict) else {}
    metrics["verification_scope"] = report.get("verification_scope") or metrics["verification_scope"]
    bundle_counts = performance.get("bundle_counts")
    if isinstance(bundle_counts, dict):
        metrics["bundle_counts"] = {"available": True, **bundle_counts}
    cache = performance.get("cache")
    if isinstance(cache, dict):
        metrics["cache"] = {"available": True, **cache}
    per_suite_timing = performance.get("per_suite_timing")
    if isinstance(per_suite_timing, list):
        metrics["per_suite_timing"] = per_suite_timing
    outcome_counts = performance.get("outcome_counts")
    if isinstance(outcome_counts, dict):
        metrics["outcome_counts"] = outcome_counts
    reported_solver_time_ms = performance.get("reported_solver_time_ms")
    if isinstance(reported_solver_time_ms, int):
        metrics["reported_solver_time_ms"] = reported_solver_time_ms
    measurement_state = performance.get("measurement_state")
    if isinstance(measurement_state, str):
        metrics["measurement_state"] = measurement_state

print(json.dumps(metrics, sort_keys=True, separators=(",", ":")))
PY
}

run_full_verify_step() {
    local label="$1"
    shift

    local rendered
    rendered="$(format_command "$@")"
    printf 'FULL_VERIFY_STEP\t%s\t%s\n' "$label" "$rendered"

    if [[ -n "$STUB_LOG" ]]; then
        mkdir -p "$(dirname "$STUB_LOG")"
        printf '%s\t%s\n' "$label" "$rendered" >>"$STUB_LOG"
    fi

    if full_verify_is_stubbed; then
        return 0
    fi

    log "Running full-verify step: $label"

    local step_log="$FULL_VERIFY_LOG_DIR/${label}.log"
    local status=0
    local started_utc
    local finished_utc
    local start_epoch
    local end_epoch
    local duration_sec
    local state
    local metrics_json

    mkdir -p "$FULL_VERIFY_LOG_DIR"
    started_utc="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
    start_epoch="$(full_verify_epoch_seconds)"
    {
        echo "step=$label"
        echo "started_utc=$started_utc"
        echo "command=$rendered"
        echo
        "$@"
    } >"$step_log" 2>&1 || status=$?
    finished_utc="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
    end_epoch="$(full_verify_epoch_seconds)"
    duration_sec="$(FULL_VERIFY_STEP_START_EPOCH="$start_epoch" FULL_VERIFY_STEP_END_EPOCH="$end_epoch" "$FULL_VERIFY_PYTHON" - <<'PY'
import os

start = float(os.environ["FULL_VERIFY_STEP_START_EPOCH"])
end = float(os.environ["FULL_VERIFY_STEP_END_EPOCH"])
print(f"{max(0.0, end - start):.3f}")
PY
)"
    state="$(full_verify_step_state "$status")"
    {
        echo
        echo "finished_utc=$finished_utc"
        echo "duration_sec=$duration_sec"
        echo "state=$state"
        echo "exit_status=$status"
    } >>"$step_log"

    local report_step_log=""
    if [[ "$FULL_VERIFY_ARTIFACTS_INITIALIZED" == "1" ]]; then
        report_step_log="$FULL_VERIFY_REPORT_LOG_DIR/${label}.log"
        if ! cp -p "$step_log" "$report_step_log"; then
            log "Full-verify cannot preserve report log for $label: $report_step_log"
            if [[ "$status" -eq 0 ]]; then
                status=2
                state="$(full_verify_step_state "$status")"
            fi
        elif [[ ! -s "$report_step_log" ]]; then
            log "Full-verify copied an empty report log for $label: $report_step_log"
            if [[ "$status" -eq 0 ]]; then
                status=2
                state="$(full_verify_step_state "$status")"
            fi
        fi
    fi

    if ! metrics_json="$(full_verify_step_metrics_json "$label" "$status" "$state" "$duration_sec")"; then
        metrics_json='{"schema":"trust.full-verify.step-metrics.v1","metrics_available":false,"error":"metrics collection failed"}'
    fi

    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$label" "$status" "$step_log" "$state" "$started_utc" "$finished_utc" \
        "$duration_sec" "$metrics_json" >>"$FULL_VERIFY_STATUS_LOG"
    if [[ "$FULL_VERIFY_ARTIFACTS_INITIALIZED" == "1" ]]; then
        printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
            "$label" "$status" "$report_step_log" "$state" "$started_utc" \
            "$finished_utc" "$duration_sec" "$metrics_json" >>"$FULL_VERIFY_REPORT_STATUS_LOG"
    fi
    if [[ "$status" -ne 0 ]]; then
        log "Full-verify step failed: $label (exit $status; see $step_log)"
        return "$status"
    fi
    log "Full-verify step complete: $label (log: $step_log)"
}

find_stage2_trustc() {
    local candidate
    for candidate in \
        "$REPO_ROOT/build/host/stage2/bin/trustc" \
        "$REPO_ROOT"/build/*/stage2/bin/trustc
    do
        if [[ -x "$candidate" ]]; then
            echo "$candidate"
            return 0
        fi
    done

    die "stage2 trustc not found after build; expected build/<host>/stage2/bin/trustc"
}

require_full_verify_repo_stage2_sysroot() {
    local raw="$1"
    local source="$2"

    [[ -d "$raw" ]] || die "$source does not name an existing stage2 sysroot directory: $raw"

    local repo_real
    repo_real="$(cd "$REPO_ROOT" && pwd -P)" || die "failed to canonicalize repo root: $REPO_ROOT"

    local sysroot
    sysroot="$(cd "$raw" && pwd -P)" || die "failed to canonicalize $source: $raw"
    case "$sysroot" in
        "$repo_real"/build/*/stage2) ;;
        *)
            die "$source must resolve to a repo-local build/<host>/stage2 sysroot; got $sysroot"
            ;;
    esac

    local exact_error
    if exact_error="$(
        trust_toolchain_exact_executable_error \
            "$sysroot/bin" \
            targo trustc targo-trust trustd trustdoc trustfmt targo-fmt \
            tippy targo-tippy tippy-driver trust-analyzer
    )"; then
        die "$source rejected its canonical tool surface: $exact_error"
    fi
    echo "$sysroot"
}

find_full_verify_trust_sysroot() {
    if [[ -n "${TRUST_FULL_VERIFY_TRUST_SYSROOT:-}" ]]; then
        local configured="${TRUST_FULL_VERIFY_TRUST_SYSROOT%/}"
        require_full_verify_repo_stage2_sysroot "$configured" TRUST_FULL_VERIFY_TRUST_SYSROOT
        return 0
    fi

    local candidate
    for candidate in \
        "$REPO_ROOT/build/host/stage2" \
        "$REPO_ROOT"/build/*/stage2
    do
        if trust_toolchain_exact_executables_valid \
            "$candidate/bin" \
            targo trustc trustdoc targo-trust trustd trustfmt targo-fmt \
            tippy targo-tippy tippy-driver trust-analyzer; then
            require_full_verify_repo_stage2_sysroot "$candidate" "full-verify stage2 sysroot"
            return 0
        fi
    done

    die "fresh Trust sysroot with canonical Trust tools not found; expected build/<host>/stage2/bin/{targo,trustc,trustdoc,targo-trust,trustd,trustfmt,targo-fmt,tippy,targo-tippy,tippy-driver,trust-analyzer} after dist-default-profile"
}

check_full_verify_trust_sysroot_rust_compat_aliases() {
    local sysroot="$1"
    local pair alias canonical expected_bin alias_real canonical_real
    expected_bin="$(python3 -c 'import os,sys; print(os.path.realpath(sys.argv[1]))' "$sysroot/bin")"
    for pair in rustc:trustc cargo:targo; do
        alias="${pair%:*}"
        canonical="${pair#*:}"
        [[ -x "$sysroot/bin/$alias" ]] \
            || die "full-verify Trust sysroot is missing required compatibility alias bin/$alias"
        alias_real="$(python3 -c 'import os,sys; print(os.path.realpath(sys.argv[1]))' "$sysroot/bin/$alias")"
        canonical_real="$(python3 -c 'import os,sys; print(os.path.realpath(sys.argv[1]))' "$sysroot/bin/$canonical")"
        [[ "$(dirname "$alias_real")" == "$expected_bin" ]] \
            || die "full-verify Trust sysroot alias bin/$alias resolves outside the selected sysroot: $alias_real"
        [[ "$(dirname "$canonical_real")" == "$expected_bin" ]] \
            || die "full-verify Trust canonical bin/$canonical resolves outside the selected sysroot: $canonical_real"
        if [[ "$sysroot/bin/$alias" -ef "$sysroot/bin/$canonical" ]] \
            || cmp -s "$sysroot/bin/$alias" "$sysroot/bin/$canonical"; then
            continue
        fi
        die "full-verify Trust sysroot alias bin/$alias is not the same artifact as bin/$canonical"
    done
}

activate_full_verify_trust_toolchain() {
    local sysroot
    sysroot="$(find_full_verify_trust_sysroot)"
    check_full_verify_trust_sysroot_rust_compat_aliases "$sysroot"
    command -v rustup >/dev/null 2>&1 || die "rustup is required to link the post-dist Trust toolchain selector"
    # Bootstrap owns the two load-bearing Rust-compatible aliases. Requiring
    # them above prevents this activation wrapper from masking a broken dist
    # surface with post-build repairs.
    rustup toolchain link trust "$sysroot" || die "failed to link rustup toolchain trust to $sysroot"
    export PATH="$sysroot/bin:$PATH"
    log "Using standalone Trust toolchain at $sysroot (Trust-preferred binaries)"
}

resolve_full_verify_targo() {
    if [[ -n "$FULL_VERIFY_TARGO" ]]; then
        return 0
    fi

    local sysroot
    sysroot="$(find_full_verify_trust_sysroot)"
    check_full_verify_trust_sysroot_rust_compat_aliases "$sysroot"
    local targo="$sysroot/bin/targo"
    [[ -x "$targo" ]] || die "canonical full-verify targo is not executable: $targo"

    local bin_dir
    bin_dir="$(cd "$(dirname "$targo")" && pwd -P)" || die "failed to canonicalize full-verify targo directory: $targo"
    FULL_VERIFY_TARGO="$bin_dir/$(basename "$targo")"
    [[ -x "$FULL_VERIFY_TARGO" ]] || die "canonicalized full-verify targo is not executable: $FULL_VERIFY_TARGO"

    local version
    version="$("$FULL_VERIFY_TARGO" --version 2>/dev/null | head -n 1)" \
        || die "full-verify targo identity command failed: $FULL_VERIFY_TARGO"
    [[ -n "$version" ]] || die "full-verify targo identity command produced no version: $FULL_VERIFY_TARGO"

    export TRUST_FULL_VERIFY_TARGO="$FULL_VERIFY_TARGO"
    export TRUST_TARGO_BIN="$FULL_VERIFY_TARGO"
    log "Using canonical full-verify targo: $FULL_VERIFY_TARGO ($version)"
}

cmd_stage2_identity() {
    if full_verify_is_stubbed; then
        run_full_verify_step stage2-identity build/host/stage2/bin/trustc -Vv
        return
    fi

    local compiler
    compiler="$(find_stage2_trustc)"
    run_full_verify_step stage2-identity "$compiler" -Vv
}

require_full_verify_fail_closed_env() {
    require_bool TRUST_BUILD_DRY_RUN "$DRY_RUN"
    require_bool TRUST_BUILD_STUB "$STUB"
    require_bool TRUST_BUILD_ALLOW_NON_RELEASE_STUBS "$ALLOW_NON_RELEASE_STUBS"

    local deprecated
    for deprecated in \
        TRUST_FULL_VERIFY_PREFLIGHT_REPORT \
        TRUST_FULL_VERIFY_POST_STAGE_PREFLIGHT_REPORT \
        TRUST_COMPILER_VERIFIER_CHECK_TRANSCRIPT
    do
        if [[ -n "${!deprecated-}" ]]; then
            die "$deprecated has been removed; use Rust release metadata reports and targo trust verify self --full-verifier"
        fi
    done

    if full_verify_is_stubbed && [[ "$ALLOW_NON_RELEASE_STUBS" != "1" ]]; then
        die "full-verify is release evidence; TRUST_BUILD_DRY_RUN/TRUST_BUILD_STUB require TRUST_BUILD_ALLOW_NON_RELEASE_STUBS=1 for non-release tests"
    fi

    if [[ "${TRUST_ALLOW_REVIEW_GATE_SKIPS:-0}" == "1" ]]; then
        die "full-verify is release evidence; unset TRUST_ALLOW_REVIEW_GATE_SKIPS"
    fi
    if [[ "${TRUST_ALLOW_VERIFY_SUITE_ALL_SKIPPED:-0}" == "1" ]]; then
        die "full-verify is release evidence; unset TRUST_ALLOW_VERIFY_SUITE_ALL_SKIPPED"
    fi
}

configure_full_verify_clean_builder_env() {
    local original_cargo_home="${CARGO_HOME:-}"
    local default_seed_home="$REPO_ROOT/build/full-verify/cargo-seed-home"

    export TRUST_FULL_VERIFY_TMPDIR="${TRUST_FULL_VERIFY_TMPDIR:-$REPO_ROOT/build/full-verify/tmp}"
    export TMPDIR="$TRUST_FULL_VERIFY_TMPDIR"

    export TRUST_FULL_VERIFY_CARGO_HOME="${TRUST_FULL_VERIFY_CARGO_HOME:-$REPO_ROOT/build/full-verify/cargo-home}"
    if [[ -z "${TRUST_FULL_VERIFY_CARGO_SEED_HOME:-}" ]]; then
        if full_verify_cargo_seed_candidate_is_release_ready "$original_cargo_home"; then
            export TRUST_FULL_VERIFY_CARGO_SEED_HOME="$original_cargo_home"
        elif full_verify_cargo_seed_candidate_is_release_ready "$default_seed_home"; then
            export TRUST_FULL_VERIFY_CARGO_SEED_HOME="$default_seed_home"
        fi
    fi
    export CARGO_HOME="$TRUST_FULL_VERIFY_CARGO_HOME"
}

full_verify_cargo_seed_candidate_is_release_ready() {
    local seed_home="${1:-}"

    [[ -n "$seed_home" ]] || return 1
    [[ "$seed_home" != "$TRUST_FULL_VERIFY_CARGO_HOME" ]] || return 1
    if [[ -n "${HOME:-}" && "$seed_home" == "$HOME/.cargo" ]]; then
        return 1
    fi
    [[ -d "$seed_home/registry/index" && -d "$seed_home/registry/cache" ]] || return 1
    [[ ! -e "$seed_home/git" ]] || return 1
    [[ -f "$seed_home/.trust-full-verify-cargo-cache-materialization.json" ]] || return 1
}

seed_full_verify_cargo_home() {
    local seed_home="${TRUST_FULL_VERIFY_CARGO_SEED_HOME:-}"

    if [[ -z "$seed_home" ]]; then
        die "full-verify uses offline Cargo; first materialize a dedicated seed with: targo trust verify cargo-cache --repo-root \"$REPO_ROOT\" --cargo-home \"$REPO_ROOT/build/full-verify/cargo-seed-home\" --json-output \"$REPO_ROOT/build/full-verify/cargo-cache-materialization.json\"; then set TRUST_FULL_VERIFY_CARGO_SEED_HOME=$REPO_ROOT/build/full-verify/cargo-seed-home"
    fi
    if [[ ! -d "$seed_home" ]]; then
        die "TRUST_FULL_VERIFY_CARGO_SEED_HOME is not a directory: $seed_home"
    fi
    if [[ "$seed_home" == "$CARGO_HOME" ]]; then
        die "TRUST_FULL_VERIFY_CARGO_SEED_HOME must be distinct from isolated TRUST_FULL_VERIFY_CARGO_HOME"
    fi
    if [[ -n "${HOME:-}" && "$seed_home" == "$HOME/.cargo" ]]; then
        die "TRUST_FULL_VERIFY_CARGO_SEED_HOME must be a dedicated materialized seed, not the shared user Cargo cache: $seed_home"
    fi
    if [[ ! -d "$seed_home/registry/index" || ! -d "$seed_home/registry/cache" ]]; then
        die "TRUST_FULL_VERIFY_CARGO_SEED_HOME must contain registry/index and registry/cache for offline bootstrap: $seed_home"
    fi
    if [[ -e "$seed_home/git" ]]; then
        die "TRUST_FULL_VERIFY_CARGO_SEED_HOME must not contain Cargo git checkout/cache state; rematerialize a registry-only seed with targo trust verify cargo-cache: $seed_home"
    fi
    if [[ ! -f "$seed_home/.trust-full-verify-cargo-cache-materialization.json" ]]; then
        die "TRUST_FULL_VERIFY_CARGO_SEED_HOME must contain .trust-full-verify-cargo-cache-materialization.json from targo trust verify cargo-cache: $seed_home"
    fi
    if [[ -e "$CARGO_HOME/git" ]]; then
        die "isolated TRUST_FULL_VERIFY_CARGO_HOME must not contain Cargo git checkout/cache state; remove $CARGO_HOME/git and reseed from a registry-only TRUST_FULL_VERIFY_CARGO_SEED_HOME"
    fi

    mkdir -p "$CARGO_HOME"
    log "Seeding isolated full-verify Cargo cache from $seed_home."
    mkdir -p "$CARGO_HOME/registry"
    rsync -a "$seed_home/registry/" "$CARGO_HOME/registry/"
    if [[ -f "$seed_home/config.toml" ]]; then
        cp -p "$seed_home/config.toml" "$CARGO_HOME/config.toml"
    elif [[ -f "$seed_home/config" ]]; then
        cp -p "$seed_home/config" "$CARGO_HOME/config"
    fi
}

run_full_verify_release_metadata_check() {
    local phase="${1:-early}"
    local report_path="${2:-}"
    configure_full_verify_clean_builder_env
    resolve_full_verify_targo

    if [[ -z "$report_path" ]]; then
        report_path="${TRUST_FULL_VERIFY_RELEASE_METADATA_REPORT:-$FULL_VERIFY_BUILD_ROOT/release-metadata-report.json}"
    fi

    mkdir -p "$(dirname "$report_path")"
    log "Running full-verify Rust release metadata check phase: $phase."
    "$FULL_VERIFY_TARGO" trust release check \
        --repo-root "$REPO_ROOT" \
        --profile metadata \
        --format=json >"$report_path"
}

run_full_verify_post_stage_release_metadata_check() {
    activate_full_verify_trust_toolchain
    run_full_verify_release_metadata_check \
        post-stage-release-metadata \
        "${TRUST_FULL_VERIFY_POST_STAGE_RELEASE_METADATA_REPORT:-$FULL_VERIFY_BUILD_ROOT/post-stage-release-metadata-report.json}"
}

write_full_verify_failure_triage() {
    local exit_status="$1"

    if [[ "$FULL_VERIFY_ARTIFACTS_INITIALIZED" != "1" ]]; then
        return 0
    fi

    local failed_label=""
    local failed_step_status=""
    local failed_log=""
    if [[ -f "$FULL_VERIFY_STATUS_LOG" ]]; then
        local failed_line
        failed_line="$(awk -F '\t' '$2 != "0" {print; exit}' "$FULL_VERIFY_STATUS_LOG" || true)"
        if [[ -n "$failed_line" ]]; then
            IFS=$'\t' read -r failed_label failed_step_status failed_log _ <<<"$failed_line"
        fi
    fi

    {
        echo "# Full-verify failure triage"
        echo
        echo "- run_id: ${TRUST_FULL_VERIFY_RUN_ID:-unknown}"
        echo "- exit_status: $exit_status"
        echo "- head: $(git rev-parse HEAD 2>/dev/null || echo unknown)"
        echo "- branch: $(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo unknown)"
        echo "- transcript: $FULL_VERIFY_TRANSCRIPT"
        echo "- release_metadata_report: $FULL_VERIFY_RELEASE_METADATA_REPORT"
        echo "- post_stage_release_metadata_report: $FULL_VERIFY_POST_STAGE_RELEASE_METADATA_REPORT"
        echo "- status_log: $FULL_VERIFY_STATUS_LOG"
        echo "- report_status_log: $FULL_VERIFY_REPORT_STATUS_LOG"
        echo "- disk_capacity: $FULL_VERIFY_CAPACITY_REPORT"
        echo
        if [[ -n "$failed_label" ]]; then
            echo "## First Failing Step"
            echo
            echo "- label: $failed_label"
            echo "- status: $failed_step_status"
            echo "- log: $failed_log"
            echo
        fi
        echo "## First Hard Error"
        echo
        FULL_VERIFY_RELEASE_METADATA_REPORT_PATH="$FULL_VERIFY_RELEASE_METADATA_REPORT" \
        FULL_VERIFY_POST_STAGE_RELEASE_METADATA_REPORT_PATH="$FULL_VERIFY_POST_STAGE_RELEASE_METADATA_REPORT" \
        FULL_VERIFY_FAILED_LOG_PATH="$failed_log" \
        FULL_VERIFY_TRANSCRIPT_PATH="$FULL_VERIFY_TRANSCRIPT" \
        "$FULL_VERIFY_PYTHON" - <<'PY' || true
import json
import os
import re
from pathlib import Path


PATTERN = re.compile(r"(ERROR:|error:|failed|No space left|short by)", re.IGNORECASE)


def first_matching_line(path: Path) -> str | None:
    try:
        for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
            stripped = line.strip()
            if stripped and PATTERN.search(stripped):
                return stripped
    except OSError:
        return None
    return None


for env_name, source in (
    ("FULL_VERIFY_RELEASE_METADATA_REPORT_PATH", "release_metadata_report"),
    ("FULL_VERIFY_POST_STAGE_RELEASE_METADATA_REPORT_PATH", "post_stage_release_metadata_report"),
):
    raw = os.environ.get(env_name)
    if not raw:
        continue
    try:
        data = json.loads(Path(raw).read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        data = {}
    errors = data.get("errors") if isinstance(data, dict) else None
    if isinstance(errors, list) and errors:
        print(f"- source: {source}")
        print(f"- message: {errors[0]}")
        raise SystemExit(0)
    reports = data.get("reports") if isinstance(data, dict) else None
    if isinstance(reports, list):
        for report in reports:
            if not isinstance(report, dict):
                continue
            findings = report.get("findings")
            if not isinstance(findings, list) or not findings:
                continue
            first = findings[0]
            if not isinstance(first, dict):
                continue
            code = first.get("code") or "release-finding"
            message = first.get("message") or code
            print(f"- source: {source}")
            print(f"- message: {code}: {message}")
            raise SystemExit(0)

for env_name, label in (
    ("FULL_VERIFY_FAILED_LOG_PATH", "first_failing_step_log"),
    ("FULL_VERIFY_TRANSCRIPT_PATH", "transcript"),
):
    raw = os.environ.get(env_name)
    if not raw:
        continue
    line = first_matching_line(Path(raw))
    if line:
        print(f"- source: {label}")
        print(f"- message: {line}")
        raise SystemExit(0)

print("- none recorded")
PY
        echo
        for release_report in "$FULL_VERIFY_RELEASE_METADATA_REPORT" "$FULL_VERIFY_POST_STAGE_RELEASE_METADATA_REPORT"; do
            if [[ ! -f "$release_report" ]]; then
                continue
            fi
            echo "## Release Metadata Findings"
            echo
            FULL_VERIFY_RELEASE_METADATA_REPORT_PATH="$release_report" "$FULL_VERIFY_PYTHON" - <<'PY' || true
import json
import os
from pathlib import Path

path = Path(os.environ["FULL_VERIFY_RELEASE_METADATA_REPORT_PATH"])
try:
    data = json.loads(path.read_text(encoding="utf-8"))
except (OSError, json.JSONDecodeError) as exc:
    print(f"- unable to parse release metadata report: {exc}")
else:
    print(f"- report: {path}")
    errors = data.get("errors") or []
    if errors:
        for error in errors:
            print(f"- {error}")
    elif isinstance(data.get("reports"), list):
        any_findings = False
        for report in data["reports"]:
            if not isinstance(report, dict):
                continue
            for finding in report.get("findings") or []:
                if not isinstance(finding, dict):
                    continue
                any_findings = True
                code = finding.get("code") or "release-finding"
                message = finding.get("message") or code
                print(f"- {report.get('gate', 'unknown')}: {code}: {message}")
        if not any_findings:
            print("- none recorded")
    else:
        print("- none recorded")
PY
            echo
        done
        if [[ -n "$failed_log" && -f "$failed_log" ]]; then
            echo "## First Failing Step Log Tail"
            echo
            echo '```text'
            tail -n 120 "$failed_log" || true
            echo '```'
            echo
        fi
    } >"$FULL_VERIFY_FAILURE_TRIAGE"
}

full_verify_status_logs_are_complete() {
    if [[ ! -s "$FULL_VERIFY_STATUS_LOG" ]]; then
        log "Full-verify cannot pass: missing or empty status log: $FULL_VERIFY_STATUS_LOG"
        return 1
    fi
    if [[ ! -s "$FULL_VERIFY_REPORT_STATUS_LOG" ]]; then
        log "Full-verify cannot pass: missing or empty report status log: $FULL_VERIFY_REPORT_STATUS_LOG"
        return 1
    fi

    FULL_VERIFY_EXPECTED_LABELS="$(full_verify_expected_step_labels)" \
    FULL_VERIFY_STATUS_LOG_PATH="$FULL_VERIFY_STATUS_LOG" \
    FULL_VERIFY_REPORT_STATUS_LOG_PATH="$FULL_VERIFY_REPORT_STATUS_LOG" \
    "$FULL_VERIFY_PYTHON" - <<'PY'
import json
import os
import sys
from pathlib import Path


def parse_status_log(path: Path):
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError as exc:
        print(f"{path}: failed to read status log: {exc}", file=sys.stderr)
        raise SystemExit(1) from exc
    if not lines:
        print(f"{path}: status log is empty", file=sys.stderr)
        raise SystemExit(1)

    entries = []
    for index, line in enumerate(lines, start=1):
        parts = line.split("\t")
        if len(parts) < 8:
            print(
                f"{path}:{index}: expected at least 8 tab-separated fields "
                "(label, exit status, log, state, start, finish, duration, metrics)",
                file=sys.stderr,
            )
            raise SystemExit(1)
        label, status, log_path, state, started_at, finished_at, duration, metrics = parts[:8]
        if state not in {"passed", "failed", "timed_out", "skipped"}:
            print(f"{path}:{index}: invalid step state {state!r}", file=sys.stderr)
            raise SystemExit(1)
        step_log = Path(log_path)
        if not step_log.is_file():
            print(f"{path}:{index}: referenced step log does not exist: {step_log}", file=sys.stderr)
            raise SystemExit(1)
        try:
            if step_log.stat().st_size <= 0:
                print(f"{path}:{index}: referenced step log is empty: {step_log}", file=sys.stderr)
                raise SystemExit(1)
        except OSError as exc:
            print(f"{path}:{index}: failed to stat referenced step log {step_log}: {exc}", file=sys.stderr)
            raise SystemExit(1) from exc
        try:
            with step_log.open("rb"):
                pass
        except OSError as exc:
            print(f"{path}:{index}: referenced step log is not readable: {step_log}: {exc}", file=sys.stderr)
            raise SystemExit(1) from exc
        try:
            duration_value = float(duration)
        except ValueError as exc:
            print(f"{path}:{index}: invalid duration_sec {duration!r}", file=sys.stderr)
            raise SystemExit(1) from exc
        if duration_value < 0:
            print(f"{path}:{index}: duration_sec must be nonnegative", file=sys.stderr)
            raise SystemExit(1)
        try:
            metrics_value = json.loads(metrics)
        except json.JSONDecodeError as exc:
            print(f"{path}:{index}: invalid metrics JSON: {exc}", file=sys.stderr)
            raise SystemExit(1) from exc
        if not isinstance(metrics_value, dict):
            print(f"{path}:{index}: metrics JSON must be an object", file=sys.stderr)
            raise SystemExit(1)
        entries.append(
            {
                "label": label,
                "status": status,
                "log_path": log_path,
                "state": state,
                "started_at": started_at,
                "finished_at": finished_at,
                "duration_sec": duration_value,
                "metrics": metrics_value,
            }
        )
    return entries


expected = os.environ["FULL_VERIFY_EXPECTED_LABELS"].splitlines()
parsed_logs = []
for raw_path in (
    os.environ["FULL_VERIFY_STATUS_LOG_PATH"],
    os.environ["FULL_VERIFY_REPORT_STATUS_LOG_PATH"],
):
    path = Path(raw_path)
    entries = parse_status_log(path)
    parsed_logs.append((path, entries))
    labels = [str(entry["label"]) for entry in entries]
    if labels != expected:
        missing = [label for label in expected if label not in labels]
        extra = [label for label in labels if label not in expected]
        print(f"{path}: status log does not match the canonical full-verify plan", file=sys.stderr)
        if missing:
            print(f"{path}: missing labels: {', '.join(missing)}", file=sys.stderr)
        if extra:
            print(f"{path}: unexpected labels: {', '.join(extra)}", file=sys.stderr)
        raise SystemExit(1)

    failed = [
        (str(entry["label"]), str(entry["status"]))
        for entry in entries
        if entry["status"] != "0"
    ]
    if failed:
        rendered = ", ".join(f"{label}={status}" for label, status in failed)
        print(f"{path}: nonzero full-verify step status: {rendered}", file=sys.stderr)
        raise SystemExit(1)

build_entries = parsed_logs[0][1]
report_entries = parsed_logs[1][1]
for index, (build_entry, report_entry) in enumerate(zip(build_entries, report_entries), start=1):
    for key in ("label", "status", "state", "started_at", "finished_at", "duration_sec", "metrics"):
        if build_entry[key] != report_entry[key]:
            print(
                f"status log mismatch at row {index} field {key}: "
                f"{build_entry[key]!r} != {report_entry[key]!r}",
                file=sys.stderr,
            )
            raise SystemExit(1)
PY
}

finalize_full_verify_artifacts() {
    local exit_status="$1"
    local final_status="$exit_status"

    if [[ "$FULL_VERIFY_ARTIFACTS_INITIALIZED" != "1" ]]; then
        return "$final_status"
    fi

    if [[ -f "$FULL_VERIFY_STATUS_LOG" && -f "$FULL_VERIFY_REPORT_STATUS_LOG" ]]; then
        if ! cp -p "$FULL_VERIFY_STATUS_LOG" "$FULL_VERIFY_REPORT_LOG_DIR/status.build.tsv"; then
            log "Full-verify cannot preserve build status log: $FULL_VERIFY_REPORT_LOG_DIR/status.build.tsv"
            if [[ "$final_status" -eq 0 ]]; then
                final_status=2
            fi
        fi
    fi

    if [[ "$final_status" -eq 0 ]] && full_verify_status_logs_are_complete; then
        if ! write_full_verify_metadata "$FULL_VERIFY_SUMMARY" "passed"; then
            final_status=2
            log "Full-verify cannot write passed summary: $FULL_VERIFY_SUMMARY"
            write_full_verify_failure_triage "$final_status" || true
            write_full_verify_metadata "$FULL_VERIFY_SUMMARY" "failed" || true
            log "Full-verify failure triage: $FULL_VERIFY_FAILURE_TRIAGE"
        fi
    else
        if [[ "$final_status" -eq 0 ]]; then
            final_status=2
            log "Full-verify status logs are incomplete; refusing passed summary."
        fi
        write_full_verify_failure_triage "$final_status" || true
        write_full_verify_metadata "$FULL_VERIFY_SUMMARY" "failed" || true
        log "Full-verify failure triage: $FULL_VERIFY_FAILURE_TRIAGE"
    fi

    log "Full-verify report artifacts: $FULL_VERIFY_REPORT_DIR"
    return "$final_status"
}

cmd_build() {
    log "Building Trust (Stage 2 compiler + tools) with $JOBS jobs..."
    log "This builds the entire Rust compiler from source."
    log "First build takes 30-60 minutes. Incremental rebuilds are much faster."
    echo ""
    time "$PYTHON3" x.py build $VERBOSE_FLAG -j "$JOBS" 2>&1 | tee build.log
    echo ""
    log "Build complete."
    log "Compiler: $(find build -name trustc -type f -perm +111 2>/dev/null | head -1)"
    log "Build log: build.log"
}

cmd_check() {
    log "Type-checking Trust (no codegen, fast)..."
    time "$PYTHON3" x.py check $VERBOSE_FLAG -j "$JOBS" 2>&1 | tee check.log
    log "Check complete."
}

cmd_stage1() {
    log "Building Stage 1 only (faster, for development)..."
    time "$PYTHON3" x.py build --stage 1 $VERBOSE_FLAG -j "$JOBS" 2>&1 | tee build-stage1.log
    log "Stage 1 build complete."
}

cmd_test() {
    log "Running compiler test suite..."
    time "$PYTHON3" x.py test $VERBOSE_FLAG -j "$JOBS" 2>&1 | tee test.log
    log "Tests complete. See test.log for details."
}

cmd_full_verify() {
    require_full_verify_fail_closed_env
    resolve_full_verify_targo

    if ! full_verify_is_stubbed; then
        configure_full_verify_clean_builder_env
        init_full_verify_artifacts
        start_full_verify_transcript
        trap 'full_verify_exit_status=$?; finalize_full_verify_artifacts "$full_verify_exit_status"; exit "$?"' EXIT
        ensure_full_verify_python_env
        write_full_verify_metadata "$FULL_VERIFY_METADATA" "running"
        capture_full_verify_capacity_report
        run_full_verify_release_metadata_check early
        seed_full_verify_cargo_home
    fi

    log "Running canonical full verification sequence."
    log "This builds stage2, checks bootstrap lineage, builds dist artifacts, and runs release gates."
    prepare_full_verify_step_logs
    local stage2_build_harness_report_dir
    stage2_build_harness_report_dir="${TRUST_FULL_VERIFY_STAGE2_BUILD_HARNESS_REPORT_DIR:-${FULL_VERIFY_REPORT_DIR:-reports/full-verify}/stage2-build-harness}"
    export TRUST_FULL_VERIFY_STAGE2_BUILD_HARNESS_REPORT="${TRUST_FULL_VERIFY_STAGE2_BUILD_HARNESS_REPORT:-$stage2_build_harness_report_dir/self-verify-harness.report.json}"
    local stage2_build_timeout_sec
    stage2_build_timeout_sec="${TRUST_FULL_VERIFY_STAGE2_BUILD_TIMEOUT_SEC:-0}"
    local verify_worker_threads
    verify_worker_threads="${TRUST_VERIFY_WORKER_THREADS:-2}"
    require_positive_u16 TRUST_VERIFY_WORKER_THREADS "$verify_worker_threads"
    run_full_verify_step self-verify-harness \
        env CARGO_NET_OFFLINE=true \
            TRUST_VERIFY_WORKER_THREADS="$verify_worker_threads" \
            "$FULL_VERIFY_TARGO" trust verify self \
            --repo-root "$REPO_ROOT" \
            --report-dir "${TRUST_FULL_VERIFY_SELF_VERIFY_HARNESS_REPORT_DIR:-${FULL_VERIFY_REPORT_DIR:-reports/full-verify}/self-verify-harness}" \
            --jobs "$JOBS" \
            --offline \
            --full-verifier
    run_full_verify_step stage2-build \
        env CARGO_NET_OFFLINE=true \
            TRUST_VERIFY_WORKER_THREADS="$verify_worker_threads" \
            "$FULL_VERIFY_TARGO" trust verify self \
            --repo-root "$REPO_ROOT" \
            --report-dir "$stage2_build_harness_report_dir" \
            --jobs "$JOBS" \
            --offline \
            --full-verifier \
            --timeout "$stage2_build_timeout_sec" \
            --target "stage2 full-bootstrap compiler/rustc library/std" \
            --stage-label stage2-build-verification-on \
            --stage-description "Verification-on canonical full-bootstrap stage2 build for compiler/rustc and library/std." \
            --stage-command env -u CARGO_TARGET_DIR "$FULL_VERIFY_TARGO" --unverified run \
                --locked \
                --offline \
                --target-dir "$FULL_VERIFY_BUILD_ROOT/bootstrap-target" \
                --manifest-path "$REPO_ROOT/src/bootstrap/Cargo.toml" \
                -- \
                --src "$REPO_ROOT" \
                build \
                --set llvm.ninja=false \
                --set build.full-bootstrap=true \
                --set build.extended=true \
                --set 'build.tools=["targo","targo-trust","trustdoc","trustfmt","tippy","trust-analyzer"]' \
                -j "$JOBS" \
                --stage 2 \
                compiler/rustc \
                library/std
    cmd_stage2_identity
    run_full_verify_step dist-default-profile \
        env CARGO_NET_OFFLINE=true ./x dist --set llvm.ninja=false -j "$JOBS" trustc targo trust-std trust-docs targo-trust trustfmt tippy trust-analyzer trust-src trust-llvm-tools
    run_full_verify_step post-stage-release-metadata \
        run_full_verify_post_stage_release_metadata_check
    run_full_verify_step dist-source \
        env CARGO_NET_OFFLINE=true ./x dist --set llvm.ninja=false -j "$JOBS" trust-source trust-source-gpl
    run_full_verify_step gate-upstream-rust-porting \
        "$FULL_VERIFY_TARGO" trust domination upstream-tests --release
    run_full_verify_step gate-owned-dependency-release-readiness \
        "$FULL_VERIFY_TARGO" trust deps validate \
            --production \
            --source git-index \
            --json-output "${FULL_VERIFY_REPORT_DIR:-reports/full-verify}/owned-dependency-release-readiness.report.json"
    run_full_verify_step gate-status \
        env TRUST_GATE_STATUS_INCLUDE_OPTIONAL=1 \
            TRUST_GATE_STATUS_LOG_DIR="${TRUST_GATE_STATUS_LOG_DIR:-${FULL_VERIFY_REPORT_DIR:-reports/full-verify}/gate-status-logs}" \
            bash tests/report_trust_gate_status.sh

    log "Full verification sequence complete."
}

cmd_clean() {
    log "Cleaning build artifacts..."
    "$PYTHON3" x.py clean
    log "Clean complete."
}

cmd_install() {
    log "Installing Trust to ~/.Trust..."
    "$PYTHON3" x.py install $VERBOSE_FLAG -j "$JOBS"
    log "Installed. Add ~/.Trust/bin to your PATH."
    log "  export PATH=\"\$HOME/.Trust/bin:\$PATH\""
}

cmd_status() {
    echo "=== Trust Build Status ==="
    echo "Repo:     $REPO_ROOT"
    echo "Jobs:     $JOBS"
    echo "Host:     $(uname -m) $(uname -s)"
    echo "Memory:   $(sysctl -n hw.memsize 2>/dev/null | awk '{printf "%.0f GB", $1/1024/1024/1024}')"
    echo "bootstrap host rustc: $(rustc --version 2>/dev/null || echo 'not found')"
    echo "cmake:    $(cmake --version 2>/dev/null | head -1 || echo 'not found')"
    echo "ninja:    $(ninja --version 2>/dev/null || echo 'not found')"
    echo ""
    if [[ -f build.log ]]; then
        echo "Last build: $(stat -f '%Sm' build.log 2>/dev/null || stat -c '%y' build.log 2>/dev/null)"
    else
        echo "No build yet."
    fi
    local compiler
    compiler=$(find build -name trustc -type f -perm +111 2>/dev/null | head -1)
    if [[ -n "$compiler" ]]; then
        echo "Compiler:  $compiler"
        "$compiler" --version 2>/dev/null || true
    fi
}

main() {
    case "${1:-build}" in
        build)   cmd_build ;;
        check)   cmd_check ;;
        stage1)  cmd_stage1 ;;
        test)    cmd_test ;;
        full-verify)
            shift
            if [[ "$#" -ne 0 ]]; then
                die "full-verify does not accept extra arguments: $*"
            fi
            cmd_full_verify
            ;;
        clean)   cmd_clean ;;
        install) cmd_install ;;
        status)  cmd_status ;;
        *)
            echo "Usage: $0 {build|check|stage1|test|full-verify|clean|install|status}"
            exit 1
            ;;
    esac
}

if [[ "${BASH_SOURCE[0]}" == "$0" ]]; then
    main "$@"
fi
