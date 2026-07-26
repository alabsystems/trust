#!/bin/bash
# Trust-first release suite wrapper.
#
# Most mode names intentionally use `trust-*`, not `rust-*`. The inherited
# upstream corpus is focused smoke evidence that the `trust` toolchain must
# pass; upstream test porting/release evidence enters through the canonical
# `targo trust domination upstream-tests` Rust CLI.

set -euo pipefail
umask 077

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
MODE="${1:-review}"
STRICT="${TRUST_STRICT:-0}"
RELEASE_GATE="${TRUST_RELEASE_GATE:-0}"
PUBLIC_PROOF_GRADE_CLAIM="${TRUST_PUBLIC_PROOF_GRADE_CLAIM:-0}"
PROOF_GRADE_RELEASE_TRANSCRIPT="${TRUST_PROOF_GRADE_RELEASE_TRANSCRIPT:-}"
PROOF_GRADE_RELEASE_TRANSCRIPT_DIGEST="${TRUST_PROOF_GRADE_RELEASE_TRANSCRIPT_DIGEST:-}"
ALLOW_REVIEW_GATE_SKIPS="${TRUST_ALLOW_REVIEW_GATE_SKIPS:-0}"
RUN_FULL_UPSTREAM_RUST_TESTS="${TRUST_RUN_FULL_UPSTREAM_RUST_TESTS:-0}"
ASSUME_STAGE2="${TRUST_SUPERSET_ASSUME_STAGE2:-0}"
UPSTREAM_RUST_CURRENT_REVISION="${TRUST_UPSTREAM_RUST_CURRENT_REVISION:-}"
UPSTREAM_RUST_SUMMARY="${TRUST_UPSTREAM_RUST_SUMMARY:-$TRUST_ROOT/target/trust-upstream-compat/summary.json}"
UPSTREAM_RUST_BOOTSTRAP_ARGS="${TRUST_UPSTREAM_RUST_BOOTSTRAP_ARGS:---set llvm.ninja=false}"
UPSTREAM_RUST_PORT_BOOTSTRAP_ARGS="${TRUST_UPSTREAM_RUST_PORT_BOOTSTRAP_ARGS:---set llvm.ninja=false}"
UPSTREAM_RUST_PORT_TEST_EXCEPTIONS="${TRUST_UPSTREAM_RUST_PORT_TEST_EXCEPTIONS:-$TRUST_ROOT/tests/upstream-rust/test-exceptions.toml}"
UPSTREAM_RUST_PORT_PATCH_MANIFEST="${TRUST_UPSTREAM_RUST_PORT_PATCH_MANIFEST:-$TRUST_ROOT/tests/upstream-rust/patches.toml}"
UPSTREAM_RUST_PORT_PROOF_MODE="${TRUST_UPSTREAM_RUST_PORT_PROOF_MODE:-auto}"
TRUST_SUITE_LOG_DIR="${TRUST_SUITE_LOG_DIR:-$TRUST_ROOT/target/trust-superset/logs}"
TRUST_STAGE2_REQUIRED_TOOLS=(
    targo
    trustc
    targo-trust
    trustd
    trustdoc
    trustfmt
    targo-fmt
    tippy
    targo-tippy
    tippy-driver
    trust-analyzer
    cargo
    rustc
)
TRUST_STAGE2_ALIAS_PAIRS=(
    targo:cargo
    trustc:rustc
)

log_has_unexpected_skip() {
    local log="$1"
    python3 - "$log" <<'PY'
import re
import sys

text = open(sys.argv[1], encoding="utf-8", errors="replace").read()
text = re.sub(r"\x1b\[[0-9;]*[A-Za-z]", "", text)
raise SystemExit(0 if re.search(r"(^|[\s(])SKIP(?:PING|PED)?\s*:", text, re.MULTILINE) else 1)
PY
}

case "$RELEASE_GATE" in
    0|1)
        ;;
    *)
        echo "FAIL: TRUST_RELEASE_GATE must be 0 or 1 (got: $RELEASE_GATE)" >&2
        exit 2
        ;;
esac

canonical_trust_added_mode() {
    case "$MODE" in
        quick|trust-added-compiletest|trustc-native|native-contracts-pipeline-v2|trust-extra|binary-decompilation-golden|launch|public-distribution|prepublish|installed|installed-default|stage0-lineage)
            return 0
            ;;
        *)
            return 1
            ;;
    esac
}

if [ "$RELEASE_GATE" = "1" ] && canonical_trust_added_mode; then
    echo "SETUP/BLOCKED: '$MODE' is only a local superset-suite diagnostic." >&2
    echo "Canonical command: targo trust domination trust-added --release $MODE" >&2
    echo "The canonical release mode remains blocked until authenticated native execution authority exists." >&2
    exit 2
fi

case "$PUBLIC_PROOF_GRADE_CLAIM" in
    0|1)
        ;;
    *)
        echo "FAIL: TRUST_PUBLIC_PROOF_GRADE_CLAIM must be 0 or 1 (got: $PUBLIC_PROOF_GRADE_CLAIM)" >&2
        exit 2
        ;;
esac

if [ "$PUBLIC_PROOF_GRADE_CLAIM" = "1" ] && { [ "$STRICT" != "1" ] || [ "$RELEASE_GATE" != "1" ]; }; then
    echo "FAIL: TRUST_PUBLIC_PROOF_GRADE_CLAIM=1 requires TRUST_STRICT=1 and TRUST_RELEASE_GATE=1" >&2
    exit 2
fi

case "$RUN_FULL_UPSTREAM_RUST_TESTS" in
    0|1)
        ;;
    *)
        echo "FAIL: TRUST_RUN_FULL_UPSTREAM_RUST_TESTS must be 0 or 1 (got: $RUN_FULL_UPSTREAM_RUST_TESTS)" >&2
        exit 2
        ;;
esac

case "$ASSUME_STAGE2" in
    0|1)
        ;;
    *)
        echo "FAIL: TRUST_SUPERSET_ASSUME_STAGE2 must be 0 or 1 (got: $ASSUME_STAGE2)" >&2
        exit 2
        ;;
esac

case "$UPSTREAM_RUST_PORT_PROOF_MODE" in
    auto|smoke|full)
        ;;
    *)
        echo "FAIL: TRUST_UPSTREAM_RUST_PORT_PROOF_MODE must be auto, smoke, or full (got: $UPSTREAM_RUST_PORT_PROOF_MODE)" >&2
        exit 2
        ;;
esac

section() {
    echo
    echo "--- $1"
}

timestamp_utc() {
    date -u '+%Y-%m-%dT%H:%M:%SZ'
}

timestamp_file_utc() {
    date -u '+%Y%m%dT%H%M%SZ'
}

epoch_seconds() {
    date '+%s'
}

render_command() {
    printf '%s' "$*"
}

emit_gate_telemetry_start() {
    local started="$1"
    local command="$2"
    printf 'TRUST_GATE_TELEMETRY\tstart\tstarted_at=%s\tcommand=%s\n' "$started" "$command"
}

emit_gate_telemetry_end() {
    local ended="$1"
    local status="$2"
    local duration="$3"
    local command="$4"
    printf 'TRUST_GATE_TELEMETRY\tend\tended_at=%s\texit_status=%s\tduration_seconds=%s\tcommand=%s\n' "$ended" "$status" "$duration" "$command"
}

run() {
    local command started started_epoch status ended ended_epoch duration

    command="$(render_command "$@")"
    started="$(timestamp_utc)"
    started_epoch="$(epoch_seconds)"
    echo
    echo ">>> $*"
    emit_gate_telemetry_start "$started" "$command"
    set +e
    "$@"
    status=$?
    set -e
    ended="$(timestamp_utc)"
    ended_epoch="$(epoch_seconds)"
    duration=$((ended_epoch - started_epoch))
    emit_gate_telemetry_end "$ended" "$status" "$duration" "$command"
    return "$status"
}

run_no_unexpected_skip() {
    local log saved_log command started started_epoch status ended ended_epoch duration
    log="$(/usr/bin/mktemp /tmp/trust-suite.XXXXXX)" || {
        echo "FAIL: could not create a private fixed-root suite log" >&2
        return 2
    }
    command="$(render_command "$@")"
    started="$(timestamp_utc)"
    started_epoch="$(epoch_seconds)"
    echo
    echo ">>> $*"
    emit_gate_telemetry_start "$started" "$command"
    printf 'command: %s\n' "$command" >"$log"
    set +e
    "$@" 2>&1 | tee -a "$log"
    status=${PIPESTATUS[0]}
    set -e
    ended="$(timestamp_utc)"
    ended_epoch="$(epoch_seconds)"
    duration=$((ended_epoch - started_epoch))
    emit_gate_telemetry_end "$ended" "$status" "$duration" "$command"
    if [ "$status" -ne 0 ]; then
        mkdir -p "$TRUST_SUITE_LOG_DIR"
        saved_log="$TRUST_SUITE_LOG_DIR/$(timestamp_file_utc)-trust-suite.failed.log"
        cp "$log" "$saved_log"
        echo "Saved failure log: $saved_log" >&2
        /bin/rm -f "$log"
        return "$status"
    fi
    if strict_skip_handling_enabled && log_has_unexpected_skip "$log"; then
        echo "FAIL: strict trust suite saw an unexpected skip in: $*" >&2
        echo "Set TRUST_ALLOW_REVIEW_GATE_SKIPS=1 only for local development, not review/release gates." >&2
        mkdir -p "$TRUST_SUITE_LOG_DIR"
        saved_log="$TRUST_SUITE_LOG_DIR/$(timestamp_file_utc)-trust-suite.unexpected-skip.log"
        cp "$log" "$saved_log"
        echo "Saved unexpected-skip log: $saved_log" >&2
        /bin/rm -f "$log"
        return 2
    fi
    /bin/rm -f "$log"
}

stage2_required_tool_list() {
    local tool
    for tool in "${TRUST_STAGE2_REQUIRED_TOOLS[@]}"; do
        printf 'bin/%s ' "$tool"
    done
}

stage2_bin_dir_has_required_tools() {
    local bin="$1"
    local tool pair canonical alias

    for tool in "${TRUST_STAGE2_REQUIRED_TOOLS[@]}"; do
        [ -x "$bin/$tool" ] || return 1
    done
    for pair in "${TRUST_STAGE2_ALIAS_PAIRS[@]}"; do
        canonical="${pair%%:*}"
        alias="${pair#*:}"
        cmp -s "$bin/$canonical" "$bin/$alias" || return 1
    done
}

stage2_toolchain_requirement_message() {
    echo "complete repo-local stage2 Trust toolchain not found."
    echo "Required executable surface: $(stage2_required_tool_list)"
    echo "Rust-compatible aliases must be byte-identical to their Trust-owned canonical tools."
}

trust_cargo() {
    if trust_stage2_bin="$(trust_stage2_bin_dir)"; then
        "$trust_stage2_bin/targo" --unverified "$@"
    else
        stage2_toolchain_requirement_message >&2
        echo "Build the standalone Trust toolchain." >&2
        return 2
    fi
}

trust_stage2_bin_dir() {
    local candidate
    for candidate in "$TRUST_ROOT"/build/*/stage2/bin "$TRUST_ROOT/build/host/stage2/bin"; do
        if stage2_bin_dir_has_required_tools "$candidate"; then
            printf '%s\n' "$candidate"
            return 0
        fi
    done
    return 1
}

run_with_trust_toolchain_path() {
    local trust_bin

    if ! trust_bin="$(trust_stage2_bin_dir)"; then
        stage2_toolchain_requirement_message >&2
        echo "Build the standalone Trust toolchain." >&2
        return 2
    fi

    PATH="$trust_bin:$PATH" "$@"
}

run_dev_test_lib() {
    run_with_trust_toolchain_path "$TRUST_ROOT/scripts/dev-test.sh" --lib
}

run_stage2_build_for_suite() {
    if [ "$ASSUME_STAGE2" = "1" ]; then
        if ! trust_stage2_bin_dir >/dev/null; then
            echo "FAIL: TRUST_SUPERSET_ASSUME_STAGE2=1 but the stage2 Trust toolchain is incomplete." >&2
            stage2_toolchain_requirement_message >&2
            return 2
        fi
        echo "Using existing stage2 Trust toolchain from: $(trust_stage2_bin_dir)"
        return 0
    fi

    run_no_unexpected_skip ./x.py build --stage 2
    if ! trust_stage2_bin_dir >/dev/null; then
        echo "FAIL: ./x.py build --stage 2 completed but the stage2 Trust toolchain is incomplete." >&2
        stage2_toolchain_requirement_message >&2
        return 2
    fi
}

trust_upstream_compat() {
    trust_cargo run --manifest-path "$TRUST_ROOT/crates/trust-upstream-compat/Cargo.toml" --locked -- "$@"
}

release_gate_lockfile_status() {
    git -C "$TRUST_ROOT" status --porcelain=v1 -- "${RELEASE_GATE_LOCKFILE_STABILITY_PATHS[@]}"
}

run_with_release_gate_lockfile_stability() {
    local label="$1"
    shift
    local before after status

    if ! git -C "$TRUST_ROOT" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
        "$@"
        return $?
    fi

    before="$(/usr/bin/mktemp /tmp/trust-lockfile-before.XXXXXX)" || {
        echo "FAIL: could not create a private fixed-root lockfile snapshot" >&2
        return 2
    }
    after="$(/usr/bin/mktemp /tmp/trust-lockfile-after.XXXXXX)" || {
        /bin/rm -f "$before"
        echo "FAIL: could not create a private fixed-root lockfile snapshot" >&2
        return 2
    }
    release_gate_lockfile_status >"$before"

    set +e
    "$@"
    status=$?
    set -e
    if [ "$status" -ne 0 ]; then
        /bin/rm -f "$before" "$after"
        return "$status"
    fi

    release_gate_lockfile_status >"$after"
    if ! diff -u "$before" "$after" >/dev/null; then
        echo "FAIL: $label dirtied Cargo.toml/Cargo.lock release-gate inputs" >&2
        echo "Changed manifest/lockfile status after gate:" >&2
        cat "$after" >&2
        /bin/rm -f "$before" "$after"
        return 2
    fi

    /bin/rm -f "$before" "$after"
}

strict_skip_handling_enabled() {
    if [ "$ALLOW_REVIEW_GATE_SKIPS" = "1" ]; then
        return 1
    fi
    if [ "$STRICT" = "1" ]; then
        return 0
    fi
    if [ "$MODE" = "upstream-rust-compat" ] || [ "$MODE" = "upstream-rust-porting" ] || [ "$MODE" = "trustc-native" ] || [ "$MODE" = "trust-extra" ] || [ "$MODE" = "binary-decompilation-golden" ] || [ "$MODE" = "native-contracts-pipeline-v2" ] || [ "$MODE" = "review" ] || [ "$MODE" = "release" ]; then
        return 0
    fi
    return 1
}

require_subcheck() {
    local subcheck="$1"
    local path="$TRUST_ROOT/tests/$subcheck"
    if [ ! -f "$path" ]; then
        echo "FAIL: native-contracts-pipeline-v2 required subcheck is missing: tests/$subcheck" >&2
        exit 2
    fi
}

run_upstream_rust_standalone_tests() {
    local source_dir="$TRUST_ROOT/tests/upstream-rust"
    local out_dir="$TRUST_ROOT/target/trust-upstream-compat"
    local trust_bin
    local trustc_bin
    local found=0
    local source name test_bin

    if [ ! -d "$source_dir" ]; then
        echo "No standalone Rust compatibility accounting tests found under tests/upstream-rust/*.rs"
        return 0
    fi

    if ! trust_bin="$(trust_stage2_bin_dir)"; then
        stage2_toolchain_requirement_message >&2
        echo "Required for standalone compatibility tests." >&2
        return 2
    fi
    trustc_bin="$trust_bin/trustc"

    mkdir -p "$out_dir"
    while IFS= read -r source; do
        found=1
        name="$(basename "$source" .rs)"
        test_bin="$out_dir/$name"
        if [ "$(uname -s)" = "MINGW32_NT" ] || [ "$(uname -s)" = "MINGW64_NT" ] || [ "$(uname -s)" = "MSYS_NT" ]; then
            test_bin="$test_bin.exe"
        fi
        run_no_unexpected_skip "$trustc_bin" --edition=2021 --test "$source" -o "$test_bin"
        run_no_unexpected_skip "$test_bin"
    done < <(find "$source_dir" -maxdepth 1 -type f -name '*.rs' -print | sort)

    if [ "$found" = "0" ]; then
        echo "No standalone Rust compatibility accounting tests found under tests/upstream-rust/*.rs"
    fi
}

run_upstream_rust_production_ledger_validation() {
    local ledger_dir="$TRUST_ROOT/tests/upstream-rust"
    local baseline="$ledger_dir/baseline.toml"
    local exceptions="$ledger_dir/exceptions.toml"
    local upstream_fixes="$ledger_dir/upstream-fixes.toml"
    local ledger
    local -a missing=()

    for ledger in "$baseline" "$exceptions" "$upstream_fixes"; do
        if [ ! -f "$ledger" ]; then
            missing+=("tests/upstream-rust/$(basename "$ledger")")
        fi
    done

    section "Production upstream compatibility ledgers"
    if [ "${#missing[@]}" -ne 0 ]; then
        if [ "$RELEASE_GATE" = "1" ]; then
            echo "SETUP/BLOCKED: internal upstream compatibility accounting requires production ledgers before CLI validation can run." >&2
            printf 'Missing: %s\n' "${missing[@]}" >&2
            echo "Current execution cannot claim full upstream suite coverage." >&2
            return 2
        fi

        echo "TODO: add production compatibility ledgers before trust-upstream-compat validate can run."
        printf 'Missing: %s\n' "${missing[@]}"
        echo "Current execution covers compatibility accounting checks only; it does not claim full upstream suite coverage."
        return 0
    fi

    echo "Scope: validates production compatibility ledgers only; this is not full upstream Rust suite execution."
    if [ -n "$UPSTREAM_RUST_CURRENT_REVISION" ]; then
        run_no_unexpected_skip trust_upstream_compat validate \
            --baseline "$baseline" \
            --exceptions "$exceptions" \
            --upstream-fixes "$upstream_fixes" \
            --current-upstream-revision "$UPSTREAM_RUST_CURRENT_REVISION"
    else
        run_no_unexpected_skip trust_upstream_compat validate \
            --baseline "$baseline" \
            --exceptions "$exceptions" \
            --upstream-fixes "$upstream_fixes"
    fi
}

write_upstream_rust_compat_summary() {
    local summary="$1"
    local baseline="$2"
    mkdir -p "$(dirname "$summary")"

    python3 - "$baseline" "$summary" <<'PY'
import json
import os
import sys
from datetime import datetime, timezone
try:
    import tomllib
except ModuleNotFoundError:  # pragma: no cover - Python < 3.11 fallback
    import tomli as tomllib

baseline_path, summary_path = sys.argv[1:3]
with open(baseline_path, "rb") as f:
    baseline = tomllib.load(f)

results = []
for entry in baseline.get("entries", []):
    results.append(
        {
            "baseline_entry_id": entry["id"],
            "outcome": "compatible",
            "observed": "full upstream Rust suite command passed for this baseline run",
        }
    )

summary = {
    "schema_version": baseline["schema_version"],
    "baseline_id": baseline["id"],
    "generated_on": datetime.now(timezone.utc).strftime("%Y-%m-%d"),
    "run_id": os.environ.get("TRUST_UPSTREAM_RUST_RUN_ID"),
    "totals": {
        "total": len(results),
        "compatible": len(results),
        "divergent": 0,
        "excepted": 0,
        "fixed_upstream": 0,
        "unknown": 0,
    },
    "results": results,
}
if summary["run_id"] is None:
    del summary["run_id"]

with open(summary_path, "w", encoding="utf-8") as f:
    json.dump(summary, f, indent=2, sort_keys=True)
    f.write("\n")
PY
}

collect_trust_added_compiletest_paths() {
    local baseline="$1"
    local exceptions="${2:-}"
    if ! git -C "$TRUST_ROOT" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
        return 0
    fi

    python3 - "$baseline" "$TRUST_ROOT" "$exceptions" <<'PY'
import subprocess
import sys
import tomllib
import os
from datetime import date

ALLOWED_EXCEPTION_KINDS = {
    "compiler-ice",
    "diagnostic-drift",
    "environment-or-dependency-gap",
    "missing-blessed-output",
    "pending-compiler-behavior",
    "runtime-regression",
}
ALLOWED_EXCEPTION_STATUSES = {"active", "retired"}
REQUIRED_EXCEPTION_FIELDS = (
    "path",
    "kind",
    "status",
    "owner",
    "issue",
    "reviewed_on",
    "expires_on",
    "reason",
)


def is_yyyy_mm_dd(value):
    if not isinstance(value, str) or len(value) != 10:
        return False
    year, sep1, month, sep2, day = value[:4], value[4], value[5:7], value[7], value[8:]
    if sep1 != "-" or sep2 != "-" or not (year + month + day).isdigit():
        return False
    try:
        date.fromisoformat(value)
    except ValueError:
        return False
    return True


def has_reviewed_issue_anchor(issue):
    if not isinstance(issue, str) or not issue:
        return False
    if issue.startswith("#") or "trust-added-compiletest" in issue:
        return False
    if issue.startswith("https://github.com/rust-lang/rust/issues/"):
        return issue.rsplit("/", 1)[-1].isdigit()
    if issue.startswith("https://github.com/alabsystems/Trust/issues/"):
        return issue.rsplit("/", 1)[-1].isdigit()
    return issue.startswith("reports/trust-added/") and ".md#" in issue

baseline_path = sys.argv[1]
trust_root = sys.argv[2]
exceptions_path = sys.argv[3]
with open(baseline_path, "rb") as f:
    baseline = tomllib.load(f)

revision = baseline["upstream"]["revision"]
if ":" in revision:
    revision = revision.split(":", 1)[1]

upstream = set(subprocess.check_output(
    ["git", "-C", trust_root, "ls-tree", "-r", "--name-only", revision, "--", "tests"],
    text=True,
).splitlines())
current = subprocess.check_output(
    ["git", "-C", trust_root, "ls-files", "tests"],
    text=True,
).splitlines()

compiletest_suites = (
    "tests/assembly-llvm/",
    "tests/build-std/",
    "tests/codegen-llvm/",
    "tests/codegen-units/",
    "tests/coverage/",
    "tests/coverage-run-rustdoc/",
    "tests/crashes/",
    "tests/debuginfo/",
    "tests/incremental/",
    "tests/mir-opt/",
    "tests/pretty/",
    "tests/run-make/",
    "tests/run-make-cargo/",
    "tests/rustdoc-gui/",
    "tests/rustdoc-html/",
    "tests/rustdoc-json/",
    "tests/rustdoc-js/",
    "tests/rustdoc-js-std/",
    "tests/rustdoc-ui/",
    "tests/ui/",
    "tests/ui-fulldeps/",
)
source_suffixes = (".rs", ".js", ".goml")

paths = []
seen = set()
for path in current:
    if path in upstream or not path.startswith(compiletest_suites):
        continue
    if path.startswith("tests/run-make/"):
        parts = path.split("/")
        if len(parts) >= 3:
            primary = "/".join(parts[:3])
        else:
            continue
    elif path.endswith(source_suffixes):
        primary = path
    else:
        continue
    if primary not in seen:
        seen.add(primary)
        paths.append(primary)

exceptions = set()
if exceptions_path:
    with open(exceptions_path, "rb") as f:
        ledger = tomllib.load(f)
    errors = []
    if ledger.get("schema_version") != "0.2.0":
        errors.append("trust-added compiletest exception ledger schema_version must be 0.2.0")
    validation_date = os.environ.get("TRUST_EXCEPTION_VALIDATION_DATE", date.today().isoformat())
    validation_date_is_valid = is_yyyy_mm_dd(validation_date)
    if not validation_date_is_valid:
        errors.append(f"TRUST_EXCEPTION_VALIDATION_DATE must be YYYY-MM-DD: {validation_date}")
    for idx, entry in enumerate(ledger.get("exceptions", []), 1):
        missing = [field for field in REQUIRED_EXCEPTION_FIELDS if not entry.get(field)]
        if missing:
            errors.append(f"exceptions[{idx}] missing required metadata: {', '.join(missing)}")
            continue
        path = entry["path"]
        kind = entry["kind"]
        status = entry["status"]
        owner = entry["owner"]
        issue = entry["issue"]
        reviewed_on = entry["reviewed_on"]
        expires_on = entry["expires_on"]
        if path not in seen:
            errors.append(f"exceptions[{idx}] path is not a tRust-added compiletest primary file: {path}")
            continue
        if kind not in ALLOWED_EXCEPTION_KINDS:
            errors.append(f"exceptions[{idx}] kind is not allowed: {kind}")
        if status not in ALLOWED_EXCEPTION_STATUSES:
            errors.append(f"exceptions[{idx}] status is not allowed: {status}")
        if not owner.startswith("@") or len(owner) <= 1:
            errors.append(f"exceptions[{idx}] owner must be an @team: {owner}")
        if not has_reviewed_issue_anchor(issue):
            errors.append(f"exceptions[{idx}] issue must be a real tracker URL or local review-report anchor: {issue}")
        if not is_yyyy_mm_dd(reviewed_on):
            errors.append(f"exceptions[{idx}] reviewed_on must be YYYY-MM-DD: {reviewed_on}")
        if not is_yyyy_mm_dd(expires_on):
            errors.append(f"exceptions[{idx}] expires_on must be YYYY-MM-DD: {expires_on}")
        if is_yyyy_mm_dd(reviewed_on) and is_yyyy_mm_dd(expires_on):
            if expires_on <= reviewed_on:
                errors.append(f"exceptions[{idx}] expires_on must be after reviewed_on: {expires_on}")
            if status == "active" and validation_date_is_valid and expires_on <= validation_date:
                errors.append(f"exceptions[{idx}] active exception expired on {expires_on}")
        if status == "active":
            exceptions.add(path)
    if errors:
        for error in errors:
            print(f"FAIL: {error}", file=sys.stderr)
        raise SystemExit(2)

for path in sorted(paths):
    if path not in exceptions:
        print(path)
PY
}

collect_active_upstream_test_exception_skip_paths() {
    local test_exceptions="$1"
    python3 - "$test_exceptions" <<'PY'
import sys
import tomllib
from datetime import date

ALLOWED_KINDS = {
    "expected_fail",
    "expected_skip",
    "changed_diagnostic",
    "intentional_divergence",
    "environmental_skip",
}
ALLOWED_STATUSES = {"active", "retired"}
SKIP_KINDS = {
    "expected_fail",
    "expected_skip",
    "intentional_divergence",
    "environmental_skip",
}
REQUIRED_FIELDS = (
    "id",
    "test_id",
    "suite",
    "path",
    "kind",
    "status",
    "owner",
    "reason",
    "issue",
    "reviewed_on",
    "expires_on",
)


def is_yyyy_mm_dd(value):
    if not isinstance(value, str) or len(value) != 10:
        return False
    year, sep1, month, sep2, day = value[:4], value[4], value[5:7], value[7], value[8:]
    if sep1 != "-" or sep2 != "-" or not (year + month + day).isdigit():
        return False
    try:
        date.fromisoformat(value)
    except ValueError:
        return False
    return True


def has_reviewed_issue_anchor(issue):
    if not isinstance(issue, str) or not issue:
        return False
    if issue.startswith("https://github.com/rust-lang/rust/issues/"):
        return issue.rsplit("/", 1)[-1].isdigit()
    if issue.startswith("https://github.com/alabsystems/Trust/issues/"):
        return issue.rsplit("/", 1)[-1].isdigit()
    return issue.startswith("reports/") and ".md#" in issue


with open(sys.argv[1], "rb") as f:
    ledger = tomllib.load(f)

errors = []
if ledger.get("schema_version") != "0.1.0":
    errors.append("upstream per-test exception ledger schema_version must be 0.1.0")

validation_date = date.today().isoformat()
ids = set()
paths_to_skip = []
for idx, entry in enumerate(ledger.get("exceptions", []), 1):
    prefix = f"exceptions[{idx}]"
    missing = [field for field in REQUIRED_FIELDS if not entry.get(field)]
    if missing:
        errors.append(f"{prefix} missing required metadata: {', '.join(missing)}")
        continue

    exc_id = entry["id"]
    kind = entry["kind"]
    status = entry["status"]
    owner = entry["owner"]
    issue = entry["issue"]
    reviewed_on = entry["reviewed_on"]
    expires_on = entry["expires_on"]
    path = entry["path"]

    if exc_id in ids:
        errors.append(f"{prefix}.id is duplicated: {exc_id}")
    ids.add(exc_id)
    if kind not in ALLOWED_KINDS:
        errors.append(f"{prefix}.kind is not allowed: {kind}")
    if status not in ALLOWED_STATUSES:
        errors.append(f"{prefix}.status is not allowed: {status}")
    if not owner.startswith("@") or len(owner) <= 1:
        errors.append(f"{prefix}.owner must be an @team: {owner}")
    if not has_reviewed_issue_anchor(issue):
        errors.append(f"{prefix}.issue must be a reviewed tracker URL or local report anchor: {issue}")
    if not is_yyyy_mm_dd(reviewed_on):
        errors.append(f"{prefix}.reviewed_on must be YYYY-MM-DD: {reviewed_on}")
    if not is_yyyy_mm_dd(expires_on):
        errors.append(f"{prefix}.expires_on must be YYYY-MM-DD: {expires_on}")
    if is_yyyy_mm_dd(reviewed_on) and is_yyyy_mm_dd(expires_on):
        if expires_on <= reviewed_on:
            errors.append(f"{prefix}.expires_on must be after reviewed_on: {expires_on}")
        if status == "active" and expires_on <= validation_date:
            errors.append(f"{prefix} active exception expired on {expires_on}")
    if not isinstance(path, str) or not path.startswith("tests/"):
        errors.append(f"{prefix}.path must name a tests/ path: {path}")
    elif status == "active" and kind in SKIP_KINDS:
        paths_to_skip.append(path)

if errors:
    for error in errors:
        print(f"FAIL: {error}", file=sys.stderr)
    raise SystemExit(2)

for path in sorted(set(paths_to_skip)):
    print(path)
PY
}

print_trust_added_compiletest_exceptions() {
    local exceptions="$1"
    python3 - "$exceptions" <<'PY'
import sys
import tomllib

path = sys.argv[1]
with open(path, "rb") as f:
    ledger = tomllib.load(f)

for entry in ledger.get("exceptions", []):
    if entry.get("status") != "active":
        continue
    print(
        f"  - {entry['path']} [{entry['kind']}, {entry['owner']}, expires {entry['expires_on']}]: "
        f"{entry['reason']} ({entry['issue']})"
    )
PY
}

run_trust_added_compiletest_suite() {
    local ledger_dir="$TRUST_ROOT/tests/upstream-rust"
    local baseline="$ledger_dir/baseline.toml"
    local exceptions="$TRUST_ROOT/tests/trust-added/compiletest-exceptions.toml"
    local -a trust_added_paths
    local -a runnable_paths

    trust_added_paths=()
    while IFS= read -r path; do
        [ -n "$path" ] && trust_added_paths+=("$path")
    done < <(collect_trust_added_compiletest_paths "$baseline")

    runnable_paths=()
    while IFS= read -r path; do
        [ -n "$path" ] && runnable_paths+=("$path")
    done < <(collect_trust_added_compiletest_paths "$baseline" "$exceptions")

    section "tRust-added compiletest corpus"
    echo "Scope: runs compiletest primary files that are present in tRust but absent from the audited upstream Rust baseline."
    echo "Verifier pass: Trust-added compiletest evidence must explicitly enable Trust verification for this corpus."
    echo "tRust-added compiletest paths: ${#trust_added_paths[@]}"
    echo "Runnable tRust-added compiletest paths after documented exceptions: ${#runnable_paths[@]}"
    if [ "${#trust_added_paths[@]}" -ne "${#runnable_paths[@]}" ]; then
        echo "Active exceptions are known failing tRust-added tests, not skipped passes; a green run covers only the runnable paths above."
        echo "Documented tRust-added compiletest exceptions:"
        print_trust_added_compiletest_exceptions "$exceptions"
    fi
    if [ "${#trust_added_paths[@]}" -eq 0 ]; then
        echo "No tRust-added compiletest paths were found."
        return
    fi
    if [ "${#runnable_paths[@]}" -eq 0 ]; then
        echo "No runnable tRust-added compiletest paths remain after documented exceptions."
        return
    fi
    # shellcheck disable=SC2086 # TRUST_UPSTREAM_RUST_BOOTSTRAP_ARGS is an optional word-list override.
    run_no_unexpected_skip ./x.py test --stage 2 --trust-vanilla --no-fail-fast --force-rerun "${runnable_paths[@]}" $UPSTREAM_RUST_BOOTSTRAP_ARGS
}

run_full_upstream_rust_suite() {
    local ledger_dir="$TRUST_ROOT/tests/upstream-rust"
    local baseline="$ledger_dir/baseline.toml"
    local exceptions="$ledger_dir/exceptions.toml"
    local test_exceptions="$ledger_dir/test-exceptions.toml"
    local upstream_fixes="$ledger_dir/upstream-fixes.toml"
    local -a trust_added_paths
    local -a upstream_exception_skip_paths
    local -a upstream_vanilla_skip_args

    trust_added_paths=()
    while IFS= read -r path; do
        [ -n "$path" ] && trust_added_paths+=("$path")
    done < <(collect_trust_added_compiletest_paths "$baseline")

    upstream_exception_skip_paths=()
    while IFS= read -r path; do
        [ -n "$path" ] && upstream_exception_skip_paths+=("$path")
    done < <(collect_active_upstream_test_exception_skip_paths "$test_exceptions")

    upstream_vanilla_skip_args=()
    if [ "${#trust_added_paths[@]}" -ne 0 ]; then
        for path in "${trust_added_paths[@]}"; do
            upstream_vanilla_skip_args+=(--skip "$path")
        done
    fi
    if [ "${#upstream_exception_skip_paths[@]}" -ne 0 ]; then
        for path in "${upstream_exception_skip_paths[@]}"; do
            upstream_vanilla_skip_args+=(--skip "$path")
        done
    fi

    section "Full upstream Rust compatibility suite"
    echo "Scope: runs the full stage2 Rust-owned test suite through x.py, excluding non-baseline local compiletest files and active per-test upstream exceptions, then validates a per-baseline compatibility summary."
    echo "Skipped non-baseline local compiletest paths in vanilla upstream mode: ${#trust_added_paths[@]}"
    echo "Skipped active upstream per-test exceptions: ${#upstream_exception_skip_paths[@]}"
    if [ -n "$UPSTREAM_RUST_BOOTSTRAP_ARGS" ]; then
        echo "Extra bootstrap args: $UPSTREAM_RUST_BOOTSTRAP_ARGS"
    fi
    if [ "${#upstream_vanilla_skip_args[@]}" -ne 0 ]; then
        # shellcheck disable=SC2086 # TRUST_UPSTREAM_RUST_BOOTSTRAP_ARGS is an optional word-list override.
        run_no_unexpected_skip ./x.py test --stage 2 --trust-vanilla --no-fail-fast "${upstream_vanilla_skip_args[@]}" $UPSTREAM_RUST_BOOTSTRAP_ARGS
    else
        # shellcheck disable=SC2086 # TRUST_UPSTREAM_RUST_BOOTSTRAP_ARGS is an optional word-list override.
        run_no_unexpected_skip ./x.py test --stage 2 --trust-vanilla --no-fail-fast $UPSTREAM_RUST_BOOTSTRAP_ARGS
    fi

    write_upstream_rust_compat_summary "$UPSTREAM_RUST_SUMMARY" "$baseline"
    echo "Wrote upstream compatibility summary: $UPSTREAM_RUST_SUMMARY"

    if [ -n "$UPSTREAM_RUST_CURRENT_REVISION" ]; then
        run_no_unexpected_skip trust_upstream_compat validate \
            --baseline "$baseline" \
            --exceptions "$exceptions" \
            --upstream-fixes "$upstream_fixes" \
            --summary "$UPSTREAM_RUST_SUMMARY" \
            --current-upstream-revision "$UPSTREAM_RUST_CURRENT_REVISION"
    else
        run_no_unexpected_skip trust_upstream_compat validate \
            --baseline "$baseline" \
            --exceptions "$exceptions" \
            --upstream-fixes "$upstream_fixes" \
            --summary "$UPSTREAM_RUST_SUMMARY"
    fi
}

run_upstream_rust_compat() {
    if [ "$RELEASE_GATE" = "1" ] && [ -z "$UPSTREAM_RUST_CURRENT_REVISION" ]; then
        section "Tracked upstream Rust revision"
        echo "SETUP/BLOCKED: internal upstream compatibility accounting release mode requires TRUST_UPSTREAM_RUST_CURRENT_REVISION." >&2
        echo "Set it to the rust-lang/rust revision through which upstream fixes have been audited." >&2
        return 2
    fi

    section "Rust-owned upstream compatibility accounting"
    echo "Scope: runs the Rust-owned compatibility accounting crate and standalone tests only; this is not a full upstream Rust suite run."
    run_no_unexpected_skip trust_cargo test --manifest-path "$TRUST_ROOT/crates/trust-upstream-compat/Cargo.toml" --locked
    run_upstream_rust_production_ledger_validation

    section "Standalone Rust compatibility accounting tests"
    run_upstream_rust_standalone_tests

    if [ "$RUN_FULL_UPSTREAM_RUST_TESTS" = "1" ] || [ "$RELEASE_GATE" = "1" ]; then
        run_full_upstream_rust_suite
        return
    fi

    echo
    echo "Full upstream Rust suite: not run. Set TRUST_RUN_FULL_UPSTREAM_RUST_TESTS=1 to run ./x.py test --stage 2 --trust-vanilla --no-fail-fast and validate summary.json."
}

run_upstream_rust_porting() {
    local out_dir="${TRUST_UPSTREAM_RUST_PORT_OUT:-$TRUST_ROOT/reports/upstream-rust/porting/current}"
    local revision="${TRUST_UPSTREAM_RUST_PORT_REVISION:-rust-lang/rust:HEAD}"
    local remote="${TRUST_UPSTREAM_RUST_PORT_REMOTE:-https://github.com/rust-lang/rust.git}"
    local execute="${TRUST_UPSTREAM_RUST_PORT_EXECUTE:-1}"
    local apply="${TRUST_UPSTREAM_RUST_PORT_APPLY:-1}"
    local fetch="${TRUST_UPSTREAM_RUST_PORT_FETCH:-1}"
    local release="${TRUST_UPSTREAM_RUST_PORT_RELEASE:-$RELEASE_GATE}"
    local max_files="${TRUST_UPSTREAM_RUST_PORT_MAX_FILES:-}"
    local scorecard_log="${TRUST_UPSTREAM_RUST_PORT_LOG:-}"
    local -a args

    if [ -n "$scorecard_log" ] && [ -z "${TRUST_UPSTREAM_RUST_PORT_APPLY+x}" ]; then
        apply=0
    fi
    if [ -n "$max_files" ] && [ -z "${TRUST_UPSTREAM_RUST_PORT_APPLY+x}" ]; then
        apply=0
    fi

    case "$execute" in
        0|1)
            ;;
        *)
            echo "FAIL: TRUST_UPSTREAM_RUST_PORT_EXECUTE must be 0 or 1 (got: $execute)" >&2
            return 2
            ;;
    esac
    case "$apply" in
        0|1)
            ;;
        *)
            echo "FAIL: TRUST_UPSTREAM_RUST_PORT_APPLY must be 0 or 1 (got: $apply)" >&2
            return 2
            ;;
    esac
    case "$fetch" in
        0|1)
            ;;
        *)
            echo "FAIL: TRUST_UPSTREAM_RUST_PORT_FETCH must be 0 or 1 (got: $fetch)" >&2
            return 2
            ;;
    esac
    if [ -n "$scorecard_log" ] && [ "$execute" = "1" ]; then
        echo "FAIL: TRUST_UPSTREAM_RUST_PORT_LOG is log-parse mode; set TRUST_UPSTREAM_RUST_PORT_EXECUTE=0." >&2
        return 2
    fi
    case "$release" in
        0|1)
            ;;
        *)
            echo "FAIL: TRUST_UPSTREAM_RUST_PORT_RELEASE must be 0 or 1 (got: $release)" >&2
            return 2
            ;;
    esac
    if [ ! -f "$UPSTREAM_RUST_PORT_TEST_EXCEPTIONS" ]; then
        echo "FAIL: TRUST_UPSTREAM_RUST_PORT_TEST_EXCEPTIONS is not a file: $UPSTREAM_RUST_PORT_TEST_EXCEPTIONS" >&2
        return 2
    fi
    if [ ! -f "$UPSTREAM_RUST_PORT_PATCH_MANIFEST" ]; then
        echo "FAIL: TRUST_UPSTREAM_RUST_PORT_PATCH_MANIFEST is not a file: $UPSTREAM_RUST_PORT_PATCH_MANIFEST" >&2
        return 2
    fi
    if [ -n "$max_files" ] && [ "$apply" = "1" ]; then
        echo "FAIL: TRUST_UPSTREAM_RUST_PORT_MAX_FILES is a bounded smoke import and cannot be combined with TRUST_UPSTREAM_RUST_PORT_APPLY=1." >&2
        return 2
    fi

    args=(
        trust_cargo
        trust domination upstream-tests
        --baseline "$TRUST_ROOT/tests/upstream-rust/baseline.toml"
        --upstream-fixes "$TRUST_ROOT/tests/upstream-rust/upstream-fixes.toml"
        --test-exceptions "$UPSTREAM_RUST_PORT_TEST_EXCEPTIONS"
        --patch-manifest "$UPSTREAM_RUST_PORT_PATCH_MANIFEST"
        --upstream-revision "$revision"
        --upstream-remote "$remote"
        --out-dir "$out_dir"
        --bootstrap-args "$UPSTREAM_RUST_PORT_BOOTSTRAP_ARGS"
        --proof-mode "$UPSTREAM_RUST_PORT_PROOF_MODE"
    )

    [ "$execute" = "1" ] && args+=(--execute)
    [ "$execute" = "0" ] && args+=(--no-execute)
    [ "$apply" = "1" ] && args+=(--apply)
    [ "$apply" = "0" ] && args+=(--no-apply)
    [ "$fetch" = "0" ] && args+=(--no-fetch)
    [ "$release" = "1" ] && args+=(--release)
    [ -n "$max_files" ] && args+=(--max-files "$max_files")
    [ -n "$scorecard_log" ] && args+=(--scorecard-log "$scorecard_log")
    [ -n "${TRUST_UPSTREAM_RUST_PORT_LLM_DIRECTIVES:-}" ] && args+=(--llm-directives "$TRUST_UPSTREAM_RUST_PORT_LLM_DIRECTIVES")

    section "Repeatable upstream Rust test porting"
    echo "Scope: re-imports upstream Rust tests, applies the reviewed patch manifest with an audit log, and writes a failure scorecard."
    echo "Porting implementation: Rust CLI"
    echo "Upstream revision: $revision"
    echo "Porting artifacts: $out_dir"
    echo "Test exception ledger: $UPSTREAM_RUST_PORT_TEST_EXCEPTIONS"
    echo "Patch manifest: $UPSTREAM_RUST_PORT_PATCH_MANIFEST"
    [ -n "${TRUST_UPSTREAM_RUST_PORT_LLM_DIRECTIVES:-}" ] && echo "LLM directives: $TRUST_UPSTREAM_RUST_PORT_LLM_DIRECTIVES"
    echo "Proof mode: $UPSTREAM_RUST_PORT_PROOF_MODE"
    echo "Bootstrap args: $UPSTREAM_RUST_PORT_BOOTSTRAP_ARGS"
    echo "Rust porting command: targo trust domination upstream-tests"
    run "${args[@]}"
}

FORMULA_COMPAT_EVIDENCE="crates/trust-router/tests/formula_compat_gate.rs"
CONTRACT_SOURCE_RECOVERY_EVIDENCE="crates/trust-mir-extract/src/lib.rs"
PROOF_GRADE_RELEASE_SENTINEL_DOC="docs/release-gate-checklist.md"
PROOF_GRADE_RELEASE_SENTINEL_BLOCKERS=(
    "Transcript schema version"
    "Candidate commit"
    "Binary artifact digest"
    "Selected-image identity"
    "VC digest inventory"
    "Checked cert readback"
    "Replay transcript digest"
    "Provenance artifact digest"
    "Target proof-consumer digest"
    "Exact source/type-fact ownership"
    "Unsupported ledger empty"
    "AArch64 ordering/monitor semantics"
    "Transcript artifact binding"
)
RELEASE_GATE_LOCKFILE_STABILITY_PATHS=(
    "Cargo.toml"
    "Cargo.lock"
    "crates/Cargo.toml"
    "crates/Cargo.lock"
    "targo-trust/Cargo.toml"
    "targo-trust/Cargo.lock"
)
FORMULA_OWNER_MATRIX=(
    "separation/ownership|trust-vc|ownership-gate|FormulaFamily::SeparationOwnership|BackendRole::Ownership"
    "FFI boundary|trust-wp|ffi-gate|FormulaFamily::Ffi|BackendRole::SmtSolver"
    "data race|trust-mc|race-gate|FormulaFamily::DataRace|BackendRole::Temporal"
    "typestate/protocol|trust-wp|protocol-gate|FormulaFamily::TypestateProtocol|BackendRole::Temporal"
)

require_formula_owner_matrix() {
    local evidence="$TRUST_ROOT/$FORMULA_COMPAT_EVIDENCE"

    if [ ! -f "$evidence" ]; then
        echo "FAIL: native-contracts-pipeline-v2 Formula compatibility evidence is missing: $FORMULA_COMPAT_EVIDENCE" >&2
        exit 2
    fi

    python3 - "$evidence" "${FORMULA_OWNER_MATRIX[@]}" <<'PY'
import sys

evidence_path = sys.argv[1]
rows = [row.split("|") for row in sys.argv[2:]]
text = open(evidence_path, encoding="utf-8").read()

failures = []
for test_name in (
    "retained_formula_families_route_to_compatible_backends",
    "retained_formula_families_fail_closed_without_compatible_backend",
    "unsupported_mir_fails_closed_before_formula_routing",
):
    if test_name not in text:
        failures.append(f"missing Formula compatibility test: {test_name}")

owners = {row[1] for row in rows}
for owner in ("trust-vc", "trust-wp", "trust-mc"):
    if owner not in owners:
        failures.append(f"missing native Formula owner in matrix: {owner}")

for label, owner, backend, family, role in rows:
    for token_name, token in (
        ("Formula family label", label),
        ("compatibility backend", backend),
        ("Formula family enum", family),
        ("backend role", role),
    ):
        if token not in text:
            failures.append(f"{token_name} for {owner} is not covered by {evidence_path}: {token}")

if failures:
    print("FAIL: native-contracts-pipeline-v2 Formula-family owner matrix is incomplete", file=sys.stderr)
    for failure in failures:
        print(f"  - {failure}", file=sys.stderr)
    raise SystemExit(2)

for label, owner, backend, family, role in rows:
    print(f"Formula owner: {label} -> {owner} via {backend} ({family}, {role})")
PY
}

require_contract_source_recovery_evidence() {
    local evidence="$TRUST_ROOT/$CONTRACT_SOURCE_RECOVERY_EVIDENCE"

    if [ ! -f "$evidence" ]; then
        echo "FAIL: native-contracts-pipeline-v2 source-recovery evidence is missing: $CONTRACT_SOURCE_RECOVERY_EVIDENCE" >&2
        exit 2
    fi

    python3 - "$evidence" <<'PY'
import sys

evidence_path = sys.argv[1]
text = open(evidence_path, encoding="utf-8").read()

required_tokens = [
    (
        "compiler-owned contract bundle conversion",
        "convert_trust_contract_bundle",
    ),
    (
        "normal extraction entry point accepts a compiler bundle",
        "extract_function_with_contract_bundle",
    ),
    (
        "normal extraction reports compiler bundle ownership",
        "ContractExtractionSource::CompilerContractBundle",
    ),
    (
        "normal extraction keeps source scraping disabled",
        "source_scraping_used: false",
    ),
    (
        "default native path fails closed without source scraping",
        "native_no_contract_bundle_fails_closed_without_source_scraping",
    ),
    (
        "diagnostic says source scraping is disabled by default",
        "native contract facts unavailable; compatibility source scraping disabled",
    ),
]

# R-U §1.2-5: the compat/debug source-scraping lane was deleted outright.
# It must stay deleted — any reappearance of its symbols is a regression.
forbidden_tokens = [
    (
        "retired compat/debug source-scraping entry point",
        "extract_function_with_compat_source_recovery_for_debugging",
    ),
    (
        "retired compat/debug source-scraping policy",
        "ContractExtractionPolicy::CompatDebugSourceScraping",
    ),
    (
        "retired legacy text-fallback scraper",
        "extract_contracts_from_source_compat_debug_only",
    ),
]

failures = [
    f"missing {label}: {token}"
    for label, token in required_tokens
    if token not in text
]

failures.extend(
    f"resurfaced {label}: {token}"
    for label, token in forbidden_tokens
    if token in text
)

if "extract_function_with_contract_bundle(tcx, body, None)" not in text:
    failures.append(
        "default extract_function must route through the native-only bundle entry point"
    )

if failures:
    print(
        "FAIL: native-contracts-pipeline-v2 source-recovery evidence is incomplete",
        file=sys.stderr,
    )
    for failure in failures:
        print(f"  - {failure}", file=sys.stderr)
    raise SystemExit(2)

print("Contract source recovery: normal verification accepts compiler-owned contract bundles")
print("Contract source recovery: default native path does not enable source scraping")
print("Contract source recovery: compat/debug source-scraping lane stays deleted")
print("Contract source recovery: missing native facts fail closed")
PY
}

require_proof_grade_release_sentinel() {
    local checklist="$TRUST_ROOT/$PROOF_GRADE_RELEASE_SENTINEL_DOC"
    local transcript="$PROOF_GRADE_RELEASE_TRANSCRIPT"

    if [ ! -f "$checklist" ]; then
        echo "FAIL: public proof-grade sentinel checklist is missing: $PROOF_GRADE_RELEASE_SENTINEL_DOC" >&2
        exit 2
    fi

    if [ -n "$transcript" ] && [ "${transcript#/}" = "$transcript" ]; then
        transcript="$TRUST_ROOT/$transcript"
    fi

    python3 - "$checklist" "$PUBLIC_PROOF_GRADE_CLAIM" "$transcript" "$PROOF_GRADE_RELEASE_TRANSCRIPT_DIGEST" "${PROOF_GRADE_RELEASE_SENTINEL_BLOCKERS[@]}" <<'PY'
import json
import hashlib
import pathlib
import re
import subprocess
import sys

checklist_path = pathlib.Path(sys.argv[1])
claim_requested = sys.argv[2] == "1"
transcript_arg = sys.argv[3]
transcript_digest_arg = sys.argv[4]
expected = sys.argv[5:]
failures = []

text = checklist_path.read_text(encoding="utf-8")
start = "<!-- proof-grade-release-sentinel:start -->"
end = "<!-- proof-grade-release-sentinel:end -->"

def fail(message):
    failures.append(message)

if start not in text or end not in text:
    fail(f"public proof-grade sentinel markers missing from {checklist_path}")
    rows = {}
else:
    body = text.split(start, 1)[1].split(end, 1)[0]
    rows = {}
    for line in body.splitlines():
        stripped = line.strip()
        if not stripped.startswith("|"):
            continue
        cells = [cell.strip().strip("`") for cell in stripped.strip("|").split("|")]
        if len(cells) < 3:
            continue
        label, status = cells[0], cells[1].lower()
        if label.lower() == "blocker" or set(label) <= {"-"}:
            continue
        if set(status) <= {"-"}:
            continue
        rows[label] = status

    missing = [label for label in expected if label not in rows]
    if missing:
        fail(
            "public proof-grade sentinel is missing required blocker rows: "
            + ", ".join(missing)
        )

    non_green = []
    for label in expected:
        status = rows.get(label, "missing")
        print(f"Proof-grade release sentinel: {label}: {status}")
        if status != "green":
            non_green.append((label, status))

    if claim_requested and non_green:
        fail("public proof-grade claim requested while release blockers are not all green")
        for label, status in non_green:
            fail(f"sentinel blocker still {status}: {label}")

DIGEST_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
COMMIT_RE = re.compile(r"^[0-9a-f]{40}$")
SYNTHETIC_FIXTURE_MARKER_RE = re.compile(
    r"(^|[^A-Za-z0-9])(?:synthetic|fixture|mock|fake|placeholder)(?:[^A-Za-z0-9]|$)",
    re.IGNORECASE,
)
TRANSCRIPT_SCHEMA_VERSION = "trust.proof-grade-release-transcript.v1"
ROW_SCHEMA_VERSION = "trust.proof-grade-row.v1"
ROW_TYPE = "binary-decompilation-proof-grade"
ROW_BINDING_PROFILE_ID = "trust.proof-grade-row-binding.v1"
REAL_EVIDENCE_ORIGIN = "targo_trust_release_export"
ROW_BINDING_PROFILE_DESCRIPTION = (
    "targo-trust ProofGradeReleaseTranscriptRowBindingProfile encoded as compact "
    "UTF-8 JSON in producer field order, then SHA-256 with "
    "sha256:<lowercase-hex> prefix"
)
TRANSCRIPT_FIELDS = {
    "schema_version",
    "accepted_proof_grade_rows",
    "blocked_proof_grade_rows",
}
ROW_FIELDS = {
    "schema_version",
    "row_type",
    "evidence_origin",
    "status",
    "accepted",
    "rejection_reason",
    "candidate_commit",
    "proof_required_vc_count",
    "binary_digest",
    "selected_image",
    "vc_digests",
    "checked_certificate_digests",
    "replay_transcript_digests",
    "provenance_artifact_digests",
    "unsupported_ledgers_empty",
    "target_proof_consumer_artifact_digests",
    "exact_source_ownership_evidence",
    "type_ownership_evidence",
    "aarch64_ordering_monitor_evidence",
    "release_transcript_binding_digest",
    "blockers",
}
SELECTED_IMAGE_FIELDS = {
    "identity",
    "digest",
}
SIMPLE_DIGEST_LISTS = [
    "replay_transcript_digests",
    "provenance_artifact_digests",
    "target_proof_consumer_artifact_digests",
]
EVIDENCE_DIGEST_FIELDS = {
    "status",
    "digest",
}
SUPPORTED_DIGEST_ALGORITHM = "sha256"
VC_DIGEST_ENTRY_SCHEMA_VERSION = "trust.vc-digest-entry.v1"
CHECKED_CERT_DIGEST_ENTRY_SCHEMA_VERSION = (
    "trust.checked-certificate-readback-digest-entry.v1"
)
DIGEST_INVENTORY_COMMON_FIELDS = {
    "schema_version",
    "artifact_kind",
    "digest_algorithm",
    "digest",
    "candidate_commit",
    "binary_digest",
    "selected_image",
    "inventory_index",
    "inventory_count",
}
VC_DIGEST_ENTRY_FIELDS = DIGEST_INVENTORY_COMMON_FIELDS | {
    "vc_id",
}
CHECKED_CERT_DIGEST_ENTRY_FIELDS = DIGEST_INVENTORY_COMMON_FIELDS | {
    "vc_digest",
    "certificate_role",
    "readback_status",
}
AARCH64_ORDERING_MONITOR_FIELDS = {
    "status",
    "opcode",
    "ordering",
    "exclusive_monitor",
    "digest",
    "blockers",
}
PRODUCER_BLOCKERS = [
    "schema_version",
    "row_type",
    "evidence_origin",
    "status",
    "accepted",
    "rejection_reason",
    "candidate_commit",
    "proof_required_vc_count",
    "binary_digest",
    "selected_image.identity",
    "selected_image.digest",
    "vc_digests",
    "checked_certificate_digests",
    "replay_transcript_digests",
    "provenance_artifact_digests",
    "unsupported_ledgers_empty",
    "target_proof_consumer_artifact_digests",
    "exact_source_ownership_evidence",
    "type_ownership_evidence",
    "release_transcript_binding_digest",
    "blockers",
]

class DuplicateKeyError(ValueError):
    pass

class NonFiniteJsonConstantError(ValueError):
    pass

def reject_duplicate_keys(pairs):
    seen = set()
    result = {}
    for key, value in pairs:
        if key in seen:
            raise DuplicateKeyError(key)
        seen.add(key)
        result[key] = value
    return result

def reject_nonfinite_json_constant(value):
    raise NonFiniteJsonConstantError(value)

def is_nonempty_string(value):
    return isinstance(value, str) and bool(value.strip())

def is_digest(value):
    return isinstance(value, str) and DIGEST_RE.fullmatch(value) is not None

def is_nonnegative_int(value):
    return isinstance(value, int) and not isinstance(value, bool) and value >= 0

def is_positive_int(value):
    return isinstance(value, int) and not isinstance(value, bool) and value > 0

def validate_known_fields(value, allowed, label):
    unknown = sorted(set(value) - allowed)
    if unknown:
        fail(f"{label}: unknown acceptance-critical field(s): {', '.join(unknown)}")

def require_present(value, field, label):
    if field not in value:
        fail(
            f"{label}: {field} is absent; typed release transcript requires an explicit value"
        )
        return False
    return True

def validate_proof_required_vc_count(row, row_label):
    value = row.get("proof_required_vc_count")
    if not is_positive_int(value):
        fail(f"{row_label}: proof_required_vc_count must be a positive integer")
        return None
    return value

def validate_digest_list(row, field, row_label):
    value = row.get(field)
    if not isinstance(value, list) or not value:
        fail(f"{row_label}: {field} must be a non-empty list of sha256:<hex> digests")
        return []
    seen = set()
    valid = []
    for idx, digest in enumerate(value):
        if not is_digest(digest):
            fail(f"{row_label}: {field}[{idx}] is not a canonical sha256:<hex> digest")
            continue
        if digest in seen:
            fail(f"{row_label}: {field}[{idx}] duplicates an earlier digest")
        seen.add(digest)
        valid.append(digest)
    return valid

def validate_entry_selected_image_binding(entry, entry_label, row_selected_image):
    selected_image = entry.get("selected_image")
    if not isinstance(selected_image, dict):
        fail(f"{entry_label}: selected_image must bind this digest to the row image")
        return

    validate_known_fields(selected_image, SELECTED_IMAGE_FIELDS, f"{entry_label}: selected_image")
    for field in sorted(SELECTED_IMAGE_FIELDS):
        require_present(selected_image, field, f"{entry_label}: selected_image")

    if not is_nonempty_string(selected_image.get("identity")):
        fail(f"{entry_label}: selected_image.identity must be non-empty")
    if not is_digest(selected_image.get("digest")):
        fail(f"{entry_label}: selected_image.digest must be a canonical sha256:<hex> digest")

    if isinstance(row_selected_image, dict):
        if selected_image.get("identity") != row_selected_image.get("identity"):
            fail(f"{entry_label}: selected_image.identity must match the row selected_image.identity")
        if selected_image.get("digest") != row_selected_image.get("digest"):
            fail(f"{entry_label}: selected_image.digest must match the row selected_image.digest")

def validate_digest_inventory_entry_common(
    entry,
    entry_label,
    *,
    row,
    row_label,
    field,
    expected_schema_version,
    expected_artifact_kind,
    expected_count,
):
    validate_known_fields(
        entry,
        VC_DIGEST_ENTRY_FIELDS
        if field == "vc_digests"
        else CHECKED_CERT_DIGEST_ENTRY_FIELDS,
        entry_label,
    )
    for required in sorted(
        DIGEST_INVENTORY_COMMON_FIELDS
        | ({"vc_id"} if field == "vc_digests" else {"vc_digest", "certificate_role", "readback_status"})
    ):
        require_present(entry, required, entry_label)

    if entry.get("schema_version") != expected_schema_version:
        fail(f"{entry_label}: schema_version must be {expected_schema_version}")
    if entry.get("artifact_kind") != expected_artifact_kind:
        fail(f"{entry_label}: artifact_kind must be {expected_artifact_kind}")

    digest_algorithm = entry.get("digest_algorithm")
    if digest_algorithm != SUPPORTED_DIGEST_ALGORITHM:
        fail(
            f"{entry_label}: unknown digest_algorithm {digest_algorithm!r}; "
            f"only {SUPPORTED_DIGEST_ALGORITHM} is supported"
        )

    digest = entry.get("digest")
    if not is_digest(digest):
        fail(f"{entry_label}: digest must be a canonical sha256:<hex> digest")

    candidate_commit = row.get("candidate_commit")
    if entry.get("candidate_commit") != candidate_commit:
        fail(f"{entry_label}: candidate_commit must match {row_label}.candidate_commit")
    if entry.get("binary_digest") != row.get("binary_digest"):
        fail(f"{entry_label}: binary_digest must match {row_label}.binary_digest")
    validate_entry_selected_image_binding(entry, entry_label, row.get("selected_image"))

    inventory_index = entry.get("inventory_index")
    if not is_nonnegative_int(inventory_index):
        fail(f"{entry_label}: inventory_index must be a non-negative integer")
    inventory_count = entry.get("inventory_count")
    if not is_positive_int(inventory_count):
        fail(f"{entry_label}: inventory_count must be a positive integer")
    else:
        if expected_count is not None and inventory_count != expected_count:
            fail(
                f"{entry_label}: inventory_count {inventory_count} does not match "
                f"{row_label}.proof_required_vc_count {expected_count}"
            )
    return {
        "digest": digest if is_digest(digest) else None,
        "inventory_index": inventory_index if is_nonnegative_int(inventory_index) else None,
        "inventory_count": inventory_count if is_positive_int(inventory_count) else None,
    }

def validate_inventory_indexes(indexes, field, row_label, expected_count):
    if expected_count is None:
        return
    valid_indexes = [index for index in indexes if index is not None]
    if len(valid_indexes) != len(indexes):
        return
    expected_indexes = set(range(expected_count))
    actual_indexes = set(valid_indexes)
    if actual_indexes != expected_indexes:
        fail(
            f"{row_label}: {field} inventory_index values must cover "
            f"0..{expected_count - 1}"
        )
    if len(valid_indexes) != len(set(valid_indexes)):
        fail(f"{row_label}: {field} inventory_index values must be unique")

def validate_vc_digest_inventory(row, row_label, expected_count):
    field = "vc_digests"
    value = row.get(field)
    if not isinstance(value, list) or not value:
        fail(f"{row_label}: {field} must be a non-empty list of typed digest inventory entries")
        return []
    if expected_count is not None and len(value) != expected_count:
        fail(
            f"{row_label}: proof_required_vc_count {expected_count} does not match "
            f"{field} length {len(value)}"
        )

    seen_digests = {}
    indexes = []
    vc_entries = []
    for idx, entry in enumerate(value):
        entry_label = f"{row_label}: {field}[{idx}]"
        if not isinstance(entry, dict):
            fail(f"{entry_label}: entry must be a JSON object with typed digest inventory fields")
            continue
        common = validate_digest_inventory_entry_common(
            entry,
            entry_label,
            row=row,
            row_label=row_label,
            field=field,
            expected_schema_version=VC_DIGEST_ENTRY_SCHEMA_VERSION,
            expected_artifact_kind="verification-condition",
            expected_count=expected_count,
        )
        indexes.append(common["inventory_index"])
        digest = common["digest"]
        if digest is not None:
            previous = seen_digests.get(digest)
            if previous is not None:
                fail(f"{entry_label}: digest duplicates {field}[{previous}]")
            else:
                seen_digests[digest] = idx
        if not is_nonempty_string(entry.get("vc_id")):
            fail(f"{entry_label}: vc_id must be non-empty")
        vc_entries.append(entry)

    validate_inventory_indexes(indexes, field, row_label, expected_count)
    return vc_entries

def validate_checked_certificate_digest_inventory(row, row_label, expected_count, vc_entries):
    field = "checked_certificate_digests"
    value = row.get(field)
    if not isinstance(value, list) or not value:
        fail(f"{row_label}: {field} must be a non-empty list of typed digest inventory entries")
        return
    if expected_count is not None and len(value) != expected_count:
        fail(
            f"{row_label}: proof_required_vc_count {expected_count} does not match "
            f"{field} length {len(value)}"
        )

    vc_digest_to_index = {
        entry.get("digest"): idx
        for idx, entry in enumerate(vc_entries)
        if isinstance(entry, dict) and is_digest(entry.get("digest"))
    }
    seen_cert_digests = {}
    seen_vc_digests = {}
    indexes = []
    for idx, entry in enumerate(value):
        entry_label = f"{row_label}: {field}[{idx}]"
        if not isinstance(entry, dict):
            fail(f"{entry_label}: entry must be a JSON object with typed digest inventory fields")
            continue
        common = validate_digest_inventory_entry_common(
            entry,
            entry_label,
            row=row,
            row_label=row_label,
            field=field,
            expected_schema_version=CHECKED_CERT_DIGEST_ENTRY_SCHEMA_VERSION,
            expected_artifact_kind="checked-certificate-readback",
            expected_count=expected_count,
        )
        indexes.append(common["inventory_index"])
        digest = common["digest"]
        if digest is not None:
            previous = seen_cert_digests.get(digest)
            if previous is not None:
                fail(f"{entry_label}: digest duplicates {field}[{previous}]")
            else:
                seen_cert_digests[digest] = idx

        vc_digest = entry.get("vc_digest")
        if not is_digest(vc_digest):
            fail(f"{entry_label}: vc_digest must be a canonical sha256:<hex> digest")
        else:
            previous = seen_vc_digests.get(vc_digest)
            if previous is not None:
                fail(f"{entry_label}: vc_digest duplicates {field}[{previous}]")
            else:
                seen_vc_digests[vc_digest] = idx
            if vc_digest not in vc_digest_to_index:
                fail(f"{entry_label}: vc_digest is not present in the row vc_digests inventory")

        if entry.get("certificate_role") != "checked-certificate":
            fail(f"{entry_label}: certificate_role must be checked-certificate")
        if entry.get("readback_status") != "accepted":
            fail(f"{entry_label}: readback_status must be accepted")

    validate_inventory_indexes(indexes, field, row_label, expected_count)

    missing = sorted(set(vc_digest_to_index) - set(seen_vc_digests))
    extra = sorted(set(seen_vc_digests) - set(vc_digest_to_index))
    if missing:
        fail(
            f"{row_label}: checked_certificate_digests is missing readback for "
            f"vc_digests digest(s): {', '.join(missing)}"
        )
    if extra:
        fail(
            f"{row_label}: checked_certificate_digests references unknown "
            f"vc_digests digest(s): {', '.join(extra)}"
        )

def validate_required_evidence_digest(row, field, row_label):
    value = row.get(field)
    label = f"{row_label}: {field}"
    if not isinstance(value, dict):
        fail(f"{label} must be an accepted evidence digest object")
        return
    validate_known_fields(value, EVIDENCE_DIGEST_FIELDS, label)
    require_present(value, "status", label)
    require_present(value, "digest", label)
    if value.get("status") != "accepted":
        fail(f"{label}.status must be accepted")
    if not is_digest(value.get("digest")):
        fail(f"{label}.digest must be a canonical sha256:<hex> digest")

def validate_blockers(row, row_label):
    value = row.get("blockers")
    if not isinstance(value, list):
        fail(f"{row_label}: blockers must be an explicit empty list")
        return
    if value:
        fail(f"{row_label}: blockers must be empty for accepted rows")

def validate_no_synthetic_fixture_markers(value, label):
    if isinstance(value, dict):
        for key, child in value.items():
            validate_no_synthetic_fixture_markers(child, f"{label}.{key}")
        return
    if isinstance(value, list):
        for index, child in enumerate(value):
            validate_no_synthetic_fixture_markers(child, f"{label}[{index}]")
        return
    if isinstance(value, str) and SYNTHETIC_FIXTURE_MARKER_RE.search(value):
        fail(
            f"{label}: synthetic fixture marker is not accepted in public "
            "proof-grade release evidence"
        )

def validate_aarch64_ordering_monitor_evidence(row, row_label):
    if "aarch64_ordering_monitor_evidence" not in row:
        return
    value = row.get("aarch64_ordering_monitor_evidence")
    if not isinstance(value, list):
        fail(f"{row_label}: aarch64_ordering_monitor_evidence must be a list")
        return
    for idx, entry in enumerate(value):
        entry_label = f"{row_label}: aarch64_ordering_monitor_evidence[{idx}]"
        if not isinstance(entry, dict):
            fail(f"{entry_label}: entry must be a JSON object")
            continue
        validate_known_fields(entry, AARCH64_ORDERING_MONITOR_FIELDS, entry_label)
        for field in ("status", "opcode", "ordering", "exclusive_monitor", "digest"):
            require_present(entry, field, entry_label)
        if entry.get("status") != "accepted":
            fail(f"{entry_label}: status must be accepted")
        for field in ("opcode", "ordering", "exclusive_monitor"):
            if not is_nonempty_string(entry.get(field)):
                fail(f"{entry_label}: {field} must be non-empty")
        if not is_digest(entry.get("digest")):
            fail(f"{entry_label}: digest must be a canonical sha256:<hex> digest")
        blockers = entry.get("blockers", [])
        if not isinstance(blockers, list):
            fail(f"{entry_label}: blockers must be a list when present")
        elif blockers:
            fail(f"{entry_label}: blockers must be empty for accepted AArch64 evidence")

def resolve_current_candidate_commit():
    trust_root = checklist_path.resolve().parent.parent
    try:
        result = subprocess.run(
            ["git", "-C", str(trust_root), "rev-parse", "--verify", "HEAD^{commit}"],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
    except (OSError, subprocess.CalledProcessError) as exc:
        detail = getattr(exc, "stderr", "") or str(exc)
        fail(
            "proof-grade release transcript cannot resolve current candidate commit HEAD "
            f"from {trust_root}: {detail.strip()}"
        )
        return None
    commit = result.stdout.strip()
    if COMMIT_RE.fullmatch(commit) is None:
        fail(f"current candidate commit is not a full lowercase git commit: {commit}")
        return None
    return commit

def canonical_json_bytes(value):
    return json.dumps(
        value,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")

def transcript_artifact_digest(path):
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()

def selected_image_binding(value):
    if not isinstance(value, dict):
        return value
    return {
        "identity": value.get("identity"),
        "digest": value.get("digest"),
    }

def vc_digest_entry_binding(value):
    if not isinstance(value, dict):
        return value
    return {
        "schema_version": value.get("schema_version"),
        "artifact_kind": value.get("artifact_kind"),
        "digest_algorithm": value.get("digest_algorithm"),
        "digest": value.get("digest"),
        "candidate_commit": value.get("candidate_commit"),
        "binary_digest": value.get("binary_digest"),
        "selected_image": selected_image_binding(value.get("selected_image")),
        "inventory_index": value.get("inventory_index"),
        "inventory_count": value.get("inventory_count"),
        "vc_id": value.get("vc_id"),
    }

def checked_certificate_digest_entry_binding(value):
    if not isinstance(value, dict):
        return value
    return {
        "schema_version": value.get("schema_version"),
        "artifact_kind": value.get("artifact_kind"),
        "digest_algorithm": value.get("digest_algorithm"),
        "digest": value.get("digest"),
        "candidate_commit": value.get("candidate_commit"),
        "binary_digest": value.get("binary_digest"),
        "selected_image": selected_image_binding(value.get("selected_image")),
        "inventory_index": value.get("inventory_index"),
        "inventory_count": value.get("inventory_count"),
        "vc_digest": value.get("vc_digest"),
        "certificate_role": value.get("certificate_role"),
        "readback_status": value.get("readback_status"),
    }

def evidence_digest_binding(value):
    if not isinstance(value, dict):
        return value
    result = {
        "status": value.get("status"),
    }
    if "digest" in value:
        result["digest"] = value.get("digest")
    return result

def aarch64_ordering_monitor_binding(value):
    if not isinstance(value, dict):
        return value
    result = {
        "status": value.get("status"),
        "opcode": value.get("opcode"),
        "ordering": value.get("ordering"),
        "exclusive_monitor": value.get("exclusive_monitor"),
    }
    if "digest" in value:
        result["digest"] = value.get("digest")
    blockers = value.get("blockers", [])
    if blockers:
        result["blockers"] = blockers
    return result

def row_binding_profile(row):
    return {
        "schema_version": ROW_BINDING_PROFILE_ID,
        "row_schema_version": row.get("schema_version"),
        "row_type": row.get("row_type"),
        "evidence_origin": row.get("evidence_origin"),
        "status": row.get("status"),
        "accepted": row.get("accepted"),
        "rejection_reason": row.get("rejection_reason") if "rejection_reason" in row else None,
        "candidate_commit": row.get("candidate_commit") if "candidate_commit" in row else None,
        "proof_required_vc_count": row.get("proof_required_vc_count")
        if is_positive_int(row.get("proof_required_vc_count"))
        else 0,
        "binary_digest": row.get("binary_digest") if "binary_digest" in row else None,
        "selected_image": selected_image_binding(row.get("selected_image")),
        "vc_digests": [
            vc_digest_entry_binding(entry) for entry in row.get("vc_digests", [])
        ]
        if isinstance(row.get("vc_digests"), list)
        else [],
        "checked_certificate_digests": [
            checked_certificate_digest_entry_binding(entry)
            for entry in row.get("checked_certificate_digests", [])
        ]
        if isinstance(row.get("checked_certificate_digests"), list)
        else [],
        "replay_transcript_digests": row.get("replay_transcript_digests")
        if isinstance(row.get("replay_transcript_digests"), list)
        else [],
        "provenance_artifact_digests": row.get("provenance_artifact_digests")
        if isinstance(row.get("provenance_artifact_digests"), list)
        else [],
        "unsupported_ledgers_empty": row.get("unsupported_ledgers_empty"),
        "target_proof_consumer_artifact_digests": row.get(
            "target_proof_consumer_artifact_digests"
        )
        if isinstance(row.get("target_proof_consumer_artifact_digests"), list)
        else [],
        "exact_source_ownership_evidence": evidence_digest_binding(
            row.get("exact_source_ownership_evidence")
        ),
        "type_ownership_evidence": evidence_digest_binding(
            row.get("type_ownership_evidence")
        ),
        "aarch64_ordering_monitor_evidence": [
            aarch64_ordering_monitor_binding(entry)
            for entry in row.get("aarch64_ordering_monitor_evidence", [])
        ]
        if isinstance(row.get("aarch64_ordering_monitor_evidence", []), list)
        else row.get("aarch64_ordering_monitor_evidence"),
        "blockers": row.get("blockers") if isinstance(row.get("blockers"), list) else [],
    }

def row_binding_digest(row):
    return "sha256:" + hashlib.sha256(canonical_json_bytes(row_binding_profile(row))).hexdigest()

def accepted_row_identity(row):
    selected_image = row.get("selected_image")
    if not isinstance(selected_image, dict):
        return None
    candidate_commit = row.get("candidate_commit")
    binary_digest = row.get("binary_digest")
    selected_image_identity = selected_image.get("identity")
    selected_image_digest = selected_image.get("digest")
    if (
        isinstance(candidate_commit, str)
        and COMMIT_RE.fullmatch(candidate_commit) is not None
        and is_digest(binary_digest)
        and is_nonempty_string(selected_image_identity)
        and is_digest(selected_image_digest)
    ):
        return (
            candidate_commit,
            binary_digest,
            selected_image_identity.strip(),
            selected_image_digest,
        )
    return None

def validate_transcript_path_commit(path, current_candidate_commit):
    if not current_candidate_commit:
        return
    markers = []
    for part in path.parts:
        markers.extend(
            re.findall(r"(?<![0-9A-Fa-f])([0-9A-Fa-f]{40})(?![0-9A-Fa-f])", part)
        )
    for marker in sorted(set(markers)):
        if marker != marker.lower():
            fail(
                "proof-grade release transcript path commit marker must be lowercase: "
                f"{marker}"
            )
        elif marker != current_candidate_commit:
            fail(
                "proof-grade release transcript path commit marker "
                f"{marker} does not match current candidate commit "
                f"{current_candidate_commit}: {path}"
            )

def validate_row(row, index, current_candidate_commit):
    row_label = f"accepted_proof_grade_rows[{index}]"
    if not isinstance(row, dict):
        fail(f"{row_label}: row must be a JSON object")
        return

    validate_no_synthetic_fixture_markers(row, row_label)
    validate_known_fields(row, ROW_FIELDS, row_label)
    for field in sorted(ROW_FIELDS - {"rejection_reason", "aarch64_ordering_monitor_evidence"}):
        require_present(row, field, row_label)

    if row.get("schema_version") != ROW_SCHEMA_VERSION:
        fail(f"{row_label}: schema_version must be {ROW_SCHEMA_VERSION}")
    if row.get("row_type") != ROW_TYPE:
        fail(f"{row_label}: row_type must be {ROW_TYPE}")
    if row.get("evidence_origin") != REAL_EVIDENCE_ORIGIN:
        fail(f"{row_label}: evidence_origin must be {REAL_EVIDENCE_ORIGIN}")
    if row.get("status") != "accepted":
        fail(f"{row_label}: status must be accepted")
    if row.get("accepted") is not True:
        fail(f"{row_label}: accepted must be true")
    if "rejection_reason" not in row:
        fail(f"{row_label}: rejection_reason must be present as explicit null for accepted rows")
    elif row.get("rejection_reason") is not None:
        fail(f"{row_label}: rejection_reason must be explicit null for accepted rows")
    candidate_commit = row.get("candidate_commit")
    if not isinstance(candidate_commit, str) or COMMIT_RE.fullmatch(candidate_commit) is None:
        fail(f"{row_label}: candidate_commit must be a full 40-character lowercase git commit")
    elif current_candidate_commit and candidate_commit != current_candidate_commit:
        fail(
            f"{row_label}: candidate_commit {candidate_commit} does not match "
            f"current candidate commit {current_candidate_commit}"
        )
    proof_required_vc_count = validate_proof_required_vc_count(row, row_label)
    if not is_digest(row.get("binary_digest")):
        fail(f"{row_label}: binary_digest must be a canonical sha256:<hex> digest")
    if not is_digest(row.get("release_transcript_binding_digest")):
        fail(
            f"{row_label}: release_transcript_binding_digest must be a canonical sha256:<hex> digest"
        )
    else:
        expected_binding_digest = row_binding_digest(row)
        if row.get("release_transcript_binding_digest") != expected_binding_digest:
            fail(
                f"{row_label}: release_transcript_binding_digest "
                f"{row.get('release_transcript_binding_digest')} does not match "
                f"canonical row binding digest {expected_binding_digest} "
                f"using {ROW_BINDING_PROFILE_ID}"
            )

    selected_image = row.get("selected_image")
    if not isinstance(selected_image, dict):
        fail(f"{row_label}: selected_image must identify the replayed image")
    else:
        validate_known_fields(selected_image, SELECTED_IMAGE_FIELDS, f"{row_label}: selected_image")
        for field in sorted(SELECTED_IMAGE_FIELDS):
            require_present(selected_image, field, f"{row_label}: selected_image")
        if not is_nonempty_string(selected_image.get("identity")):
            fail(f"{row_label}: selected_image.identity must be non-empty")
        if not is_digest(selected_image.get("digest")):
            fail(f"{row_label}: selected_image.digest must be a canonical sha256:<hex> digest")

    vc_entries = validate_vc_digest_inventory(row, row_label, proof_required_vc_count)
    validate_checked_certificate_digest_inventory(
        row,
        row_label,
        proof_required_vc_count,
        vc_entries,
    )

    for field in SIMPLE_DIGEST_LISTS:
        validate_digest_list(row, field, row_label)

    if row.get("unsupported_ledgers_empty") is not True:
        fail(f"{row_label}: unsupported_ledgers_empty must be true")
    validate_required_evidence_digest(row, "exact_source_ownership_evidence", row_label)
    validate_required_evidence_digest(row, "type_ownership_evidence", row_label)
    validate_aarch64_ordering_monitor_evidence(row, row_label)
    validate_blockers(row, row_label)

def validate_unique_accepted_rows(rows):
    seen_binding_digests = {}
    seen_identities = {}
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            continue
        binding_digest = row.get("release_transcript_binding_digest")
        if is_digest(binding_digest):
            previous = seen_binding_digests.get(binding_digest)
            if previous is not None:
                fail(
                    f"accepted_proof_grade_rows[{index}]: release_transcript_binding_digest "
                    f"duplicates accepted_proof_grade_rows[{previous}]"
                )
            else:
                seen_binding_digests[binding_digest] = index
        identity = accepted_row_identity(row)
        if identity is None:
            continue
        previous = seen_identities.get(identity)
        if previous is not None:
            fail(
                f"accepted_proof_grade_rows[{index}]: duplicate/ambiguous accepted row "
                f"identity also used by accepted_proof_grade_rows[{previous}]"
            )
        else:
            seen_identities[identity] = index

def validate_transcript(path_arg):
    path = pathlib.Path(path_arg)
    if not path.is_file():
        fail(f"TRUST_PROOF_GRADE_RELEASE_TRANSCRIPT does not name a file: {path}")
        return 0
    actual_transcript_digest = transcript_artifact_digest(path)
    if not transcript_digest_arg:
        fail(
            "TRUST_PROOF_GRADE_RELEASE_TRANSCRIPT_DIGEST is required to bind "
            "the proof-grade release transcript artifact bytes"
        )
    elif not is_digest(transcript_digest_arg):
        fail(
            "TRUST_PROOF_GRADE_RELEASE_TRANSCRIPT_DIGEST must be a canonical "
            "sha256:<hex> digest"
        )
    elif transcript_digest_arg != actual_transcript_digest:
        fail(
            "TRUST_PROOF_GRADE_RELEASE_TRANSCRIPT_DIGEST "
            f"{transcript_digest_arg} does not match transcript artifact digest "
            f"{actual_transcript_digest}"
        )
    try:
        transcript = json.loads(
            path.read_text(encoding="utf-8"),
            object_pairs_hook=reject_duplicate_keys,
            parse_constant=reject_nonfinite_json_constant,
        )
    except DuplicateKeyError as exc:
        fail(f"proof-grade release transcript contains duplicate JSON key: {exc}")
        return 0
    except NonFiniteJsonConstantError as exc:
        fail(f"proof-grade release transcript contains non-finite JSON constant: {exc}")
        return 0
    except json.JSONDecodeError as exc:
        fail(f"proof-grade release transcript is not valid JSON: {path}: {exc}")
        return 0
    if not isinstance(transcript, dict):
        fail("proof-grade release transcript must be a JSON object")
        return 0
    validate_known_fields(transcript, TRANSCRIPT_FIELDS, "proof-grade release transcript")
    require_present(transcript, "schema_version", "proof-grade release transcript")
    require_present(transcript, "accepted_proof_grade_rows", "proof-grade release transcript")
    if transcript.get("schema_version") != TRANSCRIPT_SCHEMA_VERSION:
        fail(f"proof-grade release transcript schema_version must be {TRANSCRIPT_SCHEMA_VERSION}")
    rows = transcript.get("accepted_proof_grade_rows")
    if not isinstance(rows, list):
        fail("proof-grade release transcript missing accepted_proof_grade_rows list")
        return 0
    blocked_rows = transcript.get("blocked_proof_grade_rows", [])
    if not isinstance(blocked_rows, list):
        fail("proof-grade release transcript blocked_proof_grade_rows must be a list when present")
    elif blocked_rows:
        fail(
            "proof-grade release transcript blocked_proof_grade_rows must be empty "
            "for release artifacts"
        )
    current_candidate_commit = resolve_current_candidate_commit()
    validate_transcript_path_commit(path, current_candidate_commit)
    for index, row in enumerate(rows):
        validate_row(row, index, current_candidate_commit)
    validate_unique_accepted_rows(rows)
    if rows:
        print(
            f"Proof-grade release transcript: validated {len(rows)} accepted row(s) "
            f"with {ROW_BINDING_PROFILE_ID} and artifact digest {actual_transcript_digest}"
        )
    else:
        print("Proof-grade release transcript: no accepted proof-grade rows")
    return len(rows)

accepted_rows = 0
if transcript_arg:
    accepted_rows = validate_transcript(transcript_arg)
elif claim_requested:
    fail("public proof-grade claim requested without TRUST_PROOF_GRADE_RELEASE_TRANSCRIPT")
    fail("producer blockers remain explicit: " + ", ".join(PRODUCER_BLOCKERS))
else:
    print("Proof-grade release transcript: not supplied; no public proof-grade claim requested")

if claim_requested and transcript_arg and accepted_rows == 0:
    fail("public proof-grade claim requires at least one accepted proof-grade transcript row")

if failures:
    print("FAIL: proof-grade release sentinel/accounting is incomplete", file=sys.stderr)
    for failure in failures:
        print(f"  - {failure}", file=sys.stderr)
    raise SystemExit(2)

if claim_requested:
    print("Proof-grade release sentinel: public claim allowed by all-green checklist and content-addressed transcript")
else:
    print("Proof-grade release sentinel: public proof-grade claim not requested")
PY
}

usage() {
    cat <<'USAGE'
Usage: tests/run_trust_superset_suite.sh [review|quick|trust-compat|upstream-rust-porting|trust-added-compiletest|trustc-native|trust-extra|binary-decompilation-golden|native-contracts-pipeline-v2|release]

Default: review. A no-argument run is the fresh-clone reviewer path for the
standalone Trust toolchain. It builds stage2 and runs Trust-owned verification
gates only. It does not run public upload, publication, installed-rustup, or
full upstream Rust compatibility lanes.

Modes:
  review         Fresh-clone Trust-owned proof path: stage2 build,
                 trustc-native, binary-decompilation-golden,
                 native-contracts-pipeline-v2, and trust-extra.
  quick          Fast tRust crate/unit feedback only.
  trust-compat   Focused inherited upstream compatibility smoke corpus for the trust toolchain.
  upstream-rust-porting
                 Local compatibility wrapper that delegates to the canonical
                 Rust-owned `targo trust domination upstream-tests` command.
                 It re-imports upstream Rust tests into an out-of-tree overlay,
                 applies the reviewed patch manifest with JSONL/Markdown audit
                 logs, then executes the full upstream compatibility suite
                 or parses an existing execution log to write a failure
                 scorecard. Defaults:
                 TRUST_UPSTREAM_RUST_PORT_REVISION=rust-lang/rust:HEAD,
                 TRUST_UPSTREAM_RUST_PORT_REMOTE=https://github.com/rust-lang/rust.git,
                 TRUST_UPSTREAM_RUST_PORT_OUT=reports/upstream-rust/porting/current,
                 TRUST_UPSTREAM_RUST_PORT_EXECUTE=1,
                 TRUST_UPSTREAM_RUST_PORT_APPLY=1,
                 TRUST_UPSTREAM_RUST_PORT_FETCH=1, and
                 TRUST_UPSTREAM_RUST_PORT_RELEASE=$TRUST_RELEASE_GATE.
                 TRUST_UPSTREAM_RUST_PORT_TEST_EXCEPTIONS defaults to
                 tests/upstream-rust/test-exceptions.toml.
                 TRUST_UPSTREAM_RUST_PORT_PATCH_MANIFEST defaults to
                 tests/upstream-rust/patches.toml and is reapplied after each
                 upstream refetch/import.
                 TRUST_UPSTREAM_RUST_PORT_LLM_DIRECTIVES overrides the default
                 out-dir llm-directives.md handoff artifact.
                 TRUST_UPSTREAM_RUST_PORT_PROOF_MODE=auto resolves bounded
                 TRUST_UPSTREAM_RUST_PORT_MAX_FILES runs to smoke proof and
                 unbounded runs to full proof.
                 TRUST_UPSTREAM_RUST_PORT_BOOTSTRAP_ARGS supplies extra direct
                 bootstrap args for execution (default: --set llvm.ninja=false).
                 Shell-wrapper transcripts are local diagnostics only; release
                 evidence must cite the Rust-owned
                 `targo trust domination upstream-tests` front door, backed by
                 the internal trust-upstream-compat port engine.
                 Set
                 TRUST_UPSTREAM_RUST_PORT_LOG to scorecard an existing log and
                 TRUST_UPSTREAM_RUST_PORT_EXECUTE=0 for audit-only/log-parse
                 iteration. Set TRUST_UPSTREAM_RUST_PORT_APPLY=0 when you
                 want to review the adapter audit before mutating tests/; the
                 apply path refuses dirty tests/ changes. Successful execute
                 writes trust-upstream-compat inventory/results/proof
                 artifacts under the porting out-dir proof/ subdirectory.
  trust-added-compiletest
                 Local diagnostic for compiletest primary files present in
                 tRust but absent from the audited upstream Rust baseline.
  trustc-native  Local trustc/native verification transport diagnostic.
  trust-extra    Local tRust-only verifier/backend/corpus diagnostic.
  binary-decompilation-golden
                 Build targo-trust and validate focused binary CLI JSON/terminal evidence.
  native-contracts-pipeline-v2
                 First #1049 hook for native Trust contracts: dispatches
                 focused native compiler transport, basic contract corpus
                 smoke checks, and the Formula-family owner matrix backed by
                 crates/trust-router/tests/formula_compat_gate.rs. Also checks
                 source-recovery evidence that normal verification uses
                 compiler-owned contract bundles and does not source-scrape by
                 default; fails closed if required subchecks, Formula evidence,
                 or source-recovery evidence are absent. This is not a full
                 Pipeline v2 release-evidence claim.
  release        Fail-closed canonical release-inventory entrypoint. It does
                 not execute weaker shell diagnostics. The named trust-added
                 release commands remain blocked until independently
                 authenticated native execution authority exists.

Internal compatibility/accounting mode:
  upstream-rust-compat
                 Legacy accounting-only gate for production ledgers,
                 crates/trust-upstream-compat, and standalone fixtures. Do not
                 cite this as release-facing upstream test porting evidence;
                 use `targo trust domination upstream-tests`.

Review/release modes review, upstream-rust-porting,
trustc-native, trust-extra, binary-decompilation-golden,
native-contracts-pipeline-v2, and release fail on unexpected SKIP lines by
default. Set
TRUST_ALLOW_REVIEW_GATE_SKIPS=1 only for local development runs where skipped
e2e coverage is intentional.
Set TRUST_STRICT=1 to apply the same skip handling to other wrapped modes.
Set TRUST_UPSTREAM_RUST_PORT_REVISION to select the upstream revision for the
canonical porting gate. Set TRUST_UPSTREAM_RUST_PORT_BOOTSTRAP_ARGS to override
the default extra Rust bootstrap args (`--set llvm.ninja=false`). The internal
accounting wrapper runs through Trust-owned `targo` without verifier-disabling
rustflags; verification suppression belongs only in explicit negative tests.
Trust-owned targo invocations use the canonical repo-local stage2 `targo`.
Review/release evidence requires the complete repo-local stage2 Trust toolchain:
canonical Trust entrypoints plus Rust-compatible aliases in the same bin dir.
Set TRUST_SUPERSET_ASSUME_STAGE2=1 only when a containing harness has already
run `./x.py build --stage 2`; the suite still fails closed if that stage2
toolchain is incomplete.
Set TRUST_RELEASE_GATE=1 to turn on additional proof-grade native verification
checks in release evidence paths.
Set TRUST_PUBLIC_PROOF_GRADE_CLAIM=1 only when release wording claims public
proof-grade binary decompilation; the checklist sentinel must have every
current blocker marked green and TRUST_PROOF_GRADE_RELEASE_TRANSCRIPT must
point at a JSON transcript. TRUST_PROOF_GRADE_RELEASE_TRANSCRIPT_DIGEST must
bind the exact transcript artifact bytes as sha256:<lowercase-hex>. The
transcript accepted rows must be typed content-addressed
views over real targo_trust_release_export origin, schema, commit, binary,
selected-image, complete VC digest
inventories, complete checked-certificate readback inventories, replay,
provenance, unsupported-ledger, exact source/type ownership, empty blockers,
and target proof-consumer evidence.
Each accepted row's release_transcript_binding_digest uses
trust.proof-grade-row-binding.v1: SHA-256 over the targo-trust producer
ProofGradeReleaseTranscriptRowBindingProfile JSON with compact separators,
UTF-8 bytes, producer field order, and lowercase sha256:<hex> output.
USAGE
}

echo "=== tRust Superset Test Suite ($MODE) ==="

superset_local_diagnostic_mode() {
    case "$MODE" in
        review|quick|trust-added-compiletest|trustc-native|trust-extra|binary-decompilation-golden|native-contracts-pipeline-v2)
            return 0
            ;;
        *)
            return 1
            ;;
    esac
}

case "$MODE" in
    review)
        section "Fresh-clone Trust reviewer proof"
        echo "Scope: standalone Trust-owned stage2 build and default verification gates."
        echo "Not included: public upload, publication, rustup install rehearsal, full upstream Rust compatibility, or legacy Rust-named public entrypoints."
        run_stage2_build_for_suite
        run env TRUST_STRICT=1 bash "$TRUST_ROOT/tests/run_trust_superset_suite.sh" trustc-native
        run env TRUST_STRICT=1 bash "$TRUST_ROOT/tests/run_trust_superset_suite.sh" binary-decompilation-golden
        run env TRUST_STRICT=1 bash "$TRUST_ROOT/tests/run_trust_superset_suite.sh" native-contracts-pipeline-v2
        run env TRUST_STRICT=1 bash "$TRUST_ROOT/tests/run_trust_superset_suite.sh" trust-extra
        ;;
    quick)
        section "Fast trust crate feedback"
        run run_dev_test_lib
        section "Standalone temporal specification corpus"
        run_no_unexpected_skip trust_cargo test \
            --manifest-path "$TRUST_ROOT/crates/trust-spec-temporal/Cargo.toml" \
            --locked
        run trust_cargo test --manifest-path "$TRUST_ROOT/targo-trust/Cargo.toml"
        ;;
    trust-compat)
        section "Trust compatibility corpus"
        run_stage2_build_for_suite
        run_full_upstream_rust_suite
        ;;
    upstream-rust-compat)
        run_upstream_rust_compat
        ;;
    upstream-rust-porting)
        run_upstream_rust_porting
        ;;
    trust-added-compiletest)
        run_trust_added_compiletest_suite
        ;;
    trustc-native)
        section "trustc native verification transport"
        run_no_unexpected_skip bash "$TRUST_ROOT/tests/e2e_compiler_verify.sh"
        run_no_unexpected_skip bash "$TRUST_ROOT/tests/e2e_targo_trust_cli.sh"
        run_no_unexpected_skip bash "$TRUST_ROOT/tests/e2e_targo_trust_root_resolution.sh"
        ;;
    trust-extra)
        section "Verifier-example regression diagnostic (not proof or release evidence)"
        echo "Local diagnostic configuration: stage2 Trust compiler with default verification; source/tool provenance is unauthenticated"
        run_no_unexpected_skip env -u TRUST_RELEASE_GATE TRUST_COMPLETE_CORPUS_DIAGNOSTIC="$RELEASE_GATE" bash "$TRUST_ROOT/tests/e2e_verify_suite.sh"
        # The trust-cg half of this mode is `targo trust domination trust-added
        # --release trust-extra`, whose `trust_cg_parity` sub-check compares the
        # two backends at the metadata level. This shell mode never had one: it
        # dispatched a script that was never written, so the 127 made the lane
        # structurally unable to report green.
        section "Trust crate/library corpus"
        run run_dev_test_lib
        section "Standalone temporal specification corpus"
        run_no_unexpected_skip trust_cargo test \
            --manifest-path "$TRUST_ROOT/crates/trust-spec-temporal/Cargo.toml" \
            --locked
        section "Full-verifier three-suite sample"
        run_no_unexpected_skip bash "$TRUST_ROOT/tests/e2e_full_verifier_three_suite_sample.sh"
        ;;
    binary-decompilation-golden)
        section "Binary decompilation golden JSON"
        echo "Scope: decompile/convert golden JSON, verify-binary proof-evidence JSON/terminal summaries, exact-byte replay unit gates, checked binary certificate gates, and fail-closed unsupported binary targets. Exploit confirmation remains a separate gap."
        section "Public proof-grade claim sentinel"
        require_proof_grade_release_sentinel
        run_with_release_gate_lockfile_stability "binary-decompilation-golden" \
            run_no_unexpected_skip bash "$TRUST_ROOT/tests/e2e_binary_decompilation_golden_json.sh"
        ;;
    native-contracts-pipeline-v2)
        section "Native Trust contract Pipeline v2 hook"
        echo "Scope: first #1049 runner hook only. This dispatches focused native transport, basic contract corpus, and Formula-family owner checks; it does not claim full Pipeline v2 release validation."
        section "Formula-family native owner matrix"
        echo "Evidence: $FORMULA_COMPAT_EVIDENCE"
        require_formula_owner_matrix
        section "Contract source-recovery fail-closed evidence"
        echo "Evidence: $CONTRACT_SOURCE_RECOVERY_EVIDENCE"
        require_contract_source_recovery_evidence
        require_subcheck e2e_compiler_verify.sh
        require_subcheck e2e_targo_trust_cli.sh
        require_subcheck e2e_targo_trust_root_resolution.sh
        require_subcheck e2e_basic_contracts_smoke.sh
        run_no_unexpected_skip bash "$TRUST_ROOT/tests/e2e_compiler_verify.sh"
        run_no_unexpected_skip bash "$TRUST_ROOT/tests/e2e_targo_trust_cli.sh"
        run_no_unexpected_skip bash "$TRUST_ROOT/tests/e2e_targo_trust_root_resolution.sh"
        run_no_unexpected_skip bash "$TRUST_ROOT/tests/e2e_basic_contracts_smoke.sh"
        run_no_unexpected_skip trust_cargo test -p trust-router --test formula_compat_gate
        ;;
    release)
        section "Canonical release inventory (fail-closed)"
        echo "The legacy superset harness cannot promote local diagnostics to release evidence."
        run env TRUST_RELEASE_GATE=1 bash "$TRUST_ROOT/tests/run_trust_robust_suite.sh" prepublish
        echo "FAIL: canonical prepublish unexpectedly returned success" >&2
        exit 2
        ;;
    -h|--help|help)
        usage
        exit 0
        ;;
    *)
        usage >&2
        exit 2
        ;;
esac

echo
if superset_local_diagnostic_mode; then
    echo "=== tRust Superset Test Suite ($MODE): LOCAL DIAGNOSTIC PASS (non-authoritative) ==="
else
    echo "=== tRust Superset Test Suite ($MODE): PASS ==="
fi
