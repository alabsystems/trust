#!/bin/bash
# Comprehensive Trust replacement test harness.
#
# The default profile is the release profile. It is intentionally expensive:
# it builds the standalone Trust toolchain, runs the upstream Rust compatibility
# path, runs Trust-specific proof gates, runs install/dist gates, and writes a
# machine-readable report. Manifest and quick profiles exist only to validate
# the harness itself during development; they are not replacement evidence.

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
MODE="${1:-release}"
RUN_STARTED_AT="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
RUN_ID="${TRUST_COMPREHENSIVE_RUN_ID:-$(date -u '+comprehensive-%Y%m%dT%H%M%SZ')}"
OUT_DIR="${TRUST_COMPREHENSIVE_OUT_DIR:-$TRUST_ROOT/reports/trust-comprehensive/$RUN_ID}"
LOG_DIR="$OUT_DIR/logs"
RESULTS_TSV="$OUT_DIR/results.tsv"
REPORT_JSON="$OUT_DIR/report.json"
REPORT_MD="$OUT_DIR/report.md"
DIVERGENCE_LEDGER="$TRUST_ROOT/tests/trust-comprehensive/divergences.toml"
DEFAULT_FAIL_FAST=0
[ "$MODE" = "release" ] && DEFAULT_FAIL_FAST=1
FAIL_FAST="${TRUST_COMPREHENSIVE_FAIL_FAST:-$DEFAULT_FAIL_FAST}"

usage() {
    cat <<'USAGE'
Usage: tests/run_trust_comprehensive_harness.sh [release|quick|fast|suites|slow|manifest|list|--list|--help]

Profiles:
  release   Full replacement evidence path. This is the default.
  quick     Fast local confidence path. Not replacement evidence.
  fast      Everything that needs no stage2 build: drift, supply-chain,
            style/lint ratchets, workspace compile, script tests, and the
            payload-independent js262 lanes. This is the pre-push tier.
  suites    The compiletest suites, one gate per suite, in Trust mode.
  slow      Overnight lanes: Clean-kernel re-derivation, js262 calibration.
  manifest  Static harness/script/ledger checks only. Not replacement evidence.
  list      Print the selected profile's gate manifest without executing it.

Outputs:
  reports/trust-comprehensive/<run-id>/results.tsv
  reports/trust-comprehensive/<run-id>/report.json
  reports/trust-comprehensive/<run-id>/report.md

The harness never uploads or publishes artifacts. Any gate that prepares
publication evidence must stop at local/internal dry-run or rehearsal evidence.
USAGE
}

case "$MODE" in
    -h|--help|help)
        usage
        exit 0
        ;;
    --list|list)
        MODE="${2:-release}"
        ;;
    release|quick|fast|suites|slow|manifest)
        ;;
    *)
        usage >&2
        exit 2
        ;;
esac

case "$FAIL_FAST" in
    0|1)
        ;;
    *)
        echo "FAIL: TRUST_COMPREHENSIVE_FAIL_FAST must be 0 or 1 (got: $FAIL_FAST)" >&2
        exit 2
        ;;
esac

timestamp_utc() {
    date -u '+%Y-%m-%dT%H:%M:%SZ'
}

epoch_seconds() {
    date '+%s'
}

safe_log_name() {
    printf '%s' "$1" | tr -c 'A-Za-z0-9_.-' '_'
}

gate_selected() {
    local profiles="$1"
    case ",$profiles," in
        *",all,"*|*",$MODE,"*)
            return 0
            ;;
        *)
            return 1
            ;;
    esac
}

# The `trust.examples.complete-corpus-diagnostic` row remains a required
# release-profile regression tripwire. Its success is not evidence: the report
# serializer hard-codes `non-evidence-regression-diagnostic` to false proof and
# release-evidence flags and the distinct `diagnostic_passed` status.
# THE MANIFEST IS THE INVENTORY. A lane that exists in the tree but appears in
# no row below is a lane nobody runs, so `manifest.lane-coverage` walks the
# on-disk lane inventory and fails when a lane is unnamed here. Adding a gate
# script, an e2e, a witness/elide regression, or a compiletest suite without a
# row is therefore a hard error, not a silent omission.
#
# Columns: gate_id|profiles|category|required|last_green|command
#
# `last_green` is the ISO date of the most recent observed PASS, or `never`
# when this manifest has never recorded one. It is deliberately not inferred:
# a lane that has run green somewhere untracked still reads `never` here, which
# is the honest statement that the manifest has no evidence. A run prints a
# `LAST-GREEN` line for every gate whose recorded date it just superseded.
emit_gate_manifest() {
    cat <<'EOF'
manifest.syntax.comprehensive|all|harness|true|2026-07-25|bash -n tests/run_trust_comprehensive_harness.sh
manifest.syntax.superset|all|harness|true|2026-07-25|bash -n tests/run_trust_superset_suite.sh
manifest.syntax.robust|all|harness|true|2026-07-25|bash -n tests/run_trust_robust_suite.sh
manifest.syntax.targo-cli|all|harness|true|2026-07-25|bash -n tests/e2e_targo_trust_cli.sh
manifest.syntax.targo-root-resolution|all|harness|true|2026-07-25|bash -n tests/e2e_targo_trust_root_resolution.sh
manifest.syntax.run-tests-after-build-failclosed|all|harness|true|2026-07-25|bash -n tests/e2e_run_tests_after_build_fail_closed.sh
manifest.syntax.gate-scripts|all|harness|true|2026-07-25|bash scripts/check_gate_script_syntax.sh
manifest.ledgers|all|harness|true|2026-07-25|test -f tests/upstream-rust/test-exceptions.toml && test -f tests/upstream-rust/patches.toml && test -f tests/upstream-rust/divergence-audit.toml && test -f tests/trust-added/compiletest-exceptions.toml && test -f tests/trust-added/manifest.toml && test -f tests/trust-comprehensive/divergences.toml
manifest.canonical-targo-e2e-names|all|harness|true|2026-07-25|test -x tests/e2e_targo_trust_cli.sh && test -x tests/e2e_targo_trust_root_resolution.sh && test ! -e tests/e2e_cargo_trust_cli.sh && test ! -e tests/e2e_cargo_trust_root_resolution.sh
manifest.lane-coverage|all|harness|true|2026-07-25|python3 scripts/check_gate_lane_coverage.py
fast.ledger-expirations|fast|ledger|true|2026-07-25|python3 scripts/check_ledger_expirations.py --warn-days 14
fast.pr-gate|fast|drift|true|2026-07-25|bash scripts/pr_gate.sh
fast.pin-coherence|fast|supply-chain|true|2026-07-25|bash scripts/check_pin_coherence.sh
fast.bridge-pin|fast|supply-chain|true|never|bash scripts/check_bridge_pin.sh --check
fast.tcb-panic-freedom|fast|soundness|true|2026-07-25|bash scripts/check_tcb_panic_freedom.sh
fast.tcb-document-exhaustiveness|fast|soundness|true|never|RUSTC_BOOTSTRAP=1 cargo test --manifest-path crates/Cargo.toml -p trust-integration-tests --test tcb_document_exhaustiveness --locked
fast.tcb-direct-trust-vc-certificate-boundary|fast|soundness|true|never|RUSTC_BOOTSTRAP=1 cargo test --manifest-path crates/Cargo.toml -p trust-vc-bridge --features trust-build direct_mir_memory_admission_binds_the_alethe_certificate_but_never_rechecks_it --locked
fast.tcb-direct-trust-vc-kernel-shape|fast|soundness|true|never|RUSTC_BOOTSTRAP=1 cargo test --manifest-path crates/Cargo.toml -p trust-certify --test direct_trust_vc_lane_shape --locked
fast.tidy|fast|style|true|2026-07-25|python3 x.py test --stage 1 src/tools/tidy
fast.crates-workspace-check|fast|compile|true|never|RUSTC_BOOTSTRAP=1 cargo check --manifest-path crates/Cargo.toml --workspace --all-targets --keep-going --locked
fast.targo-trust-check|fast|compile|true|never|RUSTC_BOOTSTRAP=1 cargo check --manifest-path targo-trust/Cargo.toml --all-targets --keep-going --locked
fast.compiler-check|fast|compile|true|2026-07-25|RUSTC_BOOTSTRAP=1 python3 x.py check --stage 1 compiler
fast.js262-corpus-verify|fast|trustjs|true|never|RUSTC_BOOTSTRAP=1 cargo run --manifest-path crates/Cargo.toml -p trust-js-differential -- corpus-verify
fast.js262-ledger-validate|fast|trustjs|true|never|RUSTC_BOOTSTRAP=1 cargo run --manifest-path crates/Cargo.toml -p trust-js-differential -- validate
fast.js262-selftest|fast|trustjs|true|never|RUSTC_BOOTSTRAP=1 cargo run --manifest-path crates/Cargo.toml -p trust-js-differential -- selftest
scripts.tests.suite|fast|script-tests|true|never|bash scripts/check_script_tests.sh
quick.targo-domination-unit|quick|harness|true|never|cargo test --manifest-path targo-trust/Cargo.toml trust_added_dispatch_accepts_full_verify_trust_compat_mode
quick.superset|quick|verification|true|never|bash tests/run_trust_superset_suite.sh quick
quick.robust-smoke|quick|compatibility|true|never|bash tests/run_trust_robust_suite.sh smoke
quick.crates-lib-tests|quick|crates|true|never|RUSTC_BOOTSTRAP=1 cargo test --manifest-path crates/Cargo.toml --workspace --lib --locked --no-fail-fast
quick.targo-trust-tests|quick|crates|true|never|RUSTC_BOOTSTRAP=1 cargo test --manifest-path targo-trust/Cargo.toml --locked --no-fail-fast
quick.compiler-unit-tests|quick|compile|true|never|RUSTC_BOOTSTRAP=1 python3 x.py test --stage 1 compiler/rustc_driver_impl compiler/rustc_session compiler/rustc_mir_transform
trust.added.quick|release|blocked-release-inventory|true|never|TRUST_RELEASE_GATE=1 bash tests/run_trust_robust_suite.sh quick
stage2.build|release|bootstrap|true|never|python3 x.py build --stage 2
upstream.trust-compat|release|upstream|true|never|TRUST_STRICT=1 TRUST_SUPERSET_ASSUME_STAGE2=1 bash tests/run_trust_superset_suite.sh trust-compat
upstream.porting|release|upstream|true|never|TRUST_STRICT=1 TRUST_RELEASE_GATE=1 TRUST_UPSTREAM_RUST_PORT_RELEASE=1 bash tests/run_trust_superset_suite.sh upstream-rust-porting
trust.examples.complete-corpus-diagnostic|release|non-evidence-regression-diagnostic|true|never|env -u TRUST_RELEASE_GATE TRUST_COMPLETE_CORPUS_DIAGNOSTIC=1 bash tests/e2e_verify_suite.sh
trust.added.compiletest|release|blocked-release-inventory|true|never|TRUST_RELEASE_GATE=1 bash tests/run_trust_robust_suite.sh trust-added-compiletest
trustc.native|release|blocked-release-inventory|true|never|TRUST_RELEASE_GATE=1 bash tests/run_trust_robust_suite.sh trustc-native
native-contracts.pipeline-v2|release|blocked-release-inventory|true|never|TRUST_RELEASE_GATE=1 bash tests/run_trust_robust_suite.sh native-contracts-pipeline-v2
trust.extra|release|blocked-release-inventory|true|never|TRUST_RELEASE_GATE=1 bash tests/run_trust_robust_suite.sh trust-extra
binary.decompilation-golden|release|blocked-release-inventory|true|never|TRUST_RELEASE_GATE=1 bash tests/run_trust_robust_suite.sh binary-decompilation-golden
semantic.parity|release|compatibility|true|never|bash tests/e2e_semantic_parity.sh
robust.launch|release|blocked-release-inventory|true|never|TRUST_RELEASE_GATE=1 bash tests/run_trust_robust_suite.sh launch
robust.public-distribution|release|blocked-release-inventory|true|never|TRUST_RELEASE_GATE=1 bash tests/run_trust_robust_suite.sh public-distribution
robust.prepublish|release|blocked-release-inventory|true|never|TRUST_RELEASE_GATE=1 bash tests/run_trust_robust_suite.sh prepublish
robust.installed|release|blocked-release-inventory|true|never|TRUST_RELEASE_GATE=1 bash tests/run_trust_robust_suite.sh installed
robust.installed-default|release|blocked-release-inventory|true|never|TRUST_RELEASE_GATE=1 bash tests/run_trust_robust_suite.sh installed-default
robust.stage0-lineage|release|blocked-release-inventory|true|never|TRUST_RELEASE_GATE=1 bash tests/run_trust_robust_suite.sh stage0-lineage
gate.status|release|reporting|true|never|bash tests/report_trust_gate_status.sh
integrated.full-verify|release|integrated|true|never|scripts/build.sh full-verify
verify.e2e-shell-corpus|release|e2e|true|never|bash scripts/run_e2e_shell_corpus.sh
verify.falsification|release|soundness|true|never|bash scripts/trust_falsification_gate.sh
verify.codegen|release|soundness|true|never|bash scripts/trust_codegen_gate.sh
verify.ownership|release|soundness|true|never|bash scripts/trust_ownership_gate.sh
verify.superiority|release|soundness|true|never|bash scripts/trust_superiority_gate.sh
verify.temporal|release|soundness|true|never|bash scripts/trust_temporal_gate.sh
verify.clean-certification|release|soundness|true|never|bash scripts/trust_clean_certification_gate.sh
witness.replay-regression|release|witness|true|never|python3 tests/trust-witness/replay_regression.py
witness.auto-router-smoke|release|witness|true|never|python3 tests/trust-witness/auto_router_smoke.py
witness.closure-parity-smoke|release|witness|true|never|python3 tests/trust-witness/closure_parity_smoke.py
witness.generics-parity-smoke|release|witness|true|never|python3 tests/trust-witness/generics_parity_smoke.py
witness.precise-parity-smoke|release|witness|true|never|python3 tests/trust-witness/precise_parity_smoke.py
elide.regression|release|elide|true|never|python3 tests/trust-elide/elide_regression.py
suite.ui|suites|compiletest|true|never|python3 x.py test --stage 2 tests/ui
suite.ui-fulldeps|suites|compiletest|true|never|python3 x.py test --stage 2 tests/ui-fulldeps
suite.crashes|suites|compiletest|true|never|python3 x.py test --stage 2 tests/crashes
suite.codegen-llvm|suites|compiletest|true|never|python3 x.py test --stage 2 tests/codegen-llvm
suite.codegen-units|suites|compiletest|true|never|python3 x.py test --stage 2 tests/codegen-units
suite.assembly-llvm|suites|compiletest|true|never|python3 x.py test --stage 2 tests/assembly-llvm
suite.incremental|suites|compiletest|true|never|python3 x.py test --stage 2 tests/incremental
suite.debuginfo|suites|compiletest|true|never|python3 x.py test --stage 2 tests/debuginfo
suite.mir-opt|suites|compiletest|true|never|python3 x.py test --stage 2 tests/mir-opt
suite.pretty|suites|compiletest|true|never|python3 x.py test --stage 2 tests/pretty
suite.run-make|suites|compiletest|true|never|python3 x.py test --stage 2 tests/run-make
suite.run-make-cargo|suites|compiletest|true|never|python3 x.py test --stage 2 tests/run-make-cargo
suite.build-std|suites|compiletest|true|never|python3 x.py test --stage 2 tests/build-std
suite.coverage|suites|compiletest|true|never|python3 x.py test --stage 2 tests/coverage
suite.coverage-run-rustdoc|suites|compiletest|true|never|python3 x.py test --stage 2 tests/coverage-run-rustdoc
suite.rustdoc-html|suites|compiletest|true|never|python3 x.py test --stage 2 tests/rustdoc-html
suite.rustdoc-ui|suites|compiletest|true|never|python3 x.py test --stage 2 tests/rustdoc-ui
suite.rustdoc-json|suites|compiletest|true|never|python3 x.py test --stage 2 tests/rustdoc-json
suite.rustdoc-js|suites|compiletest|true|never|python3 x.py test --stage 2 tests/rustdoc-js
suite.rustdoc-js-std|suites|compiletest|true|never|python3 x.py test --stage 2 tests/rustdoc-js-std
suite.rustdoc-gui|suites|compiletest|false|never|python3 x.py test --stage 2 tests/rustdoc-gui
slow.kernel-derivation|slow|kernel|true|never|bash scripts/trust_kernel_derivation_lane.sh
slow.js262-calibrate|slow|trustjs|true|never|bash scripts/js262/calibrate.sh
EOF
}

list_gates() {
    local gate_id profiles category required last_green command
    emit_gate_manifest \
        | while IFS='|' read -r gate_id profiles category required last_green command; do
        [ -n "$gate_id" ] || continue
        if gate_selected "$profiles"; then
            printf '%s\t%s\t%s\t%s\t%s\n' \
                "$gate_id" "$category" "$required" "$last_green" "$command"
        fi
    done
}

if [ "${1:-}" = "--list" ] || [ "${1:-}" = "list" ]; then
    list_gates
    exit 0
fi

mkdir -p "$LOG_DIR"
printf 'gate_id\tcategory\trequired\tlast_green\tstarted_at\tended_at\tduration_seconds\texit_code\tcommand\tlog_path\n' >"$RESULTS_TSV"

run_gate() {
    local gate_id="$1"
    local category="$2"
    local required="$3"
    local last_green="$4"
    local command="$5"
    local log_name log_path started_at ended_at started_epoch ended_epoch duration status

    log_name="$(safe_log_name "$gate_id").log"
    log_path="$LOG_DIR/$log_name"
    started_at="$(timestamp_utc)"
    started_epoch="$(epoch_seconds)"

    echo
    echo "=== gate: $gate_id ==="
    echo "category: $category"
    echo "last green: $last_green"
    echo "command:  $command"
    echo "log:      $log_path"

    set +e
    (
        cd "$TRUST_ROOT" || exit 2
        bash -o pipefail -c "$command"
    ) >"$log_path" 2>&1
    status=$?
    set -u

    ended_at="$(timestamp_utc)"
    ended_epoch="$(epoch_seconds)"
    duration=$((ended_epoch - started_epoch))

    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$gate_id" "$category" "$required" "$last_green" "$started_at" "$ended_at" \
        "$duration" "$status" "$command" "$log_path" >>"$RESULTS_TSV"

    if [ "$status" -eq 0 ]; then
        echo "status:   PASS (${duration}s)"
        if [ "$last_green" != "${started_at%%T*}" ]; then
            echo "LAST-GREEN: update the manifest row for $gate_id to ${started_at%%T*}"
        fi
    else
        echo "status:   FAIL exit=$status (${duration}s)"
        echo "--- tail: $log_path"
        tail -n 80 "$log_path" || true
        echo "--- end tail"
    fi

    return "$status"
}

selected_count=0
failed_count=0

while IFS='|' read -r gate_id profiles category required last_green command; do
    [ -n "$gate_id" ] || continue
    if ! gate_selected "$profiles"; then
        continue
    fi
    selected_count=$((selected_count + 1))
    run_gate "$gate_id" "$category" "$required" "$last_green" "$command"
    status=$?
    if [ "$status" -ne 0 ]; then
        failed_count=$((failed_count + 1))
        if [ "$FAIL_FAST" = "1" ]; then
            break
        fi
    fi
done < <(emit_gate_manifest)

if [ "$selected_count" -eq 0 ]; then
    echo "FAIL: no gates selected for profile $MODE" >&2
    exit 2
fi

RUN_ENDED_AT="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"

set +e
python3 - "$TRUST_ROOT" "$MODE" "$RUN_ID" "$RUN_STARTED_AT" "$RUN_ENDED_AT" \
    "$RESULTS_TSV" "$DIVERGENCE_LEDGER" "$REPORT_JSON" "$REPORT_MD" <<'PY'
import csv
import json
import os
import platform
import subprocess
import sys
from datetime import date
from pathlib import Path

try:
    import tomllib
except ModuleNotFoundError:  # pragma: no cover
    import tomli as tomllib

root = Path(sys.argv[1])
profile = sys.argv[2]
run_id = sys.argv[3]
started_at = sys.argv[4]
ended_at = sys.argv[5]
results_path = Path(sys.argv[6])
ledger_path = Path(sys.argv[7])
report_json = Path(sys.argv[8])
report_md = Path(sys.argv[9])


def run_git(*args: str) -> str | None:
    try:
        proc = subprocess.run(
            ["git", "-C", str(root), *args],
            check=False,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    except OSError:
        return None
    if proc.returncode != 0:
        return None
    return proc.stdout.strip()


def rel(path: str) -> str:
    p = Path(path)
    try:
        return str(p.relative_to(root))
    except ValueError:
        return str(p)


def load_ledger(path: Path) -> tuple[list[dict], list[str]]:
    if not path.exists():
        return [], [f"missing comprehensive divergence ledger: {rel(str(path))}"]
    try:
        data = tomllib.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:
        return [], [f"invalid comprehensive divergence ledger: {exc}"]
    errors: list[str] = []
    if data.get("schema_version") != "0.1.0":
        errors.append("comprehensive divergence ledger schema_version must be 0.1.0")
    divergences = data.get("divergences", [])
    if not isinstance(divergences, list):
        errors.append("comprehensive divergence ledger divergences must be a list")
        divergences = []
    return [d for d in divergences if isinstance(d, dict)], errors


def as_date(value):
    if isinstance(value, date):
        return value
    if isinstance(value, str):
        return date.fromisoformat(value)
    raise ValueError(f"not a date: {value!r}")


divergences, ledger_errors = load_ledger(ledger_path)
today = date.today()

rows: list[dict] = []
non_evidence_categories = {"non-evidence-regression-diagnostic"}
with results_path.open("r", encoding="utf-8", newline="") as fh:
    reader = csv.DictReader(fh, delimiter="\t")
    for row in reader:
        row["required"] = row["required"].lower() == "true"
        row["duration_seconds"] = int(row["duration_seconds"])
        row["exit_code"] = int(row["exit_code"])
        if row["category"] in non_evidence_categories:
            row["evidence_classification"] = "not_evidence"
            row["proof_evidence"] = False
            row["release_evidence"] = False
        else:
            # This harness does not infer evidence eligibility merely from an
            # unrecognized category. Dedicated consumers must classify it.
            row["evidence_classification"] = "unspecified"
            row["proof_evidence"] = None
            row["release_evidence"] = None
        rows.append(row)


def matching_divergences(row: dict) -> list[dict]:
    if row["exit_code"] == 0:
        return []
    matches: list[dict] = []
    for divergence in divergences:
        if divergence.get("status") != "active":
            continue
        if divergence.get("gate_id") != row["gate_id"]:
            continue
        try:
            expires_on = as_date(divergence["expires_on"])
        except Exception:
            continue
        if expires_on < today:
            continue
        allowed_exit_codes = divergence.get("allowed_exit_codes", [])
        if allowed_exit_codes and row["exit_code"] not in allowed_exit_codes:
            continue
        patterns = divergence.get("allowed_patterns", [])
        if patterns:
            try:
                log_text = Path(row["log_path"]).read_text(encoding="utf-8", errors="replace")
            except OSError:
                continue
            if not any(pattern in log_text for pattern in patterns):
                continue
        matches.append(divergence)
    return matches


for row in rows:
    row["log_path"] = rel(row["log_path"])
    matching = matching_divergences(row)
    if row["exit_code"] == 0:
        row["status"] = (
            "diagnostic_passed"
            if row["evidence_classification"] == "not_evidence"
            else "passed"
        )
    elif matching:
        row["status"] = "documented_divergence"
        row["divergence_ids"] = [divergence.get("id") for divergence in matching]
        row["divergence_issues"] = [divergence.get("issue") for divergence in matching]
        row["divergence_expires_on"] = sorted(
            {str(divergence.get("expires_on")) for divergence in matching}
        )
        row["divergence_id"] = ", ".join(row["divergence_ids"])
    else:
        row["status"] = "failed"

counts: dict[str, int] = {}
for row in rows:
    counts[row["status"]] = counts.get(row["status"], 0) + 1

required_failed = [row for row in rows if row["required"] and row["status"] == "failed"]
required_divergent = [
    row for row in rows if row["required"] and row["status"] == "documented_divergence"
]

if ledger_errors:
    verdict = "failed_harness_ledger"
elif required_failed:
    verdict = "failed_undocumented"
elif required_divergent:
    verdict = "blocked_documented_divergence"
else:
    verdict = "passed"

report = {
    "schema_version": "trust.comprehensive-test-harness.v1",
    "run_id": run_id,
    "profile": profile,
    "started_at": started_at,
    "ended_at": ended_at,
    "verdict": verdict,
    "host": {
        "platform": platform.platform(),
        "machine": platform.machine(),
        "python": platform.python_version(),
    },
    "git": {
        "commit": run_git("rev-parse", "HEAD"),
        "branch": run_git("branch", "--show-current"),
        "status_porcelain": run_git("status", "--porcelain=v1"),
    },
    "policy": {
        "public_uploads_allowed": False,
        "default_profile_is_release": True,
        "documented_divergence_blocks_replacement_claim": True,
        "non_evidence_categories": sorted(non_evidence_categories),
        "non_evidence_success_can_block_but_never_satisfies_evidence": True,
        "upstream_per_test_ledger": "tests/upstream-rust/test-exceptions.toml",
        "trust_added_compiletest_ledger": "tests/trust-added/compiletest-exceptions.toml",
        "command_divergence_ledger": rel(str(ledger_path)),
    },
    "summary": {
        "total": len(rows),
        "counts": counts,
        "evidence_eligible_passed": sum(
            1
            for row in rows
            if row["status"] == "passed"
            and row["evidence_classification"] != "not_evidence"
        ),
        "non_evidence_diagnostic_passed": sum(
            1 for row in rows if row["status"] == "diagnostic_passed"
        ),
        "ledger_errors": ledger_errors,
    },
    "gates": rows,
}

report_json.parent.mkdir(parents=True, exist_ok=True)
report_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")

lines = [
    "# Trust Comprehensive Harness Report",
    "",
    f"- Run id: `{run_id}`",
    f"- Profile: `{profile}`",
    f"- Verdict: `{verdict}`",
    f"- Commit: `{report['git']['commit'] or 'unknown'}`",
    f"- Started: `{started_at}`",
    f"- Ended: `{ended_at}`",
    f"- Command divergence ledger: `{rel(str(ledger_path))}`",
    "",
    "Public uploads are forbidden and were not part of this harness contract.",
    "A required non-evidence diagnostic can block this run, but its success is not proof or release evidence.",
    "",
    "## Gate Results",
    "",
    "| Gate | Category | Evidence | Status | Exit | Seconds | Log |",
    "| --- | --- | --- | --- | ---: | ---: | --- |",
]
for row in rows:
    lines.append(
        f"| `{row['gate_id']}` | `{row['category']}` | "
        f"`{row['evidence_classification']}` | `{row['status']}` | {row['exit_code']} | "
        f"{row['duration_seconds']} | `{row['log_path']}` |"
    )

if ledger_errors:
    lines.extend(["", "## Harness Ledger Errors", ""])
    lines.extend(f"- {error}" for error in ledger_errors)

if required_failed:
    lines.extend(["", "## Undocumented Failures", ""])
    lines.extend(
        f"- `{row['gate_id']}` failed with exit {row['exit_code']}; see `{row['log_path']}`."
        for row in required_failed
    )

if required_divergent:
    lines.extend(["", "## Documented Divergences", ""])
    lines.extend(
        f"- `{row['gate_id']}` is documented by `{row.get('divergence_id')}` "
        f"through `{', '.join(row.get('divergence_expires_on', []))}`."
        for row in required_divergent
    )

report_md.write_text("\n".join(lines) + "\n", encoding="utf-8")

print(f"wrote {rel(str(report_json))}")
print(f"wrote {rel(str(report_md))}")

raise SystemExit(0 if verdict == "passed" else 1)
PY
report_status=$?
set -u

echo
echo "Comprehensive harness report:"
echo "  JSON: $REPORT_JSON"
echo "  MD:   $REPORT_MD"

exit "$report_status"
