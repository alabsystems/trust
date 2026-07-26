#!/bin/bash
# End-to-end fail-closed evidence gate for the trust-mc/trust-wp/trust-vc sample.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
HOST_TRIPLE="$(uname -m)-$(uname -s | tr '[:upper:]' '[:lower:]')"
case "$HOST_TRIPLE" in
    arm64-darwin)
        HOST_TRIPLE="aarch64-apple-darwin"
        ;;
esac

CRATES_MANIFEST="$TRUST_ROOT/crates/Cargo.toml"
TARGET_DIR="${TRUST_THREE_SUITE_TARGET_DIR:-$TRUST_ROOT/build/full-verifier-three-suite-target}"
OUTPUT_DIR="${TRUST_THREE_SUITE_OUTPUT_DIR:-$TRUST_ROOT/build/full-verifier-three-suite-evidence}"
REPORT_JSON="${TRUST_THREE_SUITE_REPORT:-$OUTPUT_DIR/report.json}"
STATUS_TSV="$OUTPUT_DIR/suite-status.tsv"
ROUTER_MANIFEST="$OUTPUT_DIR/router-verification-run-manifest.json"

mkdir -p "$OUTPUT_DIR" "$TARGET_DIR"
: > "$STATUS_TSV"

fail() {
    echo "FAIL: $*" >&2
    exit 2
}

first_executable() {
    local candidate

    for candidate in "$@"; do
        if [ -n "$candidate" ] && [ -x "$candidate" ]; then
            printf '%s\n' "$candidate"
            return 0
        fi
    done
    return 1
}

resolve_targo() {
    local candidate

    for candidate in \
        "$TRUST_ROOT/build/$HOST_TRIPLE/stage2/bin" \
        "$TRUST_ROOT/build/host/stage2/bin" \
        "$TRUST_ROOT"/build/*/stage2/bin
    do
        if [ -x "$candidate/targo" ] && [ -x "$candidate/trustc" ]; then
            printf '%s\n' "$candidate/targo"
            return 0
        fi
    done
    return 1
}

resolve_trustc() {
    local candidate

    for candidate in \
        "$TRUST_ROOT/build/$HOST_TRIPLE/stage2/bin" \
        "$TRUST_ROOT/build/host/stage2/bin" \
        "$TRUST_ROOT"/build/*/stage2/bin
    do
        if [ -x "$candidate/targo" ] && [ -x "$candidate/trustc" ]; then
            printf '%s\n' "$candidate/trustc"
            return 0
        fi
    done
    return 1
}

TARGO_BIN="$(resolve_targo)" || fail "repo-local stage2 Trust targo/trustc not found. Run ./x.py build --stage 2."
TRUSTC_BIN="$(resolve_trustc)" || fail "repo-local stage2 Trust targo/trustc not found. Run ./x.py build --stage 2."
if [ "$(basename "$TARGO_BIN")" != "targo" ]; then
    fail "stage2 Trust cargo entrypoint must be canonical targo, got: $TARGO_BIN"
fi
if [ "$(basename "$TRUSTC_BIN")" != "trustc" ]; then
    fail "stage2 Trust compiler entrypoint must be canonical trustc, got: $TRUSTC_BIN"
fi
RUSTC_BIN="$TRUSTC_BIN"
COMPILER_STAGE="stage2"
RUSTC_PRIVATE_SYSROOT_FILTER="$TRUST_ROOT/scripts/trust_rustc_private_sysroot_filter.py"
TRUSTC_LIB_DIR="$(cd "$(dirname "$TRUSTC_BIN")/../lib" && pwd)"
case "$(uname -s)" in
    Darwin)
        export DYLD_LIBRARY_PATH="$TRUSTC_LIB_DIR${DYLD_LIBRARY_PATH:+:$DYLD_LIBRARY_PATH}"
        ;;
    *)
        export LD_LIBRARY_PATH="$TRUSTC_LIB_DIR${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
        ;;
esac

if [ ! -x "$RUSTC_PRIVATE_SYSROOT_FILTER" ]; then
    fail "rustc-private sysroot filter is not executable: $RUSTC_PRIVATE_SYSROOT_FILTER"
fi

run_and_capture() {
    local suite="$1"
    local log="$2"
    shift 2

    echo
    echo ">>> $suite: $*"
    set +e
    CARGO_TARGET_DIR="$TARGET_DIR" \
        RUSTC="$RUSTC_BIN" \
        "$@" >"$log" 2>&1
    local status=$?
    set -e
    return "$status"
}

run_and_capture_with_rustc_wrapper() {
    local suite="$1"
    local log="$2"
    local rustc_wrapper="$3"
    shift 3

    echo
    echo ">>> $suite: RUSTC_WRAPPER=$rustc_wrapper $*"
    set +e
    CARGO_TARGET_DIR="$TARGET_DIR" \
        RUSTC="$RUSTC_BIN" \
        RUSTC_WRAPPER="$rustc_wrapper" \
        "$@" >"$log" 2>&1
    local status=$?
    set -e
    return "$status"
}

assert_tests_ran_without_ignored() {
    local suite="$1"
    local log="$2"

    python3 - "$suite" "$log" <<'PY'
import re
import sys

suite, log_path = sys.argv[1:3]
text = open(log_path, encoding="utf-8", errors="replace").read()
text = re.sub(r"\x1b\[[0-9;]*[A-Za-z]", "", text)
running = [int(match.group(1)) for match in re.finditer(r"running\s+(\d+)\s+tests?", text)]
if not running or max(running) == 0:
    print(f"FAIL: {suite} did not execute any tests", file=sys.stderr)
    raise SystemExit(2)
ignored = [
    int(match.group(1))
    for match in re.finditer(r";\s+(\d+)\s+ignored\b", text)
]
if any(count for count in ignored):
    print(f"FAIL: {suite} ignored tests in a required native-suite gate", file=sys.stderr)
    raise SystemExit(2)
if re.search(r"(^|[\s(])SKIP(?:PING|PED)?\s*:", text, re.MULTILINE):
    print(f"FAIL: {suite} emitted an explicit SKIP marker", file=sys.stderr)
    raise SystemExit(2)
PY
}

record_status() {
    local suite="$1"
    local status="$2"
    local log="$3"
    local command="$4"

    printf '%s\t%s\t%s\t%s\n' "$suite" "$status" "$log" "$command" >> "$STATUS_TSV"
}

write_report() {
    TARGO_BIN="$TARGO_BIN" \
    RUSTC_BIN="$RUSTC_BIN" \
    TRUSTC_BIN="$TRUSTC_BIN" \
    CARGO_NET_OFFLINE="${CARGO_NET_OFFLINE:-}" \
    COMPILER_STAGE="$COMPILER_STAGE" \
    STAGE2_RUSTC_PRESENT=false \
    STAGE2_TRUSTC_PRESENT=true \
    REPORT_JSON="$REPORT_JSON" \
    STATUS_TSV="$STATUS_TSV" \
        python3 <<'PY'
import json
import os
from pathlib import Path

rows = []
for line in Path(os.environ["STATUS_TSV"]).read_text(encoding="utf-8").splitlines():
    suite, status, log, command = line.split("\t", 3)
    rows.append({
        "suite": suite,
        "status": status,
        "log": log,
        "command": command,
    })

report = {
    "schema": "trust.full-verifier-three-suite-evidence.v2",
    "status": (
        "passed-with-recorded-gaps"
        if any(
            row["status"] in {"blocked-fail-closed", "passed-fail-closed"}
            for row in rows
        )
        else "passed"
    ),
    "toolchain": {
        "targo": os.environ["TARGO_BIN"],
        "rustc": os.environ["RUSTC_BIN"],
        "trustc": os.environ["TRUSTC_BIN"] or None,
        "compiler_stage": os.environ["COMPILER_STAGE"],
        "stage2_rustc_present": os.environ["STAGE2_RUSTC_PRESENT"] == "true",
        "stage2_trustc_present": os.environ["STAGE2_TRUSTC_PRESENT"] == "true",
    },
    "environment": {
        "cargo_net_offline": os.environ.get("CARGO_NET_OFFLINE") or None,
        "cargo_offline_enabled": os.environ.get("CARGO_NET_OFFLINE") == "true",
    },
    "suites": rows,
}
Path(os.environ["REPORT_JSON"]).write_text(
    json.dumps(report, indent=2, sort_keys=True) + "\n",
    encoding="utf-8",
)
PY
}

validate_router_manifest() {
    local manifest_path="$1"

    python3 - "$manifest_path" <<'PY'
import json
import stat
import sys
from pathlib import Path

path = Path(sys.argv[1])
errors = []
try:
    metadata = path.lstat()
except FileNotFoundError:
    print(f"FAIL: router sample did not materialize its verifier manifest: {path}", file=sys.stderr)
    raise SystemExit(2)

if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISREG(metadata.st_mode):
    errors.append("router verifier manifest must be a regular, non-symlink file")
if metadata.st_size == 0:
    errors.append("router verifier manifest is empty")
if metadata.st_size > 8 * 1024 * 1024:
    errors.append("router verifier manifest exceeds the 8 MiB envelope limit")

manifest = None
if not errors:
    try:
        manifest = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        errors.append(f"router verifier manifest is not valid bounded UTF-8 JSON: {error}")

if isinstance(manifest, dict):
    if manifest.get("status") != "Inconclusive":
        errors.append(f"router aggregate must be Inconclusive, got {manifest.get('status')!r}")

    summary = manifest.get("summary") if isinstance(manifest.get("summary"), dict) else {}
    # After the ratified b62 "reject unreplayed native proof authority" hardening,
    # only trust-wp supplies same-run materialized native proof for this synthetic
    # sample; trust-mc and trust-vc are both native-authority debt. The honest
    # aggregate is 1/3, NOT 2/3 — do not restore proved=2 without genuine live
    # native trust-mc authority.
    expected_summary = {
        "requested_obligations": 3,
        "evidence_count": 3,
        "proved": 1,
        "unsupported": 2,
    }
    for key, expected_value in expected_summary.items():
        if summary.get(key) != expected_value:
            errors.append(
                f"router summary.{key} must be {expected_value}, got {summary.get(key)!r}"
            )
    for key in (
        "bounded_proved",
        "insufficient_strength",
        "missing_proof_artifacts",
        "failed",
        "unknown",
        "timed_out",
        "cancelled",
        "skipped",
        "publication_conflicts",
        "admitted",
    ):
        if summary.get(key, 0) != 0:
            errors.append(f"router summary.{key} must remain zero, got {summary.get(key)!r}")

    accepted = manifest.get("accepted_evidence", [])
    rejected = manifest.get("rejected_evidence", [])
    skipped = manifest.get("skipped", [])
    if not isinstance(accepted, list) or len(accepted) != 1:
        errors.append("router manifest must contain exactly one accepted evidence row")
        accepted = []
    if not isinstance(rejected, list) or len(rejected) != 2:
        errors.append("router manifest must contain exactly two rejected evidence rows")
        rejected = []
    if skipped:
        errors.append("router manifest must not skip any requested suite")

    expected_accepted = {
        "sample::trust-wp-postcondition": "trust-wp",
    }
    accepted_by_obligation = {
        row.get("obligation_id"): row for row in accepted if isinstance(row, dict)
    }
    if set(accepted_by_obligation) != set(expected_accepted):
        errors.append(
            "accepted router obligations must be exactly the trust-wp postcondition"
        )
    for obligation_id, suite in expected_accepted.items():
        row = accepted_by_obligation.get(obligation_id)
        if row is None:
            continue
        engine = row.get("engine") if isinstance(row.get("engine"), dict) else {}
        diagnostics = row.get("diagnostics", [])
        artifacts = row.get("artifacts", [])
        if engine.get("name") != "trust-full-verifier":
            errors.append(f"{suite}: accepted row has the wrong engine")
        if row.get("status") != "Proved" or row.get("disposition") != "AcceptedProof":
            errors.append(f"{suite}: row is not accepted proof evidence")
        if not isinstance(artifacts, list) or not artifacts:
            errors.append(f"{suite}: accepted row has no proof artifacts")
        elif not any(
            isinstance(artifact, dict) and artifact.get("materialization") is not None
            for artifact in artifacts
        ):
            errors.append(f"{suite}: accepted row has no materialized same-run artifact")
        if not any(
            isinstance(diagnostic, str)
            and f"primary owner {suite}@" in diagnostic
            and "accepted evidence" in diagnostic
            for diagnostic in diagnostics
        ):
            errors.append(f"{suite}: accepted row lacks its primary-owner acceptance diagnostic")

    # trust-mc and trust-vc are both rejected as unsupported, artifact-free
    # native-authority debt. Each keeps its specific fail-closed cause: trust-mc
    # requires a live opaque native-bundle CHC/PDR authority the sample does not
    # carry; trust-vc's admitted native bundle contains no TrustVc request.
    expected_rejected = {
        "sample::trust-mc-arithmetic-safety": (
            "trust-mc",
            "trust-mc proof-grade admission requires a live opaque native-bundle authority",
        ),
        "sample::trust-vc-ownership": (
            "trust-vc",
            "contains no TrustVc requests",
        ),
    }
    rejected_by_obligation = {
        row.get("obligation_id"): row for row in rejected if isinstance(row, dict)
    }
    if set(rejected_by_obligation) != set(expected_rejected):
        errors.append(
            "rejected router obligations must be exactly trust-mc arithmetic safety and trust-vc ownership"
        )
    for obligation_id, (suite, cause) in expected_rejected.items():
        row = rejected_by_obligation.get(obligation_id)
        if row is None:
            continue
        engine = row.get("engine") if isinstance(row.get("engine"), dict) else {}
        diagnostics = row.get("diagnostics", [])
        if engine.get("name") != "trust-full-verifier":
            errors.append(f"{suite}: rejected row has the wrong engine")
        if row.get("status") != "Unsupported" or row.get("disposition") != "RejectedStatus":
            errors.append(f"{suite} must remain an unsupported rejected-status row")
        if row.get("proof_strength") is not None:
            errors.append(f"{suite} rejection must not claim proof strength")
        if row.get("artifacts", []):
            errors.append(f"{suite} rejection must not carry counterfeit proof artifacts")
        if not any(
            isinstance(diagnostic, str) and cause in diagnostic
            for diagnostic in diagnostics
        ):
            errors.append(f"{suite} rejection lacks its native-authority-unavailable diagnostic")
        if not any(
            isinstance(diagnostic, str)
            and f"primary owner {suite}@" in diagnostic
            and "rejected evidence" in diagnostic
            for diagnostic in diagnostics
        ):
            errors.append(f"{suite} rejection lacks its primary-owner rejection diagnostic")
elif manifest is not None:
    errors.append("router verifier manifest must be a JSON object")

if errors:
    print("FAIL: router verifier manifest violated the fail-closed 1/3 contract", file=sys.stderr)
    for error in errors:
        print(f"  - {error}", file=sys.stderr)
    raise SystemExit(2)

print("Validated router manifest: Inconclusive, trust-wp accepted, trust-mc/trust-vc rejected pending live native authority")
PY
}

validate_evidence_report() {
    REPORT_JSON="$REPORT_JSON" \
    ROUTER_MANIFEST="$ROUTER_MANIFEST" \
        python3 <<'PY'
import json
import re
import sys
from pathlib import Path

report_path = Path(__import__("os").environ["REPORT_JSON"])
report = json.loads(report_path.read_text(encoding="utf-8"))

expected = {
    "trust-wp-native": {
        "status": {"passed"},
        "tests": ["native_verify_rejects_pure_obligation_without_replay_evidence"],
        "command": ["-p trust-wp", "--features trust-build"],
        "diagnostic": "trust-wp native replay gate exercised fail-closed before proof upgrade",
    },
    "trust-vc-native": {
        "status": {"passed-fail-closed"},
        "tests": ["legacy_native_report_cannot_convert_to_proof_certificate_evidence"],
        "command": ["-p trust-vc-bridge"],
        "diagnostic": "Legacy trust-vc report conversion rejected producer booleans and opaque payload metadata without a local replay receipt",
    },
    "trust-mc-typed-adapter": {
        "status": {"passed"},
        "tests": ["native_typed_chc_pdr_solver_proves_compiler_spec_binary_constraint_rule"],
        "command": ["-p trust-bmc", "--features trust-mc-native-solver"],
        "diagnostic": "trust-mc direct typed CHC adapter produced native proof evidence",
    },
    "trust-mc-native-bootstrap": {
        "status": {"passed", "blocked-fail-closed"},
        "tests": ["native_typed_chc_pdr_solver_feature_does_not_enable_trust_mc_compiler_facade"],
        "command": ["-p trust-bmc", "--features trust-mc-native-solver"],
        "diagnostic": "trust-mc library-only typed CHC/PDR native runner produced proof evidence",
    },
    "router-full-verifier-three-suite": {
        "status": {"passed-fail-closed", "blocked-fail-closed"},
        "tests": [
            "sample_bundle_required_suite_mode_rejects_missing_native_suite",
            "sample_bundle_records_trust_vc_memory_bridge_debt",
        ],
        "command": ["-p trust-router", "--features trust-build", "--test full_verifier_three_suite_sample"],
        "diagnostic": "Router accepted suite-native trust-wp evidence and rejected trust-mc and trust-vc because no live native-bundle CHC/PDR (trust-mc) or kernel-replayed TrustVc (trust-vc) proof authority was available",
    },
}

def suite_family(suite):
    if suite.startswith("trust-wp"):
        return "trust-wp"
    if suite.startswith("trust-vc"):
        return "trust-vc"
    if suite.startswith("trust-mc"):
        return "trust-mc"
    return "router"

def verification_evidence_for(suite, status, log_path, observed_tests, diagnostic):
    passed = status == "passed"
    inconclusive = status == "passed-fail-closed"
    family = suite_family(suite)
    artifacts = [
        {
            "kind": "test_log",
            "format": "text",
            "artifact_id": f"{suite}:log",
            "uri": str(log_path),
        }
    ]
    if inconclusive and suite == "router-full-verifier-three-suite":
        artifacts.append(
            {
                "kind": "verification_run_manifest",
                "format": "json",
                "artifact_id": f"{suite}:manifest",
                "uri": __import__("os").environ["ROUTER_MANIFEST"],
            }
        )
    return {
        "suite": family,
        "backend": suite,
        "request_id": f"{suite}:native-suite-gate",
        "evidence_id": f"{suite}:{status}",
        "native_id": f"{suite}:native-suite-gate:{','.join(observed_tests) or 'blocked'}",
        "status": "passed" if passed else "inconclusive" if inconclusive else "rejected",
        "strength": {
            "reasoning": "executable-test" if passed else "mixed" if inconclusive else "diagnostic",
            "assurance": "test-backed" if passed else "fail-closed" if inconclusive else "rejected",
        },
        "artifacts": artifacts,
        "diagnostics": [
            {
                "code": (
                    "native-suite.test.passed"
                    if passed
                    else "native-suite.inconclusive-fail-closed"
                    if inconclusive
                    else "native-suite.blocked"
                ),
                "severity": "info" if passed else "warning" if inconclusive else "error",
                "message": diagnostic,
            }
        ],
    }

def validate_structured_verification_evidence(suite, evidence):
    local_errors = []
    if not isinstance(evidence, dict):
        return [f"{suite}: verification_evidence must be a structured object"]
    for key in ("suite", "backend", "request_id", "evidence_id", "native_id", "status"):
        if not isinstance(evidence.get(key), str) or not evidence[key].strip():
            local_errors.append(f"{suite}: verification_evidence.{key} must be a non-empty string")
    if evidence.get("status") not in {"passed", "inconclusive", "rejected"}:
        local_errors.append(f"{suite}: verification_evidence.status is invalid")
    strength = evidence.get("strength")
    if not isinstance(strength, dict):
        local_errors.append(f"{suite}: verification_evidence.strength must be an object")
    else:
        for key in ("reasoning", "assurance"):
            if not isinstance(strength.get(key), str) or not strength[key].strip():
                local_errors.append(f"{suite}: verification_evidence.strength.{key} must be set")
    artifacts = evidence.get("artifacts")
    if not isinstance(artifacts, list) or not artifacts:
        local_errors.append(f"{suite}: verification_evidence.artifacts must be a non-empty list")
    elif any(not isinstance(artifact, dict) or not artifact.get("kind") or not artifact.get("uri") for artifact in artifacts):
        local_errors.append(f"{suite}: verification_evidence.artifacts must contain structured artifact objects")
    diagnostics = evidence.get("diagnostics")
    if not isinstance(diagnostics, list):
        local_errors.append(f"{suite}: verification_evidence.diagnostics must be a list")
    elif any(
        not isinstance(diagnostic, dict)
        or not diagnostic.get("code")
        or not diagnostic.get("severity")
        or not diagnostic.get("message")
        for diagnostic in diagnostics
    ):
        local_errors.append(f"{suite}: verification_evidence.diagnostics must contain structured diagnostic objects")
    return local_errors

errors = []
if report.get("schema") != "trust.full-verifier-three-suite-evidence.v2":
    errors.append(f"unexpected schema: {report.get('schema')!r}")

toolchain = report.get("toolchain") if isinstance(report.get("toolchain"), dict) else {}
targo = toolchain.get("targo")
rustc = toolchain.get("rustc")
trustc = toolchain.get("trustc")
if not isinstance(targo, str) or Path(targo).name != "targo":
    errors.append(f"toolchain cargo entrypoint must be canonical Trust targo: {targo!r}")
if not isinstance(trustc, str) or Path(trustc).name != "trustc":
    errors.append(f"toolchain trustc must be canonical Trust trustc: {trustc!r}")
if rustc != trustc:
    errors.append(f"targo builds must use canonical trustc through RUSTC, got {rustc!r}")
if toolchain.get("compiler_stage") != "stage2":
    errors.append(f"compiler_stage must be stage2, got {toolchain.get('compiler_stage')!r}")
if toolchain.get("stage2_trustc_present") is not True:
    errors.append("stage2_trustc_present must be true")

suites = report.get("suites", [])
by_suite = {}
for row in suites:
    suite = row.get("suite")
    if suite in by_suite:
        errors.append(f"duplicate suite row: {suite}")
    by_suite[suite] = row

if set(by_suite) != set(expected):
    errors.append(
        "suite set mismatch: expected "
        + ", ".join(sorted(expected))
        + "; saw "
        + ", ".join(sorted(str(name) for name in by_suite))
    )

validated = []
gaps = []
ansi = re.compile(r"\x1b\[[0-9;]*[A-Za-z]")
for suite, spec in expected.items():
    row = by_suite.get(suite)
    if row is None:
        continue
    status = row.get("status")
    if status not in spec["status"]:
        errors.append(f"{suite}: unexpected status {status!r}")
    command = row.get("command", "")
    for fragment in spec["command"]:
        if fragment not in command:
            errors.append(f"{suite}: command missing {fragment!r}: {command!r}")

    log_path = Path(row.get("log", ""))
    if not log_path.is_file():
        errors.append(f"{suite}: log is missing: {log_path}")
        continue
    text = ansi.sub("", log_path.read_text(encoding="utf-8", errors="replace"))
    if re.search(r"(^|[\s(])SKIP(?:PING|PED)?\s*:", text, re.MULTILINE):
        errors.append(f"{suite}: log contains explicit SKIP marker")
    if re.search(r";\s+[1-9][0-9]*\s+ignored\b", text):
        errors.append(f"{suite}: log reports ignored tests")

    observed_tests = []
    if status == "blocked-fail-closed":
        blocker_patterns = [
            r"RUSTUP_HOME must be set",
            r"can't find crate for `rustc_public`",
            r"compiled by an incompatible version of rustc",
            r"UnknownPreReleaseTag\(\"trust\"\)",
            r"Failed to get rustc version",
            r"test_scheduling_t030_exact_optimum\.pbp",
            r"router three-suite sample still uses proof-grade trust-wp fixture evidence",
        ]
        if not any(re.search(pattern, text, re.DOTALL) for pattern in blocker_patterns):
            errors.append(f"{suite}: blocked status lacks a classified blocker")
        if suite == "router-full-verifier-three-suite":
            gaps.append(
                {
                    "suite": suite,
                    "kind": "trust-wp-fixture-router-integration-blocker",
                    "detail": "The router required-suite sample still has fixture or text-only trust-wp proof evidence. It must use suite-native trust-wp replay/check artifacts generated from typed TrustIr before this row may be reported as passed.",
                    "log": str(log_path),
                }
            )
            for test_name in spec["tests"]:
                if re.search(rf"test [^\n]*{re.escape(test_name)}[^\n]*\.\.\. ok", text):
                    observed_tests.append(test_name)
                else:
                    errors.append(f"{suite}: expected executable test did not pass: {test_name}")
        else:
            gaps.append(
                {
                    "suite": suite,
                    "kind": "active-adapter-api-bootstrap-blocker",
                    "detail": "trust-mc library-only native typed CHC/PDR bootstrap failed before proof completion; direct typed trust-mc adapter evidence still passed.",
                    "log": str(log_path),
                }
            )
    else:
        running = [int(match.group(1)) for match in re.finditer(r"running\s+(\d+)\s+tests?", text)]
        if not running or max(running) == 0:
            errors.append(f"{suite}: host cargo test did not execute tests")
        for test_name in spec["tests"]:
            if re.search(rf"test [^\n]*{re.escape(test_name)}[^\n]*\.\.\. ok", text):
                observed_tests.append(test_name)
            else:
                errors.append(f"{suite}: expected executable test did not pass: {test_name}")

    if suite == "router-full-verifier-three-suite" and status == "passed-fail-closed":
        gaps.append(
            {
                "suite": suite,
                "kind": "trust-vc-kernel-replay-authority-gap",
                "detail": "The exact three-suite sample is intentionally Inconclusive: trust-mc and trust-wp supply accepted native evidence, while trust-vc is rejected until its exact certificate is replayed by an actual Lean kernel authority.",
                "manifest": __import__("os").environ["ROUTER_MANIFEST"],
                "log": str(log_path),
            }
        )
    if suite == "trust-vc-native" and status == "passed-fail-closed":
        gaps.append(
            {
                "suite": suite,
                "kind": "trust-vc-native-replay-receipt-gap",
                "detail": "The legacy trust-vc report DTO cannot authorize proof-certificate evidence: producer-set verification booleans and an opaque payload are rejected until a local replay authority issues a bound receipt.",
                "log": str(log_path),
            }
        )

    verification_evidence = verification_evidence_for(
        suite,
        status,
        log_path,
        observed_tests,
        spec["diagnostic"],
    )
    errors.extend(validate_structured_verification_evidence(suite, verification_evidence))
    validated.append(
        {
            "suite": suite,
            "status": status,
            "log": str(log_path),
            "observed_tests": observed_tests,
            "verification_evidence": verification_evidence,
        }
    )

if report.get("status") == "passed" and gaps:
    errors.append("report status is passed despite recorded blocker gap")
if report.get("status") == "passed-with-recorded-gaps" and not gaps:
    errors.append("report status records gaps but no fail-closed gap was found")

if errors:
    print("FAIL: full-verifier three-suite evidence report is incomplete", file=sys.stderr)
    for error in errors:
        print(f"  - {error}", file=sys.stderr)
    raise SystemExit(2)

report["validated_suites"] = validated
report["gaps"] = gaps
report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
print("Validated executable full-verifier evidence for trust-mc, trust-wp, trust-vc, and router")
PY
}

run_required_suite() {
    local suite="$1"
    local log="$2"
    shift 2
    local command="$*"

    if ! run_and_capture "$suite" "$log" "$@"; then
        tail -n 80 "$log" >&2 || true
        fail "$suite failed; log: $log"
    fi
    assert_tests_ran_without_ignored "$suite" "$log"
    record_status "$suite" "passed" "$log" "$command"
}

run_fail_closed_suite() {
    local suite="$1"
    local log="$2"
    shift 2
    local command="$*"

    if ! run_and_capture "$suite" "$log" "$@"; then
        tail -n 80 "$log" >&2 || true
        fail "$suite failed; log: $log"
    fi
    assert_tests_ran_without_ignored "$suite" "$log"
    record_status "$suite" "passed-fail-closed" "$log" "$command"
}

run_trust-mc_typed_adapter_probe() {
    local suite="trust-mc-typed-adapter"
    local log="$OUTPUT_DIR/$suite.log"
    local command

    command="RUSTC_WRAPPER=$RUSTC_PRIVATE_SYSROOT_FILTER $TARGO_BIN --unverified test --manifest-path $CRATES_MANIFEST -p trust-bmc --features trust-mc-native-solver native_typed_chc_pdr_solver_proves_compiler_spec_binary_constraint_rule"
    if ! run_and_capture_with_rustc_wrapper "$suite" "$log" "$RUSTC_PRIVATE_SYSROOT_FILTER" \
        "$TARGO_BIN" --unverified test --manifest-path "$CRATES_MANIFEST" \
        -p trust-bmc --features trust-mc-native-solver \
        native_typed_chc_pdr_solver_proves_compiler_spec_binary_constraint_rule
    then
        tail -n 80 "$log" >&2 || true
        fail "$suite failed; log: $log"
    fi

    assert_tests_ran_without_ignored "$suite" "$log"
    record_status "$suite" "passed" "$log" "$command"
}

run_router_required_suite() {
    local suite="router-full-verifier-three-suite"
    local log="$OUTPUT_DIR/$suite.log"
    local manifest="$ROUTER_MANIFEST"
    local command="TRUST_THREE_SUITE_MANIFEST_OUT=$manifest $TARGO_BIN --unverified test --manifest-path $CRATES_MANIFEST -p trust-router --features trust-build --test full_verifier_three_suite_sample"
    local router_test="$TRUST_ROOT/crates/trust-router/tests/full_verifier_three_suite_sample.rs"

    rm -f "$manifest"
    if ! run_and_capture "$suite" "$log" \
        env TRUST_THREE_SUITE_MANIFEST_OUT="$manifest" \
        "$TARGO_BIN" --unverified test --manifest-path "$CRATES_MANIFEST" \
        -p trust-router --features trust-build --test full_verifier_three_suite_sample
    then
        tail -n 80 "$log" >&2 || true
        fail "$suite failed; log: $log"
    fi
    assert_tests_ran_without_ignored "$suite" "$log"
    validate_router_manifest "$manifest"

    if grep -Eq 'ProofGradetrust-wpFixtureEngine|fixture aggregate trust-wp|trust-wp:fixture-proof' "$router_test"; then
        {
            echo
            echo "BLOCKED: router three-suite sample still uses proof-grade trust-wp fixture evidence; suite-native trust-wp replay/check artifacts are required before this row may be reported as passed."
        } >> "$log"
        record_status "$suite" "blocked-fail-closed" "$log" "$command"
        return
    fi

    record_status "$suite" "passed-fail-closed" "$log" "$command"
}

run_trust-mc_native_bootstrap_probe() {
    local suite="trust-mc-native-bootstrap"
    local log="$OUTPUT_DIR/$suite.log"
    local command

    command="RUSTC_WRAPPER=$RUSTC_PRIVATE_SYSROOT_FILTER $TARGO_BIN --unverified test --manifest-path $CRATES_MANIFEST -p trust-bmc --features trust-mc-native-solver native_typed_chc_pdr_solver_feature_does_not_enable_trust_mc_compiler_facade"
    if run_and_capture_with_rustc_wrapper "$suite" "$log" "$RUSTC_PRIVATE_SYSROOT_FILTER" \
        "$TARGO_BIN" --unverified test --manifest-path "$CRATES_MANIFEST" \
        -p trust-bmc --features trust-mc-native-solver \
        native_typed_chc_pdr_solver_feature_does_not_enable_trust_mc_compiler_facade
    then
        assert_tests_ran_without_ignored "$suite" "$log"
        record_status "$suite" "passed" "$log" "$command"
        return
    fi

    tail -n 80 "$log" >&2 || true
    if python3 - "$log" <<'PY'
import re
import sys

text = open(sys.argv[1], encoding="utf-8", errors="replace").read()
blocker_patterns = [
    r"test_scheduling_t030_exact_optimum\.pbp",
]
raise SystemExit(0 if any(re.search(pattern, text) for pattern in blocker_patterns) else 1)
PY
    then
        record_status "$suite" "blocked-fail-closed" "$log" "$command"
        return
    fi

    fail "$suite failed; log: $log"
}

run_required_suite \
    "trust-wp-native" \
    "$OUTPUT_DIR/trust-wp-native.log" \
    "$TARGO_BIN" --unverified test --manifest-path "$CRATES_MANIFEST" \
    -p trust-wp --features trust-build \
    native_verify_rejects_pure_obligation_without_replay_evidence

run_fail_closed_suite \
    "trust-vc-native" \
    "$OUTPUT_DIR/trust-vc-native.log" \
    "$TARGO_BIN" --unverified test --manifest-path "$CRATES_MANIFEST" \
    -p trust-vc-bridge \
    legacy_native_report_cannot_convert_to_proof_certificate_evidence

run_trust-mc_typed_adapter_probe

run_trust-mc_native_bootstrap_probe

export TRUST_FULL_VERIFIER_THREE_SUITE_MODE="${TRUST_FULL_VERIFIER_THREE_SUITE_MODE:-required-native-suites}"
run_router_required_suite

write_report
validate_evidence_report

echo
echo "Full-verifier three-suite evidence passed fail-closed (TrustVc kernel-replay gap recorded)"
echo "Report: $REPORT_JSON"
