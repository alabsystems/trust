#!/bin/bash
# End-to-end test: standalone `targo trust` is the canonical human-facing
# verification CLI for the standalone Trust toolchain release baseline.
#
# Verifies the supported public commands:
#   1. `targo trust check`: human-readable summary, no raw TRUST_JSON leakage
#   2. `targo trust check --format json`: canonical JSON report on stdout
#   3. `targo trust version --json`: Trust identity, distinct tool bindings
#   4. `targo trust release check --profile metadata --json`: Trust release gate
#   5. unified maintenance commands are present under `targo trust`
#   6. default config is meaningful out of the box (L1, not "no obligations")
#   7. native verification comes from the standalone Trust sysroot selected by
#      the canonical `targo` binary, without rustup selectors or fallbacks
#
# This intentionally tests the standalone subcommand from a repo-external temp
# directory with compiler/toolchain override env cleared. It is still a local
# baseline, not a packaged install/dist test.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
INPUT="$TRUST_ROOT/examples/midpoint.rs"

echo "=== Trust E2E Test: targo trust public CLI ==="
echo

fail_setup() {
    echo "ERROR: $1"
    exit 2
}

run_public_cli() {
    env -u TRUSTC -u RUSTUP_TOOLCHAIN -u RUSTC -u RUSTDOC \
        -u RUSTFLAGS -u CARGO_ENCODED_RUSTFLAGS \
        -u RUSTC_WRAPPER -u RUSTC_WORKSPACE_WRAPPER \
        -u CARGO_BUILD_RUSTC -u CARGO_BUILD_RUSTDOC \
        -u CARGO_BUILD_RUSTC_WRAPPER -u CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER \
        "$TRUST_TARGO" trust "$@"
}

require_command() {
    local cmd="$1"
    local install_hint="$2"
    if ! command -v "$cmd" >/dev/null 2>&1; then
        fail_setup "$cmd not found on PATH. $install_hint"
    fi
}

require_command python3 "Install Python 3 for JSON validation."

find_standalone_targo() {
    local candidate
    while IFS= read -r candidate; do
        if [ -x "$candidate" ] && [ -x "$(dirname "$candidate")/trustc" ]; then
            printf '%s\n' "$candidate"
            return 0
        fi
    done < <(find "$TRUST_ROOT/build" -path "*/stage2/bin/targo" -type f -perm -111 -print 2>/dev/null | sort -r)

    return 1
}

if ! TRUST_TARGO="$(find_standalone_targo)"; then
    fail_setup "repo-local stage2 Trust targo/trustc not found under build/*/stage2/bin. Run ./x.py build --stage 2."
fi
TRUSTC_BIN="$(dirname "$TRUST_TARGO")/trustc"

if ! run_public_cli --help >/dev/null 2>&1; then
    fail_setup "standalone targo does not expose the canonical \`targo trust\` subcommand"
fi

echo "Using targo:       $TRUST_TARGO"
echo "Using trustc:       $TRUSTC_BIN"
echo "Input file:         $INPUT"
echo

TMP_DIR="$(mktemp -d /tmp/targo_trust_cli_XXXXXX)"
trap 'rm -rf "$TMP_DIR"' EXIT

TERMINAL_STDOUT="$TMP_DIR/terminal.stdout"
TERMINAL_STDERR="$TMP_DIR/terminal.stderr"
DOCTOR_STDOUT="$TMP_DIR/doctor.stdout"
DOCTOR_STDERR="$TMP_DIR/doctor.stderr"
JSON_STDOUT="$TMP_DIR/json.stdout"
JSON_STDERR="$TMP_DIR/json.stderr"

cd "$TMP_DIR"

if ! run_public_cli --help >/dev/null 2>&1; then
    echo "FAIL: installed targo trust is not runnable from a repo-external temp dir"
    exit 1
fi

echo "--- doctor json"
doctor_exit=0
run_public_cli doctor --format json >"$DOCTOR_STDOUT" 2>"$DOCTOR_STDERR" || doctor_exit=$?

if [ "$doctor_exit" -ne 0 ]; then
    if [ "$doctor_exit" -gt 1 ]; then
        echo "FAIL: doctor json exited with unexpected status $doctor_exit"
        exit 1
    fi
fi
if grep -q "TRUST_JSON:" "$DOCTOR_STDOUT" "$DOCTOR_STDERR"; then
    echo "FAIL: doctor json leaked raw TRUST_JSON transport"
    exit 1
fi

doctor_parse_exit=0
TRUSTC_BIN="$TRUSTC_BIN" python3 - "$DOCTOR_STDOUT" <<'PY' || doctor_parse_exit=$?
import json
import os
import sys

with open(sys.argv[1], "r", encoding="utf-8") as fh:
    report = json.load(fh)

compiler = report.get("compiler")
if not isinstance(compiler, dict):
    raise AssertionError("missing compiler object")

required_fields = [
    "path",
    "discovery_source",
    "linked_toolchain_status",
    "linked_toolchain_path",
    "trust_verify",
    "json_transport",
    "check_report_mode",
]
missing = [field for field in required_fields if field not in compiler]
if missing:
    raise AssertionError("missing compiler fields: " + ", ".join(missing))

expected = os.environ["TRUSTC_BIN"]

# Trust product discovery uses only Trust roots: the "linked toolchain" is
# the same-sysroot compatibility surface, never an external rustup selector.
if compiler["linked_toolchain_status"] != "visible":
    raise AssertionError(
        "doctor should report the same-sysroot linked toolchain surface, got "
        + str(compiler["linked_toolchain_status"])
    )

linked_path = compiler.get("linked_toolchain_path")
if not linked_path or os.path.realpath(linked_path) != os.path.realpath(expected):
    raise AssertionError(
        "standalone doctor linked toolchain must stay inside the stage2 sysroot "
        f"(expected {expected}), got {linked_path!r}"
    )

if compiler["discovery_source"] not in {
    "sibling_trustc",
    "repo_local_stage2",
    "repo_local_stage3",
}:
    raise AssertionError(
        "doctor selected "
        + str(compiler["discovery_source"])
        + " instead of the standalone Trust toolchain"
    )

selected = compiler["path"]
if not selected or os.path.realpath(selected) != os.path.realpath(expected):
    raise AssertionError(
        f"doctor selected compiler {selected} instead of standalone Trust compiler {expected}"
    )

if compiler["trust_verify"] is not True:
    print("SETUP: standalone trustc does not verify by default", file=sys.stderr)
    sys.exit(2)

if compiler["json_transport"] is not True:
    print("SETUP: standalone trustc lacks -Z trust-verify-output=json", file=sys.stderr)
    sys.exit(2)

if compiler["check_report_mode"] != "native_compiler":
    print(
        "SETUP: doctor reports check/report mode "
        + str(compiler["check_report_mode"])
        + " instead of native_compiler",
        file=sys.stderr,
    )
    sys.exit(2)

solvers = report.get("solvers")
if not isinstance(solvers, dict):
    raise AssertionError("missing solvers object")
if solvers.get("available", 0) < 1:
    print("SETUP: doctor reports no available solver", file=sys.stderr)
    sys.exit(2)

suite_by_name = {
    suite.get("name"): suite
    for suite in report.get("verifier_suites", [])
    if isinstance(suite, dict)
}
expected_suites = ["trust-mc", "trust-wp", "trust-vc"]
missing_suites = [name for name in expected_suites if name not in suite_by_name]
if missing_suites:
    raise AssertionError("doctor missing verifier suite(s): " + ", ".join(missing_suites))
for name in expected_suites:
    suite = suite_by_name[name]
    if suite.get("adapter_compiled") is not True:
        raise AssertionError(f"{name} adapter is not compiled: {suite!r}")
    if suite.get("capability_available") is not True:
        raise AssertionError(f"{name} capability is not available: {suite!r}")

if report.get("ready") is not True:
    print(
        "SETUP: doctor reports status " + str(report.get("status")) + " instead of ready",
        file=sys.stderr,
    )
    sys.exit(2)
PY
if [ "$doctor_parse_exit" -ne 0 ]; then
    if [ "$doctor_parse_exit" -eq 2 ]; then
        fail_setup "targo trust doctor --format json reports native verification is not available"
    fi
    echo "FAIL: doctor json did not expose required native-vs-fallback diagnostics"
    echo "--- doctor stdout"
    cat "$DOCTOR_STDOUT"
    echo "--- doctor stderr"
    cat "$DOCTOR_STDERR"
    exit 1
fi
echo "  PASS: doctor json exposes standalone native compiler mode and discovery diagnostics"

echo "--- command surface"
HELP_STDOUT="$TMP_DIR/help.stdout"
SOLVERS_STDOUT="$TMP_DIR/solvers.stdout"
VERSION_STDOUT="$TMP_DIR/version.stdout"
RELEASE_METADATA_STDOUT="$TMP_DIR/release_metadata.stdout"
RELEASE_PRODUCT_PROOF_STDOUT="$TMP_DIR/release_product_proof.stdout"
REPORT_STDOUT="$TMP_DIR/report.stdout"
DIFF_STDOUT="$TMP_DIR/diff.stdout"
INIT_STDOUT="$TMP_DIR/init.stdout"
BUILD_STDERR="$TMP_DIR/build.stderr"
LOOP_STDERR="$TMP_DIR/loop.stderr"
SURFACE_INPUT="$TMP_DIR/surface_midpoint.rs"
INIT_INPUT="$TMP_DIR/init_sample.rs"
BUILD_INPUT="$TMP_DIR/build_ok.rs"
BASELINE_JSON="$TMP_DIR/baseline.json"
CURRENT_JSON="$TMP_DIR/current.json"

cp "$INPUT" "$SURFACE_INPUT"
cat > "$INIT_INPUT" <<'RUST'
pub fn increment(x: i32) -> i32 {
    x + 1
}
RUST
cat > "$BUILD_INPUT" <<'RUST'
fn main() {
}
RUST
cat > "$BASELINE_JSON" <<'JSON'
{"results":[{"kind":"overflow","message":"surface","outcome":"Failed","backend":"trust","time_ms":1}]}
JSON
cat > "$CURRENT_JSON" <<'JSON'
{"results":[{"kind":"overflow","message":"surface","outcome":"Proved","backend":"trust","time_ms":1}]}
JSON

run_public_cli help >"$HELP_STDOUT" 2>"$TMP_DIR/help.stderr"
for subcommand in check build version release verify deps report loop diff init solvers doctor help; do
    if ! grep -q "targo trust $subcommand" "$HELP_STDOUT"; then
        echo "FAIL: help output is missing subcommand surface: $subcommand"
        exit 1
    fi
done

run_public_cli version --repo-root="$TRUST_ROOT" --format=json >"$VERSION_STDOUT" 2>"$TMP_DIR/version.stderr"
python3 - "$VERSION_STDOUT" <<'PY'
import json
import sys

with open(sys.argv[1], "r", encoding="utf-8") as fh:
    report = json.load(fh)

if report.get("schema_version") != "trust.version.v2":
    raise AssertionError("unexpected Trust version schema")
if report.get("candidate_command") != "targo trust version --json":
    raise AssertionError("version identity does not name the canonical command")
tools = report.get("tools")
if not isinstance(tools, dict):
    raise AssertionError("missing tools object")
for key, name in (
    ("frontend", "targo"),
    ("extension", "targo-trust"),
    ("compiler", "trustc"),
):
    tool = tools.get(key)
    if not isinstance(tool, dict) or tool.get("name") != name:
        raise AssertionError(f"missing {name} identity")
PY

run_public_cli release check --repo-root="$TRUST_ROOT" --profile=metadata --format=json >"$RELEASE_METADATA_STDOUT" 2>"$TMP_DIR/release_metadata.stderr"
python3 - "$RELEASE_METADATA_STDOUT" <<'PY'
import json
import sys

with open(sys.argv[1], "r", encoding="utf-8") as fh:
    report = json.load(fh)

if report.get("schema_version") != "trust.release-report.v1":
    raise AssertionError("unexpected release report schema")
if report.get("profile") != "metadata":
    raise AssertionError("metadata release check reported the wrong profile")
if report.get("candidate_command") != "targo trust release check":
    raise AssertionError("metadata release check did not name the canonical command")
if report.get("candidate_command_version") != 1:
    raise AssertionError("metadata release check command version is not 1")
if "reports" not in report or not report["reports"]:
    raise AssertionError("metadata release check did not emit gate reports")
tools = report.get("tools", {})
for key, name in (
    ("frontend", "targo"),
    ("extension", "targo-trust"),
    ("compiler", "trustc"),
):
    if tools.get(key, {}).get("name") != name:
        raise AssertionError(f"metadata report missing {name} identity")
PY

product_proof_exit=0
run_public_cli release check --repo-root="$TRUST_ROOT" --profile=product-proof --format=json >"$RELEASE_PRODUCT_PROOF_STDOUT" 2>"$TMP_DIR/release_product_proof.stderr" || product_proof_exit=$?
if [ "$product_proof_exit" -gt 1 ]; then
    echo "FAIL: product-proof release check exited with unexpected status $product_proof_exit"
    exit 1
fi
python3 - "$RELEASE_PRODUCT_PROOF_STDOUT" <<'PY'
import json
import sys

with open(sys.argv[1], "r", encoding="utf-8") as fh:
    report = json.load(fh)

if report.get("profile") != "product-proof":
    raise AssertionError("product-proof release check reported the wrong profile")
components = {
    component.get("component")
    for component in report.get("product_proof_components", [])
    if isinstance(component, dict)
}
evidence_classes = {
    evidence_class.get("class")
    for evidence_class in report.get("product_proof_evidence_classes", [])
    if isinstance(evidence_class, dict)
}
required_classes = {
    "no-verification compatibility",
    "strict Tier-0 proof",
    "native proof engines",
    "hardened proof",
    "trust-cg",
    "dependency integrity",
    "upstream compatibility",
    "distribution install",
    "self-build",
}
missing_classes = sorted(required_classes - evidence_classes)
if missing_classes:
    raise AssertionError("product-proof evidence-class matrix missing: " + ", ".join(missing_classes))
required = {
    "trustc compiler",
    "targo frontend",
    "targo-trust subcommand implementation",
    "trustdoc",
    "trustfmt",
    "tippy",
    "targo-tippy",
    "tippy-driver",
    "trust-analyzer",
    "trust-miri",
    "std",
    "source/docs",
    "LLVM/trust-cg",
    "stage0",
    "verifier engines",
    "upstream tests",
    "binary/decomp gates",
}
missing = sorted(required - components)
if missing:
    raise AssertionError("product-proof matrix missing: " + ", ".join(missing))
PY

run_public_cli solvers --format json >"$SOLVERS_STDOUT" 2>"$TMP_DIR/solvers.stderr"
python3 - "$SOLVERS_STDOUT" <<'PY'
import json
import sys

with open(sys.argv[1], "r", encoding="utf-8") as fh:
    report = json.load(fh)
solvers = report.get("solvers")
if not isinstance(solvers, list) or not solvers:
    raise AssertionError("expected non-empty solver list")
if report.get("total") != len(solvers):
    raise AssertionError("solver total does not match solver list length")
if not isinstance(report.get("available"), int):
    raise AssertionError("solver report is missing available count")
PY

run_public_cli report --standalone --format json "$SURFACE_INPUT" >"$REPORT_STDOUT" 2>"$TMP_DIR/report.stderr"
python3 - "$REPORT_STDOUT" <<'PY'
import json
import sys

with open(sys.argv[1], "r", encoding="utf-8") as fh:
    report = json.load(fh)
if report.get("mode") != "source-audit":
    raise AssertionError("standalone report did not identify the non-proof source-audit mode")
for field in ("functions_found", "total_audit_rows", "present", "failed", "unknown", "functions", "audit_rows"):
    if field not in report:
        raise AssertionError(f"standalone report is missing {field}")
if not isinstance(report["functions"], list) or not report["functions"]:
    raise AssertionError("standalone report did not include analyzed functions")
PY

run_public_cli diff --baseline "$BASELINE_JSON" --current "$CURRENT_JSON" --format json >"$DIFF_STDOUT" 2>"$TMP_DIR/diff.stderr"
python3 - "$DIFF_STDOUT" <<'PY'
import json
import sys

with open(sys.argv[1], "r", encoding="utf-8") as fh:
    report = json.load(fh)
if report.get("improvements", 0) < 1:
    raise AssertionError("diff output did not report the expected improvement")
PY

run_public_cli init "$INIT_INPUT" >"$INIT_STDOUT" 2>"$TMP_DIR/init.stderr"
if ! grep -q "increment" "$INIT_STDOUT"; then
    echo "FAIL: init output did not mention the target function"
    exit 1
fi

build_exit=0
BUILD_OUTPUT_UNIX="${BUILD_INPUT%.rs}"
BUILD_OUTPUT_EXE="${BUILD_OUTPUT_UNIX}.exe"
rm -f "$BUILD_OUTPUT_UNIX" "$BUILD_OUTPUT_EXE"
run_public_cli build "$BUILD_INPUT" >"$TMP_DIR/build.stdout" 2>"$BUILD_STDERR" || build_exit=$?
if [ "$build_exit" -gt 1 ] \
    || ! grep -q "using native compiler" "$BUILD_STDERR" \
    || ! grep -Eq "\\[(PROVED|FAILED|RUNTIME[- ]CHECKED|UNKNOWN|TIMEOUT)\\]" "$BUILD_STDERR" \
    || { [ ! -x "$BUILD_OUTPUT_UNIX" ] && [ ! -x "$BUILD_OUTPUT_EXE" ]; }; then
    echo "FAIL: build command did not exercise native targo trust surface"
    cat "$BUILD_STDERR"
    exit 1
fi

loop_exit=0
run_public_cli loop --max-iterations 1 "$SURFACE_INPUT" >"$TMP_DIR/loop.stdout" 2>"$LOOP_STDERR" || loop_exit=$?
if [ "$loop_exit" -gt 1 ] || ! grep -q "starting rewrite loop" "$LOOP_STDERR"; then
    echo "FAIL: loop command did not exercise native targo trust surface"
    cat "$LOOP_STDERR"
    exit 1
fi
echo "  PASS: public subcommand surface is present and runnable"

echo "--- terminal mode"
terminal_exit=0
run_public_cli check "$INPUT" >"$TERMINAL_STDOUT" 2>"$TERMINAL_STDERR" || terminal_exit=$?

if [ "$terminal_exit" -gt 1 ]; then
    echo "FAIL: terminal mode exited with unexpected status $terminal_exit"
    exit 1
fi

if grep -q "falling back to standalone source analysis" "$TERMINAL_STDERR"; then
    echo "FAIL: terminal mode fell back to standalone analysis"
    exit 1
fi
if ! grep -Eq 'sibling trustc|repo-local stage[23] canonical trustc' "$TERMINAL_STDERR"; then
    echo "FAIL: terminal mode did not use the standalone Trust toolchain"
    exit 1
fi
if ! grep -q "=== Trust Verification Report ===" "$TERMINAL_STDERR"; then
    echo "FAIL: terminal mode did not render the human report"
    exit 1
fi
if ! grep -q "Level: L2" "$TERMINAL_STDERR"; then
    echo "FAIL: terminal mode did not use the default L2 configuration"
    exit 1
fi
if grep -q "No verification obligations found" "$TERMINAL_STDERR"; then
    echo "FAIL: terminal mode defaulted to an empty verification run"
    exit 1
fi
if ! grep -Eq "get_midpoint|main" "$TERMINAL_STDERR"; then
    echo "FAIL: terminal mode did not report the target function"
    exit 1
fi
if ! grep -Eq "\\[(PROVED|FAILED|RUNTIME[- ]CHECKED|TIMEOUT)\\]" "$TERMINAL_STDERR"; then
    echo "FAIL: terminal mode did not report any verification outcome"
    exit 1
fi
if ! grep -q "Result:" "$TERMINAL_STDERR"; then
    echo "FAIL: terminal mode did not render a final result line"
    exit 1
fi
if grep -q "TRUST_JSON:" "$TERMINAL_STDOUT" "$TERMINAL_STDERR"; then
    echo "FAIL: terminal mode leaked raw TRUST_JSON transport"
    exit 1
fi
echo "  PASS: terminal mode renders a meaningful human summary without raw transport"

echo "--- json mode"
json_exit=0
run_public_cli check --format json "$INPUT" >"$JSON_STDOUT" 2>"$JSON_STDERR" || json_exit=$?

if [ "$json_exit" -gt 1 ]; then
    echo "FAIL: json mode exited with unexpected status $json_exit"
    exit 1
fi

python3 - "$JSON_STDOUT" <<'PY'
import json
import sys

with open(sys.argv[1], "r", encoding="utf-8") as fh:
    report = json.load(fh)

assert "summary" in report, "missing summary"
assert "functions" in report, "missing functions"
assert report["summary"]["total_obligations"] >= 1, "expected at least one obligation"
assert report["functions"], "expected at least one function result"
function_names = {
    str(fn.get("function", "")).split("::")[-1]
    for fn in report["functions"]
}
assert {"get_midpoint", "main"} & function_names, "missing target function"
PY

json_stderr="$(cat "$JSON_STDERR")"
if echo "$json_stderr" | grep -q "falling back to standalone source analysis"; then
    echo "FAIL: json mode fell back to standalone analysis"
    exit 1
fi
if ! echo "$json_stderr" | grep -q "using native compiler"; then
    echo "FAIL: json mode did not use a native compiler"
    exit 1
fi
if ! echo "$json_stderr" | grep -Eq 'sibling trustc|repo-local stage[23] canonical trustc'; then
    echo "FAIL: json mode did not use the standalone Trust toolchain"
    exit 1
fi
if grep -q "TRUST_JSON:" "$JSON_STDOUT" "$JSON_STDERR"; then
    echo "FAIL: json mode leaked raw TRUST_JSON transport"
    exit 1
fi
echo "  PASS: json mode emits canonical JSON report"

echo
echo "=== targo trust public CLI test: PASS ==="
