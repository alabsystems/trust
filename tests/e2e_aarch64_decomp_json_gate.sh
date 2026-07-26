#!/bin/bash
# Narrow release-gate fixture for AArch64 binary decompilation JSON.
#
# This intentionally exercises the public `targo trust` CLI path only. It
# materializes a checked-in AArch64 ELF fixture, runs `targo trust decompile`,
# and asserts that architecture metadata plus unsupported-ledger details are
# visible in the machine-readable report.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
BUILD_PROFILE="${TRUST_CARGO_TRUST_BUILD_PROFILE:-debug}"
UNSUPPORTED_FIXTURE_HEX="$TRUST_ROOT/tests/fixtures/binary_decomp/aarch64-ret-and-unsupported-mrs-elf.hex"
UNSUPPORTED_FIXTURE_SHA256="8879be4512a39c96d0effd56f2a8ad018cc58f2bdb25cb91fbe55805d1686774"
SYSCALL_FIXTURE_HEX="$TRUST_ROOT/tests/fixtures/binary_decomp/aarch64-ret-and-unsupported-svc-elf.hex"
SYSCALL_FIXTURE_SHA256="f07f91032e34ce2fcd239d1284581c25e75be7d3c3ed6c30f2de13b3b1a47ae1"
ACCEPTED_FIXTURE_HEX="$TRUST_ROOT/tests/fixtures/binary_decomp/aarch64-stlr-ldar-ret-elf.hex"
ACCEPTED_FIXTURE_SHA256="6364d04d7cc4be9b62bec3635e3a09641582307360f5eb52e831ecbbe2cd07db"

echo "=== tRust E2E Test: AArch64 decompilation JSON gate ==="
echo

fail_setup() {
    echo "ERROR: $1" >&2
    exit 2
}

fail_test() {
    echo "FAIL: $1" >&2
    exit 1
}

require_command() {
    local cmd="$1"
    local install_hint="$2"
    if ! command -v "$cmd" >/dev/null 2>&1; then
        fail_setup "$cmd not found on PATH. $install_hint"
    fi
}

case "$BUILD_PROFILE" in
    debug|release) ;;
    *) fail_setup "TRUST_CARGO_TRUST_BUILD_PROFILE must be debug or release (got: $BUILD_PROFILE)" ;;
esac

require_command python3 "Install Python 3 for JSON validation."

TRUST_TARGO_CMD=()

resolve_trust_cargo() {
    local candidate

    for candidate in "$TRUST_ROOT/build/host/stage2/bin" "$TRUST_ROOT"/build/*/stage2/bin; do
        if [ -x "$candidate/targo" ] && [ -x "$candidate/trustc" ]; then
            TRUST_TARGO_CMD=("$candidate/targo" --unverified)
            return
        fi
    done

    fail_setup "repo-local stage2 Trust targo/trustc not found. Run ./x.py build --stage 2."
}

trust_cargo() {
    if [ "${#TRUST_TARGO_CMD[@]}" -eq 0 ]; then
        resolve_trust_cargo
    fi
    "${TRUST_TARGO_CMD[@]}" "$@"
}

materialize_fixture() {
    local fixture_hex="$1"
    local output_bin="$2"
    local expected_sha256="$3"

    python3 - "$fixture_hex" "$output_bin" "$expected_sha256" <<'PY'
import binascii
import hashlib
import pathlib
import re
import sys

hex_path = pathlib.Path(sys.argv[1])
out_path = pathlib.Path(sys.argv[2])
expected_sha256 = sys.argv[3]

text = hex_path.read_text(encoding="ascii")
compact = re.sub(r"\s+", "", text)
data = binascii.unhexlify(compact)
actual_sha256 = hashlib.sha256(data).hexdigest()
if actual_sha256 != expected_sha256:
    raise SystemExit(
        f"fixture SHA-256 mismatch for {hex_path}: "
        f"expected {expected_sha256}, got {actual_sha256}"
    )
out_path.write_bytes(data)
print(f"fixture {hex_path.name}: {len(data)} bytes, sha256={actual_sha256}")
PY
}

build_args=(build --manifest-path "$TRUST_ROOT/targo-trust/Cargo.toml" --bin targo-trust)
if [ "$BUILD_PROFILE" = "release" ]; then
    build_args+=(--release)
fi

if [ -n "${CARGO_TRUST_BIN:-}" ]; then
    CARGO_TRUST="$CARGO_TRUST_BIN"
else
    echo "--- build targo-trust with targo ($BUILD_PROFILE)"
    trust_cargo "${build_args[@]}"

    if [ "$BUILD_PROFILE" = "release" ]; then
        candidates=(
            "${CARGO_TARGET_DIR:-$TRUST_ROOT/target}/release/targo-trust"
            "$TRUST_ROOT/targo-trust/target/release/targo-trust"
            "$TRUST_ROOT/target/release/targo-trust"
            "$TRUST_ROOT/target/user/release/targo-trust"
        )
    else
        candidates=(
            "${CARGO_TARGET_DIR:-$TRUST_ROOT/target}/debug/targo-trust"
            "$TRUST_ROOT/targo-trust/target/debug/targo-trust"
            "$TRUST_ROOT/target/debug/targo-trust"
            "$TRUST_ROOT/target/user/debug/targo-trust"
        )
    fi

    CARGO_TRUST=""
    for candidate in "${candidates[@]}"; do
        if [ -x "$candidate" ]; then
            CARGO_TRUST="$candidate"
            break
        fi
    done
fi

if [ ! -x "$CARGO_TRUST" ]; then
    fail_setup "targo-trust binary is missing or not executable: $CARGO_TRUST"
fi

TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/trust-aarch64-decomp-json.XXXXXX")"
trap 'rm -rf "$TMP_DIR"' EXIT

INPUT_BIN="$TMP_DIR/aarch64-ret-and-unsupported-mrs.elf"
REPORT_JSON="$TMP_DIR/decompile-aarch64-unsupported.json"
REPORT_STDERR="$TMP_DIR/decompile-aarch64-unsupported.stderr"
SYSCALL_BIN="$TMP_DIR/aarch64-ret-and-unsupported-svc.elf"
SYSCALL_REPORT_JSON="$TMP_DIR/decompile-aarch64-unsupported-svc.json"
SYSCALL_REPORT_STDERR="$TMP_DIR/decompile-aarch64-unsupported-svc.stderr"
ACCEPTED_BIN="$TMP_DIR/aarch64-stlr-ldar-ret.elf"
ACCEPTED_REPORT_JSON="$TMP_DIR/decompile-aarch64-accepted-release-acquire.json"
ACCEPTED_REPORT_STDERR="$TMP_DIR/decompile-aarch64-accepted-release-acquire.stderr"

echo "--- materialize checked-in AArch64 unsupported-ledger fixture"
materialize_fixture "$UNSUPPORTED_FIXTURE_HEX" "$INPUT_BIN" "$UNSUPPORTED_FIXTURE_SHA256"

echo "--- targo trust decompile AArch64 fixture --json"
status=0
"$CARGO_TRUST" decompile "$INPUT_BIN" --to trust_ir --all --allow-unsupported --json \
    >"$REPORT_JSON" 2>"$REPORT_STDERR" || status=$?
if [ "$status" -ne 0 ]; then
    echo "--- decompile stderr" >&2
    cat "$REPORT_STDERR" >&2
    fail_test "targo trust decompile AArch64 unsupported-ledger fixture exited $status"
fi

python3 - "$REPORT_JSON" "$INPUT_BIN" <<'PY'
import json
import os
import sys

report_path, expected_binary = sys.argv[1:3]
with open(report_path, "r", encoding="utf-8") as fh:
    report = json.load(fh)

def require(condition, message):
    if not condition:
        raise AssertionError(message)

require(os.path.realpath(report.get("binary", "")) == os.path.realpath(expected_binary), "binary path mismatch")
require(report.get("target") == "trust_ir", f"expected trust_ir target, got {report.get('target')!r}")
require(report.get("selection") == "all", "expected all-functions selection")
require(report.get("format") == "ELF", f"expected ELF format, got {report.get('format')!r}")
require(report.get("architecture") == "AArch64", f"expected AArch64 architecture, got {report.get('architecture')!r}")
require(report.get("strict") is False, "allow-unsupported should set strict false")
require(report.get("status") == "incomplete", f"expected incomplete status, got {report.get('status')!r}")
require(report.get("functions_decompiled") == 2, f"expected two retained supported functions, got {report.get('functions_decompiled')!r}")
require(report.get("unsupported", 0) >= 1, "expected unsupported ledger entries")
require(report.get("output_kind") == "trust_ir_json", f"expected trust_ir_json output, got {report.get('output_kind')!r}")
require(report.get("output_trust_level") == "partial", "unsupported AArch64 output must remain partial")

items = report.get("unsupported_items")
require(isinstance(items, list) and items, "unsupported_items should be a non-empty list")
require(any("trust_fixture_unsupported_mrs" in item for item in items), f"missing unsupported symbol in ledger: {items!r}")
require(any("unsupported instruction semantics" in item for item in items), f"missing unsupported semantic diagnostic: {items!r}")

artifact = json.loads(report.get("output_content") or "")
records = artifact.get("unsupported", {}).get("records", [])
require(len(records) == report.get("unsupported"), "report unsupported count should match artifact ledger")
require(
    any(str(record.get("stage", "")).startswith("trust-lift") for record in records),
    "expected trust-lift unsupported ledger stage",
)
PY

echo "--- materialize checked-in AArch64 SVC syscall/trap fail-closed fixture"
materialize_fixture "$SYSCALL_FIXTURE_HEX" "$SYSCALL_BIN" "$SYSCALL_FIXTURE_SHA256"

echo "--- targo trust decompile AArch64 SVC fixture --json"
status=0
"$CARGO_TRUST" decompile "$SYSCALL_BIN" --to trust_ir --all --allow-unsupported --json \
    >"$SYSCALL_REPORT_JSON" 2>"$SYSCALL_REPORT_STDERR" || status=$?
if [ "$status" -ne 0 ]; then
    echo "--- SVC decompile stderr" >&2
    cat "$SYSCALL_REPORT_STDERR" >&2
    fail_test "targo trust decompile AArch64 SVC unsupported-ledger fixture exited $status"
fi

python3 - "$SYSCALL_REPORT_JSON" "$SYSCALL_BIN" <<'PY'
import json
import os
import sys

report_path, expected_binary = sys.argv[1:3]
with open(report_path, "r", encoding="utf-8") as fh:
    report = json.load(fh)

def require(condition, message):
    if not condition:
        raise AssertionError(message)

require(os.path.realpath(report.get("binary", "")) == os.path.realpath(expected_binary), "SVC binary path mismatch")
require(report.get("target") == "trust_ir", f"expected trust_ir target, got {report.get('target')!r}")
require(report.get("selection") == "all", "expected all-functions selection for SVC fixture")
require(report.get("format") == "ELF", f"expected ELF format, got {report.get('format')!r}")
require(report.get("architecture") == "AArch64", f"expected AArch64 architecture, got {report.get('architecture')!r}")
require(report.get("strict") is False, "allow-unsupported should set strict false")
require(report.get("status") == "incomplete", f"expected incomplete SVC status, got {report.get('status')!r}")
require(report.get("functions_decompiled") == 2, f"expected two retained supported functions, got {report.get('functions_decompiled')!r}")
require(report.get("unsupported", 0) >= 1, "expected SVC unsupported ledger entries")
require(report.get("output_kind") == "trust_ir_json", f"expected trust_ir_json output, got {report.get('output_kind')!r}")
require(report.get("output_trust_level") == "partial", "SVC unsupported output must remain partial")

items = report.get("unsupported_items")
require(isinstance(items, list) and items, "SVC unsupported_items should be a non-empty list")
for fragment in [
    "trust_fixture_unsupported_svc",
    "unsupported instruction semantics",
    "opcode Svc",
    "AArch64 syscall/trap semantics are unsupported fail-closed",
    "proof-consumed syscall/trap witnesses",
    "unsupported-ledger coverage",
    "status=not proof-consumed",
]:
    require(any(fragment in item for item in items), f"missing SVC ledger fragment {fragment!r}: {items!r}")

artifact = json.loads(report.get("output_content") or "")
records = artifact.get("unsupported", {}).get("records", [])
require(len(records) == report.get("unsupported"), "SVC report unsupported count should match artifact ledger")
svc_records = [
    record for record in records
    if "trust_fixture_unsupported_svc" in str(record.get("feature", ""))
]
require(svc_records, f"missing SVC artifact ledger record: {records!r}")
record = svc_records[0]
require(record.get("stage") == "trust-lift", f"SVC record should come from trust-lift: {record!r}")
require(record.get("architecture") == "AArch64", f"SVC record should retain AArch64 architecture: {record!r}")
origin = record.get("origin") or {}
require(origin.get("instruction_address") == 0x40000c, f"SVC record should bind exact instruction address: {origin!r}")
feature = record.get("feature", "")
for fragment in [
    "encoding 0xd4000001",
    "bytes [0x01, 0x00, 0x00, 0xd4]",
    "can enter the kernel",
    "proof-consumed syscall/trap witnesses",
]:
    require(fragment in feature, f"SVC artifact record missing {fragment!r}: {feature}")

binary_evidence = report.get("binary_evidence") or {}
evidence_ledger = binary_evidence.get("unsupported_ledger") or {}
evidence_records = evidence_ledger.get("records") or []
require(evidence_ledger.get("empty") is False, f"SVC binary evidence ledger should be non-empty: {evidence_ledger!r}")
require(evidence_ledger.get("total_records") == report.get("unsupported"), "SVC evidence ledger count should match report")
require(
    any("trust_fixture_unsupported_svc" in str(record.get("feature", "")) for record in evidence_records),
    f"SVC binary evidence should expose unsupported-ledger record: {evidence_records!r}",
)
release_gate = binary_evidence.get("release_gate") or {}
require(release_gate.get("accepted") is False, f"SVC release gate must reject proof-grade: {release_gate!r}")
PY

echo "--- materialize checked-in AArch64 accepted STLR/LDAR empty-ledger fixture"
materialize_fixture "$ACCEPTED_FIXTURE_HEX" "$ACCEPTED_BIN" "$ACCEPTED_FIXTURE_SHA256"

echo "--- targo trust decompile AArch64 accepted STLR/LDAR fixture --json"
status=0
"$CARGO_TRUST" decompile "$ACCEPTED_BIN" --to trust_ir --all --allow-unsupported --json \
    >"$ACCEPTED_REPORT_JSON" 2>"$ACCEPTED_REPORT_STDERR" || status=$?
if [ "$status" -ne 0 ]; then
    echo "--- accepted decompile stderr" >&2
    cat "$ACCEPTED_REPORT_STDERR" >&2
    fail_test "targo trust decompile AArch64 accepted STLR/LDAR fixture exited $status"
fi

python3 - "$ACCEPTED_REPORT_JSON" "$ACCEPTED_BIN" <<'PY'
import json
import os
import sys

report_path, expected_binary = sys.argv[1:3]
with open(report_path, "r", encoding="utf-8") as fh:
    report = json.load(fh)

def require(condition, message):
    if not condition:
        raise AssertionError(message)

require(os.path.realpath(report.get("binary", "")) == os.path.realpath(expected_binary), "accepted binary path mismatch")
require(report.get("target") == "trust_ir", f"expected trust_ir target, got {report.get('target')!r}")
require(report.get("selection") == "all", "expected all-functions selection for accepted fixture")
require(report.get("format") == "ELF", f"expected ELF format, got {report.get('format')!r}")
require(report.get("architecture") == "AArch64", f"expected AArch64 architecture, got {report.get('architecture')!r}")
require(report.get("strict") is False, "allow-unsupported should set strict false")
require(report.get("status") == "incomplete", f"expected fail-closed incomplete status for accepted ordering slice without provenance, got {report.get('status')!r}")
require(report.get("functions_decompiled") == 1, f"expected one accepted decompiled function, got {report.get('functions_decompiled')!r}")
require(report.get("unsupported") == 5, f"accepted ordering slice should expose only provenance/artifact fail-closed records, got {report.get('unsupported')!r}")
require(report.get("memory_facts") == 2, f"expected STLR/LDAR memory facts, got {report.get('memory_facts')!r}")
require(report.get("output_kind") == "trust_ir_json", f"expected trust_ir_json output, got {report.get('output_kind')!r}")
require(report.get("output_trust_level") == "partial", "missing provenance must keep accepted ordering slice partial")

items = report.get("unsupported_items")
require(isinstance(items, list) and len(items) == 5, f"expected five fail-closed provenance/artifact items: {items!r}")
for forbidden in [
    "symbolic formula sort",
    "incompatible with contextual destination type",
    "aggregate Undef",
]:
    require(not any(forbidden in item for item in items), f"formula-sort blocker leaked into accepted fixture ledger: {items!r}")
for fragment in [
    "trust-lift::memory-provenance @ 0x400000: unclassified memory region",
    "trust-lift::memory-provenance @ 0x400004: unclassified memory region",
    "trust-lift::source-provenance @ 0x400000: non-exact source provenance: unavailable",
    "trust-lift::type-provenance @ 0x400000: non-recovered debug type provenance: unavailable",
    "trust-binary-parse::artifact-identity: parser artifact identity is not proof-grade bindable",
]:
    require(any(fragment in item for item in items), f"missing expected fail-closed item {fragment!r}: {items!r}")

artifact = json.loads(report.get("output_content") or "")
records = artifact.get("unsupported", {}).get("records", [])
require(len(records) == report.get("unsupported"), "accepted report unsupported count should match artifact ledger")
record_pairs = [(record.get("stage"), record.get("feature")) for record in records]
require(
    record_pairs.count(("trust-lift::memory-provenance", "unclassified memory region")) == 2,
    f"expected two memory-provenance records, got {record_pairs!r}",
)
for stage, feature in [
    ("trust-lift::source-provenance", "non-exact source provenance: unavailable"),
    ("trust-lift::type-provenance", "non-recovered debug type provenance: unavailable"),
]:
    require((stage, feature) in record_pairs, f"missing fail-closed record {(stage, feature)!r}: {record_pairs!r}")
require(
    any(
        stage == "trust-binary-parse::artifact-identity"
        and str(feature).startswith("parser artifact identity is not proof-grade bindable")
        for stage, feature in record_pairs
    ),
    f"missing parser artifact identity fail-closed record: {record_pairs!r}",
)

def attr_value(op, name):
    for attr in op.get("attrs", []):
        if attr.get("name") == name:
            value = attr.get("value")
            if isinstance(value, dict) and "Str" in value:
                return value["Str"]
            return value
    return None

module_functions = artifact.get("module", {}).get("functions", [])
require(len(module_functions) == 1, f"expected one TrustIr module function, got {len(module_functions)}")
module_blocks = module_functions[0].get("blocks", [])
require(len(module_blocks) == 1, f"expected one TrustIr module block, got {len(module_blocks)}")
memory_state_ops = []
for node in module_blocks[0].get("body", []):
    op = node.get("inst", {}).get("DialectOp")
    if op and op.get("dialect") == "trust_symbolic" and op.get("op") == "memory_state":
        memory_state_ops.append((node, op))
require(len(memory_state_ops) == 1, f"expected one preserved symbolic memory-state op, got {memory_state_ops!r}")
memory_node, memory_op = memory_state_ops[0]
require(memory_node.get("results") == [], f"memory-state formula must not coerce to a scalar result: {memory_node!r}")
require(memory_op.get("result_tys") == [], f"memory-state formula must not declare a u64 result: {memory_op!r}")
require(
    attr_value(memory_op, "formula.sort") == "(Array (_ BitVec 64) (_ BitVec 8))",
    f"memory-state formula must preserve byte-addressed SMT array sort: {memory_op!r}",
)
require(
    attr_value(memory_op, "formula.context") == "lifted-memory-state",
    f"memory-state formula must carry lifted-memory-state context: {memory_op!r}",
)

functions = artifact.get("functions", [])
require(len(functions) == 1, f"expected one artifact function, got {len(functions)}")
function = functions[0]
require(function.get("name") == "trust_fixture_release_acquire", f"unexpected accepted function name: {function.get('name')!r}")
function_records = function.get("unsupported", {}).get("records", [])
require(len(function_records) == 4, f"accepted function should carry only function-scoped provenance blockers: {function_records!r}")
accesses = function.get("memory_accesses", [])
require(len(accesses) == 2, f"expected two memory facts, got {len(accesses)}")

by_role = {}
for access in accesses:
    provenance = access.get("provenance") or ""
    if "role=release" in provenance:
        by_role["release"] = (access, provenance)
    if "role=acquire" in provenance:
        by_role["acquire"] = (access, provenance)

require(set(by_role) == {"release", "acquire"}, f"missing release/acquire evidence roles: {by_role.keys()!r}")

release, release_provenance = by_role["release"]
acquire, acquire_provenance = by_role["acquire"]
require(release.get("kind") == "Write", f"STLR should be a write fact: {release!r}")
require(acquire.get("kind") == "Read", f"LDAR should be a read fact: {acquire!r}")
require(release.get("address") == acquire.get("address"), "release/acquire facts must bind the same atomic location")

common_fragments = [
    "accepted-slice:aarch64.release_acquire",
    "status=proof-consumed",
    "evidence_schema=trust-lift.aarch64.release_acquire_ordering_evidence@1",
    "artifact_row_schema=trust-lift.aarch64.ordering_monitor_evidence_row@1",
    "artifact_row_type=aarch64_ordering_monitor_evidence",
    "artifact_row_status=accepted",
    "unsupported_ledger_boundary=explicit-empty",
    "unsupported_ledger_records=0",
    "exclusive_monitor=None",
    "exclusive_monitor_witness=not-applicable-reviewed",
    "store_conditional_status=not-applicable-reviewed",
    "synchronization_edge=absent-reviewed",
    "happens_before_witness=absent-reviewed",
    "thread_identity=absent-reviewed",
    "reviewed_unsupported_absence=[barrier absent-reviewed, exclusive-monitor absent-reviewed, store-conditional-status absent-reviewed, system-register absent-reviewed, FP/SIMD absent-reviewed, trap absent-reviewed, syscall absent-reviewed, unsupported-opcode absent-reviewed]",
    "aarch64_ordering_monitor_evidence_status=accepted",
    "aarch64_ordering_monitor_evidence_exclusive_monitor=None",
    "aarch64_ordering_monitor_evidence_blockers=[]",
    "release_transcript_consumed=true",
    "release_transcript_digest=sha256:",
    "no FP/SIMD/syscall/trap/exception claim",
    "no exclusive-monitor/status claim",
]
for label, provenance in [("release", release_provenance), ("acquire", acquire_provenance)]:
    for fragment in common_fragments:
        require(fragment in provenance, f"{label} provenance missing {fragment!r}: {provenance}")

for fragment in [
    "opcode=Stlr",
    "ordering=Release",
    "ordering_event=release ordering event",
    "aarch64_ordering_monitor_evidence_opcode=Stlr",
    "aarch64_ordering_monitor_evidence_ordering=Release",
]:
    require(fragment in release_provenance, f"release provenance missing {fragment!r}: {release_provenance}")

for fragment in [
    "opcode=Ldar",
    "ordering=Acquire",
    "ordering_event=acquire ordering event",
    "aarch64_ordering_monitor_evidence_opcode=Ldar",
    "aarch64_ordering_monitor_evidence_ordering=Acquire",
]:
    require(fragment in acquire_provenance, f"acquire provenance missing {fragment!r}: {acquire_provenance}")
PY

echo
echo "=== tRust E2E Test: AArch64 decompilation JSON gate: PASS ==="
