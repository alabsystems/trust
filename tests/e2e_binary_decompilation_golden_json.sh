#!/bin/bash
# Focused release-gate smoke for targo-trust binary decompilation JSON.
#
# The gate builds the local targo-trust binary, materializes checked-in
# x86_64 and AArch64 ELF fixtures, and checks
# the stable JSON contract for Rust skeleton, TrustIr, derived conversion outputs,
# and verify-binary proof-evidence summaries. It also runs focused existing Rust
# tests for binary replay and certificate gates so this script does not duplicate
# proof logic.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
ALLOW_REVIEW_GATE_SKIPS="${TRUST_ALLOW_REVIEW_GATE_SKIPS:-0}"
BUILD_PROFILE="${TRUST_CARGO_TRUST_BUILD_PROFILE:-debug}"
X86_64_FIXTURE_HEX="$TRUST_ROOT/tests/fixtures/binary_decomp/x86_64-load-elf.hex"
X86_64_FIXTURE_SHA256="251757e36749c41d81a42feb4764e9ed80c354990f9de66858a498e549524000"
X86_64_ENTRY="0x400000"
AARCH64_FIXTURE_HEX="$TRUST_ROOT/tests/fixtures/binary_decomp/aarch64-ret-elf.hex"
AARCH64_FIXTURE_SHA256="76e21c45581b19d655f08eb1564e33b389c80a739b49296f8f339e27597a3e02"
AARCH64_UNSUPPORTED_FIXTURE_HEX="$TRUST_ROOT/tests/fixtures/binary_decomp/aarch64-ret-and-unsupported-mrs-elf.hex"
AARCH64_UNSUPPORTED_FIXTURE_SHA256="8879be4512a39c96d0effd56f2a8ad018cc58f2bdb25cb91fbe55805d1686774"

echo "=== tRust E2E Test: binary decompilation golden JSON ==="
echo

fail_setup() {
    echo "ERROR: $1" >&2
    exit 2
}

fail_test() {
    echo "FAIL: $1" >&2
    exit 1
}

skip_gate() {
    local reason="$1"
    echo "SKIP: $reason" >&2
    if [ "$ALLOW_REVIEW_GATE_SKIPS" = "1" ]; then
        exit 0
    fi
    echo "FAIL: binary decompilation release gate does not allow SKIP without TRUST_ALLOW_REVIEW_GATE_SKIPS=1" >&2
    exit 2
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

materialize_hex_fixture() {
    local hex_path="$1"
    local out_path="$2"
    local expected_sha256="$3"

    python3 - "$hex_path" "$out_path" "$expected_sha256" <<'PY'
import binascii
import hashlib
import pathlib
import re
import sys

hex_path = pathlib.Path(sys.argv[1])
out_path = pathlib.Path(sys.argv[2])
expected_sha256 = sys.argv[3]

if not hex_path.is_file():
    raise SystemExit(f"missing fixture hex: {hex_path}")

text = hex_path.read_text(encoding="ascii")
compact = re.sub(r"\s+", "", text)
if not compact:
    raise SystemExit(f"empty fixture hex: {hex_path}")
if re.search(r"[^0-9a-fA-F]", compact):
    raise SystemExit(f"fixture contains non-hex bytes: {hex_path}")

try:
    data = binascii.unhexlify(compact)
except binascii.Error as exc:
    raise SystemExit(f"invalid fixture hex {hex_path}: {exc}") from exc

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

require_named_test() {
    local source_path="$1"
    local test_name="$2"
    python3 - "$source_path" "$test_name" <<'PY'
import re
import sys

path, test_name = sys.argv[1:3]
text = open(path, encoding="utf-8").read()
pattern = rf"fn\s+{re.escape(test_name)}\s*\("
if not re.search(pattern, text):
    raise SystemExit(f"missing expected test in {path}: {test_name}")
PY
}

require_targo_trust_test() {
    local test_name="$1"
    require_named_test "$TRUST_ROOT/targo-trust/src/tests.rs" "$test_name"
}

run_targo_trust_test() {
    trust_cargo test --manifest-path "$TRUST_ROOT/targo-trust/Cargo.toml" "$@"
}

require_targo_trust_rewrite_loop_test() {
    local test_name="$1"
    require_named_test "$TRUST_ROOT/targo-trust/src/rewrite_loop/tests.rs" "$test_name"
}

require_trust_ir_bridge_test() {
    local test_name="$1"
    require_named_test "$TRUST_ROOT/crates/trust-ir-bridge/src/tests.rs" "$test_name"
}

run_checked_certificate_manifest_gate() {
    local manifest_gate_selection

    echo "--- checked certificate manifest release gate coverage"
    if ! manifest_gate_selection="$(python3 - "$TRUST_ROOT" <<'PY'
import pathlib
import re
import sys

root = pathlib.Path(sys.argv[1])


def read(rel):
    path = root / rel
    try:
        return path.read_text(encoding="utf-8")
    except FileNotFoundError:
        return ""


cargo_cli = read("targo-trust/src/cli.rs")
cargo_main = read("targo-trust/src/main.rs")
cargo_tests = read("targo-trust/src/tests.rs")
checked_src = (
    read("crates/trust-proof-cert/src/checked_binary_certificate.rs")
    + read("crates/trust-proof-cert/src/lib.rs")
)
checked_tests = read("crates/trust-proof-cert/tests/checked_binary_certificate.rs")

cargo_manifest_test = re.search(
    r"fn\s+(test_[A-Za-z0-9_]*checked_(?:certificate|cert)_manifest[A-Za-z0-9_]*)\s*\(",
    cargo_tests,
)
verify_binary_manifest_import_visible = (
    "--checked-cert-manifest" in cargo_cli
    and "--checked-cert-manifest" in cargo_main
    and "checked_certificate_manifests" in cargo_cli + cargo_main
    and "verify-binary" in cargo_main
    and cargo_manifest_test is not None
)

checked_manifest_rejection_test = re.search(
    r"fn\s+(checked_binary_certificate_manifest[A-Za-z0-9_]*reject[A-Za-z0-9_]*)\s*\(",
    checked_tests,
)
checked_manifest_rejection_visible = (
    "CheckedBinaryCertificateManifest" in checked_src
    and checked_manifest_rejection_test is not None
)

if verify_binary_manifest_import_visible:
    print(f"targo-trust:{cargo_manifest_test.group(1)}")
elif checked_manifest_rejection_visible:
    print(f"trust-proof-cert:{checked_manifest_rejection_test.group(1)}")
else:
    print(
        "binary decompilation release gate is missing checked-certificate manifest coverage",
        file=sys.stderr,
    )
    print(
        "expected either targo trust verify-binary --checked-cert-manifest visibility "
        "with a focused targo-trust test, or CheckedBinaryCertificateManifest rejection "
        "coverage in trust-proof-cert",
        file=sys.stderr,
    )
    sys.exit(1)
PY
)"; then
        fail_test "checked certificate manifest release gate coverage is missing"
    fi

    case "$manifest_gate_selection" in
        targo-trust:*)
            run_targo_trust_test "${manifest_gate_selection#targo-trust:}"
            ;;
        trust-proof-cert:*)
            trust_cargo test --manifest-path "$TRUST_ROOT/crates/Cargo.toml" -p trust-proof-cert \
                --test checked_binary_certificate "${manifest_gate_selection#trust-proof-cert:}"
            ;;
        *)
            fail_setup "unexpected checked certificate manifest gate selector: $manifest_gate_selection"
            ;;
    esac
}

run_checked_certificate_manifest_gate

echo "--- focused binary gate inventory"
require_targo_trust_test test_failed_x86_64_solver_result_replays_exact_instruction_bytes
require_targo_trust_test test_failed_x86_64_replay_with_mismatched_instruction_size_fails_closed
require_targo_trust_test test_exact_replay_sat_candidate_matches_checked_in_golden
require_targo_trust_test test_confirmed_replay_without_exact_original_bytes_fails_closed
require_targo_trust_test test_verify_binary_proof_grade_gate_rejects_missing_evidence_in_terminal_and_json
require_targo_trust_test test_verify_binary_raw_solver_proof_bytes_do_not_satisfy_proof_grade_gate
require_targo_trust_test test_decompile_output_kind_routes_derived_targets_to_text_outputs
require_targo_trust_test test_parse_convert_target_accepts_binary_conversion_targets
require_targo_trust_test test_convert_partial_derived_output_fails_without_proof_grade_claim
require_targo_trust_test test_convert_rejects_proof_grade_label_until_all_binary_release_gate_conditions_hold
require_targo_trust_test test_verify_binary_report_surfaces_checked_certificate_import_json_and_terminal
require_targo_trust_test test_x86_64_empty_ledger_release_evidence_matches_golden_and_blocks_release
require_targo_trust_test test_verify_binary_imports_produced_checked_certificate_and_matches_refutation_golden
require_targo_trust_test test_convert_report_surfaces_symbolic_formula_metadata_in_json_and_terminal
require_targo_trust_rewrite_loop_test test_strengthen_failures_rejects_binary_source_without_exact_provenance
require_targo_trust_rewrite_loop_test test_runtime_strengthen_wrapper_keeps_binary_source_closed
require_targo_trust_rewrite_loop_test test_binary_source_backpropagation_blockers_require_exact_runtime_provenance
require_targo_trust_test test_exploit_find_report_captures_phase_diagnostics_without_claiming_exploit
require_targo_trust_test test_exploit_find_raw_solver_failure_requires_replay_before_confirmation
require_targo_trust_test test_exploit_find_checked_unsat_certificate_without_claim_does_not_satisfy_refutation
require_targo_trust_test test_exploit_find_sat_candidate_requires_exact_replay_even_with_checked_unsat_evidence
require_targo_trust_test test_exploit_find_replayed_sat_candidate_without_checked_refutation_stays_blocked
require_targo_trust_test test_exploit_find_fails_even_when_binary_vcs_are_proved
require_trust_ir_bridge_test test_symbolic_operand_lowers_to_formula_dialect_not_undef
require_trust_ir_bridge_test test_symbolic_aggregate_lowers_without_undef_seed
require_trust_ir_bridge_test test_symbolic_array_repeat_lowers_without_undef_seed

echo "--- targo-trust binary release unit gates"
for targo_trust_filter in \
    verify_binary \
    decompile \
    convert \
    exact_replay \
    exploit_find \
    checked_certificate \
    binary_source \
    symbolic
do
    trust_cargo test --manifest-path "$TRUST_ROOT/targo-trust/Cargo.toml" "$targo_trust_filter"
done

echo "--- symbolic formula TrustIr lowering unit gates"
trust_cargo test --manifest-path "$TRUST_ROOT/crates/Cargo.toml" -p trust-ir-bridge symbolic

echo "--- trust-proof-cert checked binary certificate gates"
trust_cargo test --manifest-path "$TRUST_ROOT/crates/Cargo.toml" -p trust-proof-cert \
    --test checked_binary_certificate \
    --test binary_decomp_certificate_gate

build_args=(build --manifest-path "$TRUST_ROOT/targo-trust/Cargo.toml" --bin targo-trust)
if [ "$BUILD_PROFILE" = "release" ]; then
    build_args+=(--release)
fi

echo "--- build targo-trust ($BUILD_PROFILE)"
trust_cargo "${build_args[@]}"

if [ -n "${CARGO_TRUST_BIN:-}" ]; then
    CARGO_TRUST="$CARGO_TRUST_BIN"
elif [ "$BUILD_PROFILE" = "release" ]; then
    for candidate in \
        "${CARGO_TARGET_DIR:-$TRUST_ROOT/target}/release/targo-trust" \
        "$TRUST_ROOT/targo-trust/target/release/targo-trust" \
        "$TRUST_ROOT/target/release/targo-trust" \
        "$TRUST_ROOT/target/user/release/targo-trust"
    do
        if [ -x "$candidate" ]; then
            CARGO_TRUST="$candidate"
            break
        fi
    done
else
    for candidate in \
        "${CARGO_TARGET_DIR:-$TRUST_ROOT/target}/debug/targo-trust" \
        "$TRUST_ROOT/targo-trust/target/debug/targo-trust" \
        "$TRUST_ROOT/target/debug/targo-trust" \
        "$TRUST_ROOT/target/user/debug/targo-trust"
    do
        if [ -x "$candidate" ]; then
            CARGO_TRUST="$candidate"
            break
        fi
    done
fi

CARGO_TRUST="${CARGO_TRUST:-}"

if [ ! -x "$CARGO_TRUST" ]; then
    fail_setup "built targo-trust binary is missing or not executable: $CARGO_TRUST"
fi

TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/trust-binary-decomp.XXXXXX")"
trap 'rm -rf "$TMP_DIR"' EXIT

INPUT_BIN="$TMP_DIR/x86_64-load.elf"
RUST_JSON="$TMP_DIR/decompile-rust.json"
TRUST_IR_JSON="$TMP_DIR/decompile-trust_ir.json"
trust_cg_JSON="$TMP_DIR/convert-trust-cg.json"
trust_cg_STDERR="$TMP_DIR/convert-trust-cg.stderr"
WASM_JSON="$TMP_DIR/convert-wasm.json"
WASM_STDERR="$TMP_DIR/convert-wasm.stderr"
VERIFY_BINARY_JSON="$TMP_DIR/verify-binary.json"
VERIFY_BINARY_STDERR="$TMP_DIR/verify-binary.stderr"
VERIFY_BINARY_TERMINAL="$TMP_DIR/verify-binary.terminal"
VERIFY_BINARY_TERMINAL_STDERR="$TMP_DIR/verify-binary-terminal.stderr"
STRICT_JSON="$TMP_DIR/decompile-strict.json"
STRICT_STDERR="$TMP_DIR/decompile-strict.stderr"
RUST_STDERR="$TMP_DIR/decompile-rust.stderr"
TRUST_IR_STDERR="$TMP_DIR/decompile-trust_ir.stderr"
BAD_FORMAT_BIN="$TMP_DIR/not-an-object.bin"
BAD_FORMAT_JSON="$TMP_DIR/decompile-bad-format.json"
BAD_FORMAT_STDERR="$TMP_DIR/decompile-bad-format.stderr"
BAD_TARGET_BIN="$TMP_DIR/unsupported-target.o"
BAD_TARGET_JSON="$TMP_DIR/decompile-bad-target.json"
BAD_TARGET_STDERR="$TMP_DIR/decompile-bad-target.stderr"
PE_BIN="$TMP_DIR/minimal-pe.bin"
PE_JSON="$TMP_DIR/decompile-pe.json"
PE_STDERR="$TMP_DIR/decompile-pe.stderr"
I386_ELF_BIN="$TMP_DIR/minimal-i386.o"
I386_ELF_JSON="$TMP_DIR/decompile-i386.json"
I386_ELF_STDERR="$TMP_DIR/decompile-i386.stderr"
AARCH64_BIN="$TMP_DIR/aarch64-ret.elf"
AARCH64_JSON="$TMP_DIR/decompile-aarch64.json"
AARCH64_STDERR="$TMP_DIR/decompile-aarch64.stderr"
AARCH64_UNSUPPORTED_BIN="$TMP_DIR/aarch64-ret-and-unsupported-mrs.elf"
AARCH64_UNSUPPORTED_JSON="$TMP_DIR/decompile-aarch64-unsupported.json"
AARCH64_UNSUPPORTED_STDERR="$TMP_DIR/decompile-aarch64-unsupported.stderr"

echo "--- materialize checked-in x86_64 ELF fixture"
materialize_hex_fixture "$X86_64_FIXTURE_HEX" "$INPUT_BIN" "$X86_64_FIXTURE_SHA256"

if [ ! -s "$INPUT_BIN" ]; then
    fail_setup "checked-in x86_64 fixture did not materialize to a non-empty ELF binary"
fi

echo "--- targo trust decompile --to trust_ir --strict --json"
strict_status=0
"$CARGO_TRUST" decompile "$INPUT_BIN" --to trust_ir --entry "$X86_64_ENTRY" --strict --json \
    >"$STRICT_JSON" 2>"$STRICT_STDERR" || strict_status=$?
if [ "$strict_status" -eq 0 ]; then
    fail_test "targo trust decompile --to trust_ir --strict --json unexpectedly succeeded; strict mode must fail closed on unsupported coverage"
fi

echo "--- targo trust decompile --to rust --json"
rust_status=0
"$CARGO_TRUST" decompile "$INPUT_BIN" --to rust --entry "$X86_64_ENTRY" --allow-unsupported --json \
    >"$RUST_JSON" 2>"$RUST_STDERR" || rust_status=$?
if [ "$rust_status" -ne 0 ]; then
    echo "--- decompile rust stderr" >&2
    cat "$RUST_STDERR" >&2
    fail_test "targo trust decompile --to rust --json exited $rust_status"
fi

echo "--- targo trust decompile --to trust_ir --json"
trust_ir_status=0
"$CARGO_TRUST" decompile "$INPUT_BIN" --to trust_ir --entry "$X86_64_ENTRY" --allow-unsupported --json \
    >"$TRUST_IR_JSON" 2>"$TRUST_IR_STDERR" || trust_ir_status=$?
if [ "$trust_ir_status" -ne 0 ]; then
    echo "--- decompile trust_ir stderr" >&2
    cat "$TRUST_IR_STDERR" >&2
    fail_test "targo trust decompile --to trust_ir --json exited $trust_ir_status"
fi

echo "--- targo trust convert --to trust-cg --json"
trust_cg_status=0
"$CARGO_TRUST" convert "$INPUT_BIN" --to trust-cg --entry "$X86_64_ENTRY" --allow-unsupported --json \
    >"$trust_cg_JSON" 2>"$trust_cg_STDERR" || trust_cg_status=$?
if [ "$trust_cg_status" -eq 0 ]; then
    fail_test "targo trust convert --to trust-cg --json unexpectedly accepted a non-proof-grade conversion"
elif [ "$trust_cg_status" -gt 1 ]; then
    echo "--- convert trust-cg stderr" >&2
    cat "$trust_cg_STDERR" >&2
    fail_test "targo trust convert --to trust-cg --json exited setup/internal status $trust_cg_status"
fi

echo "--- targo trust convert --to wasm --json"
wasm_status=0
"$CARGO_TRUST" convert "$INPUT_BIN" --to wasm --entry "$X86_64_ENTRY" --allow-unsupported --json \
    >"$WASM_JSON" 2>"$WASM_STDERR" || wasm_status=$?
if [ "$wasm_status" -eq 0 ]; then
    fail_test "targo trust convert --to wasm --json unexpectedly accepted a non-proof-grade conversion"
elif [ "$wasm_status" -gt 1 ]; then
    echo "--- convert wasm stderr" >&2
    cat "$WASM_STDERR" >&2
    fail_test "targo trust convert --to wasm --json exited setup/internal status $wasm_status"
fi

echo "--- targo trust verify-binary exposes proof evidence JSON"
verify_binary_json_status=0
"$CARGO_TRUST" verify-binary "$INPUT_BIN" --entry "$X86_64_ENTRY" --allow-unsupported --json \
    >"$VERIFY_BINARY_JSON" 2>"$VERIFY_BINARY_STDERR" || verify_binary_json_status=$?
if [ "$verify_binary_json_status" -gt 1 ]; then
    echo "--- verify-binary json stderr" >&2
    cat "$VERIFY_BINARY_STDERR" >&2
    fail_test "targo trust verify-binary --json exited setup/internal status $verify_binary_json_status"
fi

echo "--- targo trust verify-binary exposes proof evidence terminal summary"
verify_binary_terminal_status=0
"$CARGO_TRUST" verify-binary "$INPUT_BIN" --entry "$X86_64_ENTRY" --allow-unsupported \
    >"$VERIFY_BINARY_TERMINAL" 2>"$VERIFY_BINARY_TERMINAL_STDERR" || verify_binary_terminal_status=$?
if [ "$verify_binary_terminal_status" -gt 1 ]; then
    echo "--- verify-binary terminal stderr" >&2
    cat "$VERIFY_BINARY_TERMINAL_STDERR" >&2
    fail_test "targo trust verify-binary terminal exited setup/internal status $verify_binary_terminal_status"
fi

if grep -R "SKIP:" \
    "$RUST_JSON" "$RUST_STDERR" \
    "$TRUST_IR_JSON" "$TRUST_IR_STDERR" \
    "$trust_cg_JSON" "$trust_cg_STDERR" \
    "$WASM_JSON" "$WASM_STDERR" \
    "$VERIFY_BINARY_JSON" "$VERIFY_BINARY_STDERR" \
    "$VERIFY_BINARY_TERMINAL" "$VERIFY_BINARY_TERMINAL_STDERR" \
    >/dev/null 2>&1; then
    skip_gate "targo-trust binary CLI smoke emitted a SKIP line"
fi

printf 'not an object file' > "$BAD_FORMAT_BIN"

python3 - "$BAD_TARGET_BIN" <<'PY'
import struct
import sys

path = sys.argv[1]
elf = bytearray(64)
elf[0:4] = b"\x7fELF"
elf[4] = 2  # ELFCLASS64
elf[5] = 1  # ELFDATA2LSB
elf[6] = 1  # EV_CURRENT
struct.pack_into(
    "<HHIQQQIHHHHHH",
    elf,
    16,
    1,    # ET_REL
    243,  # EM_RISCV, intentionally unsupported by the current binary lifter
    1,    # EV_CURRENT
    0,
    0,
    0,
    0,
    64,
    0,
    0,
    0,
    0,
    0,
)
with open(path, "wb") as fh:
    fh.write(elf)
PY

python3 - "$PE_BIN" "$I386_ELF_BIN" <<'PY'
import struct
import sys

pe_path, i386_path = sys.argv[1:3]

with open(pe_path, "wb") as fh:
    fh.write(b"MZ\x00\x00")

elf = bytearray(52)
elf[0:4] = b"\x7fELF"
elf[4] = 1  # ELFCLASS32
elf[5] = 1  # ELFDATA2LSB
elf[6] = 1  # EV_CURRENT
struct.pack_into(
    "<HHIIIIIHHHHHH",
    elf,
    16,
    1,  # ET_REL
    3,  # EM_386
    1,  # EV_CURRENT
    0,
    0,
    0,
    0,
    52,
    0,
    0,
    0,
    0,
    0,
)
with open(i386_path, "wb") as fh:
    fh.write(elf)
PY

echo "--- targo trust decompile rejects unsupported format"
bad_format_status=0
"$CARGO_TRUST" decompile "$BAD_FORMAT_BIN" --to trust_ir --strict --json \
    >"$BAD_FORMAT_JSON" 2>"$BAD_FORMAT_STDERR" || bad_format_status=$?
if [ "$bad_format_status" -eq 0 ]; then
    fail_test "targo trust decompile accepted unsupported non-object input"
fi

echo "--- targo trust decompile rejects unsupported target"
bad_target_status=0
"$CARGO_TRUST" decompile "$BAD_TARGET_BIN" --to trust_ir --strict --json \
    >"$BAD_TARGET_JSON" 2>"$BAD_TARGET_STDERR" || bad_target_status=$?
if [ "$bad_target_status" -eq 0 ]; then
    fail_test "targo trust decompile accepted unsupported ELF target"
fi

echo "--- targo trust decompile rejects PE/COFF fail-closed"
pe_status=0
"$CARGO_TRUST" decompile "$PE_BIN" --to trust_ir --strict --json \
    >"$PE_JSON" 2>"$PE_STDERR" || pe_status=$?
if [ "$pe_status" -eq 0 ]; then
    fail_test "targo trust decompile accepted unsupported PE/COFF input"
fi

echo "--- targo trust decompile rejects ELF i386 fail-closed"
i386_status=0
"$CARGO_TRUST" decompile "$I386_ELF_BIN" --to trust_ir --strict --json \
    >"$I386_ELF_JSON" 2>"$I386_ELF_STDERR" || i386_status=$?
if [ "$i386_status" -eq 0 ]; then
    fail_test "targo trust decompile accepted unsupported ELF i386 input"
fi

echo "--- materialize checked-in AArch64 ELF fixture"
materialize_hex_fixture "$AARCH64_FIXTURE_HEX" "$AARCH64_BIN" "$AARCH64_FIXTURE_SHA256"
if [ ! -s "$AARCH64_BIN" ]; then
    fail_setup "checked-in AArch64 fixture did not materialize to a non-empty ELF binary"
fi

echo "--- targo trust decompile reports checked-in AArch64 ELF fixture"
aarch64_status=0
"$CARGO_TRUST" decompile "$AARCH64_BIN" --to trust_ir --entry 0x400000 --allow-unsupported --json \
    >"$AARCH64_JSON" 2>"$AARCH64_STDERR" || aarch64_status=$?
if [ "$aarch64_status" -ne 0 ]; then
    echo "--- decompile AArch64 stderr" >&2
    cat "$AARCH64_STDERR" >&2
    fail_test "targo trust decompile --to trust_ir checked-in AArch64 fixture --json exited $aarch64_status"
fi

echo "--- materialize checked-in AArch64 unsupported-ledger fixture"
materialize_hex_fixture \
    "$AARCH64_UNSUPPORTED_FIXTURE_HEX" \
    "$AARCH64_UNSUPPORTED_BIN" \
    "$AARCH64_UNSUPPORTED_FIXTURE_SHA256"
if [ ! -s "$AARCH64_UNSUPPORTED_BIN" ]; then
    fail_setup "checked-in AArch64 unsupported-ledger fixture did not materialize to a non-empty ELF binary"
fi

echo "--- targo trust decompile preserves checked-in AArch64 unsupported ledger"
aarch64_unsupported_status=0
"$CARGO_TRUST" decompile "$AARCH64_UNSUPPORTED_BIN" --to trust_ir --all --allow-unsupported --json \
    >"$AARCH64_UNSUPPORTED_JSON" 2>"$AARCH64_UNSUPPORTED_STDERR" || aarch64_unsupported_status=$?
if [ "$aarch64_unsupported_status" -ne 0 ]; then
    echo "--- decompile AArch64 unsupported-ledger stderr" >&2
    cat "$AARCH64_UNSUPPORTED_STDERR" >&2
    fail_test "targo trust decompile --to trust_ir checked-in AArch64 unsupported-ledger fixture --json exited $aarch64_unsupported_status"
fi

python3 - "$RUST_JSON" "$TRUST_IR_JSON" "$trust_cg_JSON" "$WASM_JSON" "$VERIFY_BINARY_JSON" "$VERIFY_BINARY_TERMINAL" "$STRICT_JSON" "$BAD_FORMAT_JSON" "$BAD_TARGET_JSON" "$PE_JSON" "$I386_ELF_JSON" "$INPUT_BIN" "$X86_64_ENTRY" "$AARCH64_JSON" "$AARCH64_BIN" "$AARCH64_UNSUPPORTED_JSON" "$AARCH64_UNSUPPORTED_BIN" <<'PY'
import json
import os
import sys

(
    rust_json,
    trust_ir_json,
    trust_cg_json,
    wasm_json,
    verify_binary_json,
    verify_binary_terminal,
    strict_json,
    bad_format_json,
    bad_target_json,
    pe_json,
    i386_elf_json,
    expected_binary,
    expected_x86_64_entry,
    aarch64_json,
    expected_aarch64_binary,
    aarch64_unsupported_json,
    expected_aarch64_unsupported_binary,
) = sys.argv[1:18]

def load_report(path):
    with open(path, "r", encoding="utf-8") as fh:
        return json.load(fh)

def assert_common(report, target):
    if os.path.realpath(report.get("binary", "")) != os.path.realpath(expected_binary):
        raise AssertionError(f"{target}: binary path mismatch")
    if report.get("target") != target:
        raise AssertionError(f"{target}: target mismatch: {report.get('target')!r}")
    if report.get("status") not in {"ok", "incomplete"}:
        raise AssertionError(f"{target}: expected status ok/incomplete, got {report.get('status')!r}")
    if report.get("selection") != "address":
        raise AssertionError(f"{target}: expected address selection")
    if report.get("entry") != expected_x86_64_entry:
        raise AssertionError(f"{target}: expected selected entry {expected_x86_64_entry}")
    if report.get("strict") is not False:
        raise AssertionError(f"{target}: allow-unsupported should set strict false")
    if report.get("functions_decompiled", 0) < 1:
        raise AssertionError(f"{target}: expected at least one decompiled function")
    if report.get("blocks", 0) < 1:
        raise AssertionError(f"{target}: expected lifted blocks")
    if report.get("statements", 0) < 1:
        raise AssertionError(f"{target}: expected lifted statements")
    if report.get("failures") != 0:
        raise AssertionError(f"{target}: unexpected failures: {report.get('failure_items')!r}")
    if not isinstance(report.get("functions"), list) or not report["functions"]:
        raise AssertionError(f"{target}: missing function summaries")
    if report.get("format") != "ELF":
        raise AssertionError(f"{target}: expected ELF format")
    if report.get("architecture") != "x86-64":
        raise AssertionError(f"{target}: expected x86-64 architecture")
    if not isinstance(report.get("unsupported_items"), list):
        raise AssertionError(f"{target}: unsupported_items should be stable list")

rust_report = load_report(rust_json)
trust_ir_report = load_report(trust_ir_json)
trust_cg_report = load_report(trust_cg_json)
wasm_report = load_report(wasm_json)
verify_binary_report = load_report(verify_binary_json)
strict_report = load_report(strict_json)
bad_format_report = load_report(bad_format_json)
bad_target_report = load_report(bad_target_json)
pe_report = load_report(pe_json)
i386_elf_report = load_report(i386_elf_json)

assert_common(rust_report, "rust")
assert_common(trust_ir_report, "trust_ir")
assert_common(trust_cg_report, "trust-cg")
assert_common(wasm_report, "wasm")

if os.path.realpath(verify_binary_report.get("binary", "")) != os.path.realpath(expected_binary):
    raise AssertionError("verify-binary: binary path mismatch")
if verify_binary_report.get("format") != "ELF":
    raise AssertionError("verify-binary: expected ELF format")
if verify_binary_report.get("architecture") != "x86-64":
    raise AssertionError("verify-binary: expected x86-64 architecture")
if verify_binary_report.get("entry") != expected_x86_64_entry:
    raise AssertionError(f"verify-binary: expected selected entry {expected_x86_64_entry}")
if verify_binary_report.get("strict") is not False:
    raise AssertionError("verify-binary: allow-unsupported should set strict false")
if verify_binary_report.get("functions_analyzed", 0) < 1:
    raise AssertionError("verify-binary: expected at least one analyzed function")
if verify_binary_report.get("vcs", 0) < 1:
    raise AssertionError("verify-binary: expected generated binary VCs for proof-evidence coverage")
if verify_binary_report.get("trust_level") == "proof_grade":
    raise AssertionError("verify-binary: proof evidence must not upgrade this fixture to proof-grade")

proof_evidence = verify_binary_report.get("proof_evidence")
if not isinstance(proof_evidence, dict):
    raise AssertionError("verify-binary: missing proof_evidence JSON object")
proof_gate = verify_binary_report.get("proof_grade_gate")
if not isinstance(proof_gate, dict):
    raise AssertionError("verify-binary: missing top-level proof_grade_gate JSON object")
if proof_gate.get("accepted") is not False or proof_gate.get("status") != "rejected":
    raise AssertionError("verify-binary: top-level proof_grade_gate must reject this fixture")
if proof_gate.get("raw_solver_proof_bytes_sufficient") is not False:
    raise AssertionError("verify-binary: raw solver proof bytes must not be sufficient")
if not proof_gate.get("rejections"):
    raise AssertionError("verify-binary: rejected proof-grade gate should explain blockers")

shared_gate = proof_evidence.get("proof_grade_gate")
if not isinstance(shared_gate, dict):
    raise AssertionError("verify-binary: proof_evidence should include shared proof_grade_gate")
if shared_gate.get("accepted") is not False:
    raise AssertionError("verify-binary: shared proof evidence gate must reject this fixture")
if proof_evidence.get("total_vcs") != verify_binary_report.get("vcs"):
    raise AssertionError("verify-binary: proof_evidence total_vcs should match generated VCs")
if proof_evidence.get("total_vcs") != proof_gate.get("required_vcs"):
    raise AssertionError("verify-binary: proof gate required_vcs should match proof evidence")
if proof_evidence.get("solver_dispatches") != proof_gate.get("solver_dispatches"):
    raise AssertionError("verify-binary: solver dispatch accounting mismatch")
solver_counts = proof_evidence.get("solver_dispatch_status_counts")
if not isinstance(solver_counts, dict) or sum(solver_counts.values()) != proof_evidence.get("solver_dispatches"):
    raise AssertionError("verify-binary: solver dispatch counts should cover every dispatch")
replay_counts = proof_evidence.get("replay_status_counts")
if not isinstance(replay_counts, dict) or sum(replay_counts.values()) != proof_evidence.get("solver_dispatches"):
    raise AssertionError("verify-binary: replay counts should cover every dispatch")
coverage = proof_evidence.get("checked_certificate_coverage")
if not isinstance(coverage, dict):
    raise AssertionError("verify-binary: missing checked_certificate_coverage")
if coverage.get("required_vcs") != proof_evidence.get("total_vcs"):
    raise AssertionError("verify-binary: certificate coverage required_vcs mismatch")
if coverage.get("raw_solver_proof_bytes_satisfy_coverage") is not False:
    raise AssertionError("verify-binary: raw solver proof bytes must not satisfy certificate coverage")

with open(verify_binary_terminal, "r", encoding="utf-8") as fh:
    verify_binary_terminal_text = fh.read()
for expected in [
    "targo trust verify-binary report",
    "proof-grade gate: rejected",
    "proof evidence: total_vcs=",
    "proof evidence solver dispatch counts:",
    "proof evidence replay counts:",
    "proof evidence certificate coverage:",
    "shared_proof_grade_gate=rejected",
]:
    if expected not in verify_binary_terminal_text:
        raise AssertionError(f"verify-binary terminal: missing {expected!r}")
if "proof-grade gate: accepted" in verify_binary_terminal_text:
    raise AssertionError("verify-binary terminal: proof-grade gate must not be accepted")

if strict_report.get("format") != "ELF":
    raise AssertionError("strict: expected accepted x86-64 input format ELF")
if strict_report.get("architecture") != "x86-64":
    raise AssertionError("strict: expected accepted x86-64 architecture report")
if strict_report.get("strict") is not True:
    raise AssertionError("strict: expected strict true")
if strict_report.get("target") != "trust_ir":
    raise AssertionError("strict: expected trust_ir target")
if strict_report.get("functions_decompiled", 0) < 1:
    raise AssertionError("strict: expected x86-64 ELF to lift at least one function before fail-closed coverage checks")
if strict_report.get("unsupported", 0) < 1:
    raise AssertionError("strict: expected unsupported coverage to be recorded")
if not isinstance(strict_report.get("unsupported_items"), list) or not strict_report["unsupported_items"]:
    raise AssertionError("strict: expected unsupported_items to explain fail-closed strict rejection")

if bad_format_report.get("status") != "failed":
    raise AssertionError(f"bad format: expected failed, got {bad_format_report.get('status')!r}")
if bad_format_report.get("output_trust_level") != "rejected":
    raise AssertionError("bad format: expected rejected output trust")
if bad_format_report.get("failures", 0) < 1:
    raise AssertionError("bad format: expected failure item")
if bad_format_report.get("functions_decompiled") != 0:
    raise AssertionError("bad format: unsupported input should decompile zero functions")

if bad_target_report.get("status") != "incomplete":
    raise AssertionError(f"bad target: expected incomplete unsupported report, got {bad_target_report.get('status')!r}")
if bad_target_report.get("output_trust_level") != "rejected":
    raise AssertionError("bad target: expected rejected output trust")
if bad_target_report.get("unsupported", 0) < 1:
    raise AssertionError("bad target: expected unsupported target item")
if not any("unsupported ELF machine type" in item for item in bad_target_report.get("unsupported_items", [])):
    raise AssertionError(f"bad target: expected unsupported machine diagnostic, got {bad_target_report.get('unsupported_items')!r}")
if bad_target_report.get("functions_decompiled") != 0:
    raise AssertionError("bad target: unsupported target should decompile zero functions")

if pe_report.get("status") != "incomplete":
    raise AssertionError(f"PE: expected incomplete unsupported report, got {pe_report.get('status')!r}")
if pe_report.get("output_trust_level") != "rejected":
    raise AssertionError("PE: expected rejected output trust")
if pe_report.get("functions_decompiled") != 0:
    raise AssertionError("PE: unsupported target should decompile zero functions")
if not any("PE/COFF" in item and "not implemented" in item for item in pe_report.get("unsupported_items", [])):
    raise AssertionError(f"PE: expected fail-closed PE diagnostic, got {pe_report.get('unsupported_items')!r}")

if i386_elf_report.get("status") != "incomplete":
    raise AssertionError(f"i386: expected incomplete unsupported report, got {i386_elf_report.get('status')!r}")
if i386_elf_report.get("output_trust_level") != "rejected":
    raise AssertionError("i386: expected rejected output trust")
if i386_elf_report.get("functions_decompiled") != 0:
    raise AssertionError("i386: unsupported target should decompile zero functions")
if not any("32-bit x86/i386 lifting is not implemented yet" in item for item in i386_elf_report.get("unsupported_items", [])):
    raise AssertionError(f"i386: expected fail-closed i386 diagnostic, got {i386_elf_report.get('unsupported_items')!r}")

if rust_report.get("output_kind") != "rust_skeleton":
    raise AssertionError("rust: output_kind should be rust_skeleton")
if rust_report.get("output_trust_level") != "exploratory":
    raise AssertionError("rust: output should be marked exploratory")
if rust_report.get("output_validation") != "exploratory_not_validated":
    raise AssertionError("rust: output should be marked exploratory_not_validated")
if "exploratory" not in rust_report.get("validation_note", ""):
    raise AssertionError("rust: validation note should label exploratory output")
if "fn " not in (rust_report.get("output_content") or ""):
    raise AssertionError("rust: expected Rust skeleton output")

if trust_ir_report.get("output_kind") != "trust_ir_json":
    raise AssertionError("trust_ir: output_kind should be trust_ir_json")
if trust_ir_report.get("output_trust_level") != "partial":
    raise AssertionError("trust_ir: output should be marked partial")
if trust_ir_report.get("output_validation") != "lifted_trust_ir_partial":
    raise AssertionError("trust_ir: output should be marked lifted_trust_ir_partial")
if "partial" not in trust_ir_report.get("validation_note", ""):
    raise AssertionError("trust_ir: validation note should label partial output")
try:
    trust_ir_artifact = json.loads(trust_ir_report.get("output_content") or "")
except json.JSONDecodeError as exc:
    raise AssertionError(f"trust_ir: output_content should be JSON artifact: {exc}") from exc
if trust_ir_artifact.get("trust_level") != "Partial":
    raise AssertionError("trust_ir: artifact trust level should remain Partial")
if not trust_ir_artifact.get("functions"):
    raise AssertionError("trust_ir: artifact should include lifted function records")

trust_ir_symbolic_formulas = trust_ir_report.get("preserved_symbolic_formulas")
if not isinstance(trust_ir_symbolic_formulas, list) or not trust_ir_symbolic_formulas:
    raise AssertionError(
        "trust_ir: binary decompile output should expose preserved symbolic machine formulas"
    )
trust_ir_symbolic_keys = {
    (
        formula.get("function"),
        formula.get("block"),
        formula.get("statement_index"),
    )
    for formula in trust_ir_symbolic_formulas
}
for formula in trust_ir_symbolic_formulas:
    if formula.get("target") != "TrustIr":
        raise AssertionError(f"trust_ir: symbolic formula target mismatch: {formula!r}")
    if formula.get("formula") in (None, "Undef"):
        raise AssertionError(f"trust_ir: symbolic formula must be inspectable, got {formula!r}")
    if "Undef" in json.dumps(formula.get("formula"), sort_keys=True):
        raise AssertionError(f"trust_ir: symbolic formula must not be lowered to Undef: {formula!r}")

for report, target, output_kind in [
    (trust_cg_report, "trust-cg", "trust_cg_text"),
    (wasm_report, "wasm", "wasm_text"),
]:
    if report.get("output_kind") != output_kind:
        raise AssertionError(f"{target}: expected output_kind {output_kind}")
    if report.get("output_trust_level") not in {"partial", "rejected"}:
        raise AssertionError(
            f"{target}: derived output should be partial or fail-closed rejected"
        )
    if report.get("output_validation") not in {"validated_partial", "translation_rejected", "inspectable_rejected"}:
        raise AssertionError(
            f"{target}: expected validated_partial, translation_rejected, or inspectable_rejected, "
            f"got {report.get('output_validation')!r}"
        )
    if "proof-grade" not in report.get("validation_note", ""):
        raise AssertionError(f"{target}: validation note should preserve non-proof-grade claim")
    gate = report.get("conversion_gate")
    if not isinstance(gate, dict):
        raise AssertionError(f"{target}: missing conversion_gate")
    if gate.get("accepted") is not False or gate.get("status") != "rejected":
        raise AssertionError(f"{target}: conversion gate should reject non-proof-grade output")
    if gate.get("target") != target:
        raise AssertionError(f"{target}: conversion gate target mismatch")
    if gate.get("proof_grade_artifact") is not False:
        raise AssertionError(
            f"{target}: conversion gate must not mark non-proof-grade output proof-grade"
        )
    if not gate.get("blockers"):
        raise AssertionError(f"{target}: rejected conversion gate should explain blockers")
    target_blockers = report.get("target_validation_blockers")
    if not isinstance(target_blockers, list):
        raise AssertionError(f"{target}: target_validation_blockers should be a stable JSON list")
    if not any(
        blocker.get("feature") == "missing-target-semantic-validation"
        for blocker in target_blockers
    ):
        raise AssertionError(
            f"{target}: release gate must exercise missing-target-semantic-validation blocker"
        )
    validation_blockers = gate.get("validation_blockers")
    if not isinstance(validation_blockers, list):
        raise AssertionError(f"{target}: conversion gate should expose validation_blockers")
    if not any("missing-target-semantic-validation" in blocker for blocker in validation_blockers):
        raise AssertionError(
            f"{target}: conversion gate should surface missing-target-semantic-validation"
        )

def assert_convert_symbolic_formula_json_contract(report, target, symbolic_target):
    formulas = report.get("preserved_symbolic_formulas")
    if not isinstance(formulas, list) or not formulas:
        raise AssertionError(
            f"{target}: convert --to {target} --json after binary decompile should expose preserved symbolic formulas"
        )
    if report.get("output_trust_level") != "rejected":
        raise AssertionError(f"{target}: symbolic binary conversion must remain fail-closed rejected")
    if report.get("output_validation") not in {"inspectable_rejected", "translation_rejected"}:
        raise AssertionError(
            f"{target}: symbolic binary conversion should be inspectable or translation rejected, "
            f"got {report.get('output_validation')!r}"
        )
    symbolic_keys = {
        (
            formula.get("function"),
            formula.get("block"),
            formula.get("statement_index"),
        )
        for formula in formulas
    }
    if not trust_ir_symbolic_keys.intersection(symbolic_keys):
        raise AssertionError(
            f"{target}: preserved symbolic formulas should correspond to the preceding TrustIr decompile output"
        )
    blockers = report.get("target_validation_blockers")
    if not isinstance(blockers, list):
        raise AssertionError(f"{target}: target_validation_blockers should be a stable JSON list")
    gate = report.get("conversion_gate")
    validation_blockers = gate.get("validation_blockers") if isinstance(gate, dict) else None
    if not isinstance(validation_blockers, list):
        raise AssertionError(f"{target}: conversion gate should expose validation_blockers")
    for formula in formulas:
        if formula.get("target") != symbolic_target:
            raise AssertionError(f"{target}: symbolic formula target mismatch: {formula!r}")
        if formula.get("formula") in (None, "Undef"):
            raise AssertionError(f"{target}: symbolic formula must be inspectable, got {formula!r}")
        formula_json = json.dumps(formula.get("formula"), sort_keys=True)
        if "Undef" in formula_json:
            raise AssertionError(f"{target}: symbolic formula must not be lowered to Undef: {formula!r}")
        if not any(op in formula_json for op in ("Var", "Select", "BvAdd", "BvOr")):
            raise AssertionError(f"{target}: expected structured symbolic formula JSON, got {formula!r}")
    if not any(
        blocker.get("feature") == "symbolic-formula-proof-semantics"
        and blocker.get("target") == symbolic_target
        for blocker in blockers
    ):
        raise AssertionError(
            f"{target}: symbolic formulas must have an inspectable proof-semantics blocker"
        )
    if gate.get("accepted") is not False or gate.get("status") != "rejected":
        raise AssertionError(f"{target}: conversion gate must remain rejected for symbolic formulas")
    if not any(
        "symbolic-formula-proof-semantics" in blocker
        for blocker in validation_blockers
    ):
        raise AssertionError(
            f"{target}: conversion gate should surface symbolic-formula proof-semantics blockers"
        )

assert_convert_symbolic_formula_json_contract(trust_cg_report, "trust-cg", "TrustCg")
assert_convert_symbolic_formula_json_contract(wasm_report, "wasm", "Wasm")

aarch64_report = load_report(aarch64_json)
if os.path.realpath(aarch64_report.get("binary", "")) != os.path.realpath(expected_aarch64_binary):
    raise AssertionError("aarch64: binary path mismatch")
if aarch64_report.get("target") != "trust_ir":
    raise AssertionError(f"aarch64: expected trust_ir target, got {aarch64_report.get('target')!r}")
if aarch64_report.get("entry") != "0x400000":
    raise AssertionError(f"aarch64: expected selected entry 0x400000, got {aarch64_report.get('entry')!r}")
if aarch64_report.get("format") != "ELF":
    raise AssertionError("aarch64: expected ELF format")
if aarch64_report.get("architecture") != "AArch64":
    raise AssertionError(f"aarch64: expected AArch64 architecture, got {aarch64_report.get('architecture')!r}")
if aarch64_report.get("strict") is not False:
    raise AssertionError("aarch64: allow-unsupported should set strict false")
if aarch64_report.get("status") not in {"ok", "incomplete"}:
    raise AssertionError(f"aarch64: expected status ok/incomplete, got {aarch64_report.get('status')!r}")
if aarch64_report.get("functions_decompiled", 0) < 1:
    raise AssertionError("aarch64: expected at least one decompiled function")
if aarch64_report.get("blocks", 0) < 1:
    raise AssertionError("aarch64: expected lifted blocks")
if aarch64_report.get("statements", 0) < 1:
    raise AssertionError("aarch64: expected lifted statements")
if aarch64_report.get("output_kind") != "trust_ir_json":
    raise AssertionError("aarch64: output_kind should be trust_ir_json")
if aarch64_report.get("output_trust_level") != "partial":
    raise AssertionError("aarch64: output should be marked partial until proof-grade evidence exists")
if not isinstance(aarch64_report.get("unsupported_items"), list):
    raise AssertionError("aarch64: unsupported_items should be a stable list")

aarch64_unsupported_report = load_report(aarch64_unsupported_json)
if os.path.realpath(aarch64_unsupported_report.get("binary", "")) != os.path.realpath(expected_aarch64_unsupported_binary):
    raise AssertionError("aarch64 unsupported-ledger: binary path mismatch")
if aarch64_unsupported_report.get("target") != "trust_ir":
    raise AssertionError(
        f"aarch64 unsupported-ledger: expected trust_ir target, got {aarch64_unsupported_report.get('target')!r}"
    )
if aarch64_unsupported_report.get("selection") != "all":
    raise AssertionError("aarch64 unsupported-ledger: expected all-functions selection")
if aarch64_unsupported_report.get("format") != "ELF":
    raise AssertionError("aarch64 unsupported-ledger: expected ELF format")
if aarch64_unsupported_report.get("architecture") != "AArch64":
    raise AssertionError(
        "aarch64 unsupported-ledger: expected AArch64 architecture, "
        f"got {aarch64_unsupported_report.get('architecture')!r}"
    )
if aarch64_unsupported_report.get("strict") is not False:
    raise AssertionError("aarch64 unsupported-ledger: allow-unsupported should set strict false")
if aarch64_unsupported_report.get("status") != "incomplete":
    raise AssertionError(
        "aarch64 unsupported-ledger: expected incomplete status with a non-empty ledger, "
        f"got {aarch64_unsupported_report.get('status')!r}"
    )
if aarch64_unsupported_report.get("functions_decompiled") != 2:
    raise AssertionError(
        "aarch64 unsupported-ledger: expected exactly two successfully decompiled functions, "
        f"got {aarch64_unsupported_report.get('functions_decompiled')!r}"
    )
if aarch64_unsupported_report.get("blocks", 0) < 1:
    raise AssertionError("aarch64 unsupported-ledger: expected lifted blocks from supported function")
if aarch64_unsupported_report.get("statements", 0) < 1:
    raise AssertionError("aarch64 unsupported-ledger: expected lifted statements from supported function")
if aarch64_unsupported_report.get("unsupported", 0) < 1:
    raise AssertionError("aarch64 unsupported-ledger: expected unsupported ledger entries")
unsupported_items = aarch64_unsupported_report.get("unsupported_items", [])
if not isinstance(unsupported_items, list) or not unsupported_items:
    raise AssertionError("aarch64 unsupported-ledger: unsupported_items should be a non-empty stable list")
if not any("trust_fixture_unsupported_mrs" in item for item in unsupported_items):
    raise AssertionError(
        "aarch64 unsupported-ledger: expected unsupported symbol name in ledger, "
        f"got {unsupported_items!r}"
    )
if any("trust_fixture_supported_prfm" in item for item in unsupported_items):
    raise AssertionError(
        "aarch64 unsupported-ledger: supported PRFM fixture function should not be a ledger item, "
        f"got {unsupported_items!r}"
    )
if any("PRFM" in item.upper() or "opcode Prfm" in item for item in unsupported_items):
    raise AssertionError(
        "aarch64 unsupported-ledger: supported PRFM instruction should stay out of unsupported_items, "
        f"got {unsupported_items!r}"
    )
if not any("unsupported instruction semantics" in item for item in unsupported_items):
    raise AssertionError(
        "aarch64 unsupported-ledger: expected semantic-lift unsupported diagnostic, "
        f"got {unsupported_items!r}"
    )
if aarch64_unsupported_report.get("output_kind") != "trust_ir_json":
    raise AssertionError("aarch64 unsupported-ledger: output_kind should be trust_ir_json")
if aarch64_unsupported_report.get("output_trust_level") != "partial":
    raise AssertionError("aarch64 unsupported-ledger: output should remain partial, not proof-grade")
try:
    aarch64_unsupported_artifact = json.loads(
        aarch64_unsupported_report.get("output_content") or ""
    )
except json.JSONDecodeError as exc:
    raise AssertionError(
        f"aarch64 unsupported-ledger: output_content should be JSON artifact: {exc}"
    ) from exc
artifact_records = aarch64_unsupported_artifact.get("unsupported", {}).get("records", [])
if len(artifact_records) != aarch64_unsupported_report.get("unsupported"):
    raise AssertionError("aarch64 unsupported-ledger: report count should match artifact ledger")
if not any(record.get("stage") == "trust-lift" for record in artifact_records):
    raise AssertionError(
        "aarch64 unsupported-ledger: expected trust-lift stage in artifact unsupported ledger"
    )
if any("PRFM" in json.dumps(record).upper() for record in artifact_records):
    raise AssertionError(
        "aarch64 unsupported-ledger: artifact unsupported ledger should not mention supported PRFM"
    )
PY

echo
echo "=== tRust E2E Test: binary decompilation golden JSON: PASS ==="
