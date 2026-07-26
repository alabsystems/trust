#!/bin/bash
# Focused x86_64 provenance parity regression for a variable-length instruction.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
FIXTURE_HEX="$SCRIPT_DIR/x86_64-movabs-ret-elf.hex"
FIXTURE_SHA256="f2c555744bcf54e979c37afa8ea3444b07654b07282dfca69057b7a8fb74441c"
EXPECTED_BYTES_JSON='[72,184,120,86,52,18,0,0,0,0]'
EXPECTED_SIZE=10

require_command() {
    if ! command -v "$1" >/dev/null 2>&1; then
        echo "ERROR: missing required command: $1" >&2
        exit 2
    fi
}

require_command python3

TRUST_TARGO_CMD=()

resolve_trust_cargo() {
    if [ -n "${TRUST_TARGO_BIN:-}" ]; then
        if [ ! -x "$TRUST_TARGO_BIN" ]; then
            echo "ERROR: TRUST_TARGO_BIN is not executable: $TRUST_TARGO_BIN" >&2
            exit 2
        fi
        if [ "$(basename "$TRUST_TARGO_BIN")" != "targo" ]; then
            echo "ERROR: TRUST_TARGO_BIN must point at canonical targo, got: $TRUST_TARGO_BIN" >&2
            exit 2
        fi
        TRUST_TARGO_CMD=("$TRUST_TARGO_BIN" --unverified)
    elif command -v targo >/dev/null 2>&1; then
        TRUST_TARGO_CMD=(targo --unverified)
    elif command -v rustup >/dev/null 2>&1 && rustup run trust targo --version >/dev/null 2>&1; then
        TRUST_TARGO_CMD=(rustup run trust targo --unverified)
    else
        echo "ERROR: Trust targo not found. Build/link the trust toolchain or set TRUST_TARGO_BIN to the Trust-owned targo binary." >&2
        exit 2
    fi
}

trust_cargo() {
    if [ "${#TRUST_TARGO_CMD[@]}" -eq 0 ]; then
        resolve_trust_cargo
    fi
    "${TRUST_TARGO_CMD[@]}" "$@"
}

TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/trust-x86-prov.XXXXXX")"
trap 'rm -rf "$TMP_DIR"' EXIT

BIN="$TMP_DIR/x86_64-movabs-ret.o"
DISASM_JSON="$TMP_DIR/disasm.json"
LIFT_JSON="$TMP_DIR/lift.json"
DECOMPILE_JSON="$TMP_DIR/decompile.json"

python3 - "$FIXTURE_HEX" "$BIN" "$FIXTURE_SHA256" <<'PY'
import binascii
import hashlib
import pathlib
import re
import sys

hex_path = pathlib.Path(sys.argv[1])
out_path = pathlib.Path(sys.argv[2])
expected_sha256 = sys.argv[3]

compact = re.sub(r"\s+", "", hex_path.read_text(encoding="ascii"))
data = binascii.unhexlify(compact)
actual_sha256 = hashlib.sha256(data).hexdigest()
if actual_sha256 != expected_sha256:
    raise SystemExit(
        f"fixture SHA-256 mismatch: expected {expected_sha256}, got {actual_sha256}"
    )
out_path.write_bytes(data)
PY

echo "--- disasm provenance: trust-disasm keeps original bytes for MOVABS"
trust_cargo test --manifest-path "$TRUST_ROOT/crates/Cargo.toml" -p trust-disasm \
    x86_64::tests::test_original_bytes_preserved_for_10_byte_instruction

mkdir -p "$TMP_DIR/disasm-json/src"
cat >"$TMP_DIR/disasm-json/Cargo.toml" <<EOF
[package]
name = "trust-disasm-json-fixture"
version = "0.0.0"
edition = "2021"

[dependencies]
serde_json = "1"
trust-disasm = { path = "$TRUST_ROOT/crates/trust-disasm" }
EOF

cat >"$TMP_DIR/disasm-json/src/main.rs" <<'RS'
fn main() {
    let bytes = [0x48, 0xB8, 0x78, 0x56, 0x34, 0x12, 0, 0, 0, 0, 0xC3];
    let instruction = trust_disasm::decode_x86_64(&bytes, 0).expect("decode MOVABS fixture");
    println!(
        "{}",
        serde_json::json!({
            "instruction_address": instruction.address,
            "instruction_size": instruction.size,
            "instruction_bytes": instruction.bytes,
            "encoding": instruction.encoding,
        })
    );
}
RS

trust_cargo run --quiet --manifest-path "$TMP_DIR/disasm-json/Cargo.toml" >"$DISASM_JSON"

echo "--- replay guard: mismatched x86_64 instruction size remains fail-closed"
trust_cargo test --manifest-path "$TRUST_ROOT/targo-trust/Cargo.toml" \
    test_failed_x86_64_replay_with_mismatched_instruction_size_fails_closed

if [ -n "${CARGO_TRUST_BIN:-}" ]; then
    CARGO_TRUST="$CARGO_TRUST_BIN"
else
    trust_cargo build --manifest-path "$TRUST_ROOT/targo-trust/Cargo.toml" --bin targo-trust
    for candidate in \
        "$TRUST_ROOT/target/debug/targo-trust" \
        "$TRUST_ROOT/target/user/debug/targo-trust"
    do
        if [ -x "$candidate" ]; then
            CARGO_TRUST="$candidate"
            break
        fi
    done
fi

if [ ! -x "${CARGO_TRUST:-}" ]; then
    echo "ERROR: targo-trust binary is missing or not executable" >&2
    exit 2
fi

echo "--- lift JSON exposes MOVABS instruction bytes and size"
"$CARGO_TRUST" lift "$BIN" --entry 0x0 --allow-unsupported --json >"$LIFT_JSON"

echo "--- decompile JSON exposes MOVABS instruction bytes and size"
"$CARGO_TRUST" decompile "$BIN" --to trust_ir --entry 0x0 --allow-unsupported --json \
    >"$DECOMPILE_JSON"

python3 - \
    "$DISASM_JSON" \
    "$LIFT_JSON" \
    "$DECOMPILE_JSON" \
    "$EXPECTED_BYTES_JSON" \
    "$EXPECTED_SIZE" <<'PY'
import json
import sys

disasm_path, lift_path, decompile_path, expected_bytes_json, expected_size = sys.argv[1:6]
expected_bytes = json.loads(expected_bytes_json)
expected_size = int(expected_size)


def find_origin(origins):
    for origin in origins:
        if (
            origin.get("instruction_address") == 0
            and origin.get("instruction_size") == expected_size
            and origin.get("instruction_bytes") == expected_bytes
        ):
            return origin
    return None


with open(disasm_path, encoding="utf-8") as fh:
    disasm = json.load(fh)
if find_origin([disasm]) is None:
    raise AssertionError(f"disasm JSON missing MOVABS provenance: {disasm!r}")

with open(lift_path, encoding="utf-8") as fh:
    lift = json.load(fh)

lift_origins = [
    origin
    for function in lift.get("functions", [])
    for origin in function.get("instruction_provenance", [])
]
if find_origin(lift_origins) is None:
    raise AssertionError(f"lift JSON missing MOVABS provenance: {lift_origins!r}")

with open(decompile_path, encoding="utf-8") as fh:
    decompile = json.load(fh)

summary_origins = [
    origin
    for function in decompile.get("functions", [])
    for origin in function.get("instruction_provenance", [])
]
if find_origin(summary_origins) is None:
    raise AssertionError(f"decompile report missing MOVABS provenance: {summary_origins!r}")

artifact = json.loads(decompile.get("output_content") or "{}")
artifact_origins = [
    origin
    for function in artifact.get("functions", [])
    for origin in function.get("instruction_provenance", [])
]
if find_origin(artifact_origins) is None:
    raise AssertionError(f"decompile artifact missing MOVABS provenance: {artifact_origins!r}")

print("x86_64 provenance parity: PASS")
PY
