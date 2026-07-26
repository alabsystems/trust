use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

const AARCH64_UNSUPPORTED_ELF_HEX: &str =
    include_str!("../../tests/fixtures/binary_decomp/aarch64-ret-and-unsupported-mrs-elf.hex");

#[test]
fn decompile_release_json_blocks_nonempty_unsupported_ledger() {
    let tmp_dir = temp_test_dir("targo-trust-unsupported-ledger-release-json");
    fs::create_dir_all(&tmp_dir).expect("create temp directory");
    let fixture = tmp_dir.join("aarch64-ret-and-unsupported-mrs.elf");
    fs::write(&fixture, decode_hex(AARCH64_UNSUPPORTED_ELF_HEX))
        .expect("write AArch64 unsupported-ledger fixture");

    let output = Command::new(targo_trust_binary())
        .arg("decompile")
        .arg(&fixture)
        .arg("--to")
        .arg("trust_ir")
        .arg("--all")
        .arg("--allow-unsupported")
        .arg("--json")
        .output()
        .expect("run targo trust decompile --to trust_ir --json");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "allow-unsupported should emit inspectable release JSON\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let value: serde_json::Value =
        serde_json::from_slice(&output.stdout).expect("decompile stdout should be JSON");
    assert_eq!(value["target"], "trust_ir");
    assert_eq!(value["selection"], "all");
    assert_eq!(value["status"], "incomplete");
    assert_eq!(value["output_trust_level"], "partial");
    assert_ne!(value["output_trust_level"], "proof_grade");

    let report_unsupported =
        value["unsupported"].as_u64().expect("top-level unsupported count should be numeric");
    assert!(report_unsupported > 0, "fixture should carry unsupported ledger records");

    let binary_evidence = &value["binary_evidence"];
    let unsupported_ledger = &binary_evidence["unsupported_ledger"];
    assert_eq!(unsupported_ledger["empty"], false);
    assert_eq!(
        unsupported_ledger["total_records"], report_unsupported,
        "release JSON ledger total should match top-level unsupported count"
    );

    let records = unsupported_ledger["records"]
        .as_array()
        .expect("unsupported ledger records should be an array");
    assert!(!records.is_empty(), "unsupported ledger records should be surfaced");
    assert!(
        records.iter().any(|record| record["stage"] == "trust-lift"),
        "unsupported ledger should preserve the trust-lift stage: {records:?}"
    );
    assert!(
        records.iter().any(|record| {
            serde_json::to_string(record)
                .expect("record serializes")
                .contains("trust_fixture_unsupported_mrs")
        }),
        "unsupported ledger should identify the unsupported fixture symbol: {records:?}"
    );

    let release_gate = &binary_evidence["release_gate"];
    assert_eq!(
        release_gate["accepted"], false,
        "a non-empty unsupported ledger must reject the proof-grade release gate"
    );
    assert_eq!(release_gate["status"], "rejected");
    assert!(
        release_gate["reason"]
            .as_str()
            .expect("release gate reason should be a string")
            .contains("unsupported-ledger-nonempty")
    );

    let blockers =
        release_gate["blockers"].as_array().expect("release gate blockers should be an array");
    let unsupported_blocker = blockers
        .iter()
        .find(|blocker| {
            blocker["code"] == "unsupported-ledger-nonempty"
                && blocker["feature"] == "unsupported-ledger"
        })
        .expect("release gate should expose unsupported-ledger-nonempty blocker");
    assert_eq!(unsupported_blocker["stage"], "targo-trust::decompile-binary-evidence");
    assert!(
        unsupported_blocker["detail"]
            .as_str()
            .expect("unsupported-ledger blocker detail should be a string")
            .contains("decompile unsupported ledger contains")
    );
    assert!(
        unsupported_blocker["evidence_required"]
            .as_array()
            .expect("unsupported-ledger evidence_required should be an array")
            .iter()
            .any(|required| required == "empty_unsupported_ledger"),
        "unsupported-ledger blocker should require empty_unsupported_ledger evidence"
    );

    let artifact: serde_json::Value = serde_json::from_str(
        value["output_content"].as_str().expect("output_content should contain a JSON artifact"),
    )
    .expect("output_content should parse as JSON");
    let artifact_records = artifact["unsupported"]["records"]
        .as_array()
        .expect("artifact unsupported records should be an array");
    assert_eq!(
        artifact_records.len() as u64,
        report_unsupported,
        "artifact unsupported ledger should match release JSON count"
    );

    let _ = fs::remove_dir_all(tmp_dir);
}

fn targo_trust_binary() -> PathBuf {
    if let Some(path) = option_env!("CARGO_BIN_EXE_targo-trust") {
        return PathBuf::from(path);
    }

    let mut path = std::env::current_exe().expect("current test executable path");
    path.pop();
    if path.ends_with("deps") {
        path.pop();
    }
    path.push(format!("targo-trust{}", std::env::consts::EXE_SUFFIX));
    path
}

fn temp_test_dir(prefix: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock after Unix epoch")
        .as_nanos();
    std::env::temp_dir().join(format!("{prefix}-{}-{nanos}", std::process::id()))
}

fn decode_hex(hex: &str) -> Vec<u8> {
    let compact = hex.chars().filter(|ch| !ch.is_whitespace()).collect::<String>();
    let bytes = compact.as_bytes();
    assert_eq!(bytes.len() % 2, 0, "hex fixture should have an even length");
    bytes.chunks_exact(2).map(|pair| (hex_nibble(pair[0]) << 4) | hex_nibble(pair[1])).collect()
}

fn hex_nibble(byte: u8) -> u8 {
    match byte {
        b'0'..=b'9' => byte - b'0',
        b'a'..=b'f' => byte - b'a' + 10,
        b'A'..=b'F' => byte - b'A' + 10,
        _ => panic!("invalid hex byte: {byte}"),
    }
}
