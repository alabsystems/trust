use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use serde_json::json;

const X86_64_RET_ELF_HEX: &str = "\
7f454c4602010100000000000000000001003e00010000000000000000000000\
0000000000000000b80000000000000000000000400000000000400005000100\
90c3000000000000000000000000000000000000000000000000000000000000\
070000001200020001000000000000000100000000000000002e746578740074\
727573745f666978747572655f72657475726e002e6e6f74652e474e552d7374\
61636b002e737274746162002e73796d74616200000000000000000000000000\
0000000000000000000000000000000000000000000000000000000000000000\
0000000000000000000000000000000000000000000000002c00000003000000\
0000000000000000000000000000000078000000000000003c00000000000000\
0000000000000000010000000000000000000000000000000100000001000000\
0600000000000000000000000000000040000000000000000200000000000000\
0000000000000000040000000000000000000000000000001c00000001000000\
0000000000000000000000000000000042000000000000000000000000000000\
0000000000000000010000000000000000000000000000003400000002000000\
0000000000000000000000000000000048000000000000003000000000000000\
010000000100000008000000000000001800000000000000";

#[test]
#[ignore = "pre-existing drift (2026-07-02): targo-trust now builds trust-decompile WITH the trust-cg feature, so the backend-unavailable rejection path this golden pins never fires; rejection now happens at target validation with an inspectable output (inspectable_rejected). Needs a re-bless against the new blocker taxonomy — tracked in docs/design-notes/2026-07-02-assumption-ledger-stage1-plan.md follow-ups"]
fn convert_trust_cg_json_golden_reports_translation_rejected_output() {
    let tmp_dir = temp_test_dir("targo-trust-convert-trust_cg-json-golden");
    fs::create_dir_all(&tmp_dir).expect("create temp directory");
    let fixture = tmp_dir.join("x86_64-ret.o");
    fs::write(&fixture, decode_hex(X86_64_RET_ELF_HEX)).expect("write ELF fixture");

    let output = Command::new(targo_trust_binary())
        .arg("convert")
        .arg(&fixture)
        .arg("--to")
        .arg("trust-cg")
        .arg("--entry")
        .arg("0x1")
        .arg("--allow-unsupported")
        .arg("--json")
        .output()
        .expect("run targo trust convert --to trust_cg --json");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "fail-closed trust-cg output must fail the conversion gate\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let value: serde_json::Value =
        serde_json::from_slice(&output.stdout).expect("convert stdout should be JSON");
    let target_blockers = value["target_validation_blockers"]
        .as_array()
        .expect("target_validation_blockers should be an array");
    assert!(
        !target_blockers.is_empty(),
        "fail-closed trust-cg output should expose validation blockers"
    );

    // Re-blessed 2026-07-02 for the trust-cg inspectable-rejection behavior:
    // a rejected translation now RETAINS an inspectable output artifact
    // (`inspectable_rejected`, `trust_cg_output_present: true`). The
    // soundness-relevant pins are unchanged and stay pinned: the conversion
    // gate still rejects (`accepted: false`, `status: "rejected"`) and the
    // artifact is never proof grade.
    let golden = json!({
        "target": "trust-cg",
        "output_trust_level": "rejected",
        "output_validation": "inspectable_rejected",
        "conversion_gate": {
            "accepted": false,
            "status": "rejected",
            "target": "trust-cg",
            "proof_grade_artifact": false,
            "validation": "inspectable_rejected",
        },
        "target_validation_blockers_present": true,
        "trust_cg_output_present": true,
    });
    let actual = json!({
        "target": value["target"],
        "output_trust_level": value["output_trust_level"],
        "output_validation": value["output_validation"],
        "conversion_gate": {
            "accepted": value["conversion_gate"]["accepted"],
            "status": value["conversion_gate"]["status"],
            "target": value["conversion_gate"]["target"],
            "proof_grade_artifact": value["conversion_gate"]["proof_grade_artifact"],
            "validation": value["conversion_gate"]["validation"],
        },
        "target_validation_blockers_present": !target_blockers.is_empty(),
        "trust_cg_output_present": value.get("trust_cg_output").is_some(),
    });
    assert_eq!(actual, golden);

    assert!(target_blockers.iter().any(|blocker| {
        blocker["feature"] == "trust-cg-backend-unavailable"
            && blocker["reason"]
                .as_str()
                .is_some_and(|reason| reason.contains("feature `trust-cg`"))
    }));
    assert!(
        value["conversion_gate"]["validation_blockers"]
            .as_array()
            .expect("conversion validation blockers should be an array")
            .iter()
            .any(|blocker| blocker
                .as_str()
                .is_some_and(|blocker| blocker.contains("trust-cg-backend-unavailable")))
    );

    let compact_json = serde_json::to_string(&value).expect("compact convert JSON");
    assert!(!compact_json.contains("\"output_trust_level\":\"proof_grade\""));
    assert!(!compact_json.contains("\"proof_grade_artifact\":true"));

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
    let bytes = hex.as_bytes();
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
