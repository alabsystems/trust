//! Producer-level contract for `targo trust prove --format=json`.
//!
//! The coverage collector consumes this exact subprocess surface. A parser-only
//! test or fake JSON emitter cannot establish that the real binary publishes a
//! complete scorecard and couples its exit status to kernel/bridge acceptance.

use std::path::{Path, PathBuf};
use std::process::Command;

#[test]
fn real_producer_emits_status_bound_json_with_exact_loop_denominator() {
    let repo = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("targo-trust is inside the repository");
    let fixture = repo.join("crates/trust-clean/fixtures/real-spec-corpus/count_to.json");
    let temporary = tempfile::tempdir().expect("create isolated dump directory");
    std::fs::copy(&fixture, temporary.path().join("count_to.json"))
        .expect("copy one real VerifiableFunction dump");

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "prove",
            "--dump-dir",
            temporary.path().to_str().expect("UTF-8 temporary path"),
            "--budget-secs=1",
            "--format=json",
        ])
        .current_dir(repo)
        .output()
        .expect("run the real targo-trust producer");

    let stdout = String::from_utf8(output.stdout).expect("prove stdout is UTF-8 JSON");
    let document: serde_json::Value = serde_json::from_str(&stdout).unwrap_or_else(|error| {
        panic!(
            "real prove producer did not emit JSON: {error}\nstdout:\n{stdout}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stderr)
        )
    });
    assert_eq!(document["schema"], "trust.prove-scorecard.v1");
    assert_eq!(document["budget_secs_per_function"], 1);
    assert_eq!(document["scorecard"]["total"], 1);
    assert_eq!(document["scorecard"]["loop_headers_detected"], 1);
    assert_eq!(document["scorecard"]["loop_headers_recognized"], 1);
    let scorecard = &document["scorecard"];
    assert_eq!(
        scorecard["fully_faithful"].as_u64(),
        Some(
            scorecard["fully_faithful_via_trustir"].as_u64().expect("via-trustir tally")
                + scorecard["fully_faithful_mirsem_fallback"]
                    .as_u64()
                    .expect("MirSem fallback tally")
        )
    );
    let safety_faithful = scorecard["safety_vc_faithful"].as_u64().expect("safety-faithful tally");
    for field in [
        "safety_vc_faithful_overflow",
        "safety_vc_faithful_usub",
        "safety_vc_faithful_signed_overflow",
        "safety_vc_faithful_bounds",
        "safety_vc_faithful_div",
        "safety_vc_faithful_rem",
        "safety_vc_faithful_negation",
        "safety_vc_faithful_shift",
    ] {
        assert!(
            scorecard[field].as_u64().expect("safety-faithful subtype tally") <= safety_faithful,
            "{field} must be bounded by safety_vc_faithful"
        );
    }
    let proven: std::collections::BTreeSet<_> = scorecard["proven"]
        .as_array()
        .expect("proven paths")
        .iter()
        .map(|path| path.as_str().expect("proven path"))
        .collect();
    let declined: std::collections::BTreeSet<_> = scorecard["declined_paths"]
        .as_array()
        .expect("declined paths")
        .iter()
        .map(|path| path.as_str().expect("declined path"))
        .collect();
    assert!(proven.is_disjoint(&declined));

    let kernel_rejected =
        document["scorecard"]["kernel_rejected"].as_u64().expect("kernel_rejected is an integer");
    let bridge_rejected = !document["bridge_gate_error"].is_null();
    match document["status"].as_str() {
        Some("measured") => {
            assert_eq!(kernel_rejected, 0);
            assert!(!bridge_rejected);
            assert!(output.status.success(), "an accepted measured scorecard must return success");
        }
        Some("rejected") => {
            assert!(kernel_rejected > 0 || bridge_rejected);
            assert!(!output.status.success(), "a rejected scorecard must return a nonzero status");
        }
        status => panic!("unexpected real producer status: {status:?}"),
    }
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
