use run_make_support::{cmd, rfs, rustc_path, serde_json};

const POSITIVE: &[&str] = &[
    "bytes_ordered", "words_ordered", "signed_suffix", "wildcard_and_suffix",
    "bool_elements", "char_elements", "zst_rest", "local_join", "diverging_arm",
    "execute_overlap",
    "prior_fat_join_before_match", "dead_fat_join_inside_match",
    "dead_fat_local_join",
    "read_reference_join", "execute_reference_join",
    "execute_one", "execute_two", "execute_rest", "execute_empty", "execute_byte_pair", "execute_zst",
    "execute_zst_repeat", "execute_unit_array_effects", "execute_unit_array_diverge",
];
const REFUSED: &[&str] = &[
    "refuse_fat_inner_return",
    "refuse_fat_local_escape", "refuse_fat_local_read", "refuse_fat_local_nested",
    "refuse_reference_escape", "refuse_fat_result",
    "refuse_mutable", "refuse_guard", "refuse_literal", "refuse_or", "refuse_copied_binding",
    "refuse_unit_array_asm",
];
// These exact oracle bodies currently have live usize havoc. Keep the honest
// NotRun classification; the separate original-module observer must execute
// all 132 boundary controls, including every one of these functions.
const LIVE_USIZE_HAVOC: &[&str] = &[
    "execute_rest", "execute_zst", "execute_zst_repeat", "execute_unit_array_effects",
];

fn main() {
    // The ordinary compiler constructs the actual THIR and the complete
    // module. The sidecar and canonical bytes are outputs, never proof input.
    cmd(rustc_path())
        .arg("patterns.rs")
        .arg("--crate-name=ordered_slice_patterns")
        .arg("--crate-type=lib")
        .arg("--edition=2021")
        .arg("--emit=metadata")
        .arg("-Coverflow-checks=off")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-dump=ir:slice-ir")
        .arg("-o").arg("patterns.rmeta")
        .run();
    let report: serde_json::Value = serde_json::from_slice(
        &rfs::read("slice-ir/ordered_slice_patterns.coverage.json"),
    ).expect("actual complete coverage report");
    assert_eq!(report["schema"], "trust.thir-lower.crate-module.coverage.v2");
    assert_eq!(report["publication"]["commit_marker"], true);
    let bodies = report["bodies"].as_array().expect("complete body inventory");
    for name in POSITIVE.iter().chain(REFUSED) {
        let found: Vec<_> = bodies.iter().filter(|body| {
            body["def_path"].as_str().is_some_and(|path| path.rsplit("::").next() == Some(name))
        }).collect();
        assert_eq!(found.len(), 1, "missing/duplicate actual source body {name}");
        let body = found[0];
        if POSITIVE.contains(name) {
            assert_eq!(body["lowered"], true, "actual source not lowered: {body}");
            assert_eq!(body["spliced"], true, "actual body not retained: {body}");
            assert_eq!(body["unsupported"], serde_json::json!([]), "new abstraction/refusal: {body}");
            assert_eq!(body["symbolic"], false, "concrete slice became symbolic: {body}");
        } else {
            assert_eq!(body["lowered"], false, "unsupported pattern admitted: {body}");
            assert_eq!(body["spliced"], false, "unsupported body retained: {body}");
            assert!(!body["unsupported"].as_array().expect("typed refusals").is_empty(), "silent refusal: {body}");
            if name.starts_with("refuse_fat_local_") {
                assert!(body["unsupported"].to_string().contains("SliceMatch(fat pointer local join)"),
                    "missing specific deferred fat-local refusal: {body}");
            }
            if *name == "refuse_fat_inner_return" {
                assert!(body["unsupported"].to_string().contains("SliceMatch(fat pointer control-flow join)"),
                    "missing specific all-arms-diverge nested-fat refusal: {body}");
            }
            if *name == "refuse_unit_array_asm" {
                assert!(body["unsupported"].to_string().contains("Array(unsupported element)"),
                    "unit type hid an unsupported element effect: {body}");
            }
        }
    }
    // Do not hide new failures in helpers or call-bearing deferred rows.
    for body in bodies {
        for channel in ["interpreter", "derived_mir"] {
            assert_ne!(body["differentials"][channel]["verdict"], "mismatch", "{body}");
        }
        if body["differentials"]["seam"]["state"] == "resolved" {
            assert_ne!(body["differentials"]["seam"]["verdict"], "mismatch", "{body}");
        }
    }
    for name in ["execute_one", "execute_two", "execute_rest", "execute_empty", "execute_byte_pair", "execute_zst", "execute_reference_join", "execute_overlap", "execute_zst_repeat", "execute_unit_array_effects", "execute_unit_array_diverge"] {
        let body = bodies.iter().find(|body| body["def_path"].as_str()
            .is_some_and(|path| path.rsplit("::").next() == Some(name))).unwrap();
        let interpreter = &body["differentials"]["interpreter"];
        let samples = interpreter["samples"].as_u64().expect("actual internal sample count");
        if samples == 0 {
            assert!(LIVE_USIZE_HAVOC.contains(&name), "unexpected unexecuted oracle body: {body}");
            assert_eq!(interpreter["verdict"], "not-run", "unavailable oracle became agreement: {body}");
            let detail = interpreter["detail"].as_str().expect("typed oracle limitation");
            assert!(detail.starts_with("MIR oracle carries a LIVE havoc (`Inst::Undef`")
                && detail.contains("undef ty usize"), "different oracle failure hidden: {body}");
        }
        // Allocating local storage may retain the existing conservative
        // allocation-identity NotRun classification. It is not full agreement.
        assert!(matches!(interpreter["verdict"].as_str(), Some("agreed" | "not-run")), "{body}");
    }
}
