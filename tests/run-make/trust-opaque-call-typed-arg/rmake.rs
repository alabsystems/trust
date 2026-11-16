//! Refuse an opaque carrier at a concrete local call parameter before module assembly.
//! A valid module and an explicit unsupported body are required together. This does
//! not claim faithful lowering of the opaque enum or a source refinement proof.

use std::collections::BTreeSet;
use std::path::PathBuf;

use run_make_support::{bin_name, cmd, rfs, rustc_path, serde_json};

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }
    let rustc = PathBuf::from(rustc_path());
    let trustc = rustc.with_file_name(bin_name("trustc"));
    let trustc = if trustc.exists() { trustc } else { rustc };

    for lane in ["off", "on"] {
        let mut compiler = cmd(&trustc);
        compiler
            .arg("receivers.rs")
            .arg("--edition=2021")
            .arg("--crate-type=lib")
            .arg("--crate-name=receivers")
            .arg("--emit=link")
            .arg("-Copt-level=3")
            .arg("-Cdebug-assertions=off")
            .arg("-Ztrust-verify=off")
            .arg("-Ztrust-policy=strict")
            .arg(format!("-Ztrust-ir-lower={lane}"))
            .arg("-o")
            .arg(format!("receivers-{lane}.rlib"));
        if lane == "on" {
            compiler.arg("-Ztrust-dump=ir:receivers-ir").arg("-Ztrust-ir-flip=yes");
        }
        compiler.run();
    }

    let coverage: serde_json::Value =
        serde_json::from_slice(&rfs::read("receivers-ir/receivers.coverage.json"))
            .expect("published coverage must be valid JSON");
    assert_eq!(coverage["schema"], "trust.thir-lower.crate-module.coverage.v2");
    assert_eq!(coverage["publication"]["commit_marker"], true);
    let bodies = coverage["bodies"].as_array().expect("complete body inventory");
    let expected = BTreeSet::from([
        "Index::value",
        "fat_slice_read",
        "fat_dyn_read",
        "thin_read",
        "accept_unit",
        "unit_argument",
    ]);
    let actual = bodies
        .iter()
        .map(|body| body["def_path"].as_str().expect("body identity"))
        .collect::<BTreeSet<_>>();
    assert_eq!(actual, expected, "no missing or substituted body rows");
    assert_eq!(bodies.len(), expected.len(), "no duplicate body rows");
    assert_eq!(coverage["totals"]["bodies"].as_u64(), Some(expected.len() as u64));

    for body in bodies {
        let name = body["def_path"].as_str().expect("body identity");
        let unsupported = body["unsupported"].as_array().expect("unsupported inventory");
        if matches!(name, "fat_slice_read" | "fat_dyn_read") {
            assert_eq!(body["lowered"], false, "opaque receiver must be refused: {body}");
            assert_eq!(body["spliced"], false, "opaque receiver must not splice: {body}");
            assert!(
                unsupported
                    .contains(&serde_json::json!(["Call(opaque carrier typed argument)", 1])),
                "the actual typed-argument refusal must remain visible: {body}"
            );
        } else {
            assert_eq!(body["lowered"], true, "control must lower: {body}");
            assert_eq!(body["spliced"], true, "control must splice: {body}");
            assert!(unsupported.is_empty(), "control acquired a refusal: {body}");
        }
    }
}
