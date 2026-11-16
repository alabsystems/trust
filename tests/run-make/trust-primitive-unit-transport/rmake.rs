//! Completed Unit-call effects and real Unit tuple lanes remain executable.
//@ ignore-cross-compile
use run_make_support::{rfs, rustc, serde_json};
fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() { return; }
    rfs::create_dir("unit-ir");
    rustc().input("subject.rs").crate_name("primitive_unit_transport")
        .crate_type("lib").edition("2021").emit("trust-ir").out_dir("unit-ir")
        .arg("-Ztrust-verify=off").run();
    let coverage: serde_json::Value = serde_json::from_str(&rfs::read_to_string(
        "unit-ir/primitive_unit_transport.trust-ir.coverage.json")).unwrap();
    let rows = coverage["bodies"].as_array().unwrap();
    assert_eq!(rows.len(), 4);
    for key in ["bodies", "lowered", "spliced"] { assert_eq!(coverage["totals"][key], 4); }
    for key in ["symbolic", "initializer_bodies"] { assert_eq!(coverage["totals"][key], 0); }
    assert_eq!(coverage["proof_authority"], false);
    assert_eq!(coverage["native_verification_requests"], false);
    for name in ["tick", "unit_call_once", "unit_call_after_branch", "unit_tuple_field"] {
        let found: Vec<_> = rows.iter().filter(|r| r["def_path"] == name).collect();
        assert_eq!(found.len(), 1, "complete exact source identity {name}");
        assert_eq!(found[0]["lowered"], true, "{name}: {}", found[0]);
        assert_eq!(found[0]["spliced"], true, "{name}: {}", found[0]);
        assert!(found[0]["unsupported"].as_array().unwrap().is_empty(), "{name}: {}", found[0]);
    }
}
