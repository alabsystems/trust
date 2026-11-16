//! Primitive float homes preserve the complete value across actual mutable calls.
//! The separate original-module observer executes these unchanged source bodies.
//@ ignore-cross-compile

use run_make_support::{rfs, rustc, serde_json};

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }
    rfs::create_dir("float-ir");
    rustc().input("subject.rs").crate_name("float_reference_storage")
        .crate_type("lib").edition("2021").emit("trust-ir").out_dir("float-ir")
        .arg("-Ztrust-verify=off").run();
    let coverage: serde_json::Value = serde_json::from_str(&rfs::read_to_string(
        "float-ir/float_reference_storage.trust-ir.coverage.json")).unwrap();
    let rows = coverage["bodies"].as_array().unwrap();
    assert_eq!(rows.len(), 16, "all source functions stay in the population");
    assert_eq!(coverage["totals"]["bodies"], 16);
    assert_eq!(coverage["totals"]["lowered"], 16);
    assert_eq!(coverage["totals"]["spliced"], 16);
    assert_eq!(coverage["totals"]["symbolic"], 0);
    assert_eq!(coverage["totals"]["initializer_bodies"], 0);
    assert_eq!(coverage["proof_authority"], false);
    assert_eq!(coverage["native_verification_requests"], false);
    for name in ["store_f32", "store_f64", "read_f32", "read_f64",
        "replace_f32", "replace_f64", "branch_f32", "branch_f64",
        "pattern_f32", "pattern_f64", "raw_local_f32", "raw_local_f64",
        "delayed_f32", "delayed_f64", "parameter_f32", "parameter_f64"]
    {
        let found: Vec<_> = rows.iter().filter(|row| row["def_path"] == name).collect();
        assert_eq!(found.len(), 1, "one source body for {name}");
        assert_eq!(found[0]["lowered"], true, "{name}: {}", found[0]);
        assert_eq!(found[0]["spliced"], true, "{name}: {}", found[0]);
        assert!(found[0]["unsupported"].as_array().unwrap().is_empty(), "{name}: {}", found[0]);
    }
    // Missing place identity and richer pattern semantics remain explicit
    // refusals. These six bodies supplement the unchanged sixteen positives.
    rfs::create_dir("binding-refusal-ir");
    rustc().input("refusals.rs").crate_name("float_reference_binding_refusals")
        .crate_type("lib").edition("2021").emit("trust-ir").out_dir("binding-refusal-ir")
        .arg("-Ztrust-verify=off").run();
    let refusals: serde_json::Value = serde_json::from_str(&rfs::read_to_string(
        "binding-refusal-ir/float_reference_binding_refusals.trust-ir.coverage.json")).unwrap();
    let refused = refusals["bodies"].as_array().unwrap();
    assert_eq!(refused.len(), 6, "complete added refusal population");
    assert_eq!(refusals["totals"]["bodies"], 6);
    assert_eq!(refusals["totals"]["lowered"], 0);
    assert_eq!(refusals["totals"]["spliced"], 0);
    assert_eq!(refusals["totals"]["symbolic"], 0);
    assert_eq!(refusals["totals"]["initializer_bodies"], 0);
    assert_eq!(refusals["proof_authority"], false);
    assert_eq!(refusals["native_verification_requests"], false);
    for (name, tag) in [("shared_binding", "FloatMatch(unsupported pattern)"),
        ("guarded_binding", "FloatMatch(guarded arm)"),
        ("subpattern_binding", "FloatMatch(unsupported pattern)"),
        ("value_temporary", "FloatMatch(unsupported pattern)"),
        ("field_place", "FloatMatch(unsupported pattern)"),
        ("raw_pointer_place", "FloatMatch(unsupported pattern)")]
    {
        let found: Vec<_> = refused.iter().filter(|row| row["def_path"] == name).collect();
        assert_eq!(found.len(), 1, "one original refusal body for {name}");
        assert_eq!(found[0]["lowered"], false, "{name}: {}", found[0]);
        assert_eq!(found[0]["spliced"], false, "{name}: {}", found[0]);
        assert!(found[0]["unsupported"].to_string().contains(tag), "{name}: {}", found[0]);
    }
    let module = rfs::read_to_string("float-ir/float_reference_storage.trust-ir.txt");
    assert!(!module.contains(" = undef "), "source initialization must not be fabricated");
}
