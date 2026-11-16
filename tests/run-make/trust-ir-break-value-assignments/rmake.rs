//! Break-value writes must reach loop exit state; value-local bindings must
//! not become uninitialized header arguments. Keep the negative admission case.
//@ ignore-cross-compile
use run_make_support::{cmd, rfs, rustc_path, serde_json, trust_ir};
fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() { return; }
    let output = cmd(rustc_path()).args([
        "subject.rs", "--edition=2024", "--crate-type=lib", "--crate-name=break_values",
        "--emit=metadata", "-Coverflow-checks=on", "-Copt-level=0", "-Zthreads=1",
        "-Ztrust-verify=off", "-Ztrust-ir-lower=on", "-Ztrust-ir-flip=no",
        "-Ztrust-dump=ir:ir", "-o", "break_values.rmeta",
    ]).run();
    assert!(!output.stderr_utf8().contains("final Trust-IR module validation failed"));
    let coverage: serde_json::Value = serde_json::from_slice(&rfs::read("ir/break_values.coverage.json")).unwrap();
    assert_eq!(coverage["proof_authority"], false);
    let names = ["inner", "both_arms", "outer", "local_temp", "local_before_value",
        "direct_outer_assignment", "mixed_locals", "shadowed_local", "destructured_locals",
        "inner_false", "inner_true", "both_arms_false", "both_arms_true", "outer_false", "outer_true",
        "mixed_shadowed", "mixed_shadowed_false", "mixed_shadowed_true",
        "nested_value", "nested_value_false", "nested_value_true"];
    let rows = coverage["bodies"].as_array().unwrap();
    assert_eq!(rows.len(), names.len() + 1);
    let text = trust_ir::by_display_path(&rfs::read_to_string("ir/break_values.trust-ir.txt"));
    for name in names {
        let found: Vec<_> = rows.iter().filter(|row| row["def_path"] == name).collect();
        assert_eq!(found.len(), 1);
        let row = found[0];
        assert_eq!(row["lowered"], true, "{name}: {row}");
        assert_eq!(row["symbolic"], false, "{name}: {row}");
        assert!(row["unsupported"].as_array().unwrap().is_empty(), "{name}: {row}");
        assert_eq!(row["differentials"]["interpreter"]["verdict"], "agreed", "{name}: {row}");
        assert!(row["differentials"]["interpreter"]["samples"].as_u64().unwrap() > 0, "{name}: {row}");
        let plain = format!("fn @{name}(");
        let quoted = format!("fn @\"{name}\"(");
        let body = text.split_once(&plain).or_else(|| text.split_once(&quoted)).unwrap().1.split_once("\n}\n").unwrap().0;
        assert!(!body.contains("undef"));
    }
    let external: Vec<_> = rows.iter().filter(|row| row["def_path"] == "uninitialized_external").collect();
    assert_eq!(external.len(), 1);
    assert_eq!(external[0]["lowered"], false);
    assert!(external[0]["unsupported"].as_array().unwrap().iter().any(|reason| reason[0] == "Loop(carried local unbound pre-loop)"));
}
