//! Keep the entire value-temporary source census and every pending bounds row.

use run_make_support::{cmd, rfs, rustc_path, serde_json};

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }
    cmd(rustc_path())
        .args([
            "rvalue_bases.rs",
            "--edition=2024",
            "--crate-type=lib",
            "--crate-name=index_rvalue_actual",
            "--emit=mir",
            "-Coverflow-checks=on",
            "-Copt-level=0",
            "-Zthreads=1",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=on",
            "-Ztrust-ir-flip=no",
            "-Ztrust-dump=ir:rvalue-ir",
            "-o",
            "rvalue.mir",
        ])
        .run();
    let report: serde_json::Value =
        serde_json::from_slice(&rfs::read("rvalue-ir/index_rvalue_actual.coverage.json")).unwrap();
    let names = [
        "cast_reference_value",
        "cast_reference_value::{constant#0}",
        "cast_reference_value::{constant#1}",
        "cast_reference_value::{constant#2}",
        "reference_place",
        "reference_place::{constant#0}",
        "reference_place::{constant#1}",
        "block_array_value",
        "block_array_value::{constant#0}",
        "block_array_value::{constant#1}",
        "cast_slice_value",
        "cast_array_value",
        "cast_array_value::{constant#0}",
        "cast_array_value::{constant#1}",
        "cast_array_value::{constant#2}",
    ];
    let rows = report["bodies"].as_array().unwrap();
    assert_eq!(rows.len(), names.len());
    assert_eq!(report["totals"]["bodies"], 15);
    assert_eq!(report["totals"]["lowered"], 15);
    assert_eq!(report["totals"]["spliced"], 15);
    assert_eq!(report["totals"]["initializer_bodies"], 10);
    assert_eq!(report["totals"]["symbolic"], 0);
    assert_eq!(report["totals"]["unsupported"], 0);
    assert_eq!(report["proof_authority"], false);
    assert_eq!(report["native_verification_requests"], false);
    assert_eq!(report["direct_obligation_capability"], "obligation-bearing-pending-v2");
    for name in names {
        let found: Vec<_> = rows.iter().filter(|r| r["def_path"] == name).collect();
        assert_eq!(found.len(), 1, "missing/duplicate source body {name}");
        let row = found[0];
        assert_eq!(row["lowered"], true);
        assert_eq!(row["spliced"], true);
        assert_eq!(row["symbolic"], false);
        assert!(row["unsupported"].as_array().unwrap().is_empty());
    }
    let text = rfs::read_to_string("rvalue-ir/index_rvalue_actual.trust-ir.txt");
    let obligations: Vec<_> = text.lines().filter(|l| l.starts_with("obligation ")).collect();
    assert_eq!(obligations.len(), 5);
    assert!(
        obligations.iter().all(|l| l.contains(" bounds_check pending ") && l.contains(" site f"))
    );
    for name in [
        "cast_reference_value",
        "reference_place",
        "block_array_value",
        "cast_slice_value",
        "cast_array_value",
    ] {
        // WS5.2: `Function.name` is the link-time symbol; the def path is the display path.
        let header = format!("; #display-path: {name:?}\n");
        assert_eq!(text.matches(&header).count(), 1);
        let body = text.split_once(&header).unwrap().1.split_once("\n}\n").unwrap().0;
        assert_eq!(body.matches("assert ").count(), 1);
        assert_eq!(body.matches("#proof: in_bounds").count(), 1);
        assert!(body.find("icmp ult ").unwrap() < body.find("assert ").unwrap());
        let read = if name == "cast_slice_value" { "ptr_data " } else { "extractelement " };
        assert!(body.find("assert ").unwrap() < body.find(read).unwrap());
    }
}
