//! Complete source census and pending bounds for the actual array assignment fixture.

use run_make_support::{cmd, rfs, rustc_path, serde_json};

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }
    cmd(rustc_path())
        .args([
            "array_write.rs",
            "--edition=2024",
            "--crate-type=lib",
            "--crate-name=array_write_actual",
            "--emit=mir",
            "-Coverflow-checks=on",
            "-Copt-level=0",
            "-Zthreads=1",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=on",
            "-Ztrust-ir-flip=no",
            "-Ztrust-dump=ir:write-ir",
            "-o",
            "write.mir",
        ])
        .run();
    let report: serde_json::Value =
        serde_json::from_slice(&rfs::read("write-ir/array_write_actual.coverage.json")).unwrap();
    let names = [
        "rhs_reseats_array",
        "rhs_reseats_array::{constant#0}",
        "rhs_reseats_array::{constant#1}",
        "index_reseats_array",
        "index_reseats_array::{constant#0}",
        "index_reseats_array::{constant#1}",
        "rhs_before_index",
        "rhs_before_index::{constant#0}",
        "rhs_value_is_captured",
        "rhs_value_is_captured::{constant#0}",
        "pure_array_write",
        "pure_array_write::{constant#0}",
        "const_write_preserves_rhs_reseat",
        "const_write_preserves_rhs_reseat::{constant#0}",
        "const_write_preserves_rhs_reseat::{constant#1}",
    ];
    let rows = report["bodies"].as_array().unwrap();
    assert_eq!(rows.len(), names.len());
    for key in ["bodies", "lowered", "spliced"] {
        assert_eq!(report["totals"][key], 15);
    }
    assert_eq!(report["totals"]["initializer_bodies"], 9);
    assert_eq!(report["totals"]["unsupported"], 0);
    assert_eq!(report["totals"]["symbolic"], 0);
    assert_eq!(report["proof_authority"], false);
    assert_eq!(report["native_verification_requests"], false);
    assert_eq!(report["direct_obligation_capability"], "obligation-bearing-pending-v2");
    for name in names {
        let found: Vec<_> = rows.iter().filter(|r| r["def_path"] == name).collect();
        assert_eq!(found.len(), 1, "missing/duplicate body {name}");
        let row = found[0];
        assert_eq!(row["lowered"], true);
        assert_eq!(row["spliced"], true);
        assert_eq!(row["symbolic"], false);
        assert!(row["unsupported"].as_array().unwrap().is_empty());
    }
    let text = rfs::read_to_string("write-ir/array_write_actual.trust-ir.txt");
    let obligations: Vec<_> = text.lines().filter(|l| l.starts_with("obligation ")).collect();
    assert_eq!(obligations.len(), 12);
    assert!(
        obligations.iter().all(|l| l.contains(" bounds_check pending ") && l.contains(" site f"))
    );
    for name in [
        "rhs_reseats_array",
        "index_reseats_array",
        "rhs_before_index",
        "rhs_value_is_captured",
        "pure_array_write",
        "const_write_preserves_rhs_reseat",
    ] {
        // WS5.2: `Function.name` is the link-time symbol; the def path is the display path.
        let header = format!("; #display-path: {name:?}\n");
        assert_eq!(text.matches(&header).count(), 1);
        let body = text.split_once(&header).unwrap().1.split_once("\n}\n").unwrap().0;
        let assertions: Vec<_> = body.match_indices("assert ").map(|(i, _)| i).collect();
        assert_eq!(assertions.len(), 2);
        assert_eq!(body.matches("#proof: in_bounds").count(), 2);
        assert_eq!(body.matches("insertelement ").count(), 1);
        let write = body.find("insertelement ").unwrap();
        assert!(assertions[0] < write && write < assertions[1]);
        assert!(assertions[1] < body.find("extractelement ").unwrap());
    }
}
