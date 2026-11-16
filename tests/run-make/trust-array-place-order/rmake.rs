//! Actual compiler census and place-read ordering; execution lives in array_support.rs.

use run_make_support::{cmd, rfs, rustc_path, serde_json};

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }
    cmd(rustc_path())
        .args([
            "array_place.rs",
            "--edition=2024",
            "--crate-type=lib",
            "--crate-name=array_place_actual",
            "--emit=mir",
            "-Coverflow-checks=on",
            "-Copt-level=0",
            "-Zthreads=1",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=on",
            "-Ztrust-ir-flip=no",
            "-Ztrust-dump=ir:array-ir",
            "-o",
            "array.mir",
        ])
        .run();
    let report: serde_json::Value =
        serde_json::from_slice(&rfs::read("array-ir/array_place_actual.coverage.json")).unwrap();
    let names = [
        "reseat_array",
        "reseat_array::{constant#0}",
        "reseat_array::{constant#1}",
        "array_index_value_is_captured",
        "array_index_value_is_captured::{constant#0}",
        "reseat_array_through_alias",
        "reseat_array_through_alias::{constant#0}",
        "reseat_array_through_alias::{constant#1}",
    ];
    let rows = report["bodies"].as_array().unwrap();
    assert_eq!(rows.len(), names.len());
    for key in ["bodies", "lowered", "spliced"] {
        assert_eq!(report["totals"][key], 8);
    }
    assert_eq!(report["totals"]["symbolic"], 0);
    assert_eq!(report["proof_authority"], false);
    assert_eq!(report["native_verification_requests"], false);
    assert_eq!(report["direct_obligation_capability"], "obligation-bearing-pending-v2");
    for name in names {
        let found: Vec<_> = rows.iter().filter(|r| r["def_path"] == name).collect();
        assert_eq!(found.len(), 1, "missing/duplicate {name}");
        assert_eq!(found[0]["lowered"], true);
        assert_eq!(found[0]["spliced"], true);
        assert_eq!(found[0]["symbolic"], false);
        assert!(found[0]["unsupported"].as_array().unwrap().is_empty());
    }
    let text = rfs::read_to_string("array-ir/array_place_actual.trust-ir.txt");
    let obligations: Vec<_> = text.lines().filter(|line| line.starts_with("obligation ")).collect();
    assert_eq!(obligations.len(), 3);
    assert!(
        obligations.iter().all(|l| l.contains(" bounds_check pending ") && l.contains(" site f"))
    );
    for name in ["reseat_array", "array_index_value_is_captured", "reseat_array_through_alias"] {
        // WS5.2: `Function.name` is the link-time symbol; the def path is the display path.
        let header = format!("; #display-path: {name:?}\n");
        assert_eq!(text.matches(&header).count(), 1);
        let body = text.split_once(&header).unwrap().1.split_once("\n}\n").unwrap().0;
        assert_eq!(body.matches("assert ").count(), 1);
        assert_eq!(body.matches("#proof: in_bounds").count(), 1);
        let assertion = body.find("assert ").unwrap();
        let extract = body.find("extractelement u8 ").unwrap();
        assert!(body.find("icmp ult usize ").unwrap() < assertion);
        assert!(assertion < extract);
        match name {
            "reseat_array" => assert!(body.contains("extractelement u8 %1, %2")),
            "array_index_value_is_captured" => assert!(body.contains("extractelement u8 %0, %1")),
            _ => {
                let stores: Vec<_> = body.match_indices("store ").map(|(i, _)| i).collect();
                assert_eq!(stores.len(), 2);
                let loads: Vec<_> = body.match_indices("load ").map(|(i, _)| i).collect();
                assert_eq!(loads.len(), 1);
                assert!(stores[1] < assertion && assertion < loads[0] && loads[0] < extract);
            }
        }
    }
}
