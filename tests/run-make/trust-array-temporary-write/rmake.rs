//! Keep every body, including the independently unsupported promoted destination.

use run_make_support::{cmd, rfs, rustc_path, serde_json};

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }
    cmd(rustc_path())
        .args([
            "temporary_write.rs",
            "--edition=2024",
            "--crate-type=lib",
            "--crate-name=array_temporary_write_actual",
            "--emit=mir",
            "-Coverflow-checks=on",
            "-Copt-level=0",
            "-Zthreads=1",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=on",
            "-Ztrust-ir-flip=no",
            "-Ztrust-dump=ir:temporary-ir",
            "-o",
            "temporary.mir",
        ])
        .run();
    let report: serde_json::Value = serde_json::from_slice(&rfs::read(
        "temporary-ir/array_temporary_write_actual.coverage.json",
    ))
    .unwrap();
    let names = [
        "cast_temporary_write",
        "cast_temporary_write::{constant#0}",
        "cast_temporary_write::{constant#1}",
        "cast_temporary_index_reseats",
        "cast_temporary_index_reseats::{constant#0}",
        "cast_temporary_index_reseats::{constant#1}",
        "cast_temporary_index_reseats::{constant#2}",
        "cast_temporary_rhs_reseats",
        "cast_temporary_rhs_reseats::{constant#0}",
        "cast_temporary_rhs_reseats::{constant#1}",
        "cast_temporary_rhs_reseats::{constant#2}",
        "index_promotes_destination",
        "index_promotes_destination::{constant#0}",
        "index_promotes_destination::{constant#1}",
        "ordinary_array_write",
        "ordinary_array_write::{constant#0}",
    ];
    let rows = report["bodies"].as_array().unwrap();
    assert_eq!(rows.len(), names.len());
    for (key, count) in [
        ("bodies", 16),
        ("lowered", 15),
        ("spliced", 15),
        ("initializer_bodies", 11),
        ("unsupported", 1),
        ("symbolic", 0),
    ] {
        assert_eq!(report["totals"][key], count);
    }
    assert_eq!(report["proof_authority"], false);
    assert_eq!(report["native_verification_requests"], false);
    assert_eq!(report["direct_obligation_capability"], "obligation-bearing-pending-v2");
    for name in names {
        let found: Vec<_> = rows.iter().filter(|r| r["def_path"] == name).collect();
        assert_eq!(found.len(), 1, "missing/duplicate body {name}");
        let row = found[0];
        assert_eq!(row["kind"], if name.contains("::{constant#") { "const-init" } else { "fn" });
        let admitted = name != "index_promotes_destination";
        assert_eq!(row["lowered"], admitted);
        assert_eq!(row["spliced"], admitted);
        assert_eq!(row["symbolic"], false);
        if admitted {
            assert!(row["unsupported"].as_array().unwrap().is_empty());
        } else {
            assert_eq!(
                row["unsupported"],
                // The destination still refuses at the non-local assignment;
                // the earlier failed-probe diagnostics are no longer emitted.
                serde_json::json!([["Assign(non-local place)", 1]])
            );
        }
    }
    let text = rfs::read_to_string("temporary-ir/array_temporary_write_actual.trust-ir.txt");
    let obligations: Vec<_> = text.lines().filter(|l| l.starts_with("obligation ")).collect();
    assert_eq!(obligations.len(), 8);
    assert!(
        obligations.iter().all(|l| l.contains(" bounds_check pending ") && l.contains(" site f"))
    );
    assert!(!text.contains("; #display-path: \"index_promotes_destination\"\n"));
    for name in [
        "cast_temporary_write",
        "cast_temporary_index_reseats",
        "cast_temporary_rhs_reseats",
        "ordinary_array_write",
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
