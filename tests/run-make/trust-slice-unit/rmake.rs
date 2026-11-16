//! Real compiler census/obligation controls for actual Rust unit-slice reads.
//! Zero-array elements keep their own carrier and bounds check. Execute the
//! unchanged emitted body and require mutations that remove/reverse its check to fail.

use run_make_support::{bin_name, cmd, rfs, run, rustc_path, serde_json, target, trust_ir};

mod zero_array;

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return; // Stock rustc has no Trust-IR artifact interface.
    }
    rfs::write(
        "native.rs",
        format!("{}\n{}", rfs::read_to_string("unit.rs"), rfs::read_to_string("native_assertions.rs")),
    );
    cmd(rustc_path())
        .arg(format!("--target={}", target()))
        .args([
            "native.rs", "--edition=2024", "-Ztrust-verify=off", "-Ztrust-ir-lower=off",
            "-Coverflow-checks=on", "-Copt-level=0", "-o",
        ])
        .arg(bin_name("native"))
        .run();
    run(&bin_name("native"));
    cmd(rustc_path())
        .arg(format!("--target={}", target()))
        .args([
            "unit.rs",
            "--edition=2024",
            "--crate-type=lib",
            "--crate-name=slice_unit_actual",
            "--emit=mir",
            "-Coverflow-checks=on",
            "-Copt-level=0",
            "-Zthreads=1",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=on",
            "-Ztrust-ir-flip=no",
            "-Ztrust-dump=ir:unit-ir",
            "-o",
            "unit.mir",
        ])
        .run();
    let report: serde_json::Value =
        serde_json::from_slice(&rfs::read("unit-ir/slice_unit_actual.coverage.json")).unwrap();
    let names = [
        "read_unit",
        "unit_index_effect",
        "reseat_unit",
        "read_generic",
        "read_nonunit_zst",
        "read_nonunit_zst::{constant#0}",
        "read_nonunit_zst::{constant#1}",
    ];
    let rows = report["bodies"].as_array().unwrap();
    assert_eq!(rows.len(), names.len());
    assert_eq!(report["totals"]["bodies"], 7);
    assert_eq!(report["totals"]["lowered"], 6);
    assert_eq!(report["totals"]["spliced"], 6);
    assert_eq!(report["totals"]["symbolic"], 1, "generic residue remains counted");
    assert_eq!(report["proof_authority"], false);
    assert_eq!(report["native_verification_requests"], false);
    assert_eq!(report["direct_obligation_capability"], "obligation-bearing-pending-v2");
    for name in names {
        let matching: Vec<_> = rows.iter().filter(|r| r["def_path"] == name).collect();
        assert_eq!(matching.len(), 1, "missing/duplicate {name}");
        let row = matching[0];
        if name == "read_generic" {
            assert_eq!(row["lowered"], false, "generic element remains unsupported");
            assert_eq!(row["spliced"], false);
            assert!(!row["unsupported"].as_array().unwrap().is_empty());
        } else {
            assert_eq!(row["lowered"], true);
            assert_eq!(row["spliced"], true);
            assert_eq!(row["symbolic"], false);
            assert!(row["unsupported"].as_array().unwrap().is_empty());
        }
    }
    let text = rfs::read_to_string("unit-ir/slice_unit_actual.trust-ir.txt");
    let obligations: Vec<_> = text.lines().filter(|line| line.starts_with("obligation ")).collect();
    assert_eq!(obligations.len(), 4);
    assert!(
        obligations
            .iter()
            .all(|line| line.contains(" bounds_check pending ") && line.contains(" site f"))
    );
    for name in ["read_unit", "unit_index_effect", "reseat_unit", "read_nonunit_zst"] {
        // WS5.2: `Function.name` is the link-time symbol; the def path is the display path.
        let header = format!("; #display-path: {name:?}\n");
        assert_eq!(text.matches(&header).count(), 1);
        let body = text.split_once(&header).unwrap().1.split_once("\n}\n").unwrap().0;
        let mut cursor = 0;
        for instruction in ["ptr_metadata ", "bitcast ", "icmp ult usize ", "assert ", "ret"] {
            cursor += body[cursor..].find(instruction).unwrap() + instruction.len();
        }
        assert_eq!(body.matches("assert ").count(), 1);
        assert_eq!(body.matches("#proof: in_bounds").count(), 1);
        for unwanted in ["ptr_data ", "gep ", "load "] {
            assert!(!body.contains(unwanted), "unit has no payload read: {body}");
        }
        if name == "reseat_unit" {
            let metadata = body.lines().find(|line| line.contains("ptr_metadata ")).unwrap();
            assert!(metadata.split("  ;").next().unwrap().ends_with(" %1 to u64"));
        }
    }
    let module = trust_ir::reference::binary::deserialize_module(
        &rfs::read("unit-ir/slice_unit_actual.trust-ir.bin"),
    )
    .unwrap();
    zero_array::check(&module);
}
