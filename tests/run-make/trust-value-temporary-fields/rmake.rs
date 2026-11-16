//! Writes into a value temporary never rebind its source local.
//! Native execution and the actual emitted IR check values and arithmetic traps.
//@ ignore-cross-compile

use run_make_support::{cmd, rfs, rustc_path, serde_json, trust_ir};
use trust_ir::reference::{
    Ty,
    binary::deserialize_module,
    interpret::{InterpretErrorCode, InterpretValue, Interpreter},
};

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }
    rfs::write(
        "native.rs",
        format!(
            "{}\n{}",
            rfs::read_to_string("subject.rs"),
            rfs::read_to_string("native_assertions.rs")
        ),
    );
    cmd(rustc_path())
        .args([
            "native.rs",
            "--edition=2024",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=off",
            "-Coverflow-checks=on",
            "-o",
            "native",
        ])
        .run();
    cmd("./native").run();
    assert!(
        cmd("./native")
            .arg("overflow")
            .run_fail()
            .stderr_utf8()
            .contains("attempt to add with overflow")
    );
    assert!(
        cmd("./native")
            .arg("divide")
            .run_fail()
            .stderr_utf8()
            .contains("attempt to divide by zero")
    );
    assert!(
        cmd("./native").arg("array-oob").run_fail().stderr_utf8().contains("index out of bounds")
    );
    cmd(rustc_path())
        .args([
            "subject.rs",
            "--edition=2024",
            "--crate-type=lib",
            "--crate-name=field_copies",
            "--emit=metadata",
            "-Coverflow-checks=on",
            "-Copt-level=0",
            "-Zthreads=1",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=on",
            "-Ztrust-ir-flip=no",
            "-Ztrust-dump=ir:ir",
            "-o",
            "field_copies.rmeta",
        ])
        .run();
    let coverage: serde_json::Value =
        serde_json::from_slice(&rfs::read("ir/field_copies.coverage.json")).unwrap();
    assert_eq!(coverage["proof_authority"], false);
    let rows = coverage["bodies"].as_array().unwrap();
    assert_eq!(rows.len(), 43, "{rows:?}");
    let values = [
        ("struct_compound", 1),
        ("tuple_compound", 1),
        ("struct_plain", 1),
        ("tuple_plain", 1),
        ("promoted_struct_compound", 1),
        ("promoted_struct_plain", 1),
        ("promoted_tuple_compound", 1),
        ("promoted_tuple_plain", 1),
        ("nested_compound", 1),
        ("nested_plain", 1),
        ("rhs_replaces_struct", 7),
        ("rhs_replaces_tuple", 7),
        ("side_effecting_base_compound", 31),
        ("side_effecting_base_plain", 31),
        ("guard_compound", 1),
        ("real_struct_place", 4),
        ("real_tuple_place", 4),
        ("deref_of_cast_reference", 4),
        ("indexed_field_plain", 1),
        ("indexed_field_compound", 1),
        ("copied_array_field", 1),
        ("indexed_field_effect_order", 3007),
        ("copied_deref_array_plain", 1),
        ("copied_deref_array_compound", 1),
        ("deref_of_cast_array_reference_plain", 4),
        ("deref_of_cast_array_reference_compound", 4),
    ];
    let mut expected_names: Vec<_> = values.iter().map(|(name, _)| *name).collect();
    expected_names.extend([
        "overflow_temporary",
        "divide_by_zero_temporary",
        "indexed_field_oob",
        "dropping_plain_refused",
        "dropping_compound_refused",
        "asm_refused",
        "<Pair as std::clone::Clone>::clone",
        "<Outer as std::clone::Clone>::clone",
        "<Numbers as std::clone::Clone>::clone",
        "<Dropping as std::ops::Drop>::drop",
        "Numbers::arr::{constant#0}",
        "<Numbers as std::clone::Clone>::clone::{constant#0}",
        "copied_array_field::{constant#0}",
        "copied_deref_array_plain::{constant#0}",
        "copied_deref_array_compound::{constant#0}",
        "deref_of_cast_array_reference_plain::{constant#0}",
        "deref_of_cast_array_reference_compound::{constant#0}",
    ]);
    let mut observed_names: Vec<_> = rows.iter().map(|r| r["def_path"].as_str().unwrap()).collect();
    expected_names.sort();
    observed_names.sort();
    assert_eq!(observed_names, expected_names);
    for row in rows.iter().filter(|row| row["kind"] != "fn") {
        assert_eq!(row["lowered"], true, "{row}");
        assert!(row["unsupported"].as_array().unwrap().is_empty(), "{row}");
    }
    let module = deserialize_module(&rfs::read("ir/field_copies.trust-ir.bin")).unwrap();
    let interpreter = Interpreter::with_module(&module);
    for (name, value) in values {
        let matching: Vec<_> = rows.iter().filter(|r| r["def_path"] == name).collect();
        assert_eq!(matching.len(), 1, "{name}: {rows:?}");
        let row = matching[0];
        assert_eq!(row["lowered"], true, "{name}: {row}");
        assert_eq!(row["spliced"], true, "{name}: {row}");
        assert!(row["unsupported"].as_array().unwrap().is_empty(), "{name}: {row}");
        assert!(
            matches!(
                row["differentials"]["interpreter"]["verdict"].as_str(),
                Some("agreed" | "not-run")
            ),
            "{name}: {row}"
        );
        let matching: Vec<_> =
            module.functions.iter().filter(|f| f.display_path.as_deref() == Some(name)).collect();
        assert_eq!(matching.len(), 1, "{name}");
        let result = interpreter.execute_func(matching[0].id, []).unwrap();
        assert_eq!(result.host_calls, 0, "{name}");
        assert_eq!(result.returns, vec![InterpretValue::int(Ty::U32, value).unwrap()], "{name}");
    }
    for name in ["overflow_temporary", "divide_by_zero_temporary", "indexed_field_oob"] {
        let row = rows.iter().find(|r| r["def_path"] == name).unwrap();
        assert_eq!(row["lowered"], true, "{name}: {row}");
        assert!(row["unsupported"].as_array().unwrap().is_empty(), "{name}: {row}");
        let f = module.functions.iter().find(|f| f.display_path.as_deref() == Some(name)).unwrap();
        assert_eq!(interpreter.execute_func(f.id, []).unwrap_err().code, InterpretErrorCode::Panic);
    }
    for name in ["dropping_plain_refused", "dropping_compound_refused"] {
        let row = rows.iter().find(|r| r["def_path"] == name).unwrap();
        assert_eq!(row["lowered"], false, "{name}: {row}");
        assert!(
            row["unsupported"]
                .as_array()
                .unwrap()
                .iter()
                .any(|r| r[0] == "Assign(temporary field needs drop)"),
            "{name}: {row}"
        );
    }
    let row = rows.iter().find(|r| r["def_path"] == "asm_refused").unwrap();
    assert_eq!(row["lowered"], false, "{row}");
    assert!(row["unsupported"].as_array().unwrap().iter().any(|r| r[0] == "InlineAsm"));
}
