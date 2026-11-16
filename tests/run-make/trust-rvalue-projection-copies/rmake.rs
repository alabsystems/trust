//! Aggregate rvalues are temporary storage, including control-flow results.
//! Compare native observations with the emitted IR, retaining trap/drop guards.
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
    for (arg, message) in [
        ("overflow", "attempt to add with overflow"),
        ("capture-overflow", "attempt to add with overflow"),
        ("divide", "attempt to divide by zero"),
        ("oob", "index out of bounds"),
    ] {
        assert!(cmd("./native").arg(arg).run_fail().stderr_utf8().contains(message));
    }
    cmd(rustc_path())
        .args([
            "subject.rs",
            "--edition=2024",
            "--crate-type=lib",
            "--crate-name=rvalue_copies",
            "--emit=metadata",
            "-Coverflow-checks=on",
            "-Copt-level=0",
            "-Zthreads=1",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=on",
            "-Ztrust-ir-flip=no",
            "-Ztrust-dump=ir:ir",
            "-o",
            "rvalue_copies.rmeta",
        ])
        .run();
    let coverage: serde_json::Value =
        serde_json::from_slice(&rfs::read("ir/rvalue_copies.coverage.json")).unwrap();
    assert_eq!(coverage["proof_authority"], false);
    assert_eq!(coverage["totals"]["lowered"], 48);
    let rows = coverage["bodies"].as_array().unwrap();
    assert_eq!(rows.len(), 51, "{rows:?}");
    let values = [
        ("block_field_plain", 1),
        ("block_field_compound", 1),
        ("block_array_plain", 1),
        ("block_array_compound", 1),
        ("if_field_plain", 1),
        ("if_field_compound", 1),
        ("if_array_plain", 1),
        ("if_array_compound", 1),
        ("loop_field_plain", 1),
        ("loop_array_compound", 1),
        ("match_field_compound", 1),
        ("literal_field_plain", 1),
        ("literal_tuple_compound", 1),
        ("literal_array_plain", 1),
        ("repeat_array_compound", 1),
        ("call_field_plain", 1),
        ("call_array_compound", 1),
        ("named_const_field_plain", 1),
        ("inline_const_array_compound", 1),
        ("inline_const_tuple_compound", 1),
        ("inline_const_struct_compound", 1),
        ("inline_const_array_value", 17),
        ("inline_const_tuple_value", 17),
        ("inline_const_struct_value", 17),
        ("inline_const_nested_value", 17),
        ("block_field_rhs_order", 7),
        ("block_array_effect_order", 3007),
        ("if_base_effect_order", 123),
        ("loop_base_effect_order", 12),
        ("real_reference_compound", 4),
    ];
    let traps = [
        "block_field_overflow",
        "block_array_capture_overflow",
        "block_field_divide_by_zero",
        "block_array_oob",
    ];
    let mut expected_names: Vec<_> = values.iter().map(|(name, _)| *name).collect();
    expected_names.extend(traps);
    expected_names.extend([
        "make_pair",
        "make_array",
        "dropping_block_refused",
        "dropping_if_refused",
        "asm_refused",
        "<Pair as std::clone::Clone>::clone",
        "<Dropping as std::ops::Drop>::drop",
        "repeat_array_compound::{constant#0}",
        "make_array::{constant#0}",
        "PAIR",
        "inline_const_array_compound::{constant#0}",
        "inline_const_tuple_compound::{constant#0}",
        "inline_const_struct_compound::{constant#0}",
        "inline_const_array_value::{constant#0}",
        "inline_const_tuple_value::{constant#0}",
        "inline_const_struct_value::{constant#0}",
        "inline_const_nested_value::{constant#0}",
    ]);
    let mut observed_names: Vec<_> = rows.iter().map(|r| r["def_path"].as_str().unwrap()).collect();
    expected_names.sort();
    observed_names.sort();
    assert_eq!(observed_names, expected_names);
    for row in rows.iter().filter(|r| r["kind"] != "fn") {
        assert_eq!(row["lowered"], true, "{row}");
        assert!(row["unsupported"].as_array().unwrap().is_empty(), "{row}");
    }
    let module = deserialize_module(&rfs::read("ir/rvalue_copies.trust-ir.bin")).unwrap();
    let interpreter = Interpreter::with_module(&module);
    for (name, value) in values {
        let row = rows.iter().find(|r| r["def_path"] == name).unwrap();
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
        let f = module.functions.iter().find(|f| f.display_path.as_deref() == Some(name)).unwrap();
        let result = interpreter.execute_func(f.id, []).unwrap();
        assert_eq!(result.host_calls, 0, "{name}");
        assert_eq!(result.returns, vec![InterpretValue::int(Ty::U32, value).unwrap()], "{name}");
    }
    for name in traps {
        let row = rows.iter().find(|r| r["def_path"] == name).unwrap();
        assert_eq!(row["lowered"], true, "{name}: {row}");
        assert!(row["unsupported"].as_array().unwrap().is_empty(), "{name}: {row}");
        let f = module.functions.iter().find(|f| f.display_path.as_deref() == Some(name)).unwrap();
        assert_eq!(interpreter.execute_func(f.id, []).unwrap_err().code, InterpretErrorCode::Panic);
    }
    for name in ["dropping_block_refused", "dropping_if_refused"] {
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
