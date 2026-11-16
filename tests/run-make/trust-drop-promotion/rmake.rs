//! Freeze values can still need destruction; their borrows cannot become globals.
//@ ignore-cross-compile
use run_make_support::{cmd, rfs, rustc_path, serde_json, trust_ir};
use trust_ir::reference::{
    Inst, Ty,
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
            "-o",
            "native",
        ])
        .run();
    cmd("./native").run();
    for name in [
        "literal",
        "named",
        "array",
        "projected",
        "tuple",
        "projected-runtime",
        "scalar-runtime",
        "struct-runtime",
        "nested-runtime",
        "scoped-runtime",
        "call-runtime",
    ] {
        assert!(
            cmd("./native")
                .arg(name)
                .run_fail()
                .stderr_utf8()
                .contains("drop ran"),
            "{name}"
        );
    }
    cmd(rustc_path())
        .args([
            "subject.rs",
            "--edition=2024",
            "--crate-type=lib",
            "--crate-name=drop_promotion",
            "--emit=metadata",
            "-Copt-level=0",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=on",
            "-Ztrust-ir-flip=no",
            "-Ztrust-dump=ir:ir",
            "-o",
            "subject.rmeta",
        ])
        .run();
    let report: serde_json::Value =
        serde_json::from_slice(&rfs::read("ir/drop_promotion.coverage.json")).unwrap();
    assert_eq!(report["proof_authority"], false);
    assert_eq!(report["native_verification_requests"], false);
    let rows = report["bodies"].as_array().unwrap();
    let mut names: Vec<_> = rows
        .iter()
        .map(|r| r["def_path"].as_str().unwrap())
        .collect();
    let mut expected = vec![
        "<Bomb as std::ops::Drop>::drop",
        "BOMB",
        "literal_temp",
        "named_temp",
        "array_temp",
        "projected_temp",
        "tuple_temp",
        "safe_literal",
        "safe_tuple",
        "projected_runtime",
        "scalar_runtime",
        "struct_runtime",
        "nested_runtime",
        "scoped_runtime",
        "read_bomb",
        "call_runtime",
    ];
    names.sort();
    expected.sort();
    assert_eq!(names, expected);
    assert_eq!(report["totals"]["bodies"], 16);
    let module = deserialize_module(&rfs::read("ir/drop_promotion.trust-ir.bin")).unwrap();
    let interpreter = Interpreter::with_module(&module);
    for name in [
        "literal_temp",
        "named_temp",
        "array_temp",
        "projected_temp",
        "tuple_temp",
        "projected_runtime",
        "scalar_runtime",
        "struct_runtime",
        "nested_runtime",
        "scoped_runtime",
        "call_runtime",
    ] {
        let row = rows.iter().find(|r| r["def_path"] == name).unwrap();
        if name.ends_with("_runtime") {
            assert_eq!(row["lowered"], true, "{name}: {row}");
        }
        if row["lowered"] == false {
            assert!(
                !row["unsupported"].as_array().unwrap().is_empty(),
                "{name}: {row}"
            );
            continue;
        }
        let f = module
            .functions
            .iter()
            .find(|f| f.display_path.as_deref() == Some(name))
            .unwrap();
        assert!(
            f.blocks
                .iter()
                .flat_map(|b| &b.body)
                .any(|n| matches!(n.inst, Inst::Drop { .. })),
            "{name} erased destruction"
        );
        assert_eq!(
            row["differentials"]["interpreter"]["verdict"], "not-run",
            "{name}: {row}"
        );
        let args = if name.ends_with("_runtime") {
            vec![InterpretValue::int(Ty::U32, 7).unwrap()]
        } else {
            vec![]
        };
        let error = interpreter.execute_func(f.id, args).unwrap_err();
        if error.code != InterpretErrorCode::Panic {
            assert_eq!(
                error.code,
                InterpretErrorCode::UnsupportedInstruction,
                "{name}: {error:?}"
            );
            assert!(
                error.to_string().contains("no drop_glue row"),
                "{name}: {error:?}"
            );
        }
    }
    // The ordinary promotion cases keep compiling and interpreting normally.
    for name in ["safe_literal", "safe_tuple"] {
        let row = rows.iter().find(|r| r["def_path"] == name).unwrap();
        assert_eq!(row["lowered"], true, "{name}: {row}");
        let f = module
            .functions
            .iter()
            .find(|f| f.display_path.as_deref() == Some(name))
            .unwrap();
        let result = interpreter.execute_func(f.id, []).unwrap();
        assert_eq!(result.host_calls, 0);
        assert_eq!(
            result.returns,
            vec![InterpretValue::int(Ty::U32, 7).unwrap()]
        );
    }
}
