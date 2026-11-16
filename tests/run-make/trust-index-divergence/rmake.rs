//! Index operands may terminate their path without producing an indexed value.
//! Native execution and direct IR must agree, including evaluation order and traps.
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
    rfs::write("native.rs", format!("{}\n{}",
        rfs::read_to_string("subject.rs"), rfs::read_to_string("native_assertions.rs")));
    cmd(rustc_path()).args([
        "native.rs", "--edition=2024", "-Ztrust-verify=off", "-Ztrust-ir-lower=off",
        "-Coverflow-checks=on", "-o", "native",
    ]).run();
    cmd("./native").run();
    for case in ["array-oob", "slice-oob", "ordinary-slice-oob", "base-panic", "inner-array-oob",
                 "inner-slice-oob", "conditional-empty", "conditional-oob"] {
        assert!(cmd("./native").arg(case).run_fail().stderr_utf8()
            .contains("index out of bounds"), "{case}");
    }
    cmd(rustc_path()).args([
        "subject.rs", "--edition=2024", "--crate-type=lib", "--crate-name=index_divergence",
        "--emit=metadata", "-Copt-level=0", "-Coverflow-checks=on", "-Zthreads=1",
        "-Ztrust-verify=off", "-Ztrust-ir-lower=on", "-Ztrust-ir-flip=no",
        "-Ztrust-dump=ir:ir", "-o", "subject.rmeta",
    ]).run();
    let report: serde_json::Value =
        serde_json::from_slice(&rfs::read("ir/index_divergence.coverage.json")).unwrap();
    assert_eq!(report["proof_authority"], false);
    assert_eq!(report["native_verification_requests"], false);
    let rows = report["bodies"].as_array().unwrap();
    let mut observed: Vec<_> = rows.iter().map(|row| row["def_path"].as_str().unwrap()).collect();
    let mut expected = vec![
        "array_base_constant", "array_base_dynamic", "slice_base_dynamic",
        "slice_index_returns", "array_index_break", "slice_index_break",
        "ordinary_array", "ordinary_slice",
        "ordinary_slice_values",
        "ordinary_slice_empty", "both_diverge", "array_base_break",
        "slice_base_break", "inner_array_loop", "inner_slice_loop", "conditional_index",
        "trapping_base", "earlier_refusal", "array_base_with_asm", "slice_index_with_asm",
        "slice_return_empty", "slice_break_empty", "inner_slice_values",
        "conditional_empty", "conditional_values",
    ];
    observed.sort(); expected.sort();
    assert_eq!(observed, expected);
    for row in rows {
        let name = row["def_path"].as_str().unwrap();
        assert_eq!(row["symbolic"], false, "{name}: {row}");
        if ["earlier_refusal", "array_base_with_asm", "slice_index_with_asm"].contains(&name) {
            assert_eq!(row["lowered"], false, "{name}: {row}");
            assert_eq!(row["spliced"], false, "{name}: {row}");
            assert!(row["unsupported"].as_array().unwrap().iter()
                .any(|reason| reason[0] == "InlineAsm"), "{name}: {row}");
            if name != "earlier_refusal" {
                let contextual = if name == "array_base_with_asm" {
                    "Index(unsupported base)"
                } else {
                    "SliceIndex(unsupported index)"
                };
                assert!(row["unsupported"].as_array().unwrap().iter()
                    .any(|reason| reason[0] == contextual), "{name}: {row}");
            }
        } else {
            assert_eq!(row["lowered"], true, "{name}: {row}");
            assert_eq!(row["spliced"], true, "{name}: {row}");
            assert!(row["unsupported"].as_array().unwrap().is_empty(), "{name}: {row}");
        }
    }
    assert_eq!(report["totals"]["bodies"], 25);
    assert_eq!(report["totals"]["lowered"], 22);
    assert_eq!(report["totals"]["spliced"], 22);
    let module = deserialize_module(&rfs::read("ir/index_divergence.trust-ir.bin")).unwrap();
    let interpreter = Interpreter::with_module(&module);
    let u = |v| InterpretValue::int(Ty::Usize, v).unwrap();
    let mut cases = vec![
        ("array_base_constant", vec![], 7),
        ("array_index_break", vec![], 7),
        ("both_diverge", vec![], 7),
        ("slice_return_empty", vec![], 7),
        ("slice_break_empty", vec![], 7),
        ("conditional_empty", vec![InterpretValue::bool(true)], 7),
        ("conditional_values", vec![InterpretValue::bool(true), u(99)], 7),
    ];
    for i in [0, 99] {
        for name in ["array_base_dynamic", "slice_base_dynamic", "array_base_break", "slice_base_break"] {
            cases.push((name, vec![u(i)], 7));
        }
    }
    for (i, value) in [(0, 3), (1, 5)] {
        for name in ["ordinary_array", "ordinary_slice_values", "inner_array_loop", "inner_slice_values"] {
            cases.push((name, vec![u(i)], value));
        }
        cases.push(("conditional_values", vec![InterpretValue::bool(false), u(i)], value));
    }
    for (name, args, value) in cases {
        let functions: Vec<_> = module.functions.iter()
            .filter(|f| f.display_path.as_deref() == Some(name)).collect();
        assert_eq!(functions.len(), 1, "{name}");
        let result = interpreter.execute_func(functions[0].id, args).unwrap();
        assert_eq!(result.host_calls, 0, "{name}");
        assert_eq!(result.returns, vec![InterpretValue::int(Ty::U32, value).unwrap()], "{name}");
    }
    for (name, args) in [
        ("ordinary_array", vec![u(99)]),
        ("ordinary_slice_values", vec![u(99)]),
        ("ordinary_slice_empty", vec![]),
        ("inner_array_loop", vec![u(99)]),
        ("inner_slice_values", vec![u(99)]),
        ("trapping_base", vec![]),
        ("conditional_empty", vec![InterpretValue::bool(false)]),
        ("conditional_values", vec![InterpretValue::bool(false), u(99)]),
    ] {
        let f = module.functions.iter().find(|f| f.display_path.as_deref() == Some(name)).unwrap();
        let error = interpreter.execute_func(f.id, args).unwrap_err();
        assert_eq!(error.code, InterpretErrorCode::Panic, "{name}: {error:?}");
        assert!(error.to_string().contains("index out of bounds"), "{name}: {error:?}");
    }
}
