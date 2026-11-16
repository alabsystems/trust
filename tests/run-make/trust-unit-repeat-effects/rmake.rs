//! Unit repeats evaluate their operand once, including zero and large counts.
//! The direct producer retains effects, traps, divergence, and unsupported asm.
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
    for mode in ["assert", "oob", "zero", "dynamic"] {
        let failed = cmd("./native").arg(mode).run_fail();
        assert!(failed.stderr_utf8().contains(if mode == "assert" {
            "assertion failed: flag"
        } else {
            "index out of bounds"
        }));
    }
    let output = cmd(rustc_path())
        .args([
            "subject.rs",
            "--edition=2024",
            "--crate-type=lib",
            "--crate-name=unit_repeats",
            "--emit=metadata",
            "-Coverflow-checks=on",
            "-Copt-level=0",
            "-Zthreads=1",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=on",
            "-Ztrust-ir-flip=no",
            "-Ztrust-dump=ir:ir",
            "-o",
            "unit_repeats.rmeta",
        ])
        .run();
    assert!(!output.stderr_utf8().contains("final Trust-IR module validation failed"));
    let coverage: serde_json::Value =
        serde_json::from_slice(&rfs::read("ir/unit_repeats.coverage.json")).unwrap();
    assert_eq!(coverage["proof_authority"], false);
    let positive = [
        "once",
        "zero",
        "looped",
        "branches",
        "nested",
        "many",
        "early_return",
        "from_named",
        "indexed",
        "checked",
        "one",
        "indexed_dynamic",
        "index_base_and_index",
        "unit_oob",
        "unit_zero_index",
        "array_reassign_during_index",
        "rest",
        "local_slice_len",
        "inline_slice_len",
    ];
    let refused = ["asm_refused", "asm_then_return_refused"];
    let rows = coverage["bodies"].as_array().unwrap();
    let function_rows: Vec<_> = rows.iter().filter(|row| row["kind"] == "fn").collect();
    assert_eq!(function_rows.len(), positive.len() + refused.len(), "{rows:?}");
    let text = trust_ir::by_display_path(&rfs::read_to_string("ir/unit_repeats.trust-ir.txt"));
    for name in positive {
        let found: Vec<_> = function_rows.iter().filter(|row| row["def_path"] == name).collect();
        assert_eq!(found.len(), 1, "{name}: {rows:?}");
        let row = found[0];
        assert_eq!(row["lowered"], true, "{name}: {row}");
        assert_eq!(row["spliced"], true, "{name}: {row}");
        assert_eq!(row["symbolic"], false, "{name}: {row}");
        assert!(row["unsupported"].as_array().unwrap().is_empty(), "{name}: {row}");
        let verdict = row["differentials"]["interpreter"]["verdict"].as_str().unwrap();
        if ["checked", "unit_oob", "unit_zero_index", "rest", "local_slice_len", "inline_slice_len"]
            .contains(&name)
        {
            // Keep the original call/layout oracle limitation. Actual IR execution
            // below checks these bodies without relabeling NotRun as agreement.
            assert!(matches!(verdict, "agreed" | "not-run"), "{name}: {row}");
        } else {
            assert_eq!(verdict, "agreed", "{name}: {row}");
        }
        if verdict == "agreed" {
            assert!(row["differentials"]["interpreter"]["samples"].as_u64().unwrap() > 0);
        }
        let header = format!("fn @{name}(");
        let body = text
            .split_once(&header)
            .expect("exact emitted function")
            .1
            .split_once("\n}\n")
            .expect("complete function")
            .0;
        assert!(!body.contains("undef"), "{name}: {body}");
        if name == "many" {
            assert!(
                row["instr_count"].as_u64().unwrap() < 64,
                "unit payload must not be expanded once per element: {row}"
            );
        }
    }
    for name in refused {
        let found: Vec<_> = function_rows.iter().filter(|row| row["def_path"] == name).collect();
        assert_eq!(found.len(), 1, "{name}: {rows:?}");
        assert_eq!(found[0]["lowered"], false, "{name}: {}", found[0]);
        assert!(
            found[0]["unsupported"]
                .as_array()
                .unwrap()
                .iter()
                .any(|reason| reason[0] == "InlineAsm"),
            "{name}: {}",
            found[0]
        );
    }
    // Freeze the complete source-body denominator, including each count.
    let mut constants = vec!["UNIT".to_owned()];
    for owner in positive.iter().chain(refused.iter()) {
        let count =
            if ["nested", "early_return", "array_reassign_during_index", "asm_then_return_refused"]
                .contains(owner)
            {
                2
            } else {
                1
            };
        for index in 0..count {
            constants.push(format!("{owner}::{{constant#{index}}}"));
        }
    }
    assert_eq!(rows.len(), positive.len() + refused.len() + constants.len(), "{rows:?}");
    let mut observed_constants = Vec::new();
    for row in rows.iter().filter(|row| row["kind"] != "fn") {
        let name = row["def_path"].as_str().unwrap();
        observed_constants.push(name.to_owned());
        assert_eq!(row["lowered"], true, "{row}");
        assert_eq!(row["symbolic"], false, "{row}");
        assert!(row["unsupported"].as_array().unwrap().is_empty(), "{row}");
    }
    constants.sort();
    observed_constants.sort();
    assert_eq!(observed_constants, constants);

    let module = deserialize_module(&rfs::read("ir/unit_repeats.trust-ir.bin")).unwrap();
    let interpreter = Interpreter::with_module(&module);
    let function = |name: &str| {
        let matches: Vec<_> =
            module.functions.iter().filter(|f| f.display_path.as_deref() == Some(name)).collect();
        assert_eq!(matches.len(), 1, "{name}");
        matches[0].id
    };
    let evaluate = |name: &str, args: Vec<InterpretValue>, expected: u32| {
        let result = interpreter.execute_func(function(name), args).unwrap();
        assert_eq!(result.host_calls, 0, "{name}");
        assert_eq!(
            result.returns,
            vec![InterpretValue::int(Ty::U32, expected as i128).unwrap()],
            "{name}"
        );
    };
    for (name, expected) in [
        ("once", 1),
        ("zero", 1),
        ("looped", 3),
        ("nested", 3),
        ("many", 1),
        ("early_return", 7),
        ("from_named", 1),
        ("indexed", 1),
        ("one", 1),
        ("index_base_and_index", 2),
        ("array_reassign_during_index", 1),
        ("rest", 12),
        ("local_slice_len", 14),
        ("inline_slice_len", 14),
    ] {
        evaluate(name, vec![], expected);
    }
    evaluate("branches", vec![InterpretValue::bool(true)], 2);
    evaluate("branches", vec![InterpretValue::bool(false)], 5);
    evaluate("checked", vec![InterpretValue::bool(true)], 1);
    for index in [0, 3] {
        evaluate("indexed_dynamic", vec![InterpretValue::int(Ty::Usize, index).unwrap()], 3);
    }
    for name in ["unit_oob", "unit_zero_index"] {
        assert_eq!(
            interpreter.execute_func(function(name), []).unwrap_err().code,
            InterpretErrorCode::Panic
        );
    }
    assert_eq!(
        interpreter
            .execute_func(function("indexed_dynamic"), [InterpretValue::int(Ty::Usize, 4).unwrap()])
            .unwrap_err()
            .code,
        InterpretErrorCode::Panic
    );
    assert_eq!(
        interpreter
            .execute_func(function("checked"), [InterpretValue::bool(false)])
            .unwrap_err()
            .code,
        InterpretErrorCode::UnsupportedCall
    );
}
