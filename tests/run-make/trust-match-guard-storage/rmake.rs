//! Guard assignments survive successful and failed matching paths.
//! The ordinary MIR oracle refuses synthetic shallow borrows; compare the actual
//! emitted IR with native assertions while retaining its original NotRun rows.
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
    let native = format!(
        "{}\n{}",
        rfs::read_to_string("subject.rs"),
        rfs::read_to_string("native_assertions.rs")
    );
    rfs::write("native.rs", native);
    cmd(rustc_path())
        .args([
            "native.rs",
            "--edition=2024",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=off",
            "-Coverflow-checks=on",
            "-Copt-level=0",
            "-o",
            "native",
        ])
        .run();
    cmd("./native").run();
    let trap = cmd("./native").arg("trap").run_fail();
    assert!(trap.stderr_utf8().contains("assertion failed: flag"));
    let overflow = cmd("./native").arg("overflow").run_fail();
    assert!(overflow.stderr_utf8().contains("attempt to add with overflow"));
    assert!(
        cmd("./native")
            .arg("unit-overflow")
            .run_fail()
            .stderr_utf8()
            .contains("attempt to add with overflow")
    );
    cmd(rustc_path())
        .args([
            "subject.rs",
            "--edition=2024",
            "--crate-type=lib",
            "--crate-name=guard_storage",
            "--emit=metadata",
            "-Coverflow-checks=on",
            "-Copt-level=0",
            "-Zthreads=1",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=on",
            "-Ztrust-ir-flip=no",
            "-Ztrust-dump=ir:ir",
            "-o",
            "guard_storage.rmeta",
        ])
        .run();
    let coverage: serde_json::Value =
        serde_json::from_slice(&rfs::read("ir/guard_storage.coverage.json")).unwrap();
    assert_eq!(coverage["proof_authority"], false);
    let positive = [
        "literal_true",
        "literal_false",
        "catch_all",
        "chained_guards",
        "case_then_catch",
        "guard_then_range",
        "looped",
        "guard_local_shadow",
        "mutable_parameter",
        "checked_guard",
        "array_guard",
        "successive_matches",
        "nested_guard",
        "array_guard_rhs",
        "array_guard_overflow",
        "unit_guard",
        "unit_guard_rhs_assignment",
        "unit_guard_rhs_overflow",
        "unrelated_guard_shadow",
        "ssa_cast_base",
        "promoted_cast_base",
        "guard_cast_base",
        "cast_rhs_replaces_base",
    ];
    let rows = coverage["bodies"].as_array().unwrap();
    assert_eq!(rows.len(), 29, "{rows:?}");
    let text = trust_ir::by_display_path(&rfs::read_to_string("ir/guard_storage.trust-ir.txt"));
    for name in positive {
        let found: Vec<_> =
            rows.iter().filter(|r| r["kind"] == "fn" && r["def_path"] == name).collect();
        assert_eq!(found.len(), 1, "{name}: {rows:?}");
        let row = found[0];
        assert_eq!(row["lowered"], true, "{name}: {row}");
        assert_eq!(row["spliced"], true, "{name}: {row}");
        assert_eq!(row["symbolic"], false, "{name}: {row}");
        assert!(row["unsupported"].as_array().unwrap().is_empty(), "{name}: {row}");
        let verdict = row["differentials"]["interpreter"]["verdict"].as_str().unwrap();
        assert!(matches!(verdict, "agreed" | "not-run"), "{name}: {row}");
        let header = format!("fn @{name}(");
        let body =
            text.split_once(&header).expect("emitted function").1.split_once("\n}\n").unwrap().0;
        assert!(!body.contains("undef"), "{name}: {body}");
    }
    let mut constants: Vec<_> = rows
        .iter()
        .filter(|r| r["kind"] != "fn")
        .map(|r| {
            assert_eq!(r["lowered"], true, "{r}");
            assert!(r["unsupported"].as_array().unwrap().is_empty());
            r["def_path"].as_str().unwrap().to_owned()
        })
        .collect();
    constants.sort();
    let mut expected: Vec<_> =
        ["ssa_cast_base", "promoted_cast_base", "guard_cast_base", "cast_rhs_replaces_base"]
            .iter()
            .map(|n| format!("{n}::{{constant#0}}"))
            .collect();
    expected.sort();
    assert_eq!(constants, expected);
    let refused: Vec<_> = rows.iter().filter(|r| r["def_path"] == "asm_refused").collect();
    assert_eq!(refused.len(), 1);
    assert_eq!(refused[0]["lowered"], false);
    assert!(refused[0]["unsupported"].as_array().unwrap().iter().any(|r| r[0] == "InlineAsm"));
    let oob: Vec<_> = rows.iter().filter(|r| r["def_path"] == "array_guard_oob_refused").collect();
    assert_eq!(oob.len(), 1);
    assert_eq!(oob[0]["lowered"], false);
    assert!(
        oob[0]["unsupported"]
            .as_array()
            .unwrap()
            .iter()
            .any(|r| r[0] == "AssignOp(non-local place)")
    );
    let module = deserialize_module(&rfs::read("ir/guard_storage.trust-ir.bin")).unwrap();
    let interpreter = Interpreter::with_module(&module);
    let evaluate = |name: &str, args: Vec<InterpretValue>, expected: u32| {
        let found: Vec<_> =
            module.functions.iter().filter(|f| f.display_path.as_deref() == Some(name)).collect();
        assert_eq!(found.len(), 1, "exact function {name}");
        let result =
            interpreter.execute_func(found[0].id, args).unwrap_or_else(|e| panic!("{name}: {e:?}"));
        assert_eq!(result.host_calls, 0);
        assert_eq!(
            result.returns,
            vec![InterpretValue::int(Ty::U32, expected as i128).unwrap()],
            "{name}"
        );
    };
    for (name, expected) in [
        ("literal_true", 16),
        ("literal_false", 33),
        ("chained_guards", 33),
        ("looped", 2),
        ("guard_local_shadow", 14),
        ("array_guard", 10),
        ("successive_matches", 12),
        ("nested_guard", 4),
        ("array_guard_rhs", 18),
        ("unit_guard", 7),
        ("unit_guard_rhs_assignment", 7),
        ("unrelated_guard_shadow", 7),
        ("ssa_cast_base", 1),
        ("promoted_cast_base", 1),
        ("guard_cast_base", 1),
        ("cast_rhs_replaces_base", 7),
    ] {
        evaluate(name, vec![], expected);
    }
    evaluate("checked_guard", vec![InterpretValue::bool(true)], 6);
    for x in [0u32, 1, 7, 42, u32::MAX] {
        let input = || vec![InterpretValue::int(Ty::U32, x as i128).unwrap()];
        evaluate("catch_all", input(), 2 + 2 * (x & 7));
        evaluate("case_then_catch", input(), if x == 0 { 66 } else { 44 + (x & 7) });
        evaluate("guard_then_range", input(), if x <= 3 { 12 } else { 22 });
        evaluate("mutable_parameter", input(), x & 7);
    }
    let overflow = module
        .functions
        .iter()
        .find(|f| f.display_path.as_deref() == Some("array_guard_overflow"))
        .unwrap();
    assert_eq!(
        interpreter.execute_func(overflow.id, []).unwrap_err().code,
        InterpretErrorCode::Panic
    );
    let unit_overflow = module
        .functions
        .iter()
        .find(|f| f.display_path.as_deref() == Some("unit_guard_rhs_overflow"))
        .unwrap();
    assert_eq!(
        interpreter.execute_func(unit_overflow.id, []).unwrap_err().code,
        InterpretErrorCode::Panic
    );
    let checked = module
        .functions
        .iter()
        .find(|f| f.display_path.as_deref() == Some("checked_guard"))
        .unwrap();
    assert_eq!(
        interpreter.execute_func(checked.id, [InterpretValue::bool(false)]).unwrap_err().code,
        // Explicit assert! calls the bodyless core panic declaration today.
        // Keep that refusal visible; the array-overflow case above is an IR panic.
        InterpretErrorCode::UnsupportedCall
    );
}
