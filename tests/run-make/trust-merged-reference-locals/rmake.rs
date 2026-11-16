//! Reference locals keep their permissions and origin across branch parameters.
//@ ignore-cross-compile

use run_make_support::{cmd, rfs, rustc_path, serde_json, trust_ir};
use trust_ir::reference::Ty;
use trust_ir::reference::binary::deserialize_module;
use trust_ir::reference::interpret::{InterpretValue, Interpreter};

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
    cmd(rustc_path())
        .args([
            "subject.rs",
            "--edition=2024",
            "--crate-type=lib",
            "--crate-name=merged_references",
            "--emit=metadata",
            "-Coverflow-checks=on",
            "-Copt-level=0",
            "-Zthreads=1",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=on",
            "-Ztrust-ir-flip=no",
            "-Ztrust-dump=ir:ir",
            "-o",
            "merged_references.rmeta",
        ])
        .run();
    let coverage: serde_json::Value =
        serde_json::from_slice(&rfs::read("ir/merged_references.coverage.json")).unwrap();
    assert_eq!(coverage["proof_authority"], false);
    let rows = coverage["bodies"].as_array().unwrap();
    let ordinary = [
        "assigned_if",
        "assigned_bool_match",
        "assigned_int_match",
        "assigned_str_match",
        "assigned_float_match",
        "assigned_enum_match",
        "assigned_and",
        "assigned_or",
        "assigned_if_let",
        "assigned_fresh",
        "assigned_integer_tuple",
        "assigned_shadow",
        "assigned_destructure",
        "assigned_nested",
        "returned_mut_value",
    ];
    let conversions = [
        ("bool_from_u8", Ty::U8),
        ("bool_from_u16", Ty::U16),
        ("bool_from_u32", Ty::U32),
        ("bool_from_u64", Ty::U64),
        ("bool_from_u128", Ty::U128),
        ("bool_from_usize", Ty::Usize),
        ("bool_from_i8", Ty::I8),
        ("bool_from_i16", Ty::I16),
        ("bool_from_i32", Ty::I32),
        ("bool_from_i64", Ty::I64),
        ("bool_from_i128", Ty::I128),
        ("bool_from_isize", Ty::Isize),
    ];
    let refused = [
        ("assigned_tuple_match", "TupleMatch(bool literal field)"),
        ("raw_direct", "Return(borrow ptr escapes tail)"),
        ("raw_local_join", "Join(raw pointer borrow lifetime)"),
        ("raw_mixed", "Join(mixed pointer provenance)"),
    ];
    let extra = [
        "shared_fresh",
        "returned_shared_value",
        "assigned_one_reaching",
        "returned_mut",
        "returned_shared",
        "shared_from_mut",
        "raw_from_caller",
        "dead_fresh",
        "dead_changed",
        "dead_read_before",
        "dead_forwarded",
        "bool_from_argument_effect",
        "bool_from_callee_effect",
        "bool_from_ordered_effects",
        "from",
        "named_from_control",
    ];
    let extra_refused = [
        "escape_forwarded",
        "rb_escape",
        "rb_escape_shared",
        "rb_escape_or",
        "raw_live_read",
    ];
    let mut expected: Vec<_> = ordinary
        .iter()
        .chain(extra.iter())
        .copied()
        .chain(conversions.iter().map(|(name, _)| *name))
        .chain(refused.iter().map(|(name, _)| *name))
        .chain(extra_refused)
        .collect();
    let mut observed: Vec<_> = rows
        .iter()
        .map(|row| row["def_path"].as_str().unwrap())
        .collect();
    expected.sort();
    observed.sort();
    assert_eq!(observed, expected);
    for row in rows {
        let name = row["def_path"].as_str().unwrap();
        if let Some((_, reason)) = refused.iter().find(|(refused, _)| *refused == name) {
            assert_eq!(row["lowered"], false, "{name}: {row}");
            assert!(
                row["unsupported"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(|tag| tag[0].as_str() == Some(*reason)),
                "{name}: {row}"
            );
        } else if extra_refused.contains(&name) {
            assert_eq!(row["lowered"], false, "{name}: {row}");
            assert!(
                !row["unsupported"].as_array().unwrap().is_empty(),
                "{name}: {row}"
            );
        } else {
            assert_eq!(row["lowered"], true, "{name}: {row}");
            assert!(
                row["unsupported"].as_array().unwrap().is_empty(),
                "{name}: {row}"
            );
            assert!(
                matches!(
                    row["differentials"]["interpreter"]["verdict"].as_str(),
                    Some("agreed" | "not-run")
                ),
                "{name}: {row}"
            );
        }
    }
    let module = deserialize_module(&rfs::read("ir/merged_references.trust-ir.bin")).unwrap();
    let effects: serde_json::Value =
        serde_json::from_slice(&rfs::read("ir/merged_references.effect-conservation.json"))
            .unwrap();
    assert_eq!(effects["schema"], "trust.effect-conservation.v1");
    let effects = effects["functions"].as_array().unwrap();
    for name in conversions.iter().map(|(name, _)| *name).chain([
        "assigned_int_match",
        "bool_from_argument_effect",
        "bool_from_callee_effect",
        "bool_from_ordered_effects",
    ]) {
        let row = effects.iter().find(|row| row["def_path"] == name).unwrap();
        assert_eq!(row["verdict"], "conserved", "{name}: {row}");
        assert_eq!(row["equivalences"]["bool-from-integer"], 1, "{name}: {row}");
    }
    for name in ["from", "named_from_control"] {
        let row = effects.iter().find(|row| row["def_path"] == name).unwrap();
        assert_eq!(row["verdict"], "conserved", "{name}: {row}");
        assert!(
            row["equivalences"].get("bool-from-integer").is_none(),
            "{name}: {row}"
        );
    }
    let interpreter = Interpreter::with_module(&module);
    let evaluate = |name: &str, flag: bool, expected: u32| {
        let f = module
            .functions
            .iter()
            .find(|f| f.display_path.as_deref() == Some(name))
            .unwrap();
        let result = interpreter
            .execute_func(f.id, vec![InterpretValue::bool(flag)])
            .unwrap();
        assert_eq!(result.host_calls, 0, "{name}");
        assert_eq!(
            result.returns,
            vec![InterpretValue::int(Ty::U32, expected as i128).unwrap()],
            "{name}"
        );
    };
    for flag in [false, true] {
        for (name, ty) in &conversions {
            let function = module
                .functions
                .iter()
                .find(|f| f.display_path.as_deref() == Some(*name))
                .unwrap();
            let result = interpreter
                .execute_func(function.id, vec![InterpretValue::bool(flag)])
                .unwrap();
            assert_eq!(result.host_calls, 0, "{name}");
            assert_eq!(
                result.returns,
                vec![InterpretValue::int(ty.clone(), i128::from(u8::from(flag))).unwrap()],
                "{name}"
            );
        }
        for name in ordinary {
            evaluate(name, flag, if flag { 112 } else { 1102 });
        }
        evaluate("shared_fresh", flag, if flag { 2 } else { 1 });
        evaluate("shared_from_mut", flag, if flag { 2 } else { 1 });
        evaluate("returned_shared_value", flag, if flag { 2 } else { 1 });
        evaluate("assigned_one_reaching", flag, if flag { 112 } else { 7 });
        evaluate("dead_fresh", flag, u32::from(flag));
        evaluate("dead_changed", flag, 7);
        evaluate("dead_read_before", flag, 1);
        evaluate("dead_forwarded", flag, 7);
        evaluate("bool_from_argument_effect", flag, 7 + u32::from(flag));
        evaluate("bool_from_callee_effect", flag, 11 + u32::from(flag));
        evaluate("bool_from_ordered_effects", flag, 120 + u32::from(flag));
        evaluate("from", flag, if flag { 7 } else { 9 });
        evaluate("named_from_control", flag, if flag { 7 } else { 9 });
    }
}
