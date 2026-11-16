//! Temporary projection writes preserve effects, early exits and checked arithmetic.
//! Drop instructions remain explicit; their presence is not a destructor-execution proof.
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
            "native.rs", "--edition=2024", "-Ztrust-verify=off", "-Ztrust-ir-lower=off",
            "-Coverflow-checks=on", "-o", "native",
        ])
        .run();
    cmd("./native").run();
    for arg in ["hidden-drop", "hidden-drop-copy", "borrowed-drop", "borrowed-drop-copy"] {
        assert!(cmd("./native").arg(arg).run_fail().stderr_utf8().contains("drop ran"));
    }
    for arg in ["if-overflow", "match-overflow", "loop-overflow", "call-overflow", "index-overflow"] {
        assert!(
            cmd("./native").arg(arg).run_fail().stderr_utf8().contains("attempt to add with overflow")
        );
    }
    cmd(rustc_path())
        .args([
            "subject.rs", "--edition=2024", "--crate-type=lib", "--crate-name=projection_effects",
            "--emit=metadata", "-Coverflow-checks=on", "-Copt-level=0", "-Zthreads=1",
            "-Ztrust-verify=off", "-Ztrust-ir-lower=on", "-Ztrust-ir-flip=no", "-Ztrust-dump=ir:ir",
            "-o", "projection_effects.rmeta",
        ])
        .run();
    let coverage: serde_json::Value =
        serde_json::from_slice(&rfs::read("ir/projection_effects.coverage.json")).unwrap();
    assert_eq!(coverage["proof_authority"], false);
    let rows = coverage["bodies"].as_array().unwrap();
    let mut observed: Vec<_> = rows.iter().map(|row| row["def_path"].as_str().unwrap()).collect();
    let mut expected = vec![
        "union_write", "union_copy_write", "<Bomb as std::ops::Drop>::drop",
        "hidden_drop", "hidden_drop_copy", "borrowed_drop_temporary", "borrowed_drop_copy",
        "nested_reference_compound", "copied_deref_block", "copied_deref_value",
        "rhs_returns", "rhs_returns::{constant#0}", "base_returns", "base_returns::{constant#0}",
        "index_returns", "read_index_returns", "index_conditionally_returns", "mixed_branch_returns", "if_overflow", "match_overflow",
        "loop_overflow", "make_max", "call_overflow", "literal_array_order",
        "<Pair as std::clone::Clone>::clone",
    ];
    observed.sort();
    expected.sort();
    assert_eq!(observed, expected);
    let module = deserialize_module(&rfs::read("ir/projection_effects.trust-ir.bin")).unwrap();
    let interpreter = Interpreter::with_module(&module);
    for (name, value, args) in [
        ("copied_deref_block", 1, vec![]),
        ("copied_deref_value", 1, vec![]),
        ("rhs_returns", 7, vec![]),
        ("base_returns", 7, vec![]),
        ("index_returns", 7, vec![]),
        ("read_index_returns", 7, vec![]),
        ("index_conditionally_returns", 7, vec![InterpretValue::bool(true)]),
        ("mixed_branch_returns", 7, vec![InterpretValue::bool(true)]),
        ("mixed_branch_returns", 1, vec![InterpretValue::bool(false)]),
        ("literal_array_order", 123, vec![]),
    ] {
        let row = rows.iter().find(|row| row["def_path"] == name).unwrap();
        assert_eq!(row["lowered"], true, "{name}: {row}");
        assert!(row["unsupported"].as_array().unwrap().is_empty(), "{name}: {row}");
        let f = module.functions.iter().find(|f| f.display_path.as_deref() == Some(name)).unwrap();
        let result = interpreter.execute_func(f.id, args).unwrap();
        assert_eq!(result.host_calls, 0, "{name}");
        assert_eq!(result.returns, vec![InterpretValue::int(Ty::U32, value).unwrap()], "{name}");
    }
    for name in ["if_overflow", "match_overflow", "loop_overflow", "call_overflow"] {
        let row = rows.iter().find(|row| row["def_path"] == name).unwrap();
        assert_eq!(row["lowered"], true, "{name}: {row}");
        assert!(row["unsupported"].as_array().unwrap().is_empty(), "{name}: {row}");
        let f = module.functions.iter().find(|f| f.display_path.as_deref() == Some(name)).unwrap();
        assert_eq!(interpreter.execute_func(f.id, []).unwrap_err().code, InterpretErrorCode::Panic);
    }
    let conditional = module.functions.iter()
        .find(|f| f.display_path.as_deref() == Some("index_conditionally_returns")).unwrap();
    assert_eq!(
        interpreter.execute_func(conditional.id, [InterpretValue::bool(false)]).unwrap_err().code,
        InterpretErrorCode::Panic
    );
    for name in ["union_write", "union_copy_write", "nested_reference_compound"] {
        let row = rows.iter().find(|row| row["def_path"] == name).unwrap();
        assert_eq!(row["lowered"], false, "{name}: {row}");
        assert!(!row["unsupported"].as_array().unwrap().is_empty(), "{name}: {row}");
    }
    for name in ["hidden_drop", "hidden_drop_copy", "borrowed_drop_temporary", "borrowed_drop_copy"] {
        let row = rows.iter().find(|row| row["def_path"] == name).unwrap();
        if row["lowered"] == false {
            assert!(!row["unsupported"].as_array().unwrap().is_empty(), "{name}: {row}");
            continue;
        }
        let f = module.functions.iter().find(|f| f.display_path.as_deref() == Some(name)).unwrap();
        assert!(
            f.blocks.iter().flat_map(|b| b.body.iter()).any(|n| matches!(n.inst, Inst::Drop { .. })),
            "{name} lost its observable destruction"
        );
        assert_eq!(row["differentials"]["interpreter"]["verdict"], "not-run", "{name}: {row}");
        // A resolved destructor may reproduce the native panic. An unresolved
        // Drop must explicitly refuse, never become a successful no-op.
        let error = interpreter.execute_func(f.id, []).unwrap_err();
        if error.code != InterpretErrorCode::Panic {
            assert_eq!(error.code, InterpretErrorCode::UnsupportedInstruction, "{name}: {error:?}");
            assert!(error.to_string().contains("no drop_glue row"), "{name}: {error:?}");
        }
    }
}
