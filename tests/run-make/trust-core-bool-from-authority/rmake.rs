//! Language and diagnostic attributes in a dependency do not authenticate core.
//@ ignore-cross-compile

use run_make_support::{cmd, rfs, rustc_path, serde_json, trust_ir};
use trust_ir::reference::Ty;
use trust_ir::reference::binary::deserialize_module;
use trust_ir::reference::interpret::{InterpretValue, Interpreter};

fn dump_ir(source: &str, name: &str, extra: &[&str]) {
    cmd(rustc_path())
        .args([
            source,
            "--crate-type=lib",
            "--edition=2021",
            "--emit=metadata",
            "-Copt-level=0",
            "-Zthreads=1",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=on",
            "-Ztrust-ir-flip=no",
            "-Ztrust-dump=ir:ir",
        ])
        .arg(format!("--crate-name={name}"))
        .args(extra)
        .run();
}

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }
    cmd(rustc_path())
        .args([
            "fake_core.rs",
            "--crate-name=core",
            "--crate-type=rlib",
            "--edition=2021",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=off",
            "-o",
            "libfake_core.rlib",
        ])
        .run();
    // The executable semantics of the counterfeit implementation are 42,
    // regardless of its bool argument. This is an oracle, not production IR.
    cmd(rustc_path())
        .args([
            "subject.rs",
            "--crate-name=counterfeit",
            "--crate-type=lib",
            "--edition=2021",
            "--extern=core=libfake_core.rlib",
            "--emit=llvm-ir",
            "-Copt-level=3",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=off",
            "-o",
            "native.ll",
        ])
        .run();
    assert!(rfs::read_to_string("native.ll").contains("ret i32 42"));

    // Judge the no-core counterexample before the independent sysroot control.
    dump_ir("subject.rs", "counterfeit", &["--extern=core=libfake_core.rlib"]);

    let effects: serde_json::Value = serde_json::from_slice(&rfs::read(
        "ir/counterfeit.effect-conservation.json",
    ))
    .unwrap();
    let rows = effects["functions"].as_array().unwrap();
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0]["verdict"], "conserved");
    assert!(rows[0]["equivalences"].get("bool-from-integer").is_none());
    let counterfeit =
        deserialize_module(&rfs::read("ir/counterfeit.trust-ir.bin")).unwrap();
    let function = counterfeit
        .functions
        .iter()
        .find(|f| f.display_path.as_deref() == Some("counterfeit_from"))
        .unwrap();
    for flag in [false, true] {
        let error = Interpreter::with_module(&counterfeit)
            .execute_func(function.id, vec![InterpretValue::bool(flag)])
            .err()
            .expect("the foreign call must be retained, not replaced by a bool cast");
        assert!(format!("{error:?}").contains("UnsupportedCall"), "{error:?}");
    }

    dump_ir("genuine.rs", "genuine", &[]);
    let effects: serde_json::Value =
        serde_json::from_slice(&rfs::read("ir/genuine.effect-conservation.json")).unwrap();
    let rows = effects["functions"].as_array().unwrap();
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0]["verdict"], "conserved");
    assert_eq!(rows[0]["equivalences"]["bool-from-integer"], 1);
    let genuine = deserialize_module(&rfs::read("ir/genuine.trust-ir.bin")).unwrap();
    let function = genuine
        .functions
        .iter()
        .find(|f| f.display_path.as_deref() == Some("genuine_from"))
        .unwrap();
    for flag in [false, true] {
        let result = Interpreter::with_module(&genuine)
            .execute_func(function.id, vec![InterpretValue::bool(flag)])
            .unwrap();
        assert_eq!(result.host_calls, 0);
        assert_eq!(
            result.returns,
            vec![InterpretValue::int(Ty::U32, i128::from(flag)).unwrap()]
        );
    }
}
