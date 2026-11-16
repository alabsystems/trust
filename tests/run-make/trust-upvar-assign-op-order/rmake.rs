//! A captured scalar compound assignment evaluates its RHS before reading the capture.
//@ ignore-cross-compile

use run_make_support::{cmd, rfs, rustc_path, serde_json, trust_ir};
use trust_ir::reference;
mod closure_body;
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
        format!("{}\n{}", rfs::read_to_string("subject.rs"), rfs::read_to_string("native_assertions.rs")),
    );
    cmd(rustc_path())
        .args([
            "native.rs", "--edition=2024", "-Ztrust-verify=off", "-Ztrust-ir-lower=off",
            "-Coverflow-checks=on", "-Copt-level=0", "-o", "native",
        ])
        .run();
    cmd("./native").run();
    assert!(
        cmd("./native").arg("creates-overflow").run_fail().stderr_utf8()
            .contains("attempt to add with overflow")
    );
    cmd(rustc_path())
        .args([
            "subject.rs", "--edition=2024", "--crate-type=lib", "--crate-name=upvar_order",
            "--emit=metadata", "-Coverflow-checks=on", "-Copt-level=0", "-Zthreads=1",
            "-Ztrust-verify=off", "-Ztrust-ir-lower=on", "-Ztrust-ir-flip=no", "-Ztrust-dump=ir:ir",
            "-o", "subject.rmeta",
        ])
        .run();
    let report: serde_json::Value =
        serde_json::from_slice(&rfs::read("ir/upvar_order.coverage.json")).unwrap();
    assert_eq!(report["proof_authority"], false);
    assert_eq!(report["native_verification_requests"], false);
    let names = [
        "by_ref_capture", "by_value_capture", "rhs_removes_overflow",
        "rhs_creates_overflow", "unchanged_control",
    ];
    let rows = report["bodies"].as_array().unwrap();
    assert_eq!(rows.len(), 2 * names.len(), "every wrapper and closure must be inspected");
    for name in names {
        let path = format!("{name}::{{closure#0}}");
        let closure: Vec<_> = rows.iter().filter(|row| row["def_path"] == path).collect();
        assert_eq!(closure.len(), 1, "missing/duplicate closure {path}");
        assert_eq!(closure[0]["lowered"], true, "{path}: {}", closure[0]);
        assert!(closure[0]["unsupported"].as_array().unwrap().is_empty());
        let wrapper: Vec<_> = rows.iter().filter(|row| row["def_path"] == name).collect();
        assert_eq!(wrapper.len(), 1, "missing/duplicate wrapper {name}");
        assert_eq!(wrapper[0]["lowered"], true, "{name}: {}", wrapper[0]);
        assert!(wrapper[0]["unsupported"].as_array().unwrap().is_empty(),
            "{name}: {}", wrapper[0]);
    }
    let module = deserialize_module(&rfs::read("ir/upvar_order.trust-ir.bin")).unwrap();
    let mut outcomes = Vec::new();
    for (name, ty, initial, expected) in [
        ("by_ref_capture", Ty::U32, 1, Some(11)),
        ("by_value_capture", Ty::U32, 1, Some(11)),
        ("rhs_removes_overflow", Ty::U8, 255, Some(1)),
        ("rhs_creates_overflow", Ty::U8, 0, None),
        ("unchanged_control", Ty::U32, 1, Some(2)),
    ] {
        let (extended, caller) = closure_body::caller(&module, name, ty.clone(), initial);
        let actual = Interpreter::with_module(&extended).execute_func(caller, []);
        let agrees = match (&actual, expected) {
            (Ok(result), Some(value)) => result.host_calls == 0
                && result.returns == vec![InterpretValue::int(ty.clone(), value).unwrap()],
            (Err(error), None) => error.code == InterpretErrorCode::Panic,
            _ => false,
        };
        outcomes.push((name, agrees, format!("closure body: {actual:?}")));
        let wrappers: Vec<_> = module.functions.iter()
            .filter(|f| f.display_path.as_deref() == Some(name)).collect();
        assert_eq!(wrappers.len(), 1, "missing/duplicate whole wrapper {name}");
        let result = Interpreter::with_module(&module).execute_func(wrappers[0].id, []);
        let agrees = match (&result, expected) {
            (Ok(result), Some(value)) => result.host_calls == 0
                && result.returns == vec![InterpretValue::int(ty.clone(), value).unwrap()],
            (Err(error), None) => error.code == InterpretErrorCode::Panic,
            _ => false,
        };
        outcomes.push((name, agrees, format!("whole wrapper: {result:?}")));
    }
    for (name, agrees, actual) in &outcomes {
        println!("{name}: match={agrees} actual={actual}");
    }
    assert_eq!(outcomes.len(), 2 * names.len());
    assert!(outcomes.iter().all(|(_, agrees, _)| *agrees), "{outcomes:#?}");
}
