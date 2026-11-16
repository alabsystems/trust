//! A conditional pointer selection keeps its read, write and lifetime facts.
//! Compare the actual emitted IR with native values; escaping frame pointers
//! and casting a shared selection into a write must remain explicit refusals.
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
            "--crate-name=reference_joins",
            "--emit=metadata",
            "-Coverflow-checks=on",
            "-Copt-level=0",
            "-Zthreads=1",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=on",
            "-Ztrust-ir-flip=no",
            "-Ztrust-dump=ir:ir",
            "-o",
            "reference_joins.rmeta",
        ])
        .run();
    let coverage: serde_json::Value =
        serde_json::from_slice(&rfs::read("ir/reference_joins.coverage.json")).unwrap();
    assert_eq!(coverage["proof_authority"], false);
    let rows = coverage["bodies"].as_array().unwrap();
    let mut expected = vec![
        "scalar_write",
        "field_write",
        "shared_read",
        "choose_shared",
        "returned_shared",
        "choose_mut",
        "returned_mut",
        "one_live_arm",
        "nested_write",
        "static_or_caller",
        "mixed_outlives",
        "raw_direct",
        "raw_join",
        "shared_from_mut_join",
        "readonly_join_write",
        "raw_from_caller",
        "raw_from_references",
        "raw_mixed_origin",
        "local_or_caller",
        "mixed_frame",
        "raw_local_or_caller",
    ];
    let mut observed: Vec<_> = rows.iter().map(|row| row["def_path"].as_str().unwrap()).collect();
    expected.sort();
    observed.sort();
    assert_eq!(observed, expected);
    let refused = [
        "raw_direct",
        "raw_join",
        "readonly_join_write",
        "raw_mixed_origin",
        "raw_local_or_caller",
    ];
    for row in rows {
        let name = row["def_path"].as_str().unwrap();
        if refused.contains(&name) {
            assert_eq!(row["lowered"], false, "{name}: {row}");
            assert!(!row["unsupported"].as_array().unwrap().is_empty(), "{name}: {row}");
        } else {
            assert_eq!(row["lowered"], true, "{name}: {row}");
            assert!(row["unsupported"].as_array().unwrap().is_empty(), "{name}: {row}");
            assert!(
                matches!(
                    row["differentials"]["interpreter"]["verdict"].as_str(),
                    Some("agreed" | "not-run")
                ),
                "{name}: {row}"
            );
        }
    }
    let module = deserialize_module(&rfs::read("ir/reference_joins.trust-ir.bin")).unwrap();
    let interpreter = Interpreter::with_module(&module);
    let evaluate = |name: &str, args: Vec<InterpretValue>, expected: u32| {
        let f = module.functions.iter().find(|f| f.display_path.as_deref() == Some(name)).unwrap();
        let result = interpreter.execute_func(f.id, args).unwrap();
        assert_eq!(result.host_calls, 0, "{name}");
        assert_eq!(
            result.returns,
            vec![InterpretValue::int(Ty::U32, expected as i128).unwrap()],
            "{name}"
        );
    };
    for flag in [true, false] {
        let args = || vec![InterpretValue::bool(flag)];
        for name in ["scalar_write", "field_write", "returned_mut"] {
            evaluate(name, args(), if flag { 42 } else { 15 });
        }
        for name in ["shared_read", "returned_shared", "shared_from_mut_join"] {
            evaluate(name, args(), if flag { 1 } else { 2 });
        }
        evaluate("one_live_arm", args(), if flag { 22 } else { 4 });
        evaluate("mixed_outlives", args(), if flag { 99 } else { 1 });
        evaluate("mixed_frame", args(), if flag { 7 } else { 2 });
    }
    for (a, b, expected) in
        [(true, true, 423), (true, false, 153), (false, true, 126), (false, false, 126)]
    {
        evaluate("nested_write", vec![InterpretValue::bool(a), InterpretValue::bool(b)], expected);
    }
}
